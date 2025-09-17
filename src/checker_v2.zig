const std = @import("std");
const ast = @import("ast_v2.zig");
const infer = @import("infer_v2.zig");
const Diagnostics = @import("diagnostics_v2.zig").Diagnostics;
const Loc = @import("lexer.zig").Token.Loc;
const symbols = @import("symbols_v2.zig");
const types = @import("types_v2.zig");

pub const CheckerV2 = struct {
    gpa: std.mem.Allocator,
    diags: *Diagnostics,
    // typing state (merged typer)
    symtab: symbols.SymbolStore = undefined,
    t_bool: types.TypeId = undefined,
    t_i32: types.TypeId = undefined,
    t_f64: types.TypeId = undefined,
    t_string: types.TypeId = undefined,
    t_void: types.TypeId = undefined,
    t_any: types.TypeId = undefined,

    func_stack: std.ArrayListUnmanaged(FunctionCtx) = .{},
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},
    warned_meta: bool = false,

    pub fn init(gpa: std.mem.Allocator, diags: *Diagnostics) CheckerV2 {
        return .{ .gpa = gpa, .diags = diags, .symtab = symbols.SymbolStore.init(gpa) };
    }

    pub fn deinit(self: *CheckerV2) void {
        self.func_stack.deinit(self.gpa);
        self.loop_stack.deinit(self.gpa);
        self.symtab.deinit();
    }

    pub fn runWithTypes(self: *CheckerV2, a: *const ast.Ast) !infer.TypeInfoV2 {
        var info = infer.TypeInfoV2.init(self.gpa);
        const expr_len: usize = a.exprs.index.kinds.items.len;
        const decl_len: usize = a.exprs.Decl.list.len;
        try info.expr_types.appendNTimes(self.gpa, null, expr_len);
        try info.decl_types.appendNTimes(self.gpa, null, decl_len);

        // cache builtins
        self.t_bool = info.store.tBool();
        self.t_i32 = info.store.tI32();
        self.t_f64 = info.store.tF64();
        self.t_string = info.store.tString();
        self.t_void = info.store.tVoid();
        self.t_any = info.store.tAny();

        // push root scope
        _ = try self.symtab.push(null);
        defer self.symtab.pop();

        const decl_ids = a.exprs.decl_pool.slice(a.unit.decls);
        for (decl_ids) |did| {
            try self.visitDecl(&info, a, did);
        }
        return info;
    }

    // Primary API: run checker (with typing) and return the produced TypeInfoV2 by value.
    // Caller owns the returned value and must deinit it when done.
    pub fn run(self: *CheckerV2, a: *const ast.Ast) !infer.TypeInfoV2 {
        return self.runWithTypes(a);
    }

    const FunctionCtx = struct { has_result: bool };
    const LoopCtx = struct { label: ast.OptStrId };

    fn pushFunc(self: *CheckerV2, has_result: bool) !void {
        try self.func_stack.append(self.gpa, .{ .has_result = has_result });
    }
    fn popFunc(self: *CheckerV2) void {
        if (self.func_stack.items.len > 0) _ = self.func_stack.pop();
    }
    fn inFunction(self: *const CheckerV2) bool {
        return self.func_stack.items.len > 0;
    }
    fn currentFunc(self: *const CheckerV2) ?FunctionCtx {
        if (self.func_stack.items.len == 0) return null;
        return self.func_stack.items[self.func_stack.items.len - 1];
    }

    fn pushLoop(self: *CheckerV2, label: ast.OptStrId) !void {
        try self.loop_stack.append(self.gpa, .{ .label = label });
    }
    fn popLoop(self: *CheckerV2) void {
        if (self.loop_stack.items.len > 0) _ = self.loop_stack.pop();
    }
    fn inLoop(self: *const CheckerV2) bool {
        return self.loop_stack.items.len > 0;
    }

    fn locOf(_: *const CheckerV2, a: *const ast.Ast, lid: ast.LocId) Loc {
        return a.exprs.locs.get(lid);
    }

    fn checkDecl(self: *CheckerV2, a: *const ast.Ast, d: ast.Rows.Decl) !void {
        _ = self;
        _ = a;
        _ = d;
    }

    fn checkStmt(self: *CheckerV2, a: *const ast.Ast, sid: ast.StmtId) !void {
        _ = self;
        _ = a;
        _ = sid;
    }

    fn checkBlock(self: *CheckerV2, a: *const ast.Ast, id: ast.ExprId) !void {
        _ = self;
        _ = a;
        _ = id;
    }

    fn checkExpr(self: *CheckerV2, a: *const ast.Ast, id: ast.ExprId) anyerror!void {
        const kind = a.exprs.index.kinds.items[id.toRaw()];
        switch (kind) {
            .Literal, .Ident => {},

            // simple unary/binary
            .Unary => {
                const r = a.exprs.get(.Unary, id);
                try self.checkExpr(a, r.expr);
            },
            .Binary => {
                const r = a.exprs.get(.Binary, id);
                try self.checkExpr(a, r.left);
                try self.checkExpr(a, r.right);
                // Type errors are reported from typeOfBinary when runWithTypes is used
            },
            .Range => {
                const r = a.exprs.get(.Range, id);
                if (!r.start.isNone()) try self.checkExpr(a, r.start.unwrap());
                if (!r.end.isNone()) try self.checkExpr(a, r.end.unwrap());
            },
            .Deref => {
                const r = a.exprs.get(.Deref, id);
                try self.checkExpr(a, r.expr);
            },
            .ArrayLit => {
                const r = a.exprs.get(.ArrayLit, id);
                const elems = a.exprs.expr_pool.slice(r.elems);
                for (elems) |eid| try self.checkExpr(a, eid);
            },
            .TupleLit => {
                const r = a.exprs.get(.TupleLit, id);
                const elems = a.exprs.expr_pool.slice(r.elems);
                for (elems) |eid| try self.checkExpr(a, eid);
            },
            .MapLit => {
                const r = a.exprs.get(.MapLit, id);
                const kvs = a.exprs.kv_pool.slice(r.entries);
                for (kvs) |kid| {
                    const kv = a.exprs.KeyValue.get(kid.toRaw());
                    try self.checkExpr(a, kv.key);
                    try self.checkExpr(a, kv.value);
                }
            },
            .StructLit => {
                const r = a.exprs.get(.StructLit, id);
                const fids = a.exprs.sfv_pool.slice(r.fields);
                for (fids) |fid| {
                    const f = a.exprs.StructFieldValue.get(fid.toRaw());
                    try self.checkExpr(a, f.value);
                }
            },
            .VariantLit => {
                const r = a.exprs.get(.VariantLit, id);
                if (!r.value.isNone()) try self.checkExpr(a, r.value.unwrap());
            },
            .EnumLit => {
                const r = a.exprs.get(.EnumLit, id);
                if (!r.value.isNone()) try self.checkExpr(a, r.value.unwrap());
            },
            .Call => {
                const r = a.exprs.get(.Call, id);
                try self.checkExpr(a, r.callee);
                const args = a.exprs.expr_pool.slice(r.args);
                for (args) |eid| try self.checkExpr(a, eid);
            },
            .IndexAccess => {
                const r = a.exprs.get(.IndexAccess, id);
                try self.checkExpr(a, r.collection);
                try self.checkExpr(a, r.index);
            },
            .FieldAccess => {
                const r = a.exprs.get(.FieldAccess, id);
                try self.checkExpr(a, r.parent);
            },
            .FunctionLit => {
                const f = a.exprs.get(.FunctionLit, id);
                // params
                const params = a.exprs.param_pool.slice(f.params);
                for (params) |pid| {
                    const p = a.exprs.Param.get(pid.toRaw());
                    if (!p.pat.isNone()) try self.checkPattern(a, p.pat.unwrap());
                    if (!p.ty.isNone()) try self.checkExpr(a, p.ty.unwrap());
                    if (!p.value.isNone()) try self.checkExpr(a, p.value.unwrap());
                }
                if (!f.result_ty.isNone()) try self.checkExpr(a, f.result_ty.unwrap());
                if (!f.body.isNone()) {
                    try self.pushFunc(!f.result_ty.isNone());
                    defer self.popFunc();
                    try self.checkExpr(a, f.body.unwrap());
                }
            },
            .Block => try self.checkBlock(a, id),

            .ComptimeBlock => {
                const r = a.exprs.get(.ComptimeBlock, id);
                if (!self.warned_meta) {
                    // _ = self.diags.addNote(self.locOf(a, r.loc), "checker_v2: comptime not executed; walking only", .{}) catch {};
                    _ = self.diags.addNote(self.locOf(a, r.loc), .checker_comptime_not_executed, .{}) catch {};
                    self.warned_meta = true;
                }
                try self.checkExpr(a, r.block);
            },
            .CodeBlock => {
                const r = a.exprs.get(.CodeBlock, id);
                if (!self.warned_meta) {
                    // _ = self.diags.addNote(self.locOf(a, r.loc), "checker_v2: code block not executed; walking only", .{}) catch {};
                    _ = self.diags.addNote(self.locOf(a, r.loc), .checker_code_block_not_executed, .{}) catch {};
                    self.warned_meta = true;
                }
                try self.checkExpr(a, r.block);
            },
            .AsyncBlock => {
                const r = a.exprs.get(.AsyncBlock, id);
                try self.checkExpr(a, r.body);
            },
            .MlirBlock => {},

            .Insert => {
                const r = a.exprs.get(.Insert, id);
                if (!self.warned_meta) {
                    _ = self.diags.addNote(self.locOf(a, r.loc), .checker_insert_not_expanded, .{}) catch {};
                    self.warned_meta = true;
                }
                try self.checkExpr(a, r.expr);
            },
            .Return => {
                // also appears as expr in some tree shapes
                const r = a.exprs.get(.Return, id);
                if (!self.inFunction()) {
                    try self.diags.addError(self.locOf(a, r.loc), .return_outside_function, .{});
                } else {
                    const f = self.currentFunc().?;
                    if (!f.has_result and !r.value.isNone())
                        try self.diags.addError(self.locOf(a, r.loc), .return_value_in_void_function, .{});
                    if (f.has_result and r.value.isNone())
                        try self.diags.addError(self.locOf(a, r.loc), .missing_return_value, .{});
                    if (!r.value.isNone()) try self.checkExpr(a, r.value.unwrap());
                }
            },
            .If => {
                const r = a.exprs.get(.If, id);
                try self.checkExpr(a, r.cond);
                try self.checkExpr(a, r.then_block);
                if (!r.else_block.isNone()) try self.checkExpr(a, r.else_block.unwrap());
            },
            .While => {
                const r = a.exprs.get(.While, id);
                if (!r.cond.isNone()) try self.checkExpr(a, r.cond.unwrap());
                try self.pushLoop(r.label);
                defer self.popLoop();
                try self.checkExpr(a, r.body);
            },
            .For => {
                const r = a.exprs.get(.For, id);
                try self.checkPattern(a, r.pattern);
                try self.checkExpr(a, r.iterable);
                try self.pushLoop(r.label);
                defer self.popLoop();
                try self.checkExpr(a, r.body);
            },
            .Match => {
                const m = a.exprs.get(.Match, id);
                try self.checkExpr(a, m.expr);
                const arms = a.exprs.arm_pool.slice(m.arms);
                for (arms) |aid| {
                    const arm = a.exprs.MatchArm.get(aid.toRaw());
                    try self.checkPattern(a, arm.pattern);
                    if (!arm.guard.isNone()) try self.checkExpr(a, arm.guard.unwrap());
                    try self.checkExpr(a, arm.body);
                }
            },

            .Break => {
                const r = a.exprs.get(.Break, id);
                // if (!self.inLoop()) try self.diags.addError(self.locOf(a, r.loc), "'break' used outside of a loop", .{});
                if (!self.inLoop()) {
                    try self.diags.addError(self.locOf(a, r.loc), .break_outside_loop, .{});
                }
                if (!r.value.isNone()) try self.checkExpr(a, r.value.unwrap());
            },
            .Continue => {
                const r = a.exprs.get(.Continue, id);
                // if (!self.inLoop()) try self.diags.addError(self.locOf(a, r.loc), "'continue' used outside of a loop", .{});
                if (!self.inLoop()) {
                    try self.diags.addError(self.locOf(a, r.loc), .continue_outside_loop, .{});
                }
            },
            .Unreachable => {},
            .NullLit, .UndefLit => {},
            .Defer => {
                const r = a.exprs.get(.Defer, id);
                // if (!self.inFunction()) try self.diags.addError(self.locOf(a, r.loc), "'defer' only valid inside a function", .{});
                if (!self.inFunction()) try self.diags.addError(self.locOf(a, r.loc), .defer_outside_function, .{});
                try self.checkExpr(a, r.expr);
            },
            .ErrDefer => {
                const r = a.exprs.get(.ErrDefer, id);
                // if (!self.inFunction()) try self.diags.addError(self.locOf(a, r.loc), "'errdefer' only valid inside a function", .{});
                if (!self.inFunction()) try self.diags.addError(self.locOf(a, r.loc), .errdefer_outside_function, .{});
                try self.checkExpr(a, r.expr);
            },
            .ErrUnwrap => {
                const r = a.exprs.get(.ErrUnwrap, id);
                try self.checkExpr(a, r.expr);
            },
            .OptionalUnwrap => {
                const r = a.exprs.get(.OptionalUnwrap, id);
                try self.checkExpr(a, r.expr);
            },
            .Await => {
                const r = a.exprs.get(.Await, id);
                try self.checkExpr(a, r.expr);
            },
            .Closure => {
                const cl = a.exprs.get(.Closure, id);
                const params = a.exprs.param_pool.slice(cl.params);
                for (params) |pid| {
                    const p = a.exprs.Param.get(pid.toRaw());
                    if (!p.pat.isNone()) try self.checkPattern(a, p.pat.unwrap());
                    if (!p.ty.isNone()) try self.checkExpr(a, p.ty.unwrap());
                    if (!p.value.isNone()) try self.checkExpr(a, p.value.unwrap());
                }
                if (!cl.result_ty.isNone()) try self.checkExpr(a, cl.result_ty.unwrap());
                try self.pushFunc(!cl.result_ty.isNone());
                defer self.popFunc();
                try self.checkExpr(a, cl.body);
            },
            .Cast => {
                const r = a.exprs.get(.Cast, id);
                try self.checkExpr(a, r.expr);
                try self.checkExpr(a, r.ty);
            },
            .Catch => {
                const r = a.exprs.get(.Catch, id);
                try self.checkExpr(a, r.expr);
                try self.checkExpr(a, r.handler);
            },
            .Import => {
                const r = a.exprs.get(.Import, id);
                try self.checkExpr(a, r.expr);
            },
            .TypeOf => {
                const r = a.exprs.get(.TypeOf, id);
                try self.checkExpr(a, r.expr);
            },

            // Types in expression position: just walk contained expressions
            .TupleType => {
                const r = a.exprs.get(.TupleType, id);
                const es = a.exprs.expr_pool.slice(r.elems);
                for (es) |eid| try self.checkExpr(a, eid);
            },
            .ArrayType => {
                const r = a.exprs.get(.ArrayType, id);
                try self.checkExpr(a, r.elem);
                try self.checkExpr(a, r.size);
                if (!self.isIntLiteral(a, r.size)) {
                    // try self.diags.addError(self.locOf(a, r.loc), "array size must be an integer literal", .{});
                    try self.diags.addError(self.locOf(a, r.loc), .array_size_not_integer_literal, .{});
                }
            },
            .DynArrayType => {
                const r = a.exprs.get(.DynArrayType, id);
                try self.checkExpr(a, r.elem);
            },
            .MapType => {
                const r = a.exprs.get(.MapType, id);
                try self.checkExpr(a, r.key);
                try self.checkExpr(a, r.value);
            },
            .SliceType => {
                const r = a.exprs.get(.SliceType, id);
                try self.checkExpr(a, r.elem);
            },
            .OptionalType => {
                const r = a.exprs.get(.OptionalType, id);
                try self.checkExpr(a, r.elem);
            },
            .ErrorSetType => {
                const r = a.exprs.get(.ErrorSetType, id);
                try self.checkExpr(a, r.err);
                try self.checkExpr(a, r.value);
            },
            .StructType => {
                const r = a.exprs.get(.StructType, id);
                var seen = std.AutoHashMap(u32, void).init(self.gpa);
                defer seen.deinit();
                const fs = a.exprs.sfield_pool.slice(r.fields);
                for (fs) |fid| {
                    const f = a.exprs.StructField.get(fid.toRaw());
                    const key = f.name.toRaw();
                    if (seen.contains(key)) {
                        try self.diags.addError(self.locOf(a, f.loc), .duplicate_field, .{});
                    } else _ = seen.put(key, {}) catch {};
                    try self.checkExpr(a, f.ty);
                    if (!f.value.isNone()) try self.checkExpr(a, f.value.unwrap());
                }
            },
            .EnumType => {
                const r = a.exprs.get(.EnumType, id);
                var seen = std.AutoHashMap(u32, void).init(self.gpa);
                defer seen.deinit();
                const es = a.exprs.efield_pool.slice(r.fields);
                for (es) |eid2| {
                    const f = a.exprs.EnumField.get(eid2.toRaw());
                    const key = f.name.toRaw();
                    if (seen.contains(key)) {
                        // try self.diags.addError(self.locOf(a, f.loc), "duplicate enum field '{s}'", .{a.exprs.strs.get(f.name)});
                        try self.diags.addError(self.locOf(a, f.loc), .duplicate_enum_field, .{});
                    } else _ = seen.put(key, {}) catch {};
                    if (!f.value.isNone()) try self.checkExpr(a, f.value.unwrap());
                }
                if (!r.discriminant.isNone()) {
                    const did = r.discriminant.unwrap();
                    try self.checkExpr(a, did);
                    if (!self.isIntLiteral(a, did)) {
                        try self.diags.addWarning(self.locOf(a, r.loc), .enum_discriminant_not_integer, .{});
                    }
                }
            },
            .VariantType, .ErrorType => {
                const r = if (kind == .VariantType) a.exprs.get(.VariantType, id) else a.exprs.get(.ErrorType, id);
                var seen = std.AutoHashMap(u32, void).init(self.gpa);
                defer seen.deinit();
                const vs = a.exprs.vfield_pool.slice(r.fields);
                for (vs) |vid| {
                    const f = a.exprs.VariantField.get(vid.toRaw());
                    const key = f.name.toRaw();
                    if (seen.contains(key)) {
                        const nm = a.exprs.strs.get(f.name);
                        _ = nm;
                        if (kind == .VariantType) {
                            try self.diags.addError(self.locOf(a, f.loc), .duplicate_variant, .{});
                        } else {
                            try self.diags.addError(self.locOf(a, f.loc), .duplicate_error_variant, .{});
                        }
                    } else _ = seen.put(key, {}) catch {};
                    if (!f.value.isNone()) try self.checkExpr(a, f.value.unwrap());
                    if (!f.payload_elems.isNone()) {
                        const elems = a.exprs.expr_pool.slice(f.payload_elems.asRange());
                        for (elems) |eid2| try self.checkExpr(a, eid2);
                    }
                    if (!f.payload_fields.isNone()) {
                        const sfs = a.exprs.sfield_pool.slice(f.payload_fields.asRange());
                        for (sfs) |sfid| {
                            const sf = a.exprs.StructField.get(sfid.toRaw());
                            try self.checkExpr(a, sf.ty);
                            if (!sf.value.isNone()) try self.checkExpr(a, sf.value.unwrap());
                        }
                    }
                }
            },
            .UnionType => {
                const r = a.exprs.get(.UnionType, id);
                var seen = std.AutoHashMap(u32, void).init(self.gpa);
                defer seen.deinit();
                const fs = a.exprs.sfield_pool.slice(r.fields);
                for (fs) |fid| {
                    const f = a.exprs.StructField.get(fid.toRaw());
                    const key = f.name.toRaw();
                    if (seen.contains(key)) {
                        try self.diags.addError(self.locOf(a, f.loc), .duplicate_field, .{});
                    } else _ = seen.put(key, {}) catch {};
                    try self.checkExpr(a, f.ty);
                    if (!f.value.isNone()) try self.checkExpr(a, f.value.unwrap());
                }
            },
            .PointerType => {
                const r = a.exprs.get(.PointerType, id);
                try self.checkExpr(a, r.elem);
            },
            .SimdType => {
                const r = a.exprs.get(.SimdType, id);
                try self.checkExpr(a, r.elem);
                try self.checkExpr(a, r.lanes);
                if (!self.isIntLiteral(a, r.lanes)) {
                    try self.diags.addError(self.locOf(a, r.loc), .simd_lanes_not_integer_literal, .{});
                }
            },
            .ComplexType => {
                const r = a.exprs.get(.ComplexType, id);
                try self.checkExpr(a, r.elem);
            },
            .TensorType => {
                const r = a.exprs.get(.TensorType, id);
                try self.checkExpr(a, r.elem);
                const shape = a.exprs.expr_pool.slice(r.shape);
                for (shape) |eid2| {
                    try self.checkExpr(a, eid2);
                    if (!self.isIntLiteral(a, eid2)) {
                        try self.diags.addError(self.locOf(a, r.loc), .tensor_dimension_not_integer_literal, .{});
                    }
                }
            },
            .TypeType, .AnyType, .NoreturnType => {},
        }
    }

    fn isIntLiteral(self: *const CheckerV2, a: *const ast.Ast, id: ast.ExprId) bool {
        _ = self;
        const k = a.exprs.index.kinds.items[id.toRaw()];
        if (k != .Literal) return false;
        const row = a.exprs.get(.Literal, id);
        return row.kind == .int;
    }

    fn checkPattern(self: *CheckerV2, a: *const ast.Ast, id: ast.PatternId) anyerror!void {
        const kind = a.pats.index.kinds.items[id.toRaw()];
        switch (kind) {
            .Wildcard => {},
            .Literal => {
                const r = a.pats.get(.Literal, id);
                try self.checkExpr(a, r.expr);
            },
            .Path => {},
            .Binding => {},
            .Tuple => {
                const r = a.pats.get(.Tuple, id);
                const ids = a.pats.pat_pool.slice(r.elems);
                for (ids) |pid| try self.checkPattern(a, pid);
            },
            .Slice => {
                const r = a.pats.get(.Slice, id);
                const ids = a.pats.pat_pool.slice(r.elems);
                for (ids) |pid| try self.checkPattern(a, pid);
                if (!r.rest_binding.isNone()) try self.checkPattern(a, r.rest_binding.unwrap());
            },
            .Struct => {
                const r = a.pats.get(.Struct, id);
                const fids = a.pats.field_pool.slice(r.fields);
                for (fids) |fid| {
                    const f = a.pats.StructField.get(fid.toRaw());
                    try self.checkPattern(a, f.pattern);
                }
            },
            .VariantTuple => {
                const r = a.pats.get(.VariantTuple, id);
                const ids = a.pats.pat_pool.slice(r.elems);
                for (ids) |pid| try self.checkPattern(a, pid);
            },
            .VariantStruct => {
                const r = a.pats.get(.VariantStruct, id);
                const fids = a.pats.field_pool.slice(r.fields);
                for (fids) |fid| {
                    const f = a.pats.StructField.get(fid.toRaw());
                    try self.checkPattern(a, f.pattern);
                }
            },
            .Range => {
                const r = a.pats.get(.Range, id);
                if (!r.start.isNone()) try self.checkExpr(a, r.start.unwrap());
                if (!r.end.isNone()) try self.checkExpr(a, r.end.unwrap());
            },
            .Or => {
                const r = a.pats.get(.Or, id);
                const ids = a.pats.pat_pool.slice(r.alts);
                for (ids) |pid| try self.checkPattern(a, pid);
            },
            .At => {
                const r = a.pats.get(.At, id);
                try self.checkPattern(a, r.pattern);
            },
        }
    }

    fn primaryNameOfPattern(self: *CheckerV2, a: *const ast.Ast, pid: ast.PatternId) ast.OptStrId {
        _ = self;
        const k = a.pats.index.kinds.items[pid.toRaw()];
        return switch (k) {
            .Binding => ast.OptStrId.some(a.pats.get(.Binding, pid).name),
            .Path => blk: {
                const p = a.pats.get(.Path, pid);
                const segs = a.pats.seg_pool.slice(p.segments);
                if (segs.len == 0) break :blk ast.OptStrId.none();
                break :blk ast.OptStrId.some(a.pats.PathSeg.get(segs[segs.len - 1].toRaw()).name);
            },
            else => ast.OptStrId.none(),
        };
    }

    fn lookup(self: *CheckerV2, a: *const ast.Ast, name: ast.StrId) ?symbols.SymbolId {
        return self.symtab.lookup(a, self.symtab.currentId(), name);
    }

    fn isOptional(self: *CheckerV2, info: *infer.TypeInfoV2, id: types.TypeId) ?types.TypeId {
        _ = self;
        const k = info.store.index.kinds.items[id.toRaw()];
        if (k != .Optional) return null;
        const row = info.store.Optional.get(info.store.index.rows.items[id.toRaw()]);
        return row.elem;
    }

    fn typeOfFieldAccess(self: *CheckerV2, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) ?types.TypeId {
        const fr = a.exprs.get(.FieldAccess, id);
        const pt = self.typeOfExpr(info, a, fr.parent) catch return null;
        const ptv = pt orelse return null;
        var t = ptv;
        if (info.store.index.kinds.items[t.toRaw()] == .Ptr) t = info.store.Ptr.get(info.store.index.rows.items[t.toRaw()]).elem;
        if (fr.is_tuple and info.store.index.kinds.items[t.toRaw()] == .Tuple) {
            const rowt = info.store.Tuple.get(info.store.index.rows.items[t.toRaw()]);
            const idx = std.fmt.parseInt(usize, a.exprs.strs.get(fr.field), 10) catch return null;
            const ids = info.store.type_pool.slice(rowt.elems);
            if (idx < ids.len) return ids[idx];
        }
        return null;
    }

    fn typeOfIndexAccess(self: *CheckerV2, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) ?types.TypeId {
        const row = a.exprs.get(.IndexAccess, id);
        const ct = self.typeOfExpr(info, a, row.collection) catch return null;
        if (ct) |t| {
            const k = info.store.index.kinds.items[t.toRaw()];
            switch (k) {
                .Array => {
                    const r = info.store.Array.get(info.store.index.rows.items[t.toRaw()]);
                    return r.elem;
                },
                .Slice => {
                    const r = info.store.Slice.get(info.store.index.rows.items[t.toRaw()]);
                    return r.elem;
                },
                else => {},
            }
        }
        return null;
    }

    fn typeOfBinary(self: *CheckerV2, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) !?types.TypeId {
        const row = a.exprs.get(.Binary, id);
        const lt = try typeOfExpr(self, info, a, row.left);
        const rt = try typeOfExpr(self, info, a, row.right);
        if (lt == null or rt == null) {
            try self.diags.addError(a.exprs.locs.get(row.loc), .could_not_resolve_type, .{});
            return null;
        }
        const l = lt.?;
        const r = rt.?;
        const lk = info.store.index.kinds.items[l.toRaw()];
        const rk = info.store.index.kinds.items[r.toRaw()];
        // const op_str = binaryOpStr(row.op);
        switch (row.op) {
            .add, .sub, .mul, .div, .mod, .bit_and, .bit_or, .bit_xor, .shl, .shr => {
                if (row.op == .div) {
                    if (a.exprs.index.kinds.items[row.right.toRaw()] == .Literal) {
                        const lit = a.exprs.get(.Literal, row.right);
                        if (lit.kind == .int) {
                            const sval = if (!lit.value.isNone()) a.exprs.strs.get(lit.value.unwrap()) else "";
                            if (std.mem.eql(u8, sval, "0")) {
                                try self.diags.addError(a.exprs.locs.get(row.loc), .division_by_zero, .{});
                                return null;
                            }
                        } else if (lit.kind == .float) {
                            if (!lit.value.isNone()) {
                                const sval = a.exprs.strs.get(lit.value.unwrap());
                                const f = std.fmt.parseFloat(f64, sval) catch 1.0;
                                if (f == 0.0) {
                                    try self.diags.addError(a.exprs.locs.get(row.loc), .division_by_zero, .{});
                                    return null;
                                }
                            }
                        }
                    }
                }
                if (row.op == .mod) {
                    // only meaningful for integers; check literal zero rhs
                    if (isIntegerKind(lk) and isIntegerKind(rk)) {
                        if (a.exprs.index.kinds.items[row.right.toRaw()] == .Literal) {
                            const lit = a.exprs.get(.Literal, row.right);
                            const sval = if (!lit.value.isNone()) a.exprs.strs.get(lit.value.unwrap()) else "";
                            if (std.mem.eql(u8, sval, "0")) {
                                try self.diags.addError(a.exprs.locs.get(row.loc), .division_by_zero, .{});
                                return null;
                            }
                        }
                    }
                }
                const both_numeric = isNumericKind(lk) and isNumericKind(rk);
                const both_integer = isIntegerKind(lk) and isIntegerKind(rk);
                if (l.toRaw() == r.toRaw() and ((row.op == .add or row.op == .sub or row.op == .mul or row.op == .div) and both_numeric or
                    (row.op == .mod or row.op == .bit_and or row.op == .bit_or or row.op == .bit_xor or row.op == .shl or row.op == .shr) and both_integer)) return lt;
                try self.diags.addError(a.exprs.locs.get(row.loc), .could_not_resolve_type, .{});
                return null;
            },
            .eq, .neq, .lt, .lte, .gt, .gte => {
                if (l.toRaw() == r.toRaw()) {
                    if (row.op == .eq or row.op == .neq) return self.t_bool;
                    if (isNumericKind(lk)) return self.t_bool;
                }
                try self.diags.addError(a.exprs.locs.get(row.loc), .could_not_resolve_type, .{});
                return null;
            },
            .logical_and, .logical_or => {
                if (l.toRaw() == self.t_bool.toRaw() and r.toRaw() == self.t_bool.toRaw()) return self.t_bool;
                try self.diags.addError(a.exprs.locs.get(row.loc), .could_not_resolve_type, .{});
                return null;
            },
            .@"orelse" => {
                if (isOptional(self, info, l)) |elem| {
                    if (elem.toRaw() == r.toRaw()) return rt;
                }
                try self.diags.addError(a.exprs.locs.get(row.loc), .could_not_resolve_type, .{});
                return null;
            },
        }
        return null;
    }

    fn binaryOpStr(op: ast.BinaryOp) []const u8 {
        return switch (op) {
            .add => "+",
            .sub => "-",
            .mul => "*",
            .div => "/",
            .mod => "%",
            .shl => "<<",
            .shr => ">>",
            .bit_and => "&",
            .bit_or => "|",
            .bit_xor => "^",
            .eq => "==",
            .neq => "!=",
            .lt => "<",
            .lte => "<=",
            .gt => ">",
            .gte => ">=",
            .logical_and => "&&",
            .logical_or => "||",
            .@"orelse" => "orelse",
        };
    }

    fn unaryOpStr(op: ast.UnaryOp) []const u8 {
        return switch (op) {
            .plus => "+",
            .minus => "-",
            .address_of => "&",
            .logical_not => "!",
        };
    }

    fn isNumericKind(k: types.TypeKind) bool {
        return switch (k) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize => true,
            else => false,
        };
    }
    fn isIntegerKind(k: types.TypeKind) bool {
        return switch (k) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
            else => false,
        };
    }

    fn typeName(store: *types.TypeStore, id: types.TypeId) []const u8 {
        return switch (store.index.kinds.items[id.toRaw()]) {
            .Void => "void",
            .Bool => "bool",
            .I8 => "i8",
            .I16 => "i16",
            .I32 => "i32",
            .I64 => "i64",
            .U8 => "u8",
            .U16 => "u16",
            .U32 => "u32",
            .U64 => "u64",
            .F32 => "f32",
            .F64 => "f64",
            .Usize => "usize",
            .String => "string",
            .Any => "any",
            .Ptr => "ptr",
            .Slice => "slice",
            .Array => "array",
            .Optional => "optional",
            .Tuple => "tuple",
            .Function => "fn",
            .Struct => "struct",
        };
    }

    fn typeFromTypeExpr(self: *CheckerV2, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) anyerror!?types.TypeId {
        const k = a.exprs.index.kinds.items[id.toRaw()];
        return switch (k) {
            .Ident => blk_ident: {
                const name = a.exprs.get(.Ident, id).name;
                const s = a.exprs.strs.get(name);
                if (std.mem.eql(u8, s, "bool")) break :blk_ident info.store.tBool();
                if (std.mem.eql(u8, s, "i8")) break :blk_ident info.store.tI8();
                if (std.mem.eql(u8, s, "i16")) break :blk_ident info.store.tI16();
                if (std.mem.eql(u8, s, "i32")) break :blk_ident info.store.tI32();
                if (std.mem.eql(u8, s, "i64")) break :blk_ident info.store.tI64();
                if (std.mem.eql(u8, s, "u8")) break :blk_ident info.store.tU8();
                if (std.mem.eql(u8, s, "u16")) break :blk_ident info.store.tU16();
                if (std.mem.eql(u8, s, "u32")) break :blk_ident info.store.tU32();
                if (std.mem.eql(u8, s, "u64")) break :blk_ident info.store.tU64();
                if (std.mem.eql(u8, s, "f32")) break :blk_ident info.store.tF32();
                if (std.mem.eql(u8, s, "f64")) break :blk_ident info.store.tF64();
                if (std.mem.eql(u8, s, "usize")) break :blk_ident info.store.tUsize();
                if (std.mem.eql(u8, s, "string")) break :blk_ident info.store.tString();
                if (std.mem.eql(u8, s, "void")) break :blk_ident info.store.tVoid();
                if (std.mem.eql(u8, s, "any")) break :blk_ident info.store.tAny();
                break :blk_ident null;
            },
            .TupleType => blk_tt: {
                const row = a.exprs.get(.TupleType, id);
                const ids = a.exprs.expr_pool.slice(row.elems);
                var buf = try self.gpa.alloc(types.TypeId, ids.len);
                defer self.gpa.free(buf);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    buf[i] = (try self.typeFromTypeExpr(info, a, ids[i])) orelse break :blk_tt null;
                }
                break :blk_tt info.store.mkTuple(buf);
            },
            .ArrayType => blk_at: {
                const row = a.exprs.get(.ArrayType, id);
                const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_at null;
                var len_val: usize = 0;
                if (a.exprs.index.kinds.items[row.size.toRaw()] == .Literal) {
                    const lit = a.exprs.get(.Literal, row.size);
                    if (lit.kind == .int and !lit.value.isNone()) {
                        len_val = std.fmt.parseInt(usize, a.exprs.strs.get(lit.value.unwrap()), 10) catch 0;
                    }
                }
                break :blk_at info.store.mkArray(elem, len_val);
            },
            .DynArrayType => blk_dt: {
                const row = a.exprs.get(.DynArrayType, id);
                const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_dt null;
                break :blk_dt info.store.mkSlice(elem);
            },
            .SliceType => blk_st: {
                const row = a.exprs.get(.SliceType, id);
                const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_st null;
                break :blk_st info.store.mkSlice(elem);
            },
            .OptionalType => blk_ot: {
                const row = a.exprs.get(.OptionalType, id);
                const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_ot null;
                break :blk_ot info.store.mkOptional(elem);
            },
            .PointerType => blk_pt: {
                const row = a.exprs.get(.PointerType, id);
                const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_pt null;
                break :blk_pt info.store.mkPtr(elem, row.is_const);
            },
            .StructType => blk_sty: {
                const row = a.exprs.get(.StructType, id);
                const sfs = a.exprs.sfield_pool.slice(row.fields);
                var buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
                defer self.gpa.free(buf);
                var i: usize = 0;
                while (i < sfs.len) : (i += 1) {
                    const f = a.exprs.StructField.get(sfs[i].toRaw());
                    const ft = (try self.typeFromTypeExpr(info, a, f.ty)) orelse break :blk_sty null;
                    buf[i] = .{ .name = a.exprs.strs.get(f.name), .ty = ft };
                }
                break :blk_sty info.store.mkStruct(buf);
            },
            .FunctionLit => blk_fn: {
                const fnr = a.exprs.get(.FunctionLit, id);
                const params = a.exprs.param_pool.slice(fnr.params);
                var pbuf = try self.gpa.alloc(types.TypeId, params.len);
                defer self.gpa.free(pbuf);
                var i: usize = 0;
                while (i < params.len) : (i += 1) {
                    const p = a.exprs.Param.get(params[i].toRaw());
                    if (p.ty.isNone()) break :blk_fn null;
                    const pt = (try self.typeFromTypeExpr(info, a, p.ty.unwrap())) orelse break :blk_fn null;
                    pbuf[i] = pt;
                }
                const res = if (!fnr.result_ty.isNone()) (try self.typeFromTypeExpr(info, a, fnr.result_ty.unwrap())) else info.store.tVoid();
                if (res == null) break :blk_fn null;
                break :blk_fn info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic);
            },
            .AnyType => info.store.tAny(),
            .TypeType => null,
            else => null,
        };
    }

    fn typeOfExpr(self: *CheckerV2, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) anyerror!?types.TypeId {
        if (info.expr_types.items[id.toRaw()]) |t| return t;
        const k = a.exprs.index.kinds.items[id.toRaw()];
        const tid: ?types.TypeId = switch (k) {
            .Literal => blk: {
                const lit = a.exprs.get(.Literal, id);
                const t: types.TypeId = switch (lit.kind) {
                    .int => self.t_i32,
                    .float => self.t_f64,
                    .bool => self.t_bool,
                    .string => self.t_string,
                    .char => info.store.tU32(),
                };
                break :blk t;
            },
            .Ident => blk_id: {
                const row = a.exprs.get(.Ident, id);
                if (self.lookup(a, row.name)) |sid| {
                    const srow = self.symtab.syms.get(sid.toRaw());
                    if (!srow.origin_decl.isNone()) if (info.decl_types.items[srow.origin_decl.unwrap().toRaw()]) |dt| break :blk_id dt;
                }
                break :blk_id null;
            },
            .Binary => try self.typeOfBinary(info, a, id),
            .Unary => blk_un: {
                const ur = a.exprs.get(.Unary, id);
                const et = try typeOfExpr(self, info, a, ur.expr);
                if (et == null) break :blk_un null;
                const t = et.?;
                const tk = info.store.index.kinds.items[t.toRaw()];
                switch (ur.op) {
                    .plus, .minus => {
                        if (!isNumericKind(tk)) {
                            try self.diags.addError(a.exprs.locs.get(ur.loc), .could_not_resolve_type, .{});
                            break :blk_un null;
                        }
                        break :blk_un t;
                    },
                    .logical_not => {
                        if (t.toRaw() != self.t_bool.toRaw()) {
                            try self.diags.addError(a.exprs.locs.get(ur.loc), .could_not_resolve_type, .{});
                            break :blk_un null;
                        }
                        break :blk_un self.t_bool;
                    },
                    .address_of => {
                        break :blk_un info.store.mkPtr(t, false);
                    },
                }
            },
            .Range,
            .Deref,
            .ArrayLit,
            .TupleLit,
            .MapLit,
            .IndexAccess,
            .FieldAccess,
            .StructLit,
            .VariantLit,
            .EnumLit,
            .Call,
            .ComptimeBlock,
            .CodeBlock,
            .AsyncBlock,
            .MlirBlock,
            .Insert,
            .Return,
            .If,
            .While,
            .For,
            .Match,
            .Break,
            .Continue,
            .Unreachable,
            .NullLit,
            .UndefLit,
            .FunctionLit,
            .Block,
            .Defer,
            .ErrDefer,
            .ErrUnwrap,
            .OptionalUnwrap,
            .Await,
            .Closure,
            .Cast,
            .Catch,
            .Import,
            .TypeOf,
            => null,

            .TupleType, .ArrayType, .DynArrayType, .MapType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => self.t_any,
        };
        var out = tid;
        if (out == null and k == .IndexAccess) out = self.typeOfIndexAccess(info, a, id);
        if (out == null and k == .FieldAccess) out = self.typeOfFieldAccess(info, a, id);
        if (out) |tt| info.expr_types.items[id.toRaw()] = tt;
        return out;
    }

    fn walkStmtType(self: *CheckerV2, info: *infer.TypeInfoV2, a: *const ast.Ast, sid: ast.StmtId) !void {
        const kind = a.stmts.index.kinds.items[sid.toRaw()];
        switch (kind) {
            .Expr => {
                const row = a.stmts.get(.Expr, sid);
                _ = try typeOfExpr(self, info, a, row.expr);
            },
            .Decl => {
                const row = a.stmts.get(.Decl, sid);
                try visitDecl(self, info, a, row.decl);
            },
            .Assign => {
                const row = a.stmts.get(.Assign, sid);
                _ = try typeOfExpr(self, info, a, row.left);
                _ = try typeOfExpr(self, info, a, row.right);
            },
            .Insert => {
                const row = a.stmts.get(.Insert, sid);
                if (!self.warned_meta) {
                    _ = self.diags.addNote(a.exprs.locs.get(row.loc), .checker_insert_not_expanded, .{}) catch {};
                    self.warned_meta = true;
                }
                _ = try typeOfExpr(self, info, a, row.expr);
            },
            .Return => {
                const row = a.stmts.get(.Return, sid);
                if (!self.inFunction()) {
                    try self.diags.addError(a.exprs.locs.get(row.loc), .return_outside_function, .{});
                } else {
                    const f = self.currentFunc().?;
                    if (!f.has_result and !row.value.isNone())
                        try self.diags.addError(a.exprs.locs.get(row.loc), .return_value_in_void_function, .{});
                    if (f.has_result and row.value.isNone())
                        try self.diags.addError(a.exprs.locs.get(row.loc), .missing_return_value, .{});
                    if (!row.value.isNone()) _ = try typeOfExpr(self, info, a, row.value.unwrap());
                }
            },
            .Break => {
                const row = a.stmts.get(.Break, sid);
                if (!self.inLoop()) try self.diags.addError(a.exprs.locs.get(row.loc), .break_outside_loop, .{});
                if (!row.value.isNone()) _ = try typeOfExpr(self, info, a, row.value.unwrap());
            },
            .Continue => {
                const row = a.stmts.get(.Continue, sid);
                if (!self.inLoop()) try self.diags.addError(a.exprs.locs.get(row.loc), .continue_outside_loop, .{});
            },
            .Unreachable => {},
            .Defer => {
                const row = a.stmts.get(.Defer, sid);
                if (!self.inFunction()) try self.diags.addError(a.exprs.locs.get(row.loc), .defer_outside_function, .{});
                _ = try typeOfExpr(self, info, a, row.expr);
            },
            .ErrDefer => {
                const row = a.stmts.get(.ErrDefer, sid);
                if (!self.inFunction()) try self.diags.addError(a.exprs.locs.get(row.loc), .errdefer_outside_function, .{});
                _ = try typeOfExpr(self, info, a, row.expr);
            },
        }
    }

    fn visitDecl(self: *CheckerV2, info: *infer.TypeInfoV2, a: *const ast.Ast, did: ast.DeclId) !void {
        const d = a.exprs.Decl.get(did.toRaw());
        if (!d.pattern.isNone()) {
            const name = self.primaryNameOfPattern(a, d.pattern.unwrap());
            if (!name.isNone()) {
                _ = try self.symtab.declare(.{ .name = name.unwrap(), .kind = .Var, .loc = d.loc, .origin_decl = ast.OptDeclId.some(did), .origin_param = ast.OptParamId.none() });
            }
        }
        const rhs_ty = try self.typeOfExpr(info, a, d.value) orelse null;
        if (!d.ty.isNone()) {
            const annot_ty = try self.typeFromTypeExpr(info, a, d.ty.unwrap());
            if (annot_ty) |atid| {
                info.decl_types.items[did.toRaw()] = atid;
                if (rhs_ty) |rtid| {
                    if (rtid.toRaw() != atid.toRaw()) {
                        // potential mismatch hook
                    }
                }
            } else {
                // unresolved annotation hook
            }
        } else {
            if (rhs_ty) |rtid| info.decl_types.items[did.toRaw()] = rtid;
        }
    }
};
