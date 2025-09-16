const std = @import("std");
const ast = @import("ast_v2.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const Loc = @import("lexer.zig").Token.Loc;

pub const CheckerV2 = struct {
    gpa: std.mem.Allocator,
    diags: *Diagnostics,

    func_stack: std.ArrayListUnmanaged(FunctionCtx) = .{},
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},
    warned_meta: bool = false,

    pub fn init(gpa: std.mem.Allocator, diags: *Diagnostics) CheckerV2 {
        return .{ .gpa = gpa, .diags = diags };
    }

    pub fn deinit(self: *@This()) void {
        self.func_stack.deinit(self.gpa);
        self.loop_stack.deinit(self.gpa);
    }

    pub fn run(self: *@This(), a: *const ast.Ast) !void {
        const decl_ids = a.exprs.decl_pool.slice(a.unit.decls);
        for (decl_ids) |did| {
            const row = a.exprs.Decl.get(did.toRaw());
            try self.checkDecl(a, row);
        }
    }

    const FunctionCtx = struct { has_result: bool };
    const LoopCtx = struct { label: ast.OptStrId };

    fn pushFunc(self: *@This(), has_result: bool) !void {
        try self.func_stack.append(self.gpa, .{ .has_result = has_result });
    }
    fn popFunc(self: *@This()) void {
        if (self.func_stack.items.len > 0) _ = self.func_stack.pop();
    }
    fn inFunction(self: *const @This()) bool {
        return self.func_stack.items.len > 0;
    }
    fn currentFunc(self: *const @This()) ?FunctionCtx {
        if (self.func_stack.items.len == 0) return null;
        return self.func_stack.items[self.func_stack.items.len - 1];
    }

    fn pushLoop(self: *@This(), label: ast.OptStrId) !void {
        try self.loop_stack.append(self.gpa, .{ .label = label });
    }
    fn popLoop(self: *@This()) void {
        if (self.loop_stack.items.len > 0) _ = self.loop_stack.pop();
    }
    fn inLoop(self: *const @This()) bool {
        return self.loop_stack.items.len > 0;
    }

    fn locOf(_: *const @This(), a: *const ast.Ast, lid: ast.LocId) Loc {
        return a.exprs.locs.get(lid);
    }

    fn checkDecl(self: *@This(), a: *const ast.Ast, d: ast.Rows.Decl) !void {
        if (!d.ty.isNone()) try self.checkExpr(a, d.ty.unwrap());
        try self.checkExpr(a, d.value);
        if (!d.pattern.isNone()) try self.checkPattern(a, d.pattern.unwrap());
    }

    fn checkStmt(self: *@This(), a: *const ast.Ast, sid: ast.StmtId) !void {
        const kind = a.stmts.index.kinds.items[sid.toRaw()];
        switch (kind) {
            .Expr => {
                const row = a.stmts.get(.Expr, sid);
                try self.checkExpr(a, row.expr);
            },
            .Decl => {
                const row = a.stmts.get(.Decl, sid);
                const drow = a.exprs.Decl.get(row.decl.toRaw());
                try self.checkDecl(a, drow);
            },
            .Assign => {
                const row = a.stmts.get(.Assign, sid);
                try self.checkExpr(a, row.left);
                try self.checkExpr(a, row.right);
            },
            .Insert => {
                const row = a.stmts.get(.Insert, sid);
                if (!self.warned_meta) {
                    _ = self.diags.addNote(self.locOf(a, row.loc), "checker_v2: insert not expanded yet; walking only", .{}) catch {};
                    self.warned_meta = true;
                }
                try self.checkExpr(a, row.expr);
            },
            .Return => {
                const row = a.stmts.get(.Return, sid);
                if (!self.inFunction()) {
                    try self.diags.addError(self.locOf(a, row.loc), "'return' used outside of a function", .{});
                } else {
                    const f = self.currentFunc().?;
                    if (!f.has_result and !row.value.isNone())
                        try self.diags.addError(self.locOf(a, row.loc), "return with a value in a void function", .{});
                    if (f.has_result and row.value.isNone())
                        try self.diags.addError(self.locOf(a, row.loc), "missing return value", .{});
                    if (!row.value.isNone()) try self.checkExpr(a, row.value.unwrap());
                }
            },
            .Break => {
                const row = a.stmts.get(.Break, sid);
                if (!self.inLoop()) try self.diags.addError(self.locOf(a, row.loc), "'break' used outside of a loop", .{});
                if (!row.value.isNone()) try self.checkExpr(a, row.value.unwrap());
            },
            .Continue => {
                const row = a.stmts.get(.Continue, sid);
                if (!self.inLoop()) try self.diags.addError(self.locOf(a, row.loc), "'continue' used outside of a loop", .{});
            },
            .Unreachable => {},
            .Defer => {
                const row = a.stmts.get(.Defer, sid);
                if (!self.inFunction()) try self.diags.addError(self.locOf(a, row.loc), "'defer' only valid inside a function", .{});
                try self.checkExpr(a, row.expr);
            },
            .ErrDefer => {
                const row = a.stmts.get(.ErrDefer, sid);
                if (!self.inFunction()) try self.diags.addError(self.locOf(a, row.loc), "'errdefer' only valid inside a function", .{});
                try self.checkExpr(a, row.expr);
            },
        }
    }

    fn checkBlock(self: *@This(), a: *const ast.Ast, id: ast.ExprId) !void {
        const b = a.exprs.get(.Block, id);
        const stmts = a.stmts.stmt_pool.slice(b.items);
        for (stmts) |sid| try self.checkStmt(a, sid);
    }

    fn checkExpr(self: *@This(), a: *const ast.Ast, id: ast.ExprId) anyerror!void {
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
                    _ = self.diags.addNote(self.locOf(a, r.loc), "checker_v2: comptime not executed; walking only", .{}) catch {};
                    self.warned_meta = true;
                }
                try self.checkExpr(a, r.block);
            },
            .CodeBlock => {
                const r = a.exprs.get(.CodeBlock, id);
                if (!self.warned_meta) {
                    _ = self.diags.addNote(self.locOf(a, r.loc), "checker_v2: code block not executed; walking only", .{}) catch {};
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
                    _ = self.diags.addNote(self.locOf(a, r.loc), "checker_v2: insert not expanded yet; walking only", .{}) catch {};
                    self.warned_meta = true;
                }
                try self.checkExpr(a, r.expr);
            },
            .Return => {
                // also appears as expr in some tree shapes
                const r = a.exprs.get(.Return, id);
                if (!self.inFunction()) {
                    try self.diags.addError(self.locOf(a, r.loc), "'return' used outside of a function", .{});
                } else {
                    const f = self.currentFunc().?;
                    if (!f.has_result and !r.value.isNone())
                        try self.diags.addError(self.locOf(a, r.loc), "return with a value in a void function", .{});
                    if (f.has_result and r.value.isNone())
                        try self.diags.addError(self.locOf(a, r.loc), "missing return value", .{});
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
                if (!self.inLoop()) try self.diags.addError(self.locOf(a, r.loc), "'break' used outside of a loop", .{});
                if (!r.value.isNone()) try self.checkExpr(a, r.value.unwrap());
            },
            .Continue => {
                const r = a.exprs.get(.Continue, id);
                if (!self.inLoop()) try self.diags.addError(self.locOf(a, r.loc), "'continue' used outside of a loop", .{});
            },
            .Unreachable => {},
            .NullLit, .UndefLit => {},
            .Defer => {
                const r = a.exprs.get(.Defer, id);
                if (!self.inFunction()) try self.diags.addError(self.locOf(a, r.loc), "'defer' only valid inside a function", .{});
                try self.checkExpr(a, r.expr);
            },
            .ErrDefer => {
                const r = a.exprs.get(.ErrDefer, id);
                if (!self.inFunction()) try self.diags.addError(self.locOf(a, r.loc), "'errdefer' only valid inside a function", .{});
                try self.checkExpr(a, r.expr);
            },
            .ErrUnwrap => { const r = a.exprs.get(.ErrUnwrap, id); try self.checkExpr(a, r.expr); },
            .OptionalUnwrap => { const r = a.exprs.get(.OptionalUnwrap, id); try self.checkExpr(a, r.expr); },
            .Await => { const r = a.exprs.get(.Await, id); try self.checkExpr(a, r.expr); },
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
            .Cast => { const r = a.exprs.get(.Cast, id); try self.checkExpr(a, r.expr); try self.checkExpr(a, r.ty); },
            .Catch => { const r = a.exprs.get(.Catch, id); try self.checkExpr(a, r.expr); try self.checkExpr(a, r.handler); },
            .Import => { const r = a.exprs.get(.Import, id); try self.checkExpr(a, r.expr); },
            .TypeOf => { const r = a.exprs.get(.TypeOf, id); try self.checkExpr(a, r.expr); },

            // Types in expression position: just walk contained expressions
            .TupleType => { const r = a.exprs.get(.TupleType, id); const es = a.exprs.expr_pool.slice(r.elems); for (es) |eid| try self.checkExpr(a, eid); },
            .ArrayType => {
                const r = a.exprs.get(.ArrayType, id);
                try self.checkExpr(a, r.elem);
                try self.checkExpr(a, r.size);
                if (!self.isIntLiteral(a, r.size)) {
                    try self.diags.addError(self.locOf(a, r.loc), "array size must be an integer literal", .{});
                }
            },
            .DynArrayType => { const r = a.exprs.get(.DynArrayType, id); try self.checkExpr(a, r.elem); },
            .MapType => { const r = a.exprs.get(.MapType, id); try self.checkExpr(a, r.key); try self.checkExpr(a, r.value); },
            .SliceType => { const r = a.exprs.get(.SliceType, id); try self.checkExpr(a, r.elem); },
            .OptionalType => { const r = a.exprs.get(.OptionalType, id); try self.checkExpr(a, r.elem); },
            .ErrorSetType => { const r = a.exprs.get(.ErrorSetType, id); try self.checkExpr(a, r.err); try self.checkExpr(a, r.value); },
            .StructType => {
                const r = a.exprs.get(.StructType, id);
                var seen = std.AutoHashMap(u32, void).init(self.gpa);
                defer seen.deinit();
                const fs = a.exprs.sfield_pool.slice(r.fields);
                for (fs) |fid| {
                    const f = a.exprs.StructField.get(fid.toRaw());
                    const key = f.name.toRaw();
                    if (seen.contains(key)) {
                        try self.diags.addError(self.locOf(a, f.loc), "duplicate field '{s}'", .{a.exprs.strs.get(f.name)});
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
                        try self.diags.addError(self.locOf(a, f.loc), "duplicate enum field '{s}'", .{a.exprs.strs.get(f.name)});
                    } else _ = seen.put(key, {}) catch {};
                    if (!f.value.isNone()) try self.checkExpr(a, f.value.unwrap());
                }
                if (!r.discriminant.isNone()) {
                    const did = r.discriminant.unwrap();
                    try self.checkExpr(a, did);
                    if (!self.isIntLiteral(a, did)) {
                        try self.diags.addWarning(self.locOf(a, r.loc), "enum discriminant should be an integer literal", .{});
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
                        if (kind == .VariantType) {
                            try self.diags.addError(self.locOf(a, f.loc), "duplicate variant '{s}'", .{nm});
                        } else {
                            try self.diags.addError(self.locOf(a, f.loc), "duplicate error variant '{s}'", .{nm});
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
                        try self.diags.addError(self.locOf(a, f.loc), "duplicate field '{s}'", .{a.exprs.strs.get(f.name)});
                    } else _ = seen.put(key, {}) catch {};
                    try self.checkExpr(a, f.ty);
                    if (!f.value.isNone()) try self.checkExpr(a, f.value.unwrap());
                }
            },
            .PointerType => { const r = a.exprs.get(.PointerType, id); try self.checkExpr(a, r.elem); },
            .SimdType => {
                const r = a.exprs.get(.SimdType, id);
                try self.checkExpr(a, r.elem);
                try self.checkExpr(a, r.lanes);
                if (!self.isIntLiteral(a, r.lanes)) {
                    try self.diags.addError(self.locOf(a, r.loc), "SIMD lanes must be an integer literal", .{});
                }
            },
            .ComplexType => { const r = a.exprs.get(.ComplexType, id); try self.checkExpr(a, r.elem); },
            .TensorType => {
                const r = a.exprs.get(.TensorType, id);
                try self.checkExpr(a, r.elem);
                const shape = a.exprs.expr_pool.slice(r.shape);
                for (shape) |eid2| {
                    try self.checkExpr(a, eid2);
                    if (!self.isIntLiteral(a, eid2)) {
                        try self.diags.addError(self.locOf(a, r.loc), "tensor dimension must be an integer literal", .{});
                    }
                }
            },
            .TypeType, .AnyType, .NoreturnType => {},
        }
    }

    fn isIntLiteral(self: *const @This(), a: *const ast.Ast, id: ast.ExprId) bool {
        _ = self;
        const k = a.exprs.index.kinds.items[id.toRaw()];
        if (k != .Literal) return false;
        const row = a.exprs.get(.Literal, id);
        return row.kind == .int;
    }

    fn checkPattern(self: *@This(), a: *const ast.Ast, id: ast.PatternId) anyerror!void {
        const kind = a.pats.index.kinds.items[id.toRaw()];
        switch (kind) {
            .Wildcard => {},
            .Literal => { const r = a.pats.get(.Literal, id); try self.checkExpr(a, r.expr); },
            .Path => {},
            .Binding => {},
            .Tuple => { const r = a.pats.get(.Tuple, id); const ids = a.pats.pat_pool.slice(r.elems); for (ids) |pid| try self.checkPattern(a, pid); },
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
            .VariantTuple => { const r = a.pats.get(.VariantTuple, id); const ids = a.pats.pat_pool.slice(r.elems); for (ids) |pid| try self.checkPattern(a, pid); },
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
            .Or => { const r = a.pats.get(.Or, id); const ids = a.pats.pat_pool.slice(r.alts); for (ids) |pid| try self.checkPattern(a, pid); },
            .At => { const r = a.pats.get(.At, id); try self.checkPattern(a, r.pattern); },
        }
    }
};
