const std = @import("std");
const ast = @import("ast.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const diag = @import("diagnostics.zig");
const Loc = @import("lexer.zig").Token.Loc;
const symbols = @import("symbols.zig");
const types = @import("types.zig");
const TypeInfo = types.TypeInfo;
const ImportResolver = @import("import_resolver.zig").ImportResolver;
const ModuleEntry = @import("import_resolver.zig").ModuleEntry;
const pattern_matching = @import("check_pattern_matching.zig");
const check_types = @import("check_types.zig");
const Context = @import("compile.zig").Context;

const Pipeline = @import("pipeline.zig").Pipeline;

pub const Checker = struct {
    gpa: std.mem.Allocator,
    ast_unit: *const ast.Ast,
    context: *Context,
    pipeline: *Pipeline,
    type_info: *TypeInfo,

    import_base_dir: []const u8 = ".",

    symtab: symbols.SymbolStore = undefined,

    func_stack: std.ArrayListUnmanaged(FunctionCtx) = .{},
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},
    value_ctx: std.ArrayListUnmanaged(bool) = .{},
    warned_meta: bool = false,
    warned_comptime: bool = false,
    warned_code: bool = false,

    loop_binding_stack: std.ArrayListUnmanaged(LoopBindingCtx) = .{},
    const LoopBindingCtx = struct {
        pat: ast.OptPatternId,
        subject_ty: types.TypeId,
    };

    // --------- tiny helpers (readability & consistency) ----------
    inline fn typeKind(self: *const Checker, t: types.TypeId) types.TypeKind {
        return self.context.type_store.index.kinds.items[t.toRaw()];
    }
    inline fn trow(self: *const Checker, t: types.TypeId) u32 {
        return self.context.type_store.index.rows.items[t.toRaw()];
    }
    inline fn tEq(_: *const Checker, a: types.TypeId, b: types.TypeId) bool {
        return a.toRaw() == b.toRaw();
    }
    inline fn exprKind(self: *const Checker, eid: ast.ExprId) ast.ExprKind {
        return self.ast_unit.exprs.index.kinds.items[eid.toRaw()];
    }
    inline fn exprLocFromId(self: *Checker, eid: ast.ExprId) Loc {
        const k = self.exprKind(eid);
        return switch (k) {
            inline else => |x| self.exprLoc(self.getExpr(x, eid)),
        };
    }
    inline fn exprLoc(self: *const Checker, expr: anytype) Loc {
        return self.ast_unit.exprs.locs.get(expr.loc);
    }
    inline fn getStmt(self: *const Checker, comptime K: ast.StmtKind, id: ast.StmtId) ast.StmtRowT(K) {
        return self.ast_unit.stmts.get(K, id);
    }
    inline fn getStr(self: *const Checker, sid: ast.StrId) []const u8 {
        return self.ast_unit.exprs.strs.get(sid);
    }
    inline fn getExpr(self: *const Checker, comptime K: ast.ExprKind, id: ast.ExprId) ast.RowT(K) {
        return self.ast_unit.exprs.get(K, id);
    }

    pub fn init(
        gpa: std.mem.Allocator,
        unit: *ast.Ast,
        context: *Context,
        pipeline: *Pipeline,
        type_info: *TypeInfo,
    ) Checker {
        return .{
            .gpa = gpa,
            .ast_unit = unit,
            .symtab = symbols.SymbolStore.init(gpa),
            .context = context,
            .pipeline = pipeline,
            .type_info = type_info,
        };
    }

    pub fn deinit(self: *Checker) void {
        self.func_stack.deinit(self.gpa);
        self.loop_stack.deinit(self.gpa);
        self.value_ctx.deinit(self.gpa);
        self.loop_binding_stack.deinit(self.gpa);
        self.symtab.deinit();
    }

    pub fn run(self: *Checker) !void {
        _ = try self.runWithTypes();
    }

    pub fn runWithTypes(self: *Checker) !*TypeInfo {
        // pre-allocate type slots for all exprs & decls
        const expr_len: usize = self.ast_unit.exprs.index.kinds.items.len;
        const decl_len: usize = self.ast_unit.exprs.Decl.list.len;
        try self.type_info.expr_types.appendNTimes(self.gpa, null, expr_len);
        try self.type_info.decl_types.appendNTimes(self.gpa, null, decl_len);

        // Add builtin symbols to the global scope
        _ = try self.symtab.push(null);
        defer self.symtab.pop();

        const decl_ids = self.ast_unit.exprs.decl_pool.slice(self.ast_unit.unit.decls);
        // Pre-bind all top-level declaration patterns so forward references resolve.
        for (decl_ids) |did| {
            const d = self.ast_unit.exprs.Decl.get(did.toRaw());
            try self.bindDeclPattern(did, d);
        }
        // Now type-check declarations with names available in scope
        for (decl_ids) |did| {
            try self.checkDecl(did);
        }
        return self.type_info;
    }

    fn addBuiltinTypes(self: *Checker) !void {
        _ = self;
        // Add builtin types to the symbol tablea
        // const unknown_loc = Loc{ .file = 0, .start = 0, .end = 0 };
        // const unknown_loc_id = self.ast_unit.exprs.locs.add(self.gpa, unknown_loc);
        // const ti32 = self.context.type_store.tI32();
        // _ = try self.symtab.declare(.{
        //     .name = self.ast_unit.exprs.strs.intern("i32"),
        //     .kind = .Type,
        //     .loc = unknown_loc_id,
        //     .origin_decl = ast.OptDeclId.none(),
        //     .origin_param = ast.OptParamId.none(),
        // });
    }

    // --------- context
    const FunctionCtx = struct {
        result: types.TypeId,
        has_result: bool,
        pure: bool,
        require_pure: bool,
        locals: std.AutoArrayHashMapUnmanaged(u32, void) = .{},
    };
    const LoopCtx = struct {
        label: ast.OptStrId,
        result_ty: ?types.TypeId = null,
    };

    fn bindDeclPattern(self: *Checker, did: ast.DeclId, d: ast.Rows.Decl) !void {
        if (d.pattern.isNone()) return;
        try pattern_matching.declareBindingsInPattern(self, d.pattern.unwrap(), d.loc, .{ .decl = did });
    }

    fn bindParamPattern(self: *Checker, pid: ast.ParamId, p: ast.Rows.Param) !void {
        if (p.pat.isNone()) return;
        try pattern_matching.declareBindingsInPattern(self, p.pat.unwrap(), p.loc, .{ .param = pid });
    }

    fn pushFunc(self: *Checker, result_ty: types.TypeId, has_result: bool, require_pure: bool) !void {
        try self.func_stack.append(self.gpa, .{ .result = result_ty, .has_result = has_result, .pure = true, .require_pure = require_pure });
    }
    fn popFunc(self: *Checker) void {
        if (self.func_stack.items.len > 0) {
            var ctx = &self.func_stack.items[self.func_stack.items.len - 1];
            ctx.locals.deinit(self.gpa);
            _ = self.func_stack.pop();
        }
    }
    fn inFunction(self: *const Checker) bool {
        return self.func_stack.items.len > 0;
    }
    fn currentFunc(self: *const Checker) ?FunctionCtx {
        if (self.func_stack.items.len == 0) return null;
        return self.func_stack.items[self.func_stack.items.len - 1];
    }

    fn pushLoop(self: *Checker, label: ast.OptStrId) !void {
        try self.loop_stack.append(self.gpa, .{ .label = label, .result_ty = null });
    }
    fn popLoop(self: *Checker) void {
        if (self.loop_stack.items.len > 0) _ = self.loop_stack.pop();
    }
    fn inLoop(self: *const Checker) bool {
        return self.loop_stack.items.len > 0;
    }
    inline fn pushLoopBinding(self: *Checker, pat: ast.OptPatternId, subj: types.TypeId) !void {
        try self.loop_binding_stack.append(self.gpa, .{ .pat = pat, .subject_ty = subj });
    }
    inline fn popLoopBinding(self: *Checker) void {
        if (self.loop_binding_stack.items.len > 0) _ = self.loop_binding_stack.pop();
    }
    inline fn bindingTypeFromActiveLoops(self: *Checker, name: ast.StrId) ?types.TypeId {
        var i: isize = @as(isize, @intCast(self.loop_binding_stack.items.len)) - 1;
        while (i >= 0) : (i -= 1) {
            const ctx = self.loop_binding_stack.items[@intCast(i)];
            if (!ctx.pat.isNone()) {
                if (pattern_matching.bindingTypeInPattern(self, ctx.pat.unwrap(), name, ctx.subject_ty)) |bt| {
                    return bt;
                }
            }
        }
        return null;
    }

    fn pushValueReq(self: *Checker, v: bool) !void {
        try self.value_ctx.append(self.gpa, v);
    }
    fn popValueReq(self: *Checker) void {
        if (self.value_ctx.items.len > 0) _ = self.value_ctx.pop();
    }
    pub fn isValueReq(self: *const Checker) bool {
        if (self.value_ctx.items.len == 0) return true; // default: value required
        return self.value_ctx.items[self.value_ctx.items.len - 1];
    }

    pub fn lookup(self: *Checker, name: ast.StrId) ?symbols.SymbolId {
        return self.symtab.lookup(self.ast_unit, self.symtab.currentId(), name);
    }

    fn loopCtxForLabel(self: *Checker, opt_label: ast.OptStrId) ?*LoopCtx {
        if (self.loop_stack.items.len == 0) return null;
        const want: ?u32 = if (!opt_label.isNone()) opt_label.unwrap().toRaw() else null;
        var i: isize = @as(isize, @intCast(self.loop_stack.items.len)) - 1;
        while (i >= 0) : (i -= 1) {
            const idx: usize = @intCast(i);
            const lc = &self.loop_stack.items[idx];
            if (want == null) return lc;
            if (!lc.label.isNone() and lc.label.unwrap().toRaw() == want.?) return lc;
        }
        return null;
    }

    const AssignErrors = enum {
        array_length_mismatch,
        tuple_arity_mismatch,
        assign_null_to_non_optional,
        pointer_type_mismatch,
        pointer_constness_mismatch,
        expected_array_type,
        expected_tuple_type,
        expected_map_type,
        expected_pointer_type,
        expected_integer_type,
        expected_float_type,
        expected_enum_type,
        map_wrong_key_type,
        type_value_mismatch,
        noreturn_not_storable,
        expected_struct_type,
        struct_field_count_mismatch,
        unknown_struct_field,
        struct_field_name_mismatch,
        union_literal_multiple_fields,
        union_literal_no_fields,
        failure,
        success,
    };

    pub fn assignable(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
        if (self.tEq(got, expect)) return .success;
        const got_kind = self.typeKind(got);
        const expected_kind = self.typeKind(expect);
        if (expected_kind == .Any or got_kind == .Any) return .success;

        // Assigning `null` (modeled as Optional(Any)) to a non-optional target should error clearly.
        if (got_kind == .Optional and expected_kind != .Optional) {
            const got_opt = self.context.type_store.Optional.get(self.trow(got));
            const elem_kind = self.typeKind(got_opt.elem);
            if (elem_kind == .Any) return .assign_null_to_non_optional;
            // Implicit unwrap from Optional(T) -> T is not permitted.
            return .failure;
        }

        switch (expected_kind) {
            .Slice => {
                if (got_kind != .Slice) return .failure;
                const expected_ty = self.context.type_store.Slice.get(self.trow(expect));
                const got_ty = self.context.type_store.Slice.get(self.trow(got));
                return self.assignable(got_ty.elem, expected_ty.elem);
            },
            .Array => {
                if (got_kind != .Array) return .expected_array_type;
                const expected_ty = self.context.type_store.Array.get(self.trow(expect));
                const got_ty = self.context.type_store.Array.get(self.trow(got));
                const elem_ok = self.assignable(got_ty.elem, expected_ty.elem);
                if (expected_ty.len != got_ty.len)
                    return .array_length_mismatch;
                return elem_ok;
            },
            .DynArray => {
                // BUGFIX: allow assigning from DynArray itself AND from Array/Slice (element-compatible).
                const expected_ty = self.context.type_store.DynArray.get(self.trow(expect));
                switch (got_kind) {
                    .DynArray => {
                        const got_ty = self.context.type_store.DynArray.get(self.trow(got));
                        return self.assignable(got_ty.elem, expected_ty.elem);
                    },
                    .Array => {
                        const got_ty = self.context.type_store.Array.get(self.trow(got));
                        return self.assignable(got_ty.elem, expected_ty.elem);
                    },
                    .Slice => {
                        const got_ty = self.context.type_store.Slice.get(self.trow(got));
                        return self.assignable(got_ty.elem, expected_ty.elem);
                    },
                    else => return .expected_array_type,
                }
            },
            .Tuple => {
                if (got_kind != .Tuple) return .expected_tuple_type;
                const expected_ty = self.context.type_store.Tuple.get(self.trow(expect));
                const got_ty = self.context.type_store.Tuple.get(self.trow(got));
                if (expected_ty.elems.len != got_ty.elems.len) return .tuple_arity_mismatch;
                const got_elems = self.context.type_store.type_pool.slice(got_ty.elems);
                const expected_elems = self.context.type_store.type_pool.slice(expected_ty.elems);
                for (expected_elems, 0..) |et, i| {
                    const gt = got_elems[i];
                    const res = self.assignable(gt, et);
                    if (res != .success) return res;
                }
                return .success;
            },
            .Map => {
                // Allow "empty array" sugar to coerce to any map type.
                if (got_kind == .Array) {
                    const got_ty = self.context.type_store.Array.get(self.trow(got));
                    if (got_ty.len != 0) return .expected_map_type;
                    return .success;
                }
                if (got_kind != .Map) return .expected_map_type;
                const expected_ty = self.context.type_store.Map.get(self.trow(expect));
                const got_ty = self.context.type_store.Map.get(self.trow(got));
                const key_ok = self.assignable(got_ty.key, expected_ty.key);
                const value_ok = self.assignable(got_ty.value, expected_ty.value);
                if (key_ok != .success) return .map_wrong_key_type;
                if (value_ok != .success) return value_ok;
                return .success;
            },
            .Optional => {
                const expected_ty = self.context.type_store.Optional.get(self.trow(expect));
                if (got_kind == .Optional) {
                    const got_ty = self.context.type_store.Optional.get(self.trow(got));
                    return self.assignable(got_ty.elem, expected_ty.elem);
                }
                return self.assignable(got, expected_ty.elem);
            },
            .Ptr => {
                if (got_kind != .Ptr) return .expected_pointer_type;
                const expected_ty = self.context.type_store.Ptr.get(self.trow(expect));
                const got_ty = self.context.type_store.Ptr.get(self.trow(got));
                if (!expected_ty.is_const and got_ty.is_const) {
                    return .pointer_constness_mismatch;
                }
                if (self.assignable(got_ty.elem, expected_ty.elem) != .success) {
                    return .pointer_type_mismatch;
                }
                return .success;
            },
            .TypeType => {
                if (got_kind != .TypeType) return .type_value_mismatch;
            },
            .Noreturn => return .noreturn_not_storable,
            .Union => {
                if (got_kind != .Struct) return .expected_struct_type;
                const expected_ty = self.context.type_store.Union.get(self.trow(expect));
                const got_ty = self.context.type_store.Struct.get(self.trow(got));
                const expected_fields = self.context.type_store.field_pool.slice(expected_ty.fields);
                const got_fields = self.context.type_store.field_pool.slice(got_ty.fields);
                // Should only have one field set in union
                if (got_fields.len == 0) return .union_literal_no_fields;
                if (got_fields.len != 1) return .union_literal_multiple_fields;
                const gf = self.context.type_store.Field.get(got_fields[0].toRaw());
                var found = false;
                for (expected_fields) |efid| {
                    const ef = self.context.type_store.Field.get(efid.toRaw());
                    if (ef.name.toRaw() == gf.name.toRaw()) {
                        found = true;
                        const res = self.assignable(gf.ty, ef.ty);
                        if (res != .success) return res;
                        break;
                    }
                }
                if (!found) return .unknown_struct_field;
                return .success;
            },
            .Struct => {
                if (got_kind != .Struct) return .expected_struct_type;
                const expected_ty = self.context.type_store.Struct.get(self.trow(expect));
                const got_ty = self.context.type_store.Struct.get(self.trow(got));
                const expected_fields = self.context.type_store.field_pool.slice(expected_ty.fields);
                const got_fields = self.context.type_store.field_pool.slice(got_ty.fields);
                if (expected_fields.len < got_fields.len) return .unknown_struct_field;
                if (expected_fields.len > got_fields.len) return .struct_field_count_mismatch;

                // Check fields by name, not by order.
                for (expected_fields) |efid| {
                    const ef = self.context.type_store.Field.get(efid.toRaw());
                    var found = false;
                    for (got_fields) |gfid| {
                        const gf = self.context.type_store.Field.get(gfid.toRaw());
                        if (ef.name.toRaw() == gf.name.toRaw()) {
                            found = true;
                            const res = self.assignable(gf.ty, ef.ty);
                            if (res != .success) return res;
                            break;
                        }
                    }
                    if (!found) return .struct_field_name_mismatch;
                }
                return .success;
            },
            .Enum => {
                if (got_kind != .Enum) return .expected_enum_type;
                if (!self.tEq(got, expect)) return .failure;
                return .success;
            },
            .Function => {
                if (got_kind != .Function) return .failure;
                const efn = self.context.type_store.Function.get(self.trow(expect));
                const gfn = self.context.type_store.Function.get(self.trow(got));
                if (efn.is_variadic != gfn.is_variadic) return .failure;
                const eparams = self.context.type_store.type_pool.slice(efn.params);
                const gparams = self.context.type_store.type_pool.slice(gfn.params);
                if (eparams.len != gparams.len) return .failure;
                var i: usize = 0;
                while (i < eparams.len) : (i += 1) {
                    if (!self.tEq(eparams[i], gparams[i])) return .failure;
                }
                if (!self.tEq(efn.result, gfn.result)) return .failure;
                if (efn.is_pure and !gfn.is_pure) return .failure;
                return .success;
            },
            .ErrorSet => {
                const expected_ty = self.context.type_store.ErrorSet.get(self.trow(expect));
                if (got_kind == .Error) {
                    return self.assignable(got, expected_ty.error_ty);
                } else {
                    return self.assignable(got, expected_ty.value_ty);
                }
            },
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => {
                if (!check_types.isIntegerKind(self, got_kind)) return .expected_integer_type;
                return .success;
            },
            .F32, .F64 => {
                if (got_kind != .F32 and got_kind != .F64) return .expected_float_type;
                return .success;
            },
            else => {},
        }

        return .failure;
    }

    // =========================================================
    // Declarations & Statements
    // =========================================================
    fn checkDecl(self: *Checker, decl_id: ast.DeclId) !void {
        const decl = self.ast_unit.exprs.Decl.get(decl_id.toRaw());
        try self.bindDeclPattern(decl_id, decl);

        const expect_ty = if (decl.ty.isNone())
            null
        else
            try check_types.typeFromTypeExpr(self, decl.ty.unwrap());

        // Initializers must be evaluated in value context even inside statement blocks
        try self.pushValueReq(true);
        const rhs_ty = try self.checkExpr(decl.value);
        self.popValueReq();

        if (rhs_ty == null) return;

        // If LHS is a pattern, ensure the RHS type matches the pattern's shape.
        if (!decl.pattern.isNone()) {
            const shape_ok = pattern_matching.checkPatternShapeForDecl(self, decl.pattern.unwrap(), rhs_ty.?);
            switch (shape_ok) {
                .ok => {},
                .tuple_arity_mismatch => {
                    try self.context.diags.addError(self.exprLoc(decl), .tuple_arity_mismatch, .{});
                    return;
                },
                .struct_field_mismatch => {
                    try self.context.diags.addError(self.exprLoc(decl), .struct_pattern_field_mismatch, .{});
                    return;
                },
                .shape_mismatch => {
                    try self.context.diags.addError(self.exprLoc(decl), .pattern_shape_mismatch, .{});
                    return;
                },
            }
        }

        try self.tryTypeCoercion(decl_id, rhs_ty.?, expect_ty);
    }

    fn tryTypeCoercion(
        self: *Checker,
        decl: ast.DeclId,
        rhs_ty: types.TypeId,
        expect_ty: ?types.TypeId,
    ) !void {
        if (expect_ty == null) {
            // Some degenerate cases where we don't infer from RHS
            const rhs_kind = self.typeKind(rhs_ty);
            switch (rhs_kind) {
                .Array => {
                    const arr = self.context.type_store.Array.get(self.trow(rhs_ty));
                    if (arr.len == 0) {
                        try self.context.diags.addError(self.exprLoc(self.ast_unit.exprs.Decl.get(decl.toRaw())), .cannot_infer_type_from_empty_array, .{});
                        return;
                    }
                },
                else => {
                    // infer from RHS
                    self.type_info.decl_types.items[decl.toRaw()] = rhs_ty;
                },
            }
        } else {
            // Allow variant RHS written as V.C(...) or V.C{...} to type as the annotated variant.
            var is_assignable = self.assignable(rhs_ty, expect_ty.?);
            if (is_assignable == .failure) {
                const ek = self.context.type_store.getKind(expect_ty.?);
                if (ek == .Variant or ek == .Error) {
                    const d = self.ast_unit.exprs.Decl.get(decl.toRaw());
                    const vk = self.exprKind(d.value);
                    if (vk == .Call) {
                        const call = self.getExpr(.Call, d.value);
                        var cur = call.callee;
                        var last: ?ast.StrId = null;
                        while (self.exprKind(cur) == .FieldAccess) {
                            const fr = self.getExpr(.FieldAccess, cur);
                            last = fr.field;
                            cur = fr.parent;
                        }
                        if (last) |lname| {
                            const cases = if (ek == .Variant)
                                self.context.type_store.field_pool.slice(self.context.type_store.Variant.get(self.context.type_store.index.rows.items[expect_ty.?.toRaw()]).variants)
                            else
                                self.context.type_store.field_pool.slice(self.context.type_store.Error.get(self.context.type_store.index.rows.items[expect_ty.?.toRaw()]).variants);
                            var pty: ?types.TypeId = null;
                            for (cases) |fid| {
                                const f = self.context.type_store.Field.get(fid.toRaw());
                                if (f.name.toRaw() == lname.toRaw()) { pty = f.ty; break; }
                            }
                            if (pty) |pay_ty| {
                                var ok = true;
                                if (self.context.type_store.getKind(pay_ty) == .Tuple) {
                                    const tr = self.context.type_store.get(.Tuple, pay_ty);
                                    const tys = self.context.type_store.type_pool.slice(tr.elems);
                                    const args = self.ast_unit.exprs.expr_pool.slice(call.args);
                                    ok = (args.len == tys.len);
                                    if (ok) {
                                        for (args, 0..) |aid, i| {
                                            const at = try self.checkExpr(aid) orelse return;
                                            if (self.assignable(at, tys[i]) != .success) { ok = false; break; }
                                        }
                                    }
                                } else if (self.context.type_store.getKind(pay_ty) == .Void) {
                                    ok = self.ast_unit.exprs.expr_pool.slice(call.args).len == 0;
                                } else {
                                    // single payload
                                    const args = self.ast_unit.exprs.expr_pool.slice(call.args);
                                    ok = (args.len == 1);
                                    if (ok) {
                                        const at = try self.checkExpr(args[0]) orelse return;
                                        ok = (self.assignable(at, pay_ty) == .success);
                                    }
                                }
                                if (ok) {
                                    // Treat RHS as the annotated variant type
                                    self.type_info.expr_types.items[d.value.toRaw()] = expect_ty.?;
                                    is_assignable = .success;
                                }
                            }
                        }
                    } else if (vk == .StructLit) {
                        const sl = self.getExpr(.StructLit, d.value);
                        if (!sl.ty.isNone()) {
                            var cur = sl.ty.unwrap();
                            var last: ?ast.StrId = null;
                            while (self.exprKind(cur) == .FieldAccess) {
                                const fr = self.getExpr(.FieldAccess, cur);
                                last = fr.field;
                                cur = fr.parent;
                            }
                            if (last) |lname| {
                                const cases = if (ek == .Variant)
                                    self.context.type_store.field_pool.slice(self.context.type_store.Variant.get(self.context.type_store.index.rows.items[expect_ty.?.toRaw()]).variants)
                                else
                                    self.context.type_store.field_pool.slice(self.context.type_store.Error.get(self.context.type_store.index.rows.items[expect_ty.?.toRaw()]).variants);
                                var pty: ?types.TypeId = null;
                                for (cases) |fid| {
                                    const f = self.context.type_store.Field.get(fid.toRaw());
                                    if (f.name.toRaw() == lname.toRaw()) { pty = f.ty; break; }
                                }
                                if (pty) |pay_ty| {
                                    var ok = true;
                                    if (self.context.type_store.getKind(pay_ty) == .Struct) {
                                        const st = self.context.type_store.get(.Struct, pay_ty);
                                        const tfields = self.context.type_store.field_pool.slice(st.fields);
                                        const vfields = self.ast_unit.exprs.sfv_pool.slice(sl.fields);
                                        for (vfields) |sfid| {
                                            const sf = self.ast_unit.exprs.StructFieldValue.get(sfid.toRaw());
                                            if (sf.name.isNone()) { ok = false; break; }
                                            const nm = sf.name.unwrap();
                                            var want: ?types.TypeId = null;
                                            for (tfields) |tfid| {
                                                const tf = self.context.type_store.Field.get(tfid.toRaw());
                                                if (tf.name.toRaw() == nm.toRaw()) { want = tf.ty; break; }
                                            }
                                            if (want == null) { ok = false; break; }
                                            const at = try self.checkExpr(sf.value) orelse return;
                                            if (self.assignable(at, want.?) != .success) { ok = false; break; }
                                        }
                                    } else {
                                        ok = false;
                                    }
                                    if (ok) {
                                        self.type_info.expr_types.items[d.value.toRaw()] = expect_ty.?;
                                        is_assignable = .success;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            const d = self.ast_unit.exprs.Decl.get(decl.toRaw());
            switch (is_assignable) {
                .success => {
                    // Use expected type and also update RHS expr type for consistency.
                    self.type_info.decl_types.items[decl.toRaw()] = expect_ty.?;
                    self.type_info.expr_types.items[d.value.toRaw()] = expect_ty.?;
                },
                .map_wrong_key_type => try self.context.diags.addError(self.exprLoc(d), .map_wrong_key_type, .{}),
                .union_literal_no_fields => try self.context.diags.addError(self.exprLoc(d), .union_empty_literal, .{}),
                .union_literal_multiple_fields => try self.context.diags.addError(self.exprLoc(d), .union_literal_multiple_fields, .{}),
                .expected_enum_type => try self.context.diags.addError(self.exprLoc(d), .expected_enum_type, .{}),
                .expected_struct_type => try self.context.diags.addError(self.exprLoc(d), .expected_struct_type, .{}),
                .struct_field_count_mismatch => try self.context.diags.addError(self.exprLoc(d), .struct_field_count_mismatch, .{}),
                .unknown_struct_field => try self.context.diags.addError(self.exprLoc(d), .unknown_struct_field, .{}),
                .struct_field_name_mismatch => try self.context.diags.addError(self.exprLoc(d), .struct_field_name_mismatch, .{}),
                .noreturn_not_storable => try self.context.diags.addError(self.exprLoc(d), .noreturn_not_storable, .{}),
                .type_value_mismatch => try self.context.diags.addError(self.exprLoc(d), .type_value_mismatch, .{}),
                .array_length_mismatch => try self.context.diags.addError(self.exprLoc(d), .array_length_mismatch, .{}),
                .tuple_arity_mismatch => try self.context.diags.addError(self.exprLoc(d), .tuple_arity_mismatch, .{}),
                .assign_null_to_non_optional => try self.context.diags.addError(self.exprLoc(d), .assign_null_to_non_optional, .{}),
                .pointer_type_mismatch => try self.context.diags.addError(self.exprLoc(d), .pointer_type_mismatch, .{}),
                .pointer_constness_mismatch => try self.context.diags.addError(self.exprLoc(d), .pointer_constness_violation, .{}),
                .expected_array_type => try self.context.diags.addError(self.exprLoc(d), .expected_array_type, .{}),
                .expected_tuple_type => try self.context.diags.addError(self.exprLoc(d), .expected_tuple_type, .{}),
                .expected_map_type => try self.context.diags.addError(self.exprLoc(d), .expected_map_type, .{}),
                .expected_pointer_type => try self.context.diags.addError(self.exprLoc(d), .expected_pointer_type, .{}),
                .expected_integer_type => try self.context.diags.addError(self.exprLoc(d), .expected_integer_type, .{}),
                .expected_float_type => try self.context.diags.addError(self.exprLoc(d), .expected_float_type, .{}),
                .failure => try self.context.diags.addError(self.exprLoc(d), .type_annotation_mismatch, .{}),
            }
        }
    }

    fn checkStmt(self: *Checker, sid: ast.StmtId) !?types.TypeId {
        switch (self.ast_unit.stmts.index.kinds.items[sid.toRaw()]) {
            .Expr => {
                const expr = self.getStmt(.Expr, sid);
                // Statement expression: no value required
                try self.pushValueReq(false);
                defer self.popValueReq();
                _ = try self.checkExpr(expr.expr);
                return null;
            },
            .Decl => {
                const stmt = self.getStmt(.Decl, sid);
                try self.checkDecl(stmt.decl);
                if (self.inFunction()) {
                    // record local decl for purity tracking
                    const idx = self.func_stack.items.len - 1;
                    _ = self.func_stack.items[idx].locals.put(self.gpa, stmt.decl.toRaw(), {}) catch {};
                }
            },
            .Assign => {
                const stmt = self.getStmt(.Assign, sid);
                // Pattern-shaped LHS support: tuple/struct/array destructuring
                const lkind = self.exprKind(stmt.left);
                if (lkind == .TupleLit or lkind == .StructLit or lkind == .ArrayLit) {
                    // RHS of assignment should be checked in value context
                    try self.pushValueReq(true);
                    const rv_ty = try self.checkExpr(stmt.right);
                    self.popValueReq();
                    if (rv_ty != null) {
                        const shape_ok = pattern_matching.checkPatternShapeForAssignExpr(self, stmt.left, rv_ty.?);
                        switch (shape_ok) {
                            .ok => {},
                            .tuple_arity_mismatch => try self.context.diags.addError(self.exprLoc(stmt), .tuple_arity_mismatch, .{}),
                            .struct_field_mismatch => try self.context.diags.addError(self.exprLoc(stmt), .struct_pattern_field_mismatch, .{}),
                            .shape_mismatch => try self.context.diags.addError(self.exprLoc(stmt), .pattern_shape_mismatch, .{}),
                        }
                    }
                } else {
                    const lt = try self.checkExpr(stmt.left);
                    // RHS of assignment should be checked in value context
                    try self.pushValueReq(true);
                    const rt = try self.checkExpr(stmt.right);
                    self.popValueReq();
                    if (lt != null and rt != null and (self.assignable(rt.?, lt.?) != .success)) {
                        try self.context.diags.addError(self.exprLoc(stmt), .type_annotation_mismatch, .{});
                    }
                }
                // Purity: assignment writes inside pure functions are allowed only to locals
                if (self.inFunction()) {
                    const fctx = self.currentFunc().?;
                    if (fctx.require_pure) {
                        const root = self.lvalueRootKind(stmt.left);
                        switch (root) {
                            .LocalDecl => {},
                            .Param, .NonLocalDecl, .Unknown => {
                                try self.context.diags.addError(self.exprLoc(stmt), .purity_violation, .{});
                                self.func_stack.items[self.func_stack.items.len - 1].pure = false;
                            },
                        }
                    }
                }
            },
            .Insert => {
                const row = self.getStmt(.Insert, sid);
                if (!self.warned_meta) {
                    _ = self.context.diags.addNote(self.exprLoc(row), .checker_insert_not_expanded, .{}) catch {};
                    self.warned_meta = true;
                }
                _ = try self.checkExpr(row.expr);
            },
            .Return => {
                const row = self.getStmt(.Return, sid);
                return try self.checkReturn(row);
            },
            .Break => {
                const row = self.getStmt(.Break, sid);
                if (!self.inLoop())
                    try self.context.diags.addError(self.exprLoc(row), .break_outside_loop, .{});
                if (!row.value.isNone()) {
                    // Break value must be computed in value context
                    try self.pushValueReq(true);
                    const vt = try self.checkExpr(row.value.unwrap());
                    self.popValueReq();
                    if (vt == null) return null;
                    if (self.loopCtxForLabel(row.label)) |ctx| {
                        if (ctx.result_ty) |rt| {
                            if (rt.toRaw() != vt.?.toRaw()) {
                                try self.context.diags.addError(self.exprLoc(row), .loop_break_value_type_conflict, .{});
                                return null;
                            }
                        } else {
                            ctx.result_ty = vt.?;
                        }
                    }
                }
            },
            .Continue => {
                const row = self.getStmt(.Continue, sid);
                if (!self.inLoop())
                    try self.context.diags.addError(self.exprLoc(row), .continue_outside_loop, .{});
            },
            .Unreachable => {},
            .Defer => {
                const row = self.getStmt(.Defer, sid);
                _ = try self.checkDefer(row);
            },
            .ErrDefer => {
                const row = self.getStmt(.ErrDefer, sid);
                _ = try self.checkErrDefer(row);
            },
        }
        return null;
    }

    // =========================================================
    // Expressions
    // =========================================================
    pub fn checkExpr(self: *Checker, id: ast.ExprId) anyerror!?types.TypeId {
        if (self.type_info.expr_types.items[id.toRaw()]) |cached| return cached;
        const k = self.exprKind(id);

        const tid = switch (k) {
            .Literal => try self.checkLiteral(id),
            .Ident => try self.checkIdent(id),
            .Binary => try self.checkBinary(id),
            .Unary => try self.checkUnary(id),
            .FunctionLit => try self.checkFunctionLit(id),
            .ArrayLit => try self.checkArrayLit(id),
            .TupleLit => try self.checkTupleLit(id),
            .MapLit => try self.checkMapLit(id),
            .IndexAccess => self.checkIndexAccess(id),
            .FieldAccess => try self.checkFieldAccess(id),
            .StructLit => try self.checkStructLit(id),
            .Range => try self.checkRange(id),

            // still default to any for the following kinds (can be implemented later)
            .Deref => try self.checkDeref(id),
            .VariantLit => blk: {
                // Type a variant literal using available context when possible.
                // Without an expected type, leave as Any for now.
                const vl = self.getExpr(.VariantLit, id);
                // Try to locate an expected type by scanning top-level decls that bind this expr as their RHS.
                var expected_ty: ?types.TypeId = null;
                {
                    const decls = self.ast_unit.exprs.decl_pool.slice(self.ast_unit.unit.decls);
                    var i: usize = 0;
                    while (i < decls.len) : (i += 1) {
                        const d = self.ast_unit.exprs.Decl.get(decls[i].toRaw());
                        if (d.value.toRaw() == id.toRaw() and !d.ty.isNone()) {
                            expected_ty = try check_types.typeFromTypeExpr(self, d.ty.unwrap());
                            break;
                        }
                    }
                }

                if (expected_ty) |ety| {
                const etyk = self.context.type_store.getKind(ety);
                if (etyk == .Variant or etyk == .Error) {
                        // Validate payload against the case type, if any.
                        const cases = if (etyk == .Variant)
                            self.context.type_store.field_pool.slice(self.context.type_store.Variant.get(self.context.type_store.index.rows.items[ety.toRaw()]).variants)
                        else
                            self.context.type_store.field_pool.slice(self.context.type_store.Error.get(self.context.type_store.index.rows.items[ety.toRaw()]).variants);
                        var found = false;
                        var payload_ty: types.TypeId = self.context.type_store.tVoid();
                        for (cases) |fid| {
                            const f = self.context.type_store.Field.get(fid.toRaw());
                            if (f.name.toRaw() == vl.name.toRaw()) { found = true; payload_ty = f.ty; break; }
                        }
                        if (!found) break :blk null;

                        // Check value shape
                        if (!vl.value.isNone()) {
                            const vexpr = vl.value.unwrap();
                            const pk = self.context.type_store.getKind(payload_ty);
                            if (pk == .Void) break :blk null; // payload not allowed
                            if (pk == .Tuple) {
                                const tr = self.context.type_store.get(.Tuple, payload_ty);
                                const tys = self.context.type_store.type_pool.slice(tr.elems);
                                if (self.exprKind(vexpr) == .TupleLit) {
                                    const tl = self.getExpr(.TupleLit, vexpr);
                                    const elems = self.ast_unit.exprs.expr_pool.slice(tl.elems);
                                    if (elems.len != tys.len) break :blk null;
                                    for (elems, 0..) |eid, i| {
                                        const et = try self.checkExpr(eid) orelse break :blk null;
                                        if (self.assignable(et, tys[i]) != .success) break :blk null;
                                    }
                                } else {
                                    if (tys.len != 1) break :blk null;
                                    const et = try self.checkExpr(vexpr) orelse break :blk null;
                                    if (self.assignable(et, tys[0]) != .success) break :blk null;
                                }
                            } else if (pk == .Struct) {
                                if (self.exprKind(vexpr) != .StructLit) break :blk null;
                                const sl = self.getExpr(.StructLit, vexpr);
                                const vfields = self.ast_unit.exprs.sfv_pool.slice(sl.fields);
                                const st = self.context.type_store.get(.Struct, payload_ty);
                                const tfields = self.context.type_store.field_pool.slice(st.fields);
                                // For each provided field, check type.
                                for (vfields) |sfid| {
                                    const sf = self.ast_unit.exprs.StructFieldValue.get(sfid.toRaw());
                                    if (sf.name.isNone()) break :blk null;
                                    const sname = sf.name.unwrap();
                                    var fty: ?types.TypeId = null;
                                    for (tfields) |tfid| {
                                        const tf = self.context.type_store.Field.get(tfid.toRaw());
                                        if (tf.name.toRaw() == sname.toRaw()) { fty = tf.ty; break; }
                                    }
                                    if (fty == null) break :blk null;
                                    const et = try self.checkExpr(sf.value) orelse break :blk null;
                                    if (self.assignable(et, fty.?) != .success) break :blk null;
                                }
                            } else {
                                // primitive payload
                                const et = try self.checkExpr(vexpr) orelse break :blk null;
                                if (self.assignable(et, payload_ty) != .success) break :blk null;
                            }
                        } else {
                            // No payload provided; require void payload type
                            if (self.context.type_store.getKind(payload_ty) != .Void) break :blk null;
                        }
                        break :blk ety;
                    }
                }
                // Unknown context: treat as Any to keep flow; lower stages can error if needed.
                break :blk self.context.type_store.tAny();
            },
            .EnumLit => unreachable,
            .Call => try self.checkCall(id),
            .ComptimeBlock => try self.checkComptimeBlock(id),
            .CodeBlock => try self.checkCodeBlock(id),
            .AsyncBlock => try self.checkAsyncBlock(id),
            .MlirBlock => try self.checkMlirBlock(id),
            .Insert => try self.checkInsert(id),
            .Return => blk: {
                const row = self.getExpr(.Return, id);
                break :blk try self.checkReturn(row);
            },
            .If => try self.checkIf(id),
            .While => try self.checkWhile(id),
            .For => try self.checkFor(id),
            .Match => try pattern_matching.checkMatch(self, id),
            .Break => try self.checkBreak(id),
            .Continue => try self.checkContinue(id),
            .Unreachable => try self.checkUnreachable(id),
            .UndefLit => self.context.type_store.tAny(),

            .Block => try self.checkBlock(id),
            .Defer => blk: {
                const row = self.getExpr(.Defer, id);
                break :blk try self.checkDefer(row);
            },
            .ErrDefer => blk: {
                const row = self.getExpr(.ErrDefer, id);
                break :blk try self.checkErrDefer(row);
            },
            .ErrUnwrap => try self.checkErrUnwrap(id),
            .OptionalUnwrap => try self.checkOptionalUnwrap(id),
            .Await => try self.checkAwait(id),
            .Closure => try self.checkClosure(id),
            .Cast => try self.checkCast(id),
            .Catch => try self.checkCatch(id),
            .Import => try self.checkImport(id),
            .TypeOf => try check_types.checkTypeOf(self, id),
            .NullLit => self.context.type_store.mkOptional(self.context.type_store.tAny()),

            .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => blk: {
                const ty = try check_types.typeFromTypeExpr(self, id);
                if (ty == null) break :blk null;
                break :blk self.context.type_store.mkTypeType(ty.?);
            },
            .MapType => blk_mt_expr: {
                // Try to interpret as a type expression first
                const row = self.getExpr(.MapType, id);
                const key_ty = try check_types.typeFromTypeExpr(self, row.key);
                const val_ty = try check_types.typeFromTypeExpr(self, row.value);
                if (key_ty != null and val_ty != null) {
                    break :blk_mt_expr self.context.type_store.mkTypeType(self.context.type_store.mkMap(key_ty.?, val_ty.?));
                }
                // If not valid types, interpret operands as value expressions and produce a map value type
                const key_vt = try self.checkExpr(row.key);
                const val_vt = try self.checkExpr(row.value);
                if (key_vt == null or val_vt == null) break :blk_mt_expr null;
                break :blk_mt_expr self.context.type_store.mkMap(key_vt.?, val_vt.?);
            },
        };

        if (tid) |t| self.type_info.expr_types.items[id.toRaw()] = t;
        return tid;
    }

    fn checkLiteral(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const lit = self.getExpr(.Literal, id);
        return switch (lit.kind) {
            .int => blk: {
                const s = self.getStr(lit.value.unwrap());
                if (std.fmt.parseInt(i64, s, 10) catch null == null) {
                    try self.context.diags.addError(self.exprLoc(lit), .invalid_integer_literal, .{});
                    return null;
                }
                break :blk self.context.type_store.tI64();
            },
            .imaginary => blk: {
                const s = self.getStr(lit.value.unwrap());
                // Accept integer or float literal payload for imaginary; normalize to Complex(f64)
                if ((std.fmt.parseInt(i64, s, 10) catch null) == null and (std.fmt.parseFloat(f64, s) catch null) == null) {
                    try self.context.diags.addError(self.exprLoc(lit), .invalid_imaginary_literal, .{});
                    return null;
                }
                const cty = self.context.type_store.add(.Complex, types.Rows.Complex{ .elem = self.context.type_store.tF64() });
                break :blk cty;
            },
            .float => blk: {
                // try parsing the float literal
                const s = self.getStr(lit.value.unwrap());
                if (std.fmt.parseFloat(f64, s) catch null == null) {
                    try self.context.diags.addError(self.exprLoc(lit), .invalid_float_literal, .{});
                    return null;
                }
                break :blk self.context.type_store.tF64();
            },
            .bool => self.context.type_store.tBool(),
            .string => self.context.type_store.tString(),
            .char => self.context.type_store.tU32(),
        };
    }
    fn checkIdent(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const row = self.getExpr(.Ident, id);
        if (self.lookup(row.name)) |sid| {
            const srow = self.symtab.syms.get(sid.toRaw());
            // Decl-originated symbol?
            if (!srow.origin_decl.isNone()) {
                const did = srow.origin_decl.unwrap();
                // If this decl had a pattern, compute binding type from pattern and RHS type
                const drow = self.ast_unit.exprs.Decl.get(did.toRaw());
                if (!drow.pattern.isNone()) {
                    const rhs_ty = blk: {
                        if (self.type_info.expr_types.items[drow.value.toRaw()]) |t| break :blk t;
                        if (self.type_info.decl_types.items[did.toRaw()]) |t| break :blk t;
                        // Fallback: check rhs now
                        break :blk (try self.checkExpr(drow.value)) orelse return null;
                    };
                    const bt = pattern_matching.bindingTypeInPattern(self, drow.pattern.unwrap(), row.name, rhs_ty);
                    if (bt) |btid| return btid;
                }
                if (self.type_info.decl_types.items[did.toRaw()]) |dt| return dt;
            }
            // Param-originated symbol?
            if (!srow.origin_param.isNone()) {
                const pid = srow.origin_param.unwrap();
                const p = self.ast_unit.exprs.Param.get(pid.toRaw());
                if (!p.ty.isNone()) {
                    const pt = (try check_types.typeFromTypeExpr(self, p.ty.unwrap())) orelse return null;
                    if (!p.pat.isNone()) {
                        // If this param had a pattern, compute binding type from pattern and param type
                        if (pattern_matching.bindingTypeInPattern(self, p.pat.unwrap(), row.name, pt)) |bt| return bt;
                    }
                    return pt;
                } else {
                    // Unannotated param: if pattern, try infer from callee usage later; default any
                    return self.context.type_store.tAny();
                }
            }

            // Loop-pattern-originated symbol? Infer from current loop pattern context if available
            if (self.bindingTypeFromActiveLoops(row.name)) |btid| return btid;
        }
        try self.context.diags.addError(self.exprLoc(row), .undefined_identifier, .{});
        return null;
    }

    fn checkBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const br = self.getExpr(.Block, id);
        const stmts = self.ast_unit.stmts.stmt_pool.slice(br.items);
        var i: usize = 0;
        _ = try self.symtab.push(self.symtab.currentId());
        defer self.symtab.pop();

        if (stmts.len == 0) return self.context.type_store.tVoid();
        const value_required = self.isValueReq();
        var after_break: bool = false;
        if (!value_required) {
            // Statement context: just type-check children, no value produced
            while (i < stmts.len) : (i += 1) {
                if (after_break) {
                    const loc = self.stmtLoc(stmts[i]);
                    try self.context.diags.addError(loc, .unreachable_code_after_break, .{});
                    return null;
                }
                _ = try self.checkStmt(stmts[i]);
                // Track unconditional break at top-level in this block
                const sk = self.ast_unit.stmts.index.kinds.items[stmts[i].toRaw()];
                if (sk == .Break) after_break = true else if (sk == .Expr) {
                    const se = self.getStmt(.Expr, stmts[i]).expr;
                    if (self.exprKind(se) == .Break) after_break = true;
                }
            }
            return self.context.type_store.tVoid();
        }
        // Value context: the last line must be an expression to produce a value
        while (i < stmts.len - 1) : (i += 1) {
            if (after_break) {
                const loc = self.stmtLoc(stmts[i]);
                try self.context.diags.addError(loc, .unreachable_code_after_break, .{});
                return null;
            }
            _ = try self.checkStmt(stmts[i]);
            const sk = self.ast_unit.stmts.index.kinds.items[stmts[i].toRaw()];
            if (sk == .Break) after_break = true else if (sk == .Expr) {
                const se = self.getStmt(.Expr, stmts[i]).expr;
                if (self.exprKind(se) == .Break) after_break = true;
            }
        }
        // If last is an expression, evaluate it in value context directly
        const last = stmts[stmts.len - 1];
        const last_kind = self.ast_unit.stmts.index.kinds.items[last.toRaw()];
        if (last_kind == .Expr) {
            if (after_break) {
                const loc = self.stmtLoc(last);
                try self.context.diags.addError(loc, .unreachable_code_after_break, .{});
                return null;
            }
            const row = self.getStmt(.Expr, last);
            return try self.checkExpr(row.expr);
        }
        // Otherwise, type-check the statement and treat as void
        if (after_break) {
            const loc = self.stmtLoc(last);
            try self.context.diags.addError(loc, .unreachable_code_after_break, .{});
            return null;
        }
        _ = try self.checkStmt(last);
        return self.context.type_store.tVoid();
    }

    fn stmtLoc(self: *Checker, sid: ast.StmtId) Loc {
        return switch (self.ast_unit.stmts.index.kinds.items[sid.toRaw()]) {
            .Expr => blk: {
                const row = self.getStmt(.Expr, sid);
                break :blk self.exprLocFromId(row.expr);
            },
            .Decl => blk2: {
                const row = self.getStmt(.Decl, sid);
                const d = self.ast_unit.exprs.Decl.get(row.decl.toRaw());
                break :blk2 self.exprLoc(d);
            },
            .Assign => blk3: {
                const row = self.getStmt(.Assign, sid);
                break :blk3 self.exprLoc(row);
            },
            .Insert => blk4: {
                const row = self.getStmt(.Insert, sid);
                break :blk4 self.exprLoc(row);
            },
            .Return => blk5: {
                const row = self.getStmt(.Return, sid);
                break :blk5 self.exprLoc(row);
            },
            .Break => blk6: {
                const row = self.getStmt(.Break, sid);
                break :blk6 self.exprLoc(row);
            },
            .Continue => blk7: {
                const row = self.getStmt(.Continue, sid);
                break :blk7 self.exprLoc(row);
            },
            .Unreachable => blk8: {
                const row = self.getStmt(.Unreachable, sid);
                break :blk8 self.exprLoc(row);
            },
            .Defer => blk9: {
                const row = self.getStmt(.Defer, sid);
                break :blk9 self.exprLoc(row);
            },
            .ErrDefer => blk10: {
                const row = self.getStmt(.ErrDefer, sid);
                break :blk10 self.exprLoc(row);
            },
        };
    }

    fn checkBinary(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const bin: ast.Rows.Binary = self.getExpr(.Binary, id);
        const lt = try self.checkExpr(bin.left);
        const rt = try self.checkExpr(bin.right);
        if (lt == null or rt == null) return null;

        const l = lt.?;
        const r = rt.?;
        const lhs_kind = self.typeKind(l);
        const rhs_kind = self.typeKind(r);

        switch (bin.op) {
            .add, .sub, .mul, .div, .mod, .bit_and, .bit_or, .bit_xor, .shl, .shr => {
                if (bin.op == .div) try self.checkDivByZero(bin.right, self.exprLoc(bin));
                if (bin.op == .mod) {
                    const left_is_float = switch (lhs_kind) {
                        .F32, .F64 => true,
                        else => false,
                    };
                    const right_is_float = switch (rhs_kind) {
                        .F32, .F64 => true,
                        else => false,
                    };
                    if (left_is_float or right_is_float) {
                        try self.context.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return null;
                    }
                    if (check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind))
                        try self.checkIntZeroLiteral(bin.right, self.exprLoc(bin));
                }
                // Complex arithmetic: allow + - * / with Complex and with scalar numeric (promote scalar)
                const lhs_is_complex = (lhs_kind == .Complex);
                const rhs_is_complex = (rhs_kind == .Complex);
                if (lhs_is_complex or rhs_is_complex) {
                    // Only arithmetic ops allowed for Complex
                    if (!(bin.op == .add or bin.op == .sub or bin.op == .mul or bin.op == .div)) {
                        try self.context.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return null;
                    }
                    if (lhs_is_complex and rhs_is_complex) {
                        // Require same element type for now
                        const lc = self.context.type_store.Complex.get(self.trow(l));
                        const rc = self.context.type_store.Complex.get(self.trow(r));
                        if (lc.elem.toRaw() == rc.elem.toRaw()) return l;
                        try self.context.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return null;
                    }
                    // One side complex, other side numeric scalar
                    if (lhs_is_complex and check_types.isNumericKind(self, rhs_kind)) return l;
                    if (rhs_is_complex and check_types.isNumericKind(self, lhs_kind)) return r;
                    try self.context.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                    return null;
                }
                if (!check_types.isNumericKind(self, lhs_kind) or !check_types.isNumericKind(self, rhs_kind)) {
                    try self.context.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                    return null;
                }
                if (l.toRaw() == r.toRaw()) return l;
                try self.context.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                return null;
            },
            .eq, .neq, .lt, .lte, .gt, .gte => {
                const both_ints = check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind);
                const both_floats = (lhs_kind == .F32 or lhs_kind == .F64) and (rhs_kind == .F32 or rhs_kind == .F64);
                const both_bools = lhs_kind == .Bool and rhs_kind == .Bool;
                const both_same_enum = lhs_kind == .Enum and rhs_kind == .Enum and self.tEq(l, r);

                // We avoid implicit *value* coercions. For comparisons, we accept same-class operands:
                //   - int ? int (any width/sign)
                //   - float ? float (F32/F64 mixed ok)
                //   - bool ? bool
                if (!(both_ints or both_floats or both_bools or both_same_enum)) {
                    try self.context.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                    return null;
                }
                return self.context.type_store.tBool();
            },
            .logical_and, .logical_or => {
                if (l.toRaw() == self.context.type_store.tBool().toRaw() and
                    r.toRaw() == self.context.type_store.tBool().toRaw())
                    return self.context.type_store.tBool();
                try self.context.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                return null;
            },
            .@"orelse" => {
                if (check_types.isOptional(self, l)) |elem| {
                    if (self.assignable(elem, r) == .success) {
                        return elem;
                    } else return {
                        try self.context.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return null;
                    };
                }
                try self.context.diags.addError(self.exprLoc(bin), .invalid_use_of_orelse_on_non_optional, .{});
                return null;
            },
        }
        return null;
    }

    fn checkUnary(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const unary_expr = self.getExpr(.Unary, id);
        const expr_ty = try self.checkExpr(unary_expr.expr);
        if (expr_ty == null) return null;
        const t = expr_ty.?;
        const type_kind = self.typeKind(t);
        switch (unary_expr.op) {
            .pos, .neg => {
                if (!check_types.isNumericKind(self, type_kind)) {
                    try self.context.diags.addError(self.exprLoc(unary_expr), .invalid_unary_op_operand, .{});
                    return null;
                }
                return t;
            },
            .logical_not => {
                // Accept bool or any
                if (t.toRaw() != self.context.type_store.tBool().toRaw() and t.toRaw() != self.context.type_store.tAny().toRaw()) {
                    try self.context.diags.addError(self.exprLoc(unary_expr), .invalid_unary_op_operand, .{});
                    return null;
                }
                return self.context.type_store.tBool();
            },
            .address_of => return self.context.type_store.mkPtr(t, false),
        }
    }

    fn checkFunctionLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const fnr = self.getExpr(.FunctionLit, id);
        const res = if (!fnr.result_ty.isNone())
            (try check_types.typeFromTypeExpr(self, fnr.result_ty.unwrap()))
        else
            self.context.type_store.tVoid();
        const params = self.ast_unit.exprs.param_pool.slice(fnr.params);
        var pbuf = try self.gpa.alloc(types.TypeId, params.len);
        defer self.gpa.free(pbuf);
        _ = try self.symtab.push(self.symtab.currentId());
        defer self.symtab.pop();

        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = self.ast_unit.exprs.Param.get(params[i].toRaw());
            if (!p.ty.isNone()) {
                const pt = (try check_types.typeFromTypeExpr(self, p.ty.unwrap())) orelse return null;
                // If parameter uses a pattern, ensure its shape matches the annotated type
                if (!p.pat.isNone()) {
                    const shape_ok = pattern_matching.checkPatternShapeForDecl(self, p.pat.unwrap(), pt);
                    switch (shape_ok) {
                        .ok => {},
                        .tuple_arity_mismatch => {
                            try self.context.diags.addError(self.exprLoc(fnr), .tuple_arity_mismatch, .{});
                            return null;
                        },
                        .struct_field_mismatch => {
                            try self.context.diags.addError(self.exprLoc(fnr), .struct_pattern_field_mismatch, .{});
                            return null;
                        },
                        .shape_mismatch => {
                            try self.context.diags.addError(self.exprLoc(fnr), .pattern_shape_mismatch, .{});
                            return null;
                        },
                    }
                }
                pbuf[i] = pt;
            } else {
                pbuf[i] = self.context.type_store.tAny();
            }
            // store in symbol table
            try self.bindParamPattern(params[i], p);
        }

        // Temporarily record a function type (purity will be finalized after body analysis)
        if (res == null) return null;
        const temp_ty = self.context.type_store.mkFunction(pbuf, res.?, fnr.flags.is_variadic, true);
        self.type_info.expr_types.items[id.toRaw()] = temp_ty;

        try self.pushFunc(res.?, !fnr.result_ty.isNone(), !fnr.flags.is_proc);
        defer self.popFunc();
        if (!fnr.body.isNone()) {
            // Function bodies are in statement context: no value required from the block
            try self.pushValueReq(false);
            defer self.popValueReq();
            _ = try self.checkExpr(fnr.body.unwrap());
        }
        // Extern procs are considered impure; otherwise proc purity comes from body analysis.
        const is_pure = if (fnr.flags.is_proc) false else true;
        const final_ty = self.context.type_store.mkFunction(pbuf, res.?, fnr.flags.is_variadic, is_pure);
        self.type_info.expr_types.items[id.toRaw()] = final_ty;
        return final_ty;
    }

    fn checkTupleLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const tuple_lit = self.getExpr(.TupleLit, id);
        const elems = self.ast_unit.exprs.expr_pool.slice(tuple_lit.elems);

        var tbuf = try self.gpa.alloc(types.TypeId, elems.len);
        defer self.gpa.free(tbuf);
        var i: usize = 0;
        while (i < elems.len) : (i += 1) {
            const ety = try self.checkExpr(elems[i]);
            if (ety == null) return null;
            tbuf[i] = ety.?;
        }
        return self.context.type_store.mkTuple(tbuf);
    }

    fn checkArrayLit(
        self: *Checker,
        id: ast.ExprId,
    ) !?types.TypeId {
        const array_lit = self.getExpr(.ArrayLit, id);
        const elems = self.ast_unit.exprs.expr_pool.slice(array_lit.elems);

        // infer from first element, homogeneous requirement
        if (elems.len == 0) {
            return self.context.type_store.mkArray(self.context.type_store.tAny(), 0);
        }
        const first_ty = (try self.checkExpr(elems[0])) orelse return null;
        var i: usize = 1;
        while (i < elems.len) : (i += 1) {
            const ety = try self.checkExpr(elems[i]);
            if (ety == null or ety.?.toRaw() != first_ty.toRaw()) {
                try self.context.diags.addError(self.exprLoc(array_lit), .heterogeneous_array_elements, .{});
                return null;
            }
        }
        return self.context.type_store.mkArray(first_ty, elems.len);
    }

    fn checkMapLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const row = self.getExpr(.MapLit, id);
        const kvs = self.ast_unit.exprs.kv_pool.slice(row.entries);

        if (kvs.len == 0) {
            return self.context.type_store.mkMap(self.context.type_store.tAny(), self.context.type_store.tAny());
        }
        const first = self.ast_unit.exprs.KeyValue.get(kvs[0].toRaw());
        const key_ty = try self.checkExpr(first.key);
        const val_ty = try self.checkExpr(first.value);
        if (key_ty == null or val_ty == null) return null;

        var i: usize = 1;
        while (i < kvs.len) : (i += 1) {
            const kv = self.ast_unit.exprs.KeyValue.get(kvs[i].toRaw());
            const kt = try self.checkExpr(kv.key);
            const vt = try self.checkExpr(kv.value);
            if (kt == null or kt.?.toRaw() != key_ty.?.toRaw()) {
                try self.context.diags.addError(self.exprLoc(row), .map_mixed_key_types, .{});
                return null;
            }
            if (vt == null or vt.?.toRaw() != val_ty.?.toRaw()) {
                try self.context.diags.addError(self.exprLoc(row), .map_mixed_value_types, .{});
                return null;
            }
        }
        return self.context.type_store.mkMap(key_ty.?, val_ty.?);
    }

    fn checkIndexAccess(self: *Checker, id: ast.ExprId) ?types.TypeId {
        const index_expr = self.getExpr(.IndexAccess, id);
        const col_ty = self.checkExpr(index_expr.collection) catch
            return null;
        if (col_ty == null) return null;
        const col_kind = self.typeKind(col_ty.?);
        switch (col_kind) {
            .Array, .Slice => return self.indexElemTypeFromArrayLike(col_ty.?, index_expr.index, self.exprLoc(index_expr)),
            .Map => {
                const m = self.context.type_store.Map.get(self.trow(col_ty.?));
                const it = self.checkExpr(index_expr.index) catch return null;
                if (it) |iid| {
                    if (iid.toRaw() != m.key.toRaw()) {
                        _ = self.context.diags.addError(self.exprLoc(index_expr), .map_wrong_key_type, .{}) catch {};
                        return null;
                    }
                }
                return m.value;
            },

            .String => {
                const it = self.checkExpr(index_expr.index) catch return null;
                if (it) |iid| {
                    if (!check_types.isIntegerKind(self, self.typeKind(iid))) {
                        _ = self.context.diags.addError(self.exprLoc(index_expr), .non_integer_index, .{}) catch {};
                        return null;
                    }
                }
                return self.context.type_store.tU8();
            },
            else => {
                _ = self.context.diags.addError(self.exprLoc(index_expr), .not_indexable, .{}) catch {};
            },
        }
        return null;
    }

    fn indexElemTypeFromArrayLike(self: *Checker, col_ty: types.TypeId, idx_expr: ast.ExprId, loc: Loc) ?types.TypeId {
        const col_kind = self.typeKind(col_ty);
        std.debug.assert(col_kind == .Array or col_kind == .Slice);
        const idx_kind = self.exprKind(idx_expr);
        if (idx_kind == .Range) {
            _ = self.checkExpr(idx_expr) catch return null; // validate range endpoints
            return switch (col_kind) {
                .Array => blk: {
                    const r = self.context.type_store.Array.get(self.trow(col_ty));
                    break :blk self.context.type_store.mkSlice(r.elem);
                },
                .Slice => blk2: {
                    const r = self.context.type_store.Slice.get(self.trow(col_ty));
                    break :blk2 self.context.type_store.mkSlice(r.elem);
                },
                else => unreachable,
            };
        }
        const it = self.checkExpr(idx_expr) catch return null;
        if (it) |iid| {
            if (!check_types.isIntegerKind(self, self.typeKind(iid))) {
                _ = self.context.diags.addError(loc, .non_integer_index, .{}) catch {};
                return null;
            }
        }
        return switch (col_kind) {
            .Array => blk3: {
                const r = self.context.type_store.Array.get(self.trow(col_ty));
                break :blk3 r.elem;
            },
            .Slice => blk4: {
                const r = self.context.type_store.Slice.get(self.trow(col_ty));
                break :blk4 r.elem;
            },
            else => unreachable,
        };
    }

    fn checkFieldAccess(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const field_expr = self.getExpr(.FieldAccess, id);

        // -------- Module member access via import "path".member --------
        const parent_kind = self.exprKind(field_expr.parent);
        if (parent_kind == .Import) {
            if (self.importMemberType(field_expr.parent, field_expr.field)) |mt| {
                // For imported members we don't currently expose a precise index
                // into a struct; do not set a field index here.
                return mt;
            }
            _ = self.context.diags.addError(self.exprLoc(field_expr), .unknown_module_field, .{}) catch {};
            return null;
        }
        // Also allow module access when parent is an identifier bound to an import declaration
        if (parent_kind == .Ident) {
            const idr = self.getExpr(.Ident, field_expr.parent);
            if (self.lookup(idr.name)) |sid_sym| {
                const sym = self.symtab.syms.get(sid_sym.toRaw());
                if (!sym.origin_decl.isNone()) {
                    const did = sym.origin_decl.unwrap();
                    const drow = self.ast_unit.exprs.Decl.get(did.toRaw());
                    if (self.exprKind(drow.value) == .Import) {
                        if (self.importMemberType(drow.value, field_expr.field)) |mt| {
                            return mt;
                        }
                        _ = self.context.diags.addError(self.exprLoc(field_expr), .unknown_module_field, .{}) catch {};
                        return null;
                    }
                }
            }
        }

        // -------- Normal value/type field access --------
        const parent_ty = self.checkExpr(field_expr.parent) catch return null;
        if (parent_ty == null) return null;

        var ty = parent_ty.?;
        const kind = self.typeKind(ty);
        switch (kind) {
            .Complex => {
                const comp = self.context.type_store.Complex.get(self.trow(ty));
                const field_name = self.getStr(field_expr.field);
                if (std.mem.eql(u8, field_name, "real") or std.mem.eql(u8, field_name, "re")) {
                    try self.type_info.setFieldIndex(id, 0);
                    return comp.elem;
                }
                if (std.mem.eql(u8, field_name, "imag") or std.mem.eql(u8, field_name, "im")) {
                    try self.type_info.setFieldIndex(id, 1);
                    return comp.elem;
                }
                _ = self.context.diags.addError(self.exprLoc(field_expr), .unknown_struct_field, .{}) catch {};
                return null;
            },
            .Struct => {
                const struct_row = self.context.type_store.Struct.get(self.trow(ty));
                const fields = self.context.type_store.field_pool.slice(struct_row.fields);
                var i: usize = 0;
                while (i < fields.len) : (i += 1) {
                    const f = self.context.type_store.Field.get(fields[i].toRaw());
                    if (f.name.toRaw() == field_expr.field.toRaw()) {
                        try self.type_info.setFieldIndex(id, @intCast(i));
                        return f.ty;
                    }
                }
                _ = self.context.diags.addError(self.exprLoc(field_expr), .unknown_struct_field, .{}) catch {};
                return null;
            },
            .Tuple => {
                const tuple_row = self.context.type_store.Tuple.get(self.trow(ty));
                const elems = self.context.type_store.type_pool.slice(tuple_row.elems);
                const index = std.fmt.parseInt(usize, self.getStr(field_expr.field), 10) catch {
                    _ = self.context.diags.addError(self.exprLoc(field_expr), .expected_field_name_or_index, .{}) catch {};
                    return null;
                };
                if (index >= elems.len) {
                    _ = self.context.diags.addError(self.exprLoc(field_expr), .tuple_index_out_of_bounds, .{}) catch {};
                    return null;
                }
                try self.type_info.setFieldIndex(id, @intCast(index));
                return elems[index];
            },
            .Ptr => {
                const ptr_row = self.context.type_store.Ptr.get(self.trow(ty));
                ty = ptr_row.elem;
                const inner_kind = self.typeKind(ty);
                if (inner_kind == .Complex) {
                    const comp = self.context.type_store.Complex.get(self.trow(ty));
                    const field_name = self.getStr(field_expr.field);
                    if (std.mem.eql(u8, field_name, "real") or std.mem.eql(u8, field_name, "re")) {
                        try self.type_info.setFieldIndex(id, 0);
                        return comp.elem;
                    }
                    if (std.mem.eql(u8, field_name, "imag") or std.mem.eql(u8, field_name, "im")) {
                        try self.type_info.setFieldIndex(id, 1);
                        return comp.elem;
                    }
                }
                if (inner_kind == .Struct) {
                    const struct_row = self.context.type_store.Struct.get(self.trow(ty));
                    const fields = self.context.type_store.field_pool.slice(struct_row.fields);
                    var i: usize = 0;
                    while (i < fields.len) : (i += 1) {
                        const f = self.context.type_store.Field.get(fields[i].toRaw());
                        if (f.name.toRaw() == field_expr.field.toRaw()) {
                            try self.type_info.setFieldIndex(id, @intCast(i));
                            return f.ty;
                        }
                    }
                    _ = self.context.diags.addError(self.exprLoc(field_expr), .unknown_struct_field, .{}) catch {};
                    return null;
                }
                _ = self.context.diags.addError(self.exprLoc(field_expr), .field_access_on_non_aggregate, .{}) catch {};
                return null;
            },
            .TypeType => {
                const tt = self.context.type_store.TypeType.get(self.trow(ty));
                ty = tt.of;
                const inner_kind = self.typeKind(ty);

                if (inner_kind == .Enum) {
                    const en = self.context.type_store.Enum.get(self.trow(ty));
                    const members = self.context.type_store.enum_member_pool.slice(en.members);
                    var i: usize = 0;
                    while (i < members.len) : (i += 1) {
                        const m = self.context.type_store.EnumMember.get(members[i].toRaw());
                        if (m.name.toRaw() == field_expr.field.toRaw()) {
                            // Selecting an enum tag as a value of the enum type.
                            try self.type_info.setFieldIndex(id, @intCast(i));
                            return ty;
                        }
                    }
                    _ = self.context.diags.addError(self.exprLoc(field_expr), .unknown_enum_tag, .{}) catch {};
                    return null;
                } else if (inner_kind == .Variant) {
                    const vr = self.context.type_store.Variant.get(self.trow(ty));
                    const variants = self.context.type_store.field_pool.slice(vr.variants);
                    var i: usize = 0;
                    while (i < variants.len) : (i += 1) {
                        const v = self.context.type_store.Field.get(variants[i].toRaw());
                        if (v.name.toRaw() == field_expr.field.toRaw()) {
                            // In value position, selecting a variant *tag* without args:
                            // if payload is void => ok (value of the variant type)
                            // else => arity mismatch (should be constructed via call)
                            const pk = self.typeKind(v.ty);
                            if (pk == .Void) {
                                try self.type_info.setFieldIndex(id, @intCast(i));
                                return ty;
                            }
                            _ = self.context.diags.addError(self.exprLoc(field_expr), .variant_payload_arity_mismatch, .{}) catch {};
                            return null;
                        }
                    }
                    _ = self.context.diags.addError(self.exprLoc(field_expr), .unknown_variant_tag, .{}) catch {};
                    return null;
                } else if (inner_kind == .Error) {
                    const er = self.context.type_store.Error.get(self.trow(ty));
                    const tags = self.context.type_store.field_pool.slice(er.variants);
                    var i: usize = 0;
                    while (i < tags.len) : (i += 1) {
                        const t = self.context.type_store.Field.get(tags[i].toRaw());
                        if (t.name.toRaw() == field_expr.field.toRaw()) {
                            try self.type_info.setFieldIndex(id, @intCast(i));
                            return ty;
                        }
                    }
                    _ = self.context.diags.addError(self.exprLoc(field_expr), .unknown_error_tag, .{}) catch {};
                    return null;
                }

                _ = self.context.diags.addError(self.exprLoc(field_expr), .field_access_on_non_aggregate, .{}) catch {};
                return null;
            },
            else => {
                _ = self.context.diags.addError(self.exprLoc(field_expr), .field_access_on_non_aggregate, .{}) catch {};
                return null;
            },
        }
    }

    fn importHasMember(self: *Checker, import_eid: ast.ExprId, member: ast.StrId) bool {
        const ir = self.getExpr(.Import, import_eid);
        const ek = self.exprKind(ir.expr);
        if (ek != .Literal) return false;
        const lit = self.getExpr(.Literal, ir.expr);
        if (lit.value.isNone()) return false;
        var path = self.getStr(lit.value.unwrap());
        if (path.len >= 2 and path[0] == '"' and path[path.len - 1] == '"') {
            path = path[1 .. path.len - 1];
        }
        return self.importMemberTypeByPath(&self.context.resolver, path, member) != null;
    }

    fn importMemberTypeByPath(self: *Checker, res: *ImportResolver, path: []const u8, member: ast.StrId) ?types.TypeId {
        const me = res.resolve(self.import_base_dir, path, self.pipeline) catch return null;
        const target = self.getStr(member);
        if (me.syms.get(target)) |ty| {
            return ty;
        }
        return null;
    }

    fn importMemberType(self: *Checker, import_eid: ast.ExprId, member: ast.StrId) ?types.TypeId {
        const res = &self.context.resolver;
        const ir = self.getExpr(.Import, import_eid);
        const ek = self.exprKind(ir.expr);
        if (ek != .Literal) return null;
        const lit = self.getExpr(.Literal, ir.expr);
        if (lit.value.isNone()) return null;
        var path = self.getStr(lit.value.unwrap());
        if (path.len >= 2 and path[0] == '"' and path[path.len - 1] == '"') path = path[1 .. path.len - 1];
        return self.importMemberTypeByPath(res, path, member);
    }

    fn fileHasTopDecl(self: *Checker, abs_or_rel: []const u8, name: []const u8) bool {
        var cwd = std.fs.cwd();
        const content = cwd.readFileAlloc(self.gpa, abs_or_rel, 1 << 20) catch return false;
        defer self.gpa.free(content);
        var it = std.mem.splitScalar(u8, content, '\n');
        while (it.next()) |line| {
            const l = std.mem.trim(u8, line, " \t\r");
            if (l.len == 0) continue;
            // skip comment lines starting with //
            if (l.len >= 2 and l[0] == '/' and l[1] == '/') continue;

            // match identifier at start followed by optional spaces then '::'
            var i: usize = 0;
            if (!(std.ascii.isAlphabetic(l[0]) or l[0] == '_')) continue;
            i += 1;
            while (i < l.len and (std.ascii.isAlphanumeric(l[i]) or l[i] == '_')) : (i += 1) {}
            const ident = l[0..i];

            var j = i;
            while (j < l.len and (l[j] == ' ' or l[j] == '\t')) : (j += 1) {}
            if (j + 1 < l.len and l[j] == ':' and l[j + 1] == ':') {
                if (std.mem.eql(u8, ident, name)) return true;
            }
        }
        return false;
    }

    // no-op helpers removed

    fn checkRange(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const rr = self.getExpr(.Range, id);
        if (!rr.start.isNone()) {
            const st = try self.checkExpr(rr.start.unwrap());
            if (st == null or !check_types.isIntegerKind(self, self.typeKind(st.?))) {
                try self.context.diags.addError(self.exprLoc(rr), .non_integer_index, .{});
                return null;
            }
        }
        if (!rr.end.isNone()) {
            const et = try self.checkExpr(rr.end.unwrap());
            if (et == null or !check_types.isIntegerKind(self, self.typeKind(et.?))) {
                try self.context.diags.addError(self.exprLoc(rr), .non_integer_index, .{});
                return null;
            }
        }
        return self.context.type_store.mkSlice(self.context.type_store.tUsize());
    }

    fn checkStructLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const struct_lit = self.getExpr(.StructLit, id);
        const lit_fields = self.ast_unit.exprs.sfv_pool.slice(struct_lit.fields);
        var buf = try self.context.type_store.gpa.alloc(types.TypeStore.StructFieldArg, lit_fields.len);
        defer self.context.type_store.gpa.free(buf);
        var i: usize = 0;
        while (i < lit_fields.len) : (i += 1) {
            const f = self.ast_unit.exprs.StructFieldValue.get(lit_fields[i].toRaw());
            const ft = try self.checkExpr(f.value) orelse return null;
            if (f.name.isNone()) {
                // Positional field. We can't handle this yet.
                return null;
            }
            buf[i] = .{ .name = f.name.unwrap(), .ty = ft };
        }
        const struct_ty = self.context.type_store.mkStruct(buf);
        if (struct_lit.ty.isNone()) {
            return struct_ty;
        }
        const lit_ty = struct_lit.ty.unwrap();
        const expect_ty = try check_types.typeFromTypeExpr(self, lit_ty) orelse
            return null;
        const is_assignable = self.assignable(struct_ty, expect_ty);
        switch (is_assignable) {
            .success => {},
            .struct_field_count_mismatch => {
                try self.context.diags.addError(self.exprLoc(struct_lit), .struct_missing_field, .{});
                return null;
            },
            .unknown_struct_field => {
                try self.context.diags.addError(self.exprLoc(struct_lit), .unknown_struct_field, .{});
                return null;
            },
            .union_literal_multiple_fields => {
                try self.context.diags.addError(self.exprLoc(struct_lit), .union_literal_multiple_fields, .{});
                return null;
            },
            .union_literal_no_fields => {
                try self.context.diags.addError(self.exprLoc(struct_lit), .union_empty_literal, .{});
                return null;
            },
            else => {
                try self.context.diags.addError(self.exprLoc(struct_lit), .struct_field_type_mismatch, .{});
                return null;
            },
        }
        return expect_ty;
    }

    fn checkDeref(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const row = self.getExpr(.Deref, id);
        const ptr_ty_opt = try self.checkExpr(row.expr);
        if (ptr_ty_opt == null) return null;
        const ptr_ty = ptr_ty_opt.?;
        const kind = self.typeKind(ptr_ty);
        if (kind != .Ptr) {
            try self.context.diags.addError(self.exprLoc(row), .deref_non_pointer, .{});
            return null;
        }
        const ptr_row = self.context.type_store.Ptr.get(self.trow(ptr_ty));
        return ptr_row.elem;
    }

    // =========================
    // Calls & related helpers
    // =========================

    fn resolveImportedMemberType(self: *Checker, fr: ast.Rows.FieldAccess) ?types.TypeId {
        // Case 1: direct module value: (import "x").foo(...)
        const pk = self.exprKind(fr.parent);
        if (pk == .Import) return self.importMemberType(fr.parent, fr.field);

        // Case 2: 'ident' bound to an import declaration
        if (pk == .Ident) {
            const idr = self.getExpr(.Ident, fr.parent);
            if (self.lookup(idr.name)) |sid_sym| {
                const sym = self.symtab.syms.get(sid_sym.toRaw());
                if (!sym.origin_decl.isNone()) {
                    const did = sym.origin_decl.unwrap();
                    const drow = self.ast_unit.exprs.Decl.get(did.toRaw());
                    if (self.exprKind(drow.value) == .Import) {
                        return self.importMemberType(drow.value, fr.field);
                    }
                }
            }
        }
        return null;
    }

    fn resolveTagPayloadType(self: *Checker, parent_ty: types.TypeId, tag: ast.StrId) ?types.TypeId {
        const pk = self.trow(parent_ty);
        switch (pk) {
            .Variant => {
                const vt = self.context.type_store.Variant.get(self.trow(parent_ty));
                const cases = self.context.type_store.field_pool.slice(vt.variants);
                for (cases) |fid| {
                    const f = self.context.type_store.Field.get(fid.toRaw());
                    if (f.name.toRaw() == tag.toRaw()) return f.ty;
                }
            },
            .Error => {
                const et = self.context.type_store.Error.get(self.trow(parent_ty));
                const cases = self.context.type_store.field_pool.slice(et.variants);
                for (cases) |fid| {
                    const f = self.context.type_store.Field.get(fid.toRaw());
                    if (f.name.toRaw() == tag.toRaw()) return f.ty;
                }
            },
            else => {},
        }
        return null;
    }

    /// Handles `(Type).Tag(args...)` where `Type` is a Variant or Error.
    /// Supports payload kinds: Void, Tuple, Struct (new).
    fn checkTagConstructorCall(
        self: *Checker,
        parent_ty: types.TypeId,
        tag: ast.StrId,
        args: []const ast.ExprId,
        loc: Loc,
    ) !?types.TypeId {
        const pk = self.typeKind(parent_ty);
        if (pk != .Variant and pk != .Error) return null;

        // Load tag table
        const cases = if (pk == .Variant)
            self.context.type_store.field_pool.slice(self.context.type_store.Variant.get(self.trow(parent_ty)).variants)
        else
            self.context.type_store.field_pool.slice(self.context.type_store.Error.get(self.trow(parent_ty)).variants);

        // Find the tag & payload type
        var payload_ty_opt: ?types.TypeId = null;
        for (cases) |cid| {
            const c = self.context.type_store.Field.get(cid.toRaw());
            if (c.name.toRaw() == tag.toRaw()) {
                payload_ty_opt = c.ty;
                break;
            }
        }
        if (payload_ty_opt == null) {
            if (pk == .Variant) {
                try self.context.diags.addError(loc, .unknown_variant_tag, .{});
            } else {
                try self.context.diags.addError(loc, .unknown_error_tag, .{});
            }
            return null;
        }

        const payload_ty = payload_ty_opt.?;
        const payload_kind = self.typeKind(payload_ty);

        switch (payload_kind) {
            .Void => {
                // Tag-only: must have zero args
                if (args.len != 0) {
                    try self.context.diags.addError(loc, .argument_count_mismatch, .{});
                    return null;
                }
                return parent_ty;
            },
            .Tuple => {
                // Exact arity, per-element type check
                const tup = self.context.type_store.Tuple.get(self.trow(payload_ty));
                const params = self.context.type_store.type_pool.slice(tup.elems);

                if (args.len != params.len) {
                    // IMPORTANT: only one arity diagnostic
                    try self.context.diags.addError(loc, .argument_count_mismatch, .{});
                    return null;
                }

                var i: usize = 0;
                while (i < args.len) : (i += 1) {
                    const at = try self.checkExpr(args[i]) orelse return null;
                    if (self.assignable(at, params[i]) != .success) {
                        const expected_kind = self.typeKind(params[i]);
                        const actual_kind = self.typeKind(at);
                        // IMPORTANT: only one type diagnostic
                        try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_kind, actual_kind });
                        return null;
                    }
                }
                return parent_ty;
            },
            else => {
                // Non-void, non-tuple payloads (e.g. struct) are not callable: use literals like Type.Tag{...}
                try self.context.diags.addError(loc, .call_non_callable, .{});
                return null;
            },
        }
    }

    fn checkCall(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const call_expr = self.getExpr(.Call, id);
        const call_loc = self.exprLoc(call_expr);
        const callee_kind = self.exprKind(call_expr.callee);
        const args = self.ast_unit.exprs.expr_pool.slice(call_expr.args);

        // Fast path A: module member call — resolve from import without evaluating callee.
        if (callee_kind == .FieldAccess) {
            const fr = self.getExpr(.FieldAccess, call_expr.callee);
            if (self.resolveImportedMemberType(fr)) |fty| {
                const fk = self.typeKind(fty);
                if (fk != .Function) {
                    try self.context.diags.addError(call_loc, .call_non_callable, .{});
                    return null;
                }
                const fnrow = self.context.type_store.Function.get(self.trow(fty));
                const params = self.context.type_store.type_pool.slice(fnrow.params);

                if (!fnrow.is_variadic and args.len != params.len) {
                    try self.context.diags.addError(call_loc, .argument_count_mismatch, .{});
                    return null;
                }
                const fixed = if (params.len == 0) 0 else if (fnrow.is_variadic) params.len - 1 else params.len;

                var i: usize = 0;
                while (i < args.len) : (i += 1) {
                    const at = try self.checkExpr(args[i]) orelse return null;
                    const pt = if (i < fixed) params[i] else params[fixed];
                    // print types
                    if (self.assignable(at, pt) != .success) {
                        const expected_kind = self.typeKind(pt);
                        const actual_kind = self.typeKind(at);
                        const loc = self.exprLocFromId(args[i]);
                        try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_kind, actual_kind });
                        return null;
                    }
                }
                return fnrow.result;
            }

            // Fast path B: (Type).Tag(...) for Variant/Error constructors — handle ONCE and return.
            if (try check_types.typeFromTypeExpr(self, fr.parent)) |pty| {
                const pk = self.typeKind(pty);
                if (pk == .Variant or pk == .Error) {
                    // This single call either returns a type (success) or null after emitting exactly one diagnostic.
                    return try self.checkTagConstructorCall(pty, fr.field, args, call_loc);
                }
                // If parent is a type but not Variant/Error, fall through to general evaluation.
            }
        }

        // General case: the callee is a value expression.
        const func_ty_opt = try self.checkExpr(call_expr.callee);
        if (func_ty_opt == null) {
            if (callee_kind == .Ident) {
                const idr = self.getExpr(.Ident, call_expr.callee);
                if (self.lookup(idr.name) == null) {
                    try self.context.diags.addError(call_loc, .unknown_function, .{});
                }
            }
            return null;
        }
        const func_ty = func_ty_opt.?;
        const func_kind = self.typeKind(func_ty);

        // Tuple-as-constructor: `(T0,T1,..)(a0,a1,..)` -> construct the tuple type.
        if (func_kind == .Tuple) {
            const tup = self.context.type_store.Tuple.get(self.trow(func_ty));
            const params = self.context.type_store.type_pool.slice(tup.elems);
            if (args.len != params.len) {
                try self.context.diags.addError(call_loc, .argument_count_mismatch, .{});
                return null;
            }
            var i: usize = 0;
            while (i < args.len) : (i += 1) {
                const at = try self.checkExpr(args[i]) orelse return null;
                if (self.assignable(at, params[i]) != .success) {
                    const expected_kind = self.typeKind(params[i]);
                    const actual_kind = self.typeKind(at);
                    const loc = self.exprLocFromId(args[i]);
                    try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_kind, actual_kind });
                    return null;
                }
            }
            return func_ty;
        }

        if (func_kind != .Function) {
            try self.context.diags.addError(call_loc, .call_non_callable, .{});
            return null;
        }

        // Purity bookkeeping / enforcement
        const fnrow = self.context.type_store.Function.get(self.trow(func_ty));
        if (self.inFunction()) {
            const fctx = self.currentFunc().?;
            if (fctx.require_pure and !fnrow.is_pure) {
                try self.context.diags.addError(call_loc, .purity_violation, .{});
                return null;
            }
            if (!fnrow.is_pure) {
                const idx = self.func_stack.items.len - 1;
                self.func_stack.items[idx].pure = false;
            }
        }

        // Arity & argument type checks
        const params = self.context.type_store.type_pool.slice(fnrow.params);
        if (!fnrow.is_variadic) {
            if (args.len != params.len) {
                try self.context.diags.addError(call_loc, .argument_count_mismatch, .{});
                return null;
            }
        } else {
            const min_required = if (params.len == 0) 0 else params.len - 1;
            if (args.len < min_required) {
                try self.context.diags.addError(call_loc, .argument_count_mismatch, .{});
                return null;
            }
        }

        var i: usize = 0;
        while (i < args.len) : (i += 1) {
            const at = try self.checkExpr(args[i]) orelse return null;
            const pt = if (!fnrow.is_variadic)
                (if (i < params.len) params[i] else params[params.len - 1])
            else blk: {
                const fixed = if (params.len == 0) 0 else params.len - 1;
                break :blk if (i < fixed) params[i] else params[params.len - 1];
            };
            if (self.assignable(at, pt) != .success) {
                const expected_kind = self.typeKind(pt);
                const actual_kind = self.typeKind(at);
                const loc = self.exprLocFromId(args[i]);
                try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_kind, actual_kind });
                return null;
            }
        }
        return fnrow.result;
    }

    // =========================
    // Blocks, Return & Control
    // =========================

    fn checkCodeBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cb = self.getExpr(.CodeBlock, id);
        if (!self.warned_code) {
            _ = self.context.diags.addNote(self.exprLoc(cb), .checker_code_block_not_executed, .{}) catch {};
            self.warned_code = true;
        }
        return try self.checkExpr(cb.block);
    }

    fn checkComptimeBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cb = self.getExpr(.ComptimeBlock, id);
        if (!self.warned_comptime) {
            _ = self.context.diags.addNote(self.exprLoc(cb), .checker_comptime_not_executed, .{}) catch {};
            self.warned_comptime = true;
        }
        return try self.checkExpr(cb.block);
    }

    fn checkAsyncBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Treat async blocks as opaque for typing.
        return self.context.type_store.tAny();
    }

    fn checkMlirBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Treat mlir blocks as opaque for typing.
        return self.context.type_store.tAny();
    }

    fn checkInsert(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const r = self.getExpr(.Insert, id);
        _ = try self.checkExpr(r.expr);
        return self.context.type_store.tAny();
    }

    fn checkReturn(self: *Checker, rr: ast.Rows.Return) !?types.TypeId {
        if (self.func_stack.items.len == 0) {
            try self.context.diags.addError(self.exprLoc(rr), .return_outside_function, .{});
            return null;
        }
        const current_func = self.func_stack.items[self.func_stack.items.len - 1];

        if (current_func.has_result and rr.value.isNone()) {
            try self.context.diags.addError(self.exprLoc(rr), .missing_return_value, .{});
            return null;
        }
        if (!current_func.has_result and !rr.value.isNone()) {
            try self.context.diags.addError(self.exprLoc(rr), .return_value_in_void_function, .{});
            return null;
        }

        const expect_ty = current_func.result;
        const ret_ty = if (rr.value.isNone()) self.context.type_store.tVoid() else blk: {
            try self.pushValueReq(true);
            const t = try self.checkExpr(rr.value.unwrap());
            self.popValueReq();
            break :blk t;
        };
        if (ret_ty == null) return null;

        if (self.assignable(ret_ty.?, expect_ty) != .success) {
            try self.context.diags.addError(self.exprLoc(rr), .return_type_mismatch, .{});
            return null;
        }
        return ret_ty;
    }

    fn checkIf(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const if_expr = self.getExpr(.If, id);
        const cond = try self.checkExpr(if_expr.cond);
        if (cond == null or cond.?.toRaw() != self.context.type_store.tBool().toRaw()) {
            try self.context.diags.addError(self.exprLoc(if_expr), .non_boolean_condition, .{});
            return null;
        }

        const value_required = self.isValueReq();
        if (!value_required) {
            _ = try self.checkExpr(if_expr.then_block);
            if (!if_expr.else_block.isNone()) _ = try self.checkExpr(if_expr.else_block.unwrap());
            return self.context.type_store.tVoid();
        }

        const then_ty = try self.checkExpr(if_expr.then_block) orelse return null;
        if (if_expr.else_block.isNone()) {
            try self.context.diags.addError(self.exprLoc(if_expr), .if_expression_requires_else, .{});
            return null;
        }
        const else_ty = try self.checkExpr(if_expr.else_block.unwrap()) orelse return null;

        if (then_ty.toRaw() != else_ty.toRaw()) {
            try self.context.diags.addError(self.exprLoc(if_expr), .if_branch_type_mismatch, .{});
            return null;
        }
        return then_ty;
    }

    fn checkWhile(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const wr = self.getExpr(.While, id);

        if (!wr.cond.isNone() and wr.pattern.isNone()) {
            // C-like while loop
            const cond_ty = try self.checkExpr(wr.cond.unwrap()) orelse return null;
            const ck = self.typeKind(cond_ty);
            if (ck != .Bool and ck != .Any) {
                try self.context.diags.addError(self.exprLoc(wr), .non_boolean_condition, .{});
                return null;
            }
        } else if (!wr.cond.isNone() and !wr.pattern.isNone()) {
            // Pattern-matching while
            const subj_ty = try self.checkExpr(wr.cond.unwrap()) orelse return null;
            if (!(try pattern_matching.checkPattern(self, wr.pattern.unwrap(), subj_ty, true))) {
                return null;
            }
            try self.pushLoopBinding(wr.pattern, subj_ty);
        } else if (wr.cond.isNone() and wr.pattern.isNone()) {
            // Infinite loop: ok
        } else unreachable;

        try self.pushLoop(wr.label);
        defer self.popLoop();
        if (!wr.cond.isNone() and !wr.pattern.isNone()) {
            defer self.popLoopBinding();
        }

        const body_ty = try self.checkExpr(wr.body);

        if (self.isValueReq()) {
            if (self.loopCtxForLabel(wr.label)) |ctx| return ctx.result_ty;
        }
        return body_ty;
    }

    fn checkUnreachable(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.context.type_store.tAny();
    }

    fn checkFor(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const fr = self.getExpr(.For, id);
        const it = try self.checkExpr(fr.iterable) orelse return null;
        const kind = self.typeKind(it);

        switch (kind) {
            .Array, .Slice, .DynArray => {
                const pat_kind = self.ast_unit.pats.index.kinds.items[fr.pattern.toRaw()];
                const subject_ty: types.TypeId = switch (pat_kind) {
                    .Slice => it,
                    else => switch (kind) {
                        .Array => self.context.type_store.Array.get(self.trow(it)).elem,
                        .Slice => self.context.type_store.Slice.get(self.trow(it)).elem,
                        .DynArray => self.context.type_store.DynArray.get(self.trow(it)).elem,
                        else => unreachable,
                    },
                };
                if (!(try pattern_matching.checkPattern(self, fr.pattern, subject_ty, true))) {
                    return null;
                }
                try self.pushLoopBinding(ast.OptPatternId.some(fr.pattern), subject_ty);
            },
            else => {
                try self.context.diags.addError(self.exprLoc(fr), .non_iterable_in_for, .{});
                return null;
            },
        }
        try self.pushLoop(fr.label);
        defer self.popLoop();
        defer self.popLoopBinding();

        const body_ty = try self.checkExpr(fr.body);
        if (self.isValueReq()) {
            if (self.loopCtxForLabel(fr.label)) |ctx| return ctx.result_ty;
        }
        return body_ty;
    }

    // =========================
    // Casts, Catch, Optionals
    // =========================

    fn castable(self: *Checker, got: types.TypeId, expect: types.TypeId) bool {
        if (got.toRaw() == expect.toRaw()) return true;
        const gk = self.typeKind(got);
        const ek = self.typeKind(expect);

        // Numeric <-> numeric (no implicit *value* coercion, but casts allowed)
        const num_ok =
            switch (gk) {
                .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize => true,
                else => false,
            } and
            switch (ek) {
                .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize => true,
                else => false,
            };
        if (num_ok) return true;

        // Pointer-to-pointer
        if (gk == .Ptr and ek == .Ptr) return true;

        return false;
    }

    fn checkBreak(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const br = self.getExpr(.Break, id);
        if (!self.inLoop()) {
            try self.context.diags.addError(self.exprLoc(br), .break_outside_loop, .{});
            return null;
        }

        var val_ty: ?types.TypeId = null;
        if (!br.value.isNone()) {
            val_ty = try self.checkExpr(br.value.unwrap());
            if (val_ty == null) return null;
        }

        if (self.loopCtxForLabel(br.label)) |ctx| {
            if (!br.value.isNone()) {
                if (ctx.result_ty) |rt| {
                    if (val_ty.?.toRaw() != rt.toRaw()) {
                        try self.context.diags.addError(self.exprLoc(br), .loop_break_value_type_conflict, .{});
                        return null;
                    }
                } else ctx.result_ty = val_ty.?;
                return val_ty;
            } else {
                // unlabeled/valueless break in value position yields void
                return self.context.type_store.tVoid();
            }
        }
        return null;
    }

    fn checkContinue(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.context.type_store.tVoid();
    }

    fn checkDefer(self: *Checker, defer_expr: ast.Rows.Defer) !?types.TypeId {
        if (!self.inFunction()) {
            try self.context.diags.addError(self.exprLoc(defer_expr), .defer_outside_function, .{});
        }
        _ = try self.checkExpr(defer_expr.expr);
        return self.context.type_store.tVoid();
    }

    fn checkErrDefer(self: *Checker, errdefer_expr: ast.Rows.ErrDefer) !?types.TypeId {
        if (!self.inFunction()) {
            try self.context.diags.addError(self.exprLoc(errdefer_expr), .errdefer_outside_function, .{});
            return null;
        }
        const current_func = self.currentFunc().?;
        if (!current_func.has_result or self.typeKind(current_func.result) != .ErrorSet) {
            try self.context.diags.addError(self.exprLoc(errdefer_expr), .errdefer_in_non_error_function, .{});
            return null;
        }
        _ = try self.checkExpr(errdefer_expr.expr) orelse return null;
        return self.context.type_store.tVoid();
    }

    fn checkErrUnwrap(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const eur = self.getExpr(.ErrUnwrap, id);
        const et = try self.checkExpr(eur.expr) orelse return null;
        if (self.typeKind(et) != .ErrorSet) {
            try self.context.diags.addError(self.exprLoc(eur), .error_propagation_on_non_error, .{});
            return null;
        }
        const er = self.context.type_store.ErrorSet.get(self.trow(et));

        if (!self.inFunction()) {
            try self.context.diags.addError(self.exprLoc(eur), .error_propagation_mismatched_function_result, .{});
            return null;
        }
        const fctx = self.currentFunc().?;
        const fk = self.typeKind(fctx.result);
        if (fk != .ErrorSet) {
            try self.context.diags.addError(self.exprLoc(eur), .error_propagation_mismatched_function_result, .{});
            return null;
        }

        // Ensure the error/value halves align with the function result type
        const fr = self.context.type_store.ErrorSet.get(self.trow(fctx.result));
        if (self.assignable(er.error_ty, fr.error_ty) != .success or self.assignable(er.value_ty, fr.value_ty) != .success) {
            try self.context.diags.addError(self.exprLoc(eur), .error_propagation_mismatched_function_result, .{});
            return null;
        }
        return er.value_ty;
    }

    fn checkOptionalUnwrap(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const our = self.getExpr(.OptionalUnwrap, id);
        const ot = try self.checkExpr(our.expr) orelse return null;
        if (self.typeKind(ot) != .Optional) {
            try self.context.diags.addError(self.exprLoc(our), .invalid_optional_unwrap_target, .{});
            return null;
        }
        const ore = self.context.type_store.Optional.get(self.trow(ot));
        return ore.elem;
    }

    fn checkAwait(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.context.type_store.tAny();
    }

    fn checkClosure(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cr = self.getExpr(.Closure, id);
        const params = self.ast_unit.exprs.param_pool.slice(cr.params);

        var param_tys = try self.context.type_store.gpa.alloc(types.TypeId, params.len);
        defer self.context.type_store.gpa.free(param_tys);

        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = self.ast_unit.exprs.Param.get(params[i].toRaw());
            if (p.ty.isNone()) {
                try self.context.diags.addError(self.exprLoc(p), .type_annotation_mismatch, .{});
                return null;
            }
            const pt = try check_types.typeFromTypeExpr(self, p.ty.unwrap()) orelse return null;
            param_tys[i] = pt;
        }

        const body_ty = try self.checkExpr(cr.body) orelse return null;
        // Closures are always pure function *types* (no side-effect tracking here).
        return self.context.type_store.mkFunction(param_tys, body_ty, false, true);
    }

    fn checkCast(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cr = self.getExpr(.Cast, id);
        const et = try check_types.typeFromTypeExpr(self, cr.ty) orelse {
            try self.context.diags.addError(self.exprLoc(cr), .cast_target_not_type, .{});
            return null;
        };
        const vt = try self.checkExpr(cr.expr) orelse return null;

        const vk = self.typeKind(vt);
        const ek = self.typeKind(et);

        switch (cr.kind) {
            .normal => {
                if (self.assignable(vt, et) != .success and !self.castable(vt, et)) {
                    try self.context.diags.addError(self.exprLoc(cr), .invalid_cast, .{});
                    return null;
                }
            },
            .bitcast => {
                const gsize = check_types.typeSize(self, vt);
                const tsize = check_types.typeSize(self, et);
                if (gsize == null or tsize == null or gsize.? != tsize.?) {
                    try self.context.diags.addError(self.exprLoc(cr), .invalid_bitcast, .{});
                    return null;
                }
            },
            .saturate, .wrap => {
                if (!check_types.isNumericKind(self, vk) or !check_types.isNumericKind(self, ek)) {
                    try self.context.diags.addError(self.exprLoc(cr), .numeric_cast_on_non_numeric, .{});
                    return null;
                }
            },
            .checked => {
                if (self.assignable(vt, et) != .success and !self.castable(vt, et)) {
                    try self.context.diags.addError(self.exprLoc(cr), .invalid_checked_cast, .{});
                    return null;
                }
            },
        }
        return et;
    }

    fn checkCatch(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cr = self.getExpr(.Catch, id);
        const vt = try self.checkExpr(cr.expr) orelse return null;
        if (self.typeKind(vt) != .ErrorSet) {
            try self.context.diags.addError(self.exprLoc(cr), .catch_on_non_error, .{});
            return null;
        }
        const er = self.context.type_store.ErrorSet.get(self.trow(vt));
        const value_required = self.isValueReq();

        const ht = try self.checkExpr(cr.handler) orelse return null;
        if (!value_required) return self.context.type_store.tVoid();

        if (self.assignable(ht, er.value_ty) != .success) {
            try self.context.diags.addError(self.exprLoc(cr), .if_branch_type_mismatch, .{});
            return null;
        }
        return er.value_ty;
    }

    fn checkImport(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const ir = self.getExpr(.Import, id);
        const k = self.exprKind(ir.expr);
        if (k != .Literal) {
            try self.context.diags.addError(self.exprLoc(ir), .invalid_import_operand, .{});
            return null;
        }
        const lit = self.getExpr(.Literal, ir.expr);
        if (lit.kind != .string or lit.value.isNone()) {
            try self.context.diags.addError(self.exprLoc(ir), .invalid_import_operand, .{});
            return null;
        }
        var path = self.getStr(lit.value.unwrap());
        if (path.len >= 2 and path[0] == '"' and path[path.len - 1] == '"') {
            path = path[1 .. path.len - 1];
        }
        _ = self.context.resolver.resolve(self.import_base_dir, path, self.pipeline) catch {
            try self.context.diags.addError(self.exprLoc(lit), .import_not_found, .{});
        };
        return self.context.type_store.tAny();
    }

    // =========================
    // Misc helpers
    // =========================

    fn checkDivByZero(self: *Checker, rhs: ast.ExprId, loc: Loc) !void {
        if (self.exprKind(rhs) != .Literal) return;
        const lit = self.getExpr(.Literal, rhs);
        switch (lit.kind) {
            .int => {
                if (!lit.value.isNone() and std.mem.eql(u8, self.getStr(lit.value.unwrap()), "0")) {
                    try self.context.diags.addError(loc, .division_by_zero, .{});
                }
            },
            .float, .imaginary => {
                if (!lit.value.isNone()) {
                    const s = self.getStr(lit.value.unwrap());
                    const f = std.fmt.parseFloat(f64, s) catch 1.0;
                    if (f == 0.0) try self.context.diags.addError(loc, .division_by_zero, .{});
                }
            },
            else => {},
        }
    }

    fn checkIntZeroLiteral(self: *Checker, rhs: ast.ExprId, loc: Loc) !void {
        if (self.exprKind(rhs) != .Literal) return;
        const lit = self.getExpr(.Literal, rhs);
        if (lit.kind == .int and !lit.value.isNone()) {
            if (std.mem.eql(u8, self.getStr(lit.value.unwrap()), "0")) {
                try self.context.diags.addError(loc, .division_by_zero, .{});
            }
        }
    }

    const LvalueRootKind = enum { LocalDecl, Param, NonLocalDecl, Unknown };
    fn lvalueRootKind(self: *Checker, expr: ast.ExprId) LvalueRootKind {
        const k = self.exprKind(expr);
        switch (k) {
            .Ident => {
                const idr = self.getExpr(.Ident, expr);
                // Discard assignment '_' is considered local
                if (std.mem.eql(u8, self.getStr(idr.name), "_")) return .LocalDecl;
                if (self.lookup(idr.name)) |sid_sym| {
                    const sym = self.symtab.syms.get(sid_sym.toRaw());
                    if (!sym.origin_param.isNone()) return .Param;
                    if (!sym.origin_decl.isNone()) {
                        const did = sym.origin_decl.unwrap();
                        if (self.inFunction()) {
                            const fctx = self.currentFunc().?;
                            return if (fctx.locals.contains(did.toRaw())) .LocalDecl else .NonLocalDecl;
                        }
                        return .NonLocalDecl;
                    }
                }
                return .Unknown;
            },
            .Deref => {
                const dr = self.getExpr(.Deref, expr);
                return self.lvalueRootKind(dr.expr);
            },
            .FieldAccess => {
                const fr = self.getExpr(.FieldAccess, expr);
                return self.lvalueRootKind(fr.parent);
            },
            .IndexAccess => {
                const ir = self.getExpr(.IndexAccess, expr);
                return self.lvalueRootKind(ir.collection);
            },
            else => return .Unknown,
        }
    }
};
