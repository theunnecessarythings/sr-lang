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

pub const Checker = struct {
    gpa: std.mem.Allocator,
    diags: *Diagnostics,
    ast_unit: *const ast.Ast,
    type_info: TypeInfo,

    // Optional import resolver for module member resolution
    import_resolver: ?*ImportResolver = null,
    import_base_dir: []const u8 = ".",

    symtab: symbols.SymbolStore = undefined,

    func_stack: std.ArrayListUnmanaged(FunctionCtx) = .{},
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},
    value_ctx: std.ArrayListUnmanaged(bool) = .{},
    warned_meta: bool = false,
    warned_comptime: bool = false,
    warned_code: bool = false,

    // Current loop pattern context for binding type inference inside loop bodies
    current_loop_pat: ast.OptPatternId = ast.OptPatternId.none(),
    current_loop_subject_ty: ?types.TypeId = null,

    // --------- tiny helpers (readability & consistency) ----------
    inline fn typeKind(self: *const Checker, t: types.TypeId) types.TypeKind {
        return self.type_info.store.index.kinds.items[t.toRaw()];
    }
    inline fn trow(self: *const Checker, t: types.TypeId) u32 {
        return self.type_info.store.index.rows.items[t.toRaw()];
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
        diags: *Diagnostics,
        unit: *ast.Ast,
    ) Checker {
        return .{
            .gpa = gpa,
            .diags = diags,
            .ast_unit = unit,
            .symtab = symbols.SymbolStore.init(gpa),
            .type_info = types.TypeInfo.init(gpa, unit.exprs.strs),
        };
    }

    pub fn setImportResolver(self: *Checker, r: *ImportResolver, base_dir: []const u8) void {
        self.import_resolver = r;
        self.import_base_dir = base_dir;
    }

    pub fn deinit(self: *Checker) void {
        self.func_stack.deinit(self.gpa);
        self.loop_stack.deinit(self.gpa);
        self.value_ctx.deinit(self.gpa);
        self.symtab.deinit();
    }

    pub fn run(self: *Checker) !void {
        _ = try self.runWithTypes();
    }

    pub fn runWithTypes(self: *Checker) !TypeInfo {
        // pre-allocate type slots for all exprs & decls
        const expr_len: usize = self.ast_unit.exprs.index.kinds.items.len;
        const decl_len: usize = self.ast_unit.exprs.Decl.list.len;
        try self.type_info.expr_types.appendNTimes(self.gpa, null, expr_len);
        try self.type_info.decl_types.appendNTimes(self.gpa, null, decl_len);

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
        // Returning a copy-by-value is fine as long as callers treat it as BORROWED.
        // Prefer exposing a &TypeInfo accessor in the long run.
        return self.type_info;
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
            const got_opt = self.type_info.store.Optional.get(self.trow(got));
            const elem_kind = self.typeKind(got_opt.elem);
            if (elem_kind == .Any) return .assign_null_to_non_optional;
            // Implicit unwrap from Optional(T) -> T is not permitted.
            return .failure;
        }

        switch (expected_kind) {
            .Slice => {
                if (got_kind != .Slice) return .failure;
                const expected_ty = self.type_info.store.Slice.get(self.trow(expect));
                const got_ty = self.type_info.store.Slice.get(self.trow(got));
                return self.assignable(got_ty.elem, expected_ty.elem);
            },
            .Array => {
                if (got_kind != .Array) return .expected_array_type;
                const expected_ty = self.type_info.store.Array.get(self.trow(expect));
                const got_ty = self.type_info.store.Array.get(self.trow(got));
                const elem_ok = self.assignable(got_ty.elem, expected_ty.elem);
                if (expected_ty.len != got_ty.len)
                    return .array_length_mismatch;
                return elem_ok;
            },
            .DynArray => {
                // BUGFIX: allow assigning from DynArray itself AND from Array/Slice (element-compatible).
                const expected_ty = self.type_info.store.DynArray.get(self.trow(expect));
                switch (got_kind) {
                    .DynArray => {
                        const got_ty = self.type_info.store.DynArray.get(self.trow(got));
                        return self.assignable(got_ty.elem, expected_ty.elem);
                    },
                    .Array => {
                        const got_ty = self.type_info.store.Array.get(self.trow(got));
                        return self.assignable(got_ty.elem, expected_ty.elem);
                    },
                    .Slice => {
                        const got_ty = self.type_info.store.Slice.get(self.trow(got));
                        return self.assignable(got_ty.elem, expected_ty.elem);
                    },
                    else => return .expected_array_type,
                }
            },
            .Tuple => {
                if (got_kind != .Tuple) return .expected_tuple_type;
                const expected_ty = self.type_info.store.Tuple.get(self.trow(expect));
                const got_ty = self.type_info.store.Tuple.get(self.trow(got));
                if (expected_ty.elems.len != got_ty.elems.len) return .tuple_arity_mismatch;
                const got_elems = self.type_info.store.type_pool.slice(got_ty.elems);
                const expected_elems = self.type_info.store.type_pool.slice(expected_ty.elems);
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
                    const got_ty = self.type_info.store.Array.get(self.trow(got));
                    if (got_ty.len != 0) return .expected_map_type;
                    return .success;
                }
                if (got_kind != .Map) return .expected_map_type;
                const expected_ty = self.type_info.store.Map.get(self.trow(expect));
                const got_ty = self.type_info.store.Map.get(self.trow(got));
                const key_ok = self.assignable(got_ty.key, expected_ty.key);
                const value_ok = self.assignable(got_ty.value, expected_ty.value);
                if (key_ok != .success) return .map_wrong_key_type;
                if (value_ok != .success) return value_ok;
                return .success;
            },
            .Optional => {
                const expected_ty = self.type_info.store.Optional.get(self.trow(expect));
                if (got_kind == .Optional) {
                    const got_ty = self.type_info.store.Optional.get(self.trow(got));
                    return self.assignable(got_ty.elem, expected_ty.elem);
                }
                return self.assignable(got, expected_ty.elem);
            },
            .Ptr => {
                if (got_kind != .Ptr) return .expected_pointer_type;
                const expected_ty = self.type_info.store.Ptr.get(self.trow(expect));
                const got_ty = self.type_info.store.Ptr.get(self.trow(got));
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
                const expected_ty = self.type_info.store.Union.get(self.trow(expect));
                const got_ty = self.type_info.store.Struct.get(self.trow(got));
                const expected_fields = self.type_info.store.field_pool.slice(expected_ty.fields);
                const got_fields = self.type_info.store.field_pool.slice(got_ty.fields);
                // Should only have one field set in union
                if (got_fields.len == 0) return .union_literal_no_fields;
                if (got_fields.len != 1) return .union_literal_multiple_fields;
                const gf = self.type_info.store.Field.get(got_fields[0].toRaw());
                var found = false;
                for (expected_fields) |efid| {
                    const ef = self.type_info.store.Field.get(efid.toRaw());
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
                const expected_ty = self.type_info.store.Struct.get(self.trow(expect));
                const got_ty = self.type_info.store.Struct.get(self.trow(got));
                const expected_fields = self.type_info.store.field_pool.slice(expected_ty.fields);
                const got_fields = self.type_info.store.field_pool.slice(got_ty.fields);
                if (expected_fields.len < got_fields.len) return .unknown_struct_field;
                if (expected_fields.len > got_fields.len) return .struct_field_count_mismatch;

                // Check fields by name, not by order.
                for (expected_fields) |efid| {
                    const ef = self.type_info.store.Field.get(efid.toRaw());
                    var found = false;
                    for (got_fields) |gfid| {
                        const gf = self.type_info.store.Field.get(gfid.toRaw());
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
                const efn = self.type_info.store.Function.get(self.trow(expect));
                const gfn = self.type_info.store.Function.get(self.trow(got));
                if (efn.is_variadic != gfn.is_variadic) return .failure;
                const eparams = self.type_info.store.type_pool.slice(efn.params);
                const gparams = self.type_info.store.type_pool.slice(gfn.params);
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
                const expected_ty = self.type_info.store.ErrorSet.get(self.trow(expect));
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
                    try self.diags.addError(self.exprLoc(decl), .tuple_arity_mismatch, .{});
                    return;
                },
                .struct_field_mismatch => {
                    try self.diags.addError(self.exprLoc(decl), .struct_pattern_field_mismatch, .{});
                    return;
                },
                .shape_mismatch => {
                    try self.diags.addError(self.exprLoc(decl), .pattern_shape_mismatch, .{});
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
                    const arr = self.type_info.store.Array.get(self.trow(rhs_ty));
                    if (arr.len == 0) {
                        try self.diags.addError(self.exprLoc(self.ast_unit.exprs.Decl.get(decl.toRaw())), .cannot_infer_type_from_empty_array, .{});
                        return;
                    }
                },
                else => {
                    // infer from RHS
                    self.type_info.decl_types.items[decl.toRaw()] = rhs_ty;
                },
            }
        } else {
            const is_assignable = self.assignable(rhs_ty, expect_ty.?);
            const d = self.ast_unit.exprs.Decl.get(decl.toRaw());
            switch (is_assignable) {
                .success => {
                    // Use expected type and also update RHS expr type for consistency.
                    self.type_info.decl_types.items[decl.toRaw()] = expect_ty.?;
                    self.type_info.expr_types.items[d.value.toRaw()] = expect_ty.?;
                },
                .map_wrong_key_type => try self.diags.addError(self.exprLoc(d), .map_wrong_key_type, .{}),
                .union_literal_no_fields => try self.diags.addError(self.exprLoc(d), .union_empty_literal, .{}),
                .union_literal_multiple_fields => try self.diags.addError(self.exprLoc(d), .union_literal_multiple_fields, .{}),
                .expected_enum_type => try self.diags.addError(self.exprLoc(d), .expected_enum_type, .{}),
                .expected_struct_type => try self.diags.addError(self.exprLoc(d), .expected_struct_type, .{}),
                .struct_field_count_mismatch => try self.diags.addError(self.exprLoc(d), .struct_field_count_mismatch, .{}),
                .unknown_struct_field => try self.diags.addError(self.exprLoc(d), .unknown_struct_field, .{}),
                .struct_field_name_mismatch => try self.diags.addError(self.exprLoc(d), .struct_field_name_mismatch, .{}),
                .noreturn_not_storable => try self.diags.addError(self.exprLoc(d), .noreturn_not_storable, .{}),
                .type_value_mismatch => try self.diags.addError(self.exprLoc(d), .type_value_mismatch, .{}),
                .array_length_mismatch => try self.diags.addError(self.exprLoc(d), .array_length_mismatch, .{}),
                .tuple_arity_mismatch => try self.diags.addError(self.exprLoc(d), .tuple_arity_mismatch, .{}),
                .assign_null_to_non_optional => try self.diags.addError(self.exprLoc(d), .assign_null_to_non_optional, .{}),
                .pointer_type_mismatch => try self.diags.addError(self.exprLoc(d), .pointer_type_mismatch, .{}),
                .pointer_constness_mismatch => try self.diags.addError(self.exprLoc(d), .pointer_constness_violation, .{}),
                .expected_array_type => try self.diags.addError(self.exprLoc(d), .expected_array_type, .{}),
                .expected_tuple_type => try self.diags.addError(self.exprLoc(d), .expected_tuple_type, .{}),
                .expected_map_type => try self.diags.addError(self.exprLoc(d), .expected_map_type, .{}),
                .expected_pointer_type => try self.diags.addError(self.exprLoc(d), .expected_pointer_type, .{}),
                .expected_integer_type => try self.diags.addError(self.exprLoc(d), .expected_integer_type, .{}),
                .expected_float_type => try self.diags.addError(self.exprLoc(d), .expected_float_type, .{}),
                .failure => try self.diags.addError(self.exprLoc(d), .type_annotation_mismatch, .{}),
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
                            .tuple_arity_mismatch => try self.diags.addError(self.exprLoc(stmt), .tuple_arity_mismatch, .{}),
                            .struct_field_mismatch => try self.diags.addError(self.exprLoc(stmt), .struct_pattern_field_mismatch, .{}),
                            .shape_mismatch => try self.diags.addError(self.exprLoc(stmt), .pattern_shape_mismatch, .{}),
                        }
                    }
                } else {
                    const lt = try self.checkExpr(stmt.left);
                    // RHS of assignment should be checked in value context
                    try self.pushValueReq(true);
                    const rt = try self.checkExpr(stmt.right);
                    self.popValueReq();
                    if (lt != null and rt != null and (self.assignable(rt.?, lt.?) != .success)) {
                        try self.diags.addError(self.exprLoc(stmt), .type_annotation_mismatch, .{});
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
                                try self.diags.addError(self.exprLoc(stmt), .purity_violation, .{});
                                self.func_stack.items[self.func_stack.items.len - 1].pure = false;
                            },
                        }
                    }
                }
            },
            .Insert => {
                const row = self.getStmt(.Insert, sid);
                if (!self.warned_meta) {
                    _ = self.diags.addNote(self.exprLoc(row), .checker_insert_not_expanded, .{}) catch {};
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
                    try self.diags.addError(self.exprLoc(row), .break_outside_loop, .{});
                if (!row.value.isNone()) {
                    // Break value must be computed in value context
                    try self.pushValueReq(true);
                    const vt = try self.checkExpr(row.value.unwrap());
                    self.popValueReq();
                    if (vt == null) return null;
                    if (self.loopCtxForLabel(row.label)) |ctx| {
                        if (ctx.result_ty) |rt| {
                            if (rt.toRaw() != vt.?.toRaw()) {
                                try self.diags.addError(self.exprLoc(row), .loop_break_value_type_conflict, .{});
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
                    try self.diags.addError(self.exprLoc(row), .continue_outside_loop, .{});
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
            .VariantLit => unreachable,
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
            .UndefLit => self.type_info.store.tAny(),

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
            .NullLit => self.type_info.store.mkOptional(self.type_info.store.tAny()),

            .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => blk: {
                const ty = try check_types.typeFromTypeExpr(self, id);
                if (ty == null) break :blk null;
                break :blk self.type_info.store.mkTypeType(ty.?);
            },
            .MapType => blk_mt_expr: {
                // Try to interpret as a type expression first
                const row = self.getExpr(.MapType, id);
                const key_ty = try check_types.typeFromTypeExpr(self, row.key);
                const val_ty = try check_types.typeFromTypeExpr(self, row.value);
                if (key_ty != null and val_ty != null) {
                    break :blk_mt_expr self.type_info.store.mkTypeType(self.type_info.store.mkMap(key_ty.?, val_ty.?));
                }
                // If not valid types, interpret operands as value expressions and produce a map value type
                const key_vt = try self.checkExpr(row.key);
                const val_vt = try self.checkExpr(row.value);
                if (key_vt == null or val_vt == null) break :blk_mt_expr null;
                break :blk_mt_expr self.type_info.store.mkMap(key_vt.?, val_vt.?);
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
                    try self.diags.addError(self.exprLoc(lit), .invalid_integer_literal, .{});
                    return null;
                }
                break :blk self.type_info.store.tI64();
            },
            .float => blk: {
                // try parsing the float literal
                const s = self.getStr(lit.value.unwrap());
                if (std.fmt.parseFloat(f64, s) catch null == null) {
                    try self.diags.addError(self.exprLoc(lit), .invalid_float_literal, .{});
                    return null;
                }
                break :blk self.type_info.store.tF64();
            },
            .bool => self.type_info.store.tBool(),
            .string => self.type_info.store.tString(),
            .char => self.type_info.store.tU32(),
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
                    return self.type_info.store.tAny();
                }
            }
            // Loop-pattern-originated symbol? Infer from current loop pattern context if available
            if (self.current_loop_subject_ty != null and !self.current_loop_pat.isNone()) {
                const bt = pattern_matching.bindingTypeInPattern(self, self.current_loop_pat.unwrap(), row.name, self.current_loop_subject_ty.?);
                if (bt) |btid| return btid;
            }
        }
        return null;
    }

    fn checkBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const br = self.getExpr(.Block, id);
        const stmts = self.ast_unit.stmts.stmt_pool.slice(br.items);
        var i: usize = 0;
        _ = try self.symtab.push(self.symtab.currentId());
        defer self.symtab.pop();

        if (stmts.len == 0) return self.type_info.store.tVoid();
        const value_required = self.isValueReq();
        var after_break: bool = false;
        if (!value_required) {
            // Statement context: just type-check children, no value produced
            while (i < stmts.len) : (i += 1) {
                if (after_break) {
                    const loc = self.stmtLoc(stmts[i]);
                    try self.diags.addError(loc, .unreachable_code_after_break, .{});
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
            return self.type_info.store.tVoid();
        }
        // Value context: the last line must be an expression to produce a value
        while (i < stmts.len - 1) : (i += 1) {
            if (after_break) {
                const loc = self.stmtLoc(stmts[i]);
                try self.diags.addError(loc, .unreachable_code_after_break, .{});
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
                try self.diags.addError(loc, .unreachable_code_after_break, .{});
                return null;
            }
            const row = self.getStmt(.Expr, last);
            return try self.checkExpr(row.expr);
        }
        // Otherwise, type-check the statement and treat as void
        if (after_break) {
            const loc = self.stmtLoc(last);
            try self.diags.addError(loc, .unreachable_code_after_break, .{});
            return null;
        }
        _ = try self.checkStmt(last);
        return self.type_info.store.tVoid();
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
                        try self.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{});
                        return null;
                    }
                    if (check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind))
                        try self.checkIntZeroLiteral(bin.right, self.exprLoc(bin));
                }
                if (!check_types.isNumericKind(self, lhs_kind) or !check_types.isNumericKind(self, rhs_kind)) {
                    try self.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{});
                    return null;
                }
                if (l.toRaw() == r.toRaw()) return l;
                try self.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{});
                return null;
            },
            .eq, .neq, .lt, .lte, .gt, .gte => {
                const both_ints = check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind);
                const both_floats = (lhs_kind == .F32 or lhs_kind == .F64) and (rhs_kind == .F32 or rhs_kind == .F64);
                const both_bools = lhs_kind == .Bool and rhs_kind == .Bool;

                // We avoid implicit *value* coercions. For comparisons, we accept same-class operands:
                //   - int ? int (any width/sign)
                //   - float ? float (F32/F64 mixed ok)
                //   - bool ? bool
                if (!(both_ints or both_floats or both_bools)) {
                    try self.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{});
                    return null;
                }
                return self.type_info.store.tBool();
            },
            .logical_and, .logical_or => {
                if (l.toRaw() == self.type_info.store.tBool().toRaw() and
                    r.toRaw() == self.type_info.store.tBool().toRaw())
                    return self.type_info.store.tBool();
                try self.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{});
                return null;
            },
            .@"orelse" => {
                if (check_types.isOptional(self, l)) |elem| {
                    if (self.assignable(elem, r) == .success) {
                        return elem;
                    } else return {
                        try self.diags.addError(self.exprLoc(bin), .invalid_binary_op_operands, .{});
                        return null;
                    };
                }
                try self.diags.addError(self.exprLoc(bin), .invalid_use_of_orelse_on_non_optional, .{});
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
            .plus, .minus => {
                if (!check_types.isNumericKind(self, type_kind)) {
                    try self.diags.addError(self.exprLoc(unary_expr), .invalid_unary_op_operand, .{});
                    return null;
                }
                return t;
            },
            .logical_not => {
                // Accept bool or any
                if (t.toRaw() != self.type_info.store.tBool().toRaw() and t.toRaw() != self.type_info.store.tAny().toRaw()) {
                    try self.diags.addError(self.exprLoc(unary_expr), .invalid_unary_op_operand, .{});
                    return null;
                }
                return self.type_info.store.tBool();
            },
            .address_of => return self.type_info.store.mkPtr(t, false),
        }
    }

    fn checkFunctionLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const fnr = self.getExpr(.FunctionLit, id);
        const res = if (!fnr.result_ty.isNone())
            (try check_types.typeFromTypeExpr(self, fnr.result_ty.unwrap()))
        else
            self.type_info.store.tVoid();
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
                            try self.diags.addError(self.exprLoc(fnr), .tuple_arity_mismatch, .{});
                            return null;
                        },
                        .struct_field_mismatch => {
                            try self.diags.addError(self.exprLoc(fnr), .struct_pattern_field_mismatch, .{});
                            return null;
                        },
                        .shape_mismatch => {
                            try self.diags.addError(self.exprLoc(fnr), .pattern_shape_mismatch, .{});
                            return null;
                        },
                    }
                }
                pbuf[i] = pt;
            } else {
                pbuf[i] = self.type_info.store.tAny();
            }
            // store in symbol table
            try self.bindParamPattern(params[i], p);
        }

        // Temporarily record a function type (purity will be finalized after body analysis)
        if (res == null) return null;
        const temp_ty = self.type_info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic, true);
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
        const final_ty = self.type_info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic, is_pure);
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
        return self.type_info.store.mkTuple(tbuf);
    }

    fn checkArrayLit(
        self: *Checker,
        id: ast.ExprId,
    ) !?types.TypeId {
        const array_lit = self.getExpr(.ArrayLit, id);
        const elems = self.ast_unit.exprs.expr_pool.slice(array_lit.elems);

        // infer from first element, homogeneous requirement
        if (elems.len == 0) {
            return self.type_info.store.mkArray(self.type_info.store.tAny(), 0);
        }
        const first_ty = (try self.checkExpr(elems[0])) orelse return null;
        var i: usize = 1;
        while (i < elems.len) : (i += 1) {
            const ety = try self.checkExpr(elems[i]);
            if (ety == null or ety.?.toRaw() != first_ty.toRaw()) {
                try self.diags.addError(self.exprLoc(array_lit), .heterogeneous_array_elements, .{});
                return null;
            }
        }
        return self.type_info.store.mkArray(first_ty, elems.len);
    }

    fn checkMapLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const row = self.getExpr(.MapLit, id);
        const kvs = self.ast_unit.exprs.kv_pool.slice(row.entries);

        if (kvs.len == 0) {
            return self.type_info.store.mkMap(self.type_info.store.tAny(), self.type_info.store.tAny());
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
                try self.diags.addError(self.exprLoc(row), .map_mixed_key_types, .{});
                return null;
            }
            if (vt == null or vt.?.toRaw() != val_ty.?.toRaw()) {
                try self.diags.addError(self.exprLoc(row), .map_mixed_value_types, .{});
                return null;
            }
        }
        return self.type_info.store.mkMap(key_ty.?, val_ty.?);
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
                const m = self.type_info.store.Map.get(self.trow(col_ty.?));
                const it = self.checkExpr(index_expr.index) catch return null;
                if (it) |iid| {
                    if (iid.toRaw() != m.key.toRaw()) {
                        _ = self.diags.addError(self.exprLoc(index_expr), .map_wrong_key_type, .{}) catch {};
                        return null;
                    }
                }
                return m.value;
            },

            .String => {
                const it = self.checkExpr(index_expr.index) catch return null;
                if (it) |iid| {
                    if (!check_types.isIntegerKind(self, self.typeKind(iid))) {
                        _ = self.diags.addError(self.exprLoc(index_expr), .non_integer_index, .{}) catch {};
                        return null;
                    }
                }
                return self.type_info.store.tU8();
            },
            else => {
                _ = self.diags.addError(self.exprLoc(index_expr), .not_indexable, .{}) catch {};
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
                    const r = self.type_info.store.Array.get(self.trow(col_ty));
                    break :blk self.type_info.store.mkSlice(r.elem);
                },
                .Slice => blk2: {
                    const r = self.type_info.store.Slice.get(self.trow(col_ty));
                    break :blk2 self.type_info.store.mkSlice(r.elem);
                },
                else => unreachable,
            };
        }
        const it = self.checkExpr(idx_expr) catch return null;
        if (it) |iid| {
            if (!check_types.isIntegerKind(self, self.typeKind(iid))) {
                _ = self.diags.addError(loc, .non_integer_index, .{}) catch {};
                return null;
            }
        }
        return switch (col_kind) {
            .Array => blk3: {
                const r = self.type_info.store.Array.get(self.trow(col_ty));
                break :blk3 r.elem;
            },
            .Slice => blk4: {
                const r = self.type_info.store.Slice.get(self.trow(col_ty));
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
            if (self.import_resolver) |_| {
                if (self.importMemberType(field_expr.parent, field_expr.field)) |mt| {
                    // For imported members we don't currently expose a precise index
                    // into a struct; do not set a field index here.
                    return mt;
                }
            } else {
                if (self.importHasMember(field_expr.parent, field_expr.field))
                    return self.type_info.store.tAny();
                _ = self.diags.addError(self.exprLoc(field_expr), .unknown_struct_field, .{}) catch {};
                return null;
            }
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
                        if (self.import_resolver) |_| {
                            if (self.importMemberType(drow.value, field_expr.field)) |mt| {
                                return mt;
                            }
                        } else if (self.importHasMember(drow.value, field_expr.field)) {
                            return self.type_info.store.tAny();
                        }
                        _ = self.diags.addError(self.exprLoc(field_expr), .unknown_struct_field, .{}) catch {};
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
            .Struct => {
                const struct_row = self.type_info.store.Struct.get(self.trow(ty));
                const fields = self.type_info.store.field_pool.slice(struct_row.fields);
                var i: usize = 0;
                while (i < fields.len) : (i += 1) {
                    const f = self.type_info.store.Field.get(fields[i].toRaw());
                    if (f.name.toRaw() == field_expr.field.toRaw()) {
                        try self.type_info.setFieldIndex(id, @intCast(i));
                        return f.ty;
                    }
                }
                _ = self.diags.addError(self.exprLoc(field_expr), .unknown_struct_field, .{}) catch {};
                return null;
            },
            .Tuple => {
                const tuple_row = self.type_info.store.Tuple.get(self.trow(ty));
                const elems = self.type_info.store.type_pool.slice(tuple_row.elems);
                const index = std.fmt.parseInt(usize, self.getStr(field_expr.field), 10) catch {
                    _ = self.diags.addError(self.exprLoc(field_expr), .expected_field_name_or_index, .{}) catch {};
                    return null;
                };
                if (index >= elems.len) {
                    _ = self.diags.addError(self.exprLoc(field_expr), .tuple_index_out_of_bounds, .{}) catch {};
                    return null;
                }
                try self.type_info.setFieldIndex(id, @intCast(index));
                return elems[index];
            },
            .Ptr => {
                const ptr_row = self.type_info.store.Ptr.get(self.trow(ty));
                ty = ptr_row.elem;
                const inner_kind = self.typeKind(ty);
                if (inner_kind == .Struct) {
                    const struct_row = self.type_info.store.Struct.get(self.trow(ty));
                    const fields = self.type_info.store.field_pool.slice(struct_row.fields);
                    var i: usize = 0;
                    while (i < fields.len) : (i += 1) {
                        const f = self.type_info.store.Field.get(fields[i].toRaw());
                        if (f.name.toRaw() == field_expr.field.toRaw()) {
                            try self.type_info.setFieldIndex(id, @intCast(i));
                            return f.ty;
                        }
                    }
                    _ = self.diags.addError(self.exprLoc(field_expr), .unknown_struct_field, .{}) catch {};
                    return null;
                }
                _ = self.diags.addError(self.exprLoc(field_expr), .field_access_on_non_aggregate, .{}) catch {};
                return null;
            },
            .TypeType => {
                const tt = self.type_info.store.TypeType.get(self.trow(ty));
                ty = tt.of;
                const inner_kind = self.typeKind(ty);

                if (inner_kind == .Enum) {
                    const en = self.type_info.store.Enum.get(self.trow(ty));
                    const members = self.type_info.store.enum_member_pool.slice(en.members);
                    var i: usize = 0;
                    while (i < members.len) : (i += 1) {
                        const m = self.type_info.store.EnumMember.get(members[i].toRaw());
                        if (m.name.toRaw() == field_expr.field.toRaw()) {
                            // Selecting an enum tag as a value of the enum type.
                            try self.type_info.setFieldIndex(id, @intCast(i));
                            return ty;
                        }
                    }
                    _ = self.diags.addError(self.exprLoc(field_expr), .unknown_enum_tag, .{}) catch {};
                    return null;
                } else if (inner_kind == .Variant) {
                    const vr = self.type_info.store.Variant.get(self.trow(ty));
                    const variants = self.type_info.store.field_pool.slice(vr.variants);
                    var i: usize = 0;
                    while (i < variants.len) : (i += 1) {
                        const v = self.type_info.store.Field.get(variants[i].toRaw());
                        if (v.name.toRaw() == field_expr.field.toRaw()) {
                            // In value position, selecting a variant *tag* without args:
                            // if payload is void => ok (value of the variant type)
                            // else => arity mismatch (should be constructed via call)
                            const pk = self.typeKind(v.ty);
                            if (pk == .Void) {
                                try self.type_info.setFieldIndex(id, @intCast(i));
                                return ty;
                            }
                            _ = self.diags.addError(self.exprLoc(field_expr), .variant_payload_arity_mismatch, .{}) catch {};
                            return null;
                        }
                    }
                    _ = self.diags.addError(self.exprLoc(field_expr), .unknown_variant_tag, .{}) catch {};
                    return null;
                } else if (inner_kind == .Error) {
                    const er = self.type_info.store.Error.get(self.trow(ty));
                    const tags = self.type_info.store.field_pool.slice(er.variants);
                    var i: usize = 0;
                    while (i < tags.len) : (i += 1) {
                        const t = self.type_info.store.Field.get(tags[i].toRaw());
                        if (t.name.toRaw() == field_expr.field.toRaw()) {
                            try self.type_info.setFieldIndex(id, @intCast(i));
                            return ty;
                        }
                    }
                    _ = self.diags.addError(self.exprLoc(field_expr), .unknown_error_tag, .{}) catch {};
                    return null;
                }

                _ = self.diags.addError(self.exprLoc(field_expr), .field_access_on_non_aggregate, .{}) catch {};
                return null;
            },
            else => {
                _ = self.diags.addError(self.exprLoc(field_expr), .field_access_on_non_aggregate, .{}) catch {};
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
        if (self.import_resolver) |res| return self.importMemberTypeByPath(res, path, member) != null;
        // fallback: no resolver
        return false;
    }

    fn importMemberTypeByPath(self: *Checker, res: *ImportResolver, path: []const u8, member: ast.StrId) ?types.TypeId {
        const me = res.resolve(self.import_base_dir, path) catch return null;
        const target = self.getStr(member);
        if (me.syms.get(target)) |ty| {
            return check_types.translateType(self, &me.type_info.store, &self.type_info.store, ty);
        }
        return null;
    }

    fn importMemberType(self: *Checker, import_eid: ast.ExprId, member: ast.StrId) ?types.TypeId {
        if (self.import_resolver == null) return null;
        const res = self.import_resolver.?;
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
                try self.diags.addError(self.exprLoc(rr), .non_integer_index, .{});
                return null;
            }
        }
        if (!rr.end.isNone()) {
            const et = try self.checkExpr(rr.end.unwrap());
            if (et == null or !check_types.isIntegerKind(self, self.typeKind(et.?))) {
                try self.diags.addError(self.exprLoc(rr), .non_integer_index, .{});
                return null;
            }
        }
        return self.type_info.store.mkSlice(self.type_info.store.tUsize());
    }

    fn checkStructLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const struct_lit = self.getExpr(.StructLit, id);
        const lit_fields = self.ast_unit.exprs.sfv_pool.slice(struct_lit.fields);
        var buf = try self.type_info.store.gpa.alloc(types.TypeStore.StructFieldArg, lit_fields.len);
        defer self.type_info.store.gpa.free(buf);
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
        const struct_ty = self.type_info.store.mkStruct(buf);
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
                try self.diags.addError(self.exprLoc(struct_lit), .struct_missing_field, .{});
                return null;
            },
            .unknown_struct_field => {
                try self.diags.addError(self.exprLoc(struct_lit), .unknown_struct_field, .{});
                return null;
            },
            .union_literal_multiple_fields => {
                try self.diags.addError(self.exprLoc(struct_lit), .union_literal_multiple_fields, .{});
                return null;
            },
            .union_literal_no_fields => {
                try self.diags.addError(self.exprLoc(struct_lit), .union_empty_literal, .{});
                return null;
            },
            else => {
                try self.diags.addError(self.exprLoc(struct_lit), .struct_field_type_mismatch, .{});
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
            try self.diags.addError(self.exprLoc(row), .deref_non_pointer, .{});
            return null;
        }
        const ptr_row = self.type_info.store.Ptr.get(self.trow(ptr_ty));
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
                const vt = self.type_info.store.Variant.get(self.trow(parent_ty));
                const cases = self.type_info.store.field_pool.slice(vt.variants);
                for (cases) |fid| {
                    const f = self.type_info.store.Field.get(fid.toRaw());
                    if (f.name.toRaw() == tag.toRaw()) return f.ty;
                }
            },
            .Error => {
                const et = self.type_info.store.Error.get(self.trow(parent_ty));
                const cases = self.type_info.store.field_pool.slice(et.variants);
                for (cases) |fid| {
                    const f = self.type_info.store.Field.get(fid.toRaw());
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
            self.type_info.store.field_pool.slice(self.type_info.store.Variant.get(self.trow(parent_ty)).variants)
        else
            self.type_info.store.field_pool.slice(self.type_info.store.Error.get(self.trow(parent_ty)).variants);

        // Find the tag & payload type
        var payload_ty_opt: ?types.TypeId = null;
        for (cases) |cid| {
            const c = self.type_info.store.Field.get(cid.toRaw());
            if (c.name.toRaw() == tag.toRaw()) {
                payload_ty_opt = c.ty;
                break;
            }
        }
        if (payload_ty_opt == null) {
            if (pk == .Variant) {
                try self.diags.addError(loc, .unknown_variant_tag, .{});
            } else {
                try self.diags.addError(loc, .unknown_error_tag, .{});
            }
            return null;
        }

        const payload_ty = payload_ty_opt.?;
        const payload_kind = self.typeKind(payload_ty);

        switch (payload_kind) {
            .Void => {
                // Tag-only: must have zero args
                if (args.len != 0) {
                    try self.diags.addError(loc, .argument_count_mismatch, .{});
                    return null;
                }
                return parent_ty;
            },
            .Tuple => {
                // Exact arity, per-element type check
                const tup = self.type_info.store.Tuple.get(self.trow(payload_ty));
                const params = self.type_info.store.type_pool.slice(tup.elems);

                if (args.len != params.len) {
                    // IMPORTANT: only one arity diagnostic
                    try self.diags.addError(loc, .argument_count_mismatch, .{});
                    return null;
                }

                var i: usize = 0;
                while (i < args.len) : (i += 1) {
                    const at = try self.checkExpr(args[i]) orelse return null;
                    if (self.assignable(at, params[i]) != .success) {
                        // IMPORTANT: only one type diagnostic
                        try self.diags.addError(loc, .argument_type_mismatch, .{});
                        return null;
                    }
                }
                return parent_ty;
            },
            else => {
                // Non-void, non-tuple payloads (e.g. struct) are not callable: use literals like Type.Tag{...}
                try self.diags.addError(loc, .call_non_callable, .{});
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
                    try self.diags.addError(call_loc, .call_non_callable, .{});
                    return null;
                }
                const fnrow = self.type_info.store.Function.get(self.trow(fty));
                const params = self.type_info.store.type_pool.slice(fnrow.params);

                if (!fnrow.is_variadic and args.len != params.len) {
                    try self.diags.addError(call_loc, .argument_count_mismatch, .{});
                    return null;
                }
                const fixed = if (params.len == 0) 0 else if (fnrow.is_variadic) params.len - 1 else params.len;

                var i: usize = 0;
                while (i < args.len) : (i += 1) {
                    const at = try self.checkExpr(args[i]) orelse return null;
                    const pt = if (i < fixed) params[i] else params[fixed];
                    if (self.assignable(at, pt) != .success) {
                        try self.diags.addError(call_loc, .argument_type_mismatch, .{});
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
                    try self.diags.addError(call_loc, .unknown_function, .{});
                }
            }
            return null;
        }
        const func_ty = func_ty_opt.?;
        const func_kind = self.typeKind(func_ty);

        // Tuple-as-constructor: `(T0,T1,..)(a0,a1,..)` -> construct the tuple type.
        if (func_kind == .Tuple) {
            const tup = self.type_info.store.Tuple.get(self.trow(func_ty));
            const params = self.type_info.store.type_pool.slice(tup.elems);
            if (args.len != params.len) {
                try self.diags.addError(call_loc, .argument_count_mismatch, .{});
                return null;
            }
            var i: usize = 0;
            while (i < args.len) : (i += 1) {
                const at = try self.checkExpr(args[i]) orelse return null;
                if (self.assignable(at, params[i]) != .success) {
                    try self.diags.addError(call_loc, .argument_type_mismatch, .{});
                    return null;
                }
            }
            return func_ty;
        }

        if (func_kind != .Function) {
            try self.diags.addError(call_loc, .call_non_callable, .{});
            return null;
        }

        // Purity bookkeeping / enforcement
        const fnrow = self.type_info.store.Function.get(self.trow(func_ty));
        if (self.inFunction()) {
            const fctx = self.currentFunc().?;
            if (fctx.require_pure and !fnrow.is_pure) {
                try self.diags.addError(call_loc, .purity_violation, .{});
                return null;
            }
            if (!fnrow.is_pure) {
                const idx = self.func_stack.items.len - 1;
                self.func_stack.items[idx].pure = false;
            }
        }

        // Arity & argument type checks
        const params = self.type_info.store.type_pool.slice(fnrow.params);
        if (!fnrow.is_variadic) {
            if (args.len != params.len) {
                try self.diags.addError(call_loc, .argument_count_mismatch, .{});
                return null;
            }
        } else {
            const min_required = if (params.len == 0) 0 else params.len - 1;
            if (args.len < min_required) {
                try self.diags.addError(call_loc, .argument_count_mismatch, .{});
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
                try self.diags.addError(call_loc, .argument_type_mismatch, .{});
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
            _ = self.diags.addNote(self.exprLoc(cb), .checker_code_block_not_executed, .{}) catch {};
            self.warned_code = true;
        }
        return try self.checkExpr(cb.block);
    }

    fn checkComptimeBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cb = self.getExpr(.ComptimeBlock, id);
        if (!self.warned_comptime) {
            _ = self.diags.addNote(self.exprLoc(cb), .checker_comptime_not_executed, .{}) catch {};
            self.warned_comptime = true;
        }
        return try self.checkExpr(cb.block);
    }

    fn checkAsyncBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Treat async blocks as opaque for typing.
        return self.type_info.store.tAny();
    }

    fn checkMlirBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Treat mlir blocks as opaque for typing.
        return self.type_info.store.tAny();
    }

    fn checkInsert(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const r = self.getExpr(.Insert, id);
        _ = try self.checkExpr(r.expr);
        return self.type_info.store.tAny();
    }

    fn checkReturn(self: *Checker, rr: ast.Rows.Return) !?types.TypeId {
        if (self.func_stack.items.len == 0) {
            try self.diags.addError(self.exprLoc(rr), .return_outside_function, .{});
            return null;
        }
        const current_func = self.func_stack.items[self.func_stack.items.len - 1];

        if (current_func.has_result and rr.value.isNone()) {
            try self.diags.addError(self.exprLoc(rr), .missing_return_value, .{});
            return null;
        }
        if (!current_func.has_result and !rr.value.isNone()) {
            try self.diags.addError(self.exprLoc(rr), .return_value_in_void_function, .{});
            return null;
        }

        const expect_ty = current_func.result;
        const ret_ty = if (rr.value.isNone()) self.type_info.store.tVoid() else blk: {
            try self.pushValueReq(true);
            const t = try self.checkExpr(rr.value.unwrap());
            self.popValueReq();
            break :blk t;
        };
        if (ret_ty == null) return null;

        if (self.assignable(ret_ty.?, expect_ty) != .success) {
            try self.diags.addError(self.exprLoc(rr), .return_type_mismatch, .{});
            return null;
        }
        return ret_ty;
    }

    fn checkIf(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const if_expr = self.getExpr(.If, id);
        const cond = try self.checkExpr(if_expr.cond);
        if (cond == null or cond.?.toRaw() != self.type_info.store.tBool().toRaw()) {
            try self.diags.addError(self.exprLoc(if_expr), .non_boolean_condition, .{});
            return null;
        }

        const value_required = self.isValueReq();
        if (!value_required) {
            _ = try self.checkExpr(if_expr.then_block);
            if (!if_expr.else_block.isNone()) _ = try self.checkExpr(if_expr.else_block.unwrap());
            return self.type_info.store.tVoid();
        }

        const then_ty = try self.checkExpr(if_expr.then_block) orelse return null;
        if (if_expr.else_block.isNone()) {
            try self.diags.addError(self.exprLoc(if_expr), .if_expression_requires_else, .{});
            return null;
        }
        const else_ty = try self.checkExpr(if_expr.else_block.unwrap()) orelse return null;

        if (then_ty.toRaw() != else_ty.toRaw()) {
            try self.diags.addError(self.exprLoc(if_expr), .if_branch_type_mismatch, .{});
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
                try self.diags.addError(self.exprLoc(wr), .non_boolean_condition, .{});
                return null;
            }
        } else if (!wr.cond.isNone() and !wr.pattern.isNone()) {
            // Pattern-matching while
            const subj_ty = try self.checkExpr(wr.cond.unwrap()) orelse return null;
            if (!(try pattern_matching.checkPattern(self, wr.pattern.unwrap(), subj_ty, true))) {
                return null;
            }
            self.current_loop_pat = wr.pattern;
            self.current_loop_subject_ty = subj_ty;
        } else if (wr.cond.isNone() and wr.pattern.isNone()) {
            // Infinite loop: ok
        } else unreachable;

        try self.pushLoop(wr.label);
        defer self.popLoop();
        defer {
            self.current_loop_pat = ast.OptPatternId.none();
            self.current_loop_subject_ty = null;
        }

        const body_ty = try self.checkExpr(wr.body);

        if (self.isValueReq()) {
            if (self.loopCtxForLabel(wr.label)) |ctx| return ctx.result_ty;
        }
        return body_ty;
    }

    fn checkUnreachable(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.type_info.store.tAny();
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
                        .Array => self.type_info.store.Array.get(self.trow(it)).elem,
                        .Slice => self.type_info.store.Slice.get(self.trow(it)).elem,
                        .DynArray => self.type_info.store.DynArray.get(self.trow(it)).elem,
                        else => unreachable,
                    },
                };
                if (!(try pattern_matching.checkPattern(self, fr.pattern, subject_ty, true))) {
                    return null;
                }
                self.current_loop_pat = ast.OptPatternId.some(fr.pattern);
                self.current_loop_subject_ty = subject_ty;
            },
            else => {
                try self.diags.addError(self.exprLoc(fr), .non_iterable_in_for, .{});
                return null;
            },
        }

        try self.pushLoop(fr.label);
        defer self.popLoop();
        defer {
            self.current_loop_pat = ast.OptPatternId.none();
            self.current_loop_subject_ty = null;
        }

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
            try self.diags.addError(self.exprLoc(br), .break_outside_loop, .{});
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
                        try self.diags.addError(self.exprLoc(br), .loop_break_value_type_conflict, .{});
                        return null;
                    }
                } else ctx.result_ty = val_ty.?;
                return val_ty;
            } else {
                // unlabeled/valueless break in value position yields void
                return self.type_info.store.tVoid();
            }
        }
        return null;
    }

    fn checkContinue(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.type_info.store.tVoid();
    }

    fn checkDefer(self: *Checker, defer_expr: ast.Rows.Defer) !?types.TypeId {
        if (!self.inFunction()) {
            try self.diags.addError(self.exprLoc(defer_expr), .defer_outside_function, .{});
        }
        _ = try self.checkExpr(defer_expr.expr);
        return self.type_info.store.tVoid();
    }

    fn checkErrDefer(self: *Checker, errdefer_expr: ast.Rows.ErrDefer) !?types.TypeId {
        if (!self.inFunction()) {
            try self.diags.addError(self.exprLoc(errdefer_expr), .errdefer_outside_function, .{});
            return null;
        }
        const current_func = self.currentFunc().?;
        if (!current_func.has_result or self.typeKind(current_func.result) != .ErrorSet) {
            try self.diags.addError(self.exprLoc(errdefer_expr), .errdefer_in_non_error_function, .{});
            return null;
        }
        _ = try self.checkExpr(errdefer_expr.expr) orelse return null;
        return self.type_info.store.tVoid();
    }

    fn checkErrUnwrap(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const eur = self.getExpr(.ErrUnwrap, id);
        const et = try self.checkExpr(eur.expr) orelse return null;
        if (self.typeKind(et) != .ErrorSet) {
            try self.diags.addError(self.exprLoc(eur), .error_propagation_on_non_error, .{});
            return null;
        }
        const er = self.type_info.store.ErrorSet.get(self.trow(et));

        if (!self.inFunction()) {
            try self.diags.addError(self.exprLoc(eur), .error_propagation_mismatched_function_result, .{});
            return null;
        }
        const fctx = self.currentFunc().?;
        const fk = self.typeKind(fctx.result);
        if (fk != .ErrorSet) {
            try self.diags.addError(self.exprLoc(eur), .error_propagation_mismatched_function_result, .{});
            return null;
        }

        // Ensure the error/value halves align with the function result type
        const fr = self.type_info.store.ErrorSet.get(self.trow(fctx.result));
        if (self.assignable(er.error_ty, fr.error_ty) != .success or self.assignable(er.value_ty, fr.value_ty) != .success) {
            try self.diags.addError(self.exprLoc(eur), .error_propagation_mismatched_function_result, .{});
            return null;
        }
        return er.value_ty;
    }

    fn checkOptionalUnwrap(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const our = self.getExpr(.OptionalUnwrap, id);
        const ot = try self.checkExpr(our.expr) orelse return null;
        if (self.typeKind(ot) != .Optional) {
            try self.diags.addError(self.exprLoc(our), .invalid_optional_unwrap_target, .{});
            return null;
        }
        const ore = self.type_info.store.Optional.get(self.trow(ot));
        return ore.elem;
    }

    fn checkAwait(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.type_info.store.tAny();
    }

    fn checkClosure(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cr = self.getExpr(.Closure, id);
        const params = self.ast_unit.exprs.param_pool.slice(cr.params);

        var param_tys = try self.type_info.store.gpa.alloc(types.TypeId, params.len);
        defer self.type_info.store.gpa.free(param_tys);

        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = self.ast_unit.exprs.Param.get(params[i].toRaw());
            if (p.ty.isNone()) {
                try self.diags.addError(self.exprLoc(p), .type_annotation_mismatch, .{});
                return null;
            }
            const pt = try check_types.typeFromTypeExpr(self, p.ty.unwrap()) orelse return null;
            param_tys[i] = pt;
        }

        const body_ty = try self.checkExpr(cr.body) orelse return null;
        // Closures are always pure function *types* (no side-effect tracking here).
        return self.type_info.store.mkFunction(param_tys, body_ty, false, true);
    }

    fn checkCast(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cr = self.getExpr(.Cast, id);
        const et = try check_types.typeFromTypeExpr(self, cr.ty) orelse {
            try self.diags.addError(self.exprLoc(cr), .cast_target_not_type, .{});
            return null;
        };
        const vt = try self.checkExpr(cr.expr) orelse return null;

        const vk = self.typeKind(vt);
        const ek = self.typeKind(et);

        switch (cr.kind) {
            .normal => {
                if (self.assignable(vt, et) != .success and !self.castable(vt, et)) {
                    try self.diags.addError(self.exprLoc(cr), .invalid_cast, .{});
                    return null;
                }
            },
            .bitcast => {
                const gsize = check_types.typeSize(self, vt);
                const tsize = check_types.typeSize(self, et);
                if (gsize == null or tsize == null or gsize.? != tsize.?) {
                    try self.diags.addError(self.exprLoc(cr), .invalid_bitcast, .{});
                    return null;
                }
            },
            .saturate, .wrap => {
                if (!check_types.isNumericKind(self, vk) or !check_types.isNumericKind(self, ek)) {
                    try self.diags.addError(self.exprLoc(cr), .numeric_cast_on_non_numeric, .{});
                    return null;
                }
            },
            .checked => {
                if (self.assignable(vt, et) != .success and !self.castable(vt, et)) {
                    try self.diags.addError(self.exprLoc(cr), .invalid_checked_cast, .{});
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
            try self.diags.addError(self.exprLoc(cr), .catch_on_non_error, .{});
            return null;
        }
        const er = self.type_info.store.ErrorSet.get(self.trow(vt));
        const value_required = self.isValueReq();

        const ht = try self.checkExpr(cr.handler) orelse return null;
        if (!value_required) return self.type_info.store.tVoid();

        if (self.assignable(ht, er.value_ty) != .success) {
            try self.diags.addError(self.exprLoc(cr), .if_branch_type_mismatch, .{});
            return null;
        }
        return er.value_ty;
    }

    fn checkImport(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const ir = self.getExpr(.Import, id);
        const k = self.exprKind(ir.expr);
        if (k != .Literal) {
            try self.diags.addError(self.exprLoc(ir), .invalid_import_operand, .{});
            return null;
        }
        const lit = self.getExpr(.Literal, ir.expr);
        if (lit.kind != .string or lit.value.isNone()) {
            try self.diags.addError(self.exprLoc(ir), .invalid_import_operand, .{});
            return null;
        }
        // Imported module is an opaque value to the checker for now.
        return self.type_info.store.tAny();
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
                    try self.diags.addError(loc, .division_by_zero, .{});
                }
            },
            .float => {
                if (!lit.value.isNone()) {
                    const s = self.getStr(lit.value.unwrap());
                    const f = std.fmt.parseFloat(f64, s) catch 1.0;
                    if (f == 0.0) try self.diags.addError(loc, .division_by_zero, .{});
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
                try self.diags.addError(loc, .division_by_zero, .{});
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
