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
        if (got.toRaw() == expect.toRaw()) return .success;
        const got_kind = self.type_info.store.index.kinds.items[got.toRaw()];
        const expected_kind = self.type_info.store.index.kinds.items[expect.toRaw()];
        if (expected_kind == .Any or got_kind == .Any) return .success;

        // Assigning `null` (modeled as Optional(Any)) to a non-optional target should error clearly.
        if (got_kind == .Optional and expected_kind != .Optional) {
            const got_opt = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[got.toRaw()]);
            const elem_kind = self.type_info.store.index.kinds.items[got_opt.elem.toRaw()];
            if (elem_kind == .Any) return .assign_null_to_non_optional;
            // Implicit unwrap from Optional(T) -> T is not permitted.
            return .failure;
        }

        switch (expected_kind) {
            .Slice => {
                if (got_kind != .Slice) return .failure;
                const expected_ty = self.type_info.store.Slice.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Slice.get(self.type_info.store.index.rows.items[got.toRaw()]);
                return self.assignable(got_ty.elem, expected_ty.elem);
            },
            .Array => {
                if (got_kind != .Array) return .expected_array_type;
                const expected_ty = self.type_info.store.Array.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Array.get(self.type_info.store.index.rows.items[got.toRaw()]);
                const elem_ok = self.assignable(got_ty.elem, expected_ty.elem);
                if (expected_ty.len != got_ty.len)
                    return .array_length_mismatch;
                return elem_ok;
            },
            .DynArray => {
                if (got_kind != .Array) return .expected_array_type;
                const expected_ty = self.type_info.store.DynArray.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Array.get(self.type_info.store.index.rows.items[got.toRaw()]);
                return self.assignable(got_ty.elem, expected_ty.elem);
            },
            .Tuple => {
                if (got_kind != .Tuple) return .expected_tuple_type;
                const expected_ty = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[got.toRaw()]);
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
                if (got_kind == .Array) {
                    const got_ty = self.type_info.store.Array.get(self.type_info.store.index.rows.items[got.toRaw()]);
                    if (got_ty.len != 0) return .expected_map_type;
                    return .success; // empty array can be assigned to any map type
                }

                // Could be a degenerate case, single key value pair that looks like a map type
                if (got_kind == .TypeType) {}
                if (got_kind != .Map) return .expected_map_type;

                const expected_ty = self.type_info.store.Map.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Map.get(self.type_info.store.index.rows.items[got.toRaw()]);
                const key_ok = self.assignable(got_ty.key, expected_ty.key);
                const value_ok = self.assignable(got_ty.value, expected_ty.value);
                if (key_ok != .success) return .map_wrong_key_type;
                if (value_ok != .success) return value_ok;
                return .success;
            },
            .Optional => {
                const expected_ty = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                if (got_kind == .Optional) {
                    const got_ty = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[got.toRaw()]);
                    return self.assignable(got_ty.elem, expected_ty.elem);
                }
                return self.assignable(got, expected_ty.elem);
            },
            .Ptr => {
                if (got_kind != .Ptr) return .expected_pointer_type;
                const expected_ty = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[got.toRaw()]);
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
                const expected_ty = self.type_info.store.Union.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[got.toRaw()]);
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
                const expected_ty = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[got.toRaw()]);
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
                if (got.toRaw() != expect.toRaw()) return .failure;
                return .success;
            },
            .Function => {
                if (got_kind != .Function) return .failure;
                const efn = self.type_info.store.Function.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const gfn = self.type_info.store.Function.get(self.type_info.store.index.rows.items[got.toRaw()]);
                if (efn.is_variadic != gfn.is_variadic) return .failure;
                const eparams = self.type_info.store.type_pool.slice(efn.params);
                const gparams = self.type_info.store.type_pool.slice(gfn.params);
                if (eparams.len != gparams.len) return .failure;
                var i: usize = 0;
                while (i < eparams.len) : (i += 1) {
                    if (eparams[i].toRaw() != gparams[i].toRaw()) return .failure;
                }
                if (efn.result.toRaw() != gfn.result.toRaw()) return .failure;
                if (efn.is_pure and !gfn.is_pure) return .failure;
                return .success;
            },
            .ErrorSet => {
                const expected_ty = self.type_info.store.ErrorSet.get(self.type_info.store.index.rows.items[expect.toRaw()]);
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
        // const rhs_kind = if (rhs_ty != null) self.type_info.store.index.kinds.items[rhs_ty.?.toRaw()] else null;
        // const expect_kind = if (expect_ty != null) self.type_info.store.index.kinds.items[expect_ty.?.toRaw()] else null;
        // std.debug.print("Decl @ {d}, expect={?}, rhs={?}\n", .{ decl.loc.toRaw(), expect_kind, rhs_kind });
        if (rhs_ty == null)
            return;
        // If LHS is a pattern, ensure the RHS type matches the pattern's shape.
        if (!decl.pattern.isNone()) {
            const shape_ok = pattern_matching.checkPatternShapeForDecl(self, decl.pattern.unwrap(), rhs_ty.?);
            switch (shape_ok) {
                .ok => {},
                .tuple_arity_mismatch => {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(decl.loc), .tuple_arity_mismatch, .{});
                    return;
                },
                .struct_field_mismatch => {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(decl.loc), .struct_pattern_field_mismatch, .{});
                    return;
                },
                .shape_mismatch => {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(decl.loc), .pattern_shape_mismatch, .{});
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
            const rhs_kind = self.type_info.store.index.kinds.items[rhs_ty.toRaw()];
            switch (rhs_kind) {
                .Array => {
                    const arr = self.type_info.store.Array.get(self.type_info.store.index.rows.items[rhs_ty.toRaw()]);
                    if (arr.len == 0) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(self.ast_unit.exprs.Decl.get(decl.toRaw()).loc), .cannot_infer_type_from_empty_array, .{});
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
                    self.type_info.decl_types.items[decl.toRaw()] = expect_ty.?; // use expected type
                    self.type_info.expr_types.items[self.ast_unit.exprs.Decl.get(decl.toRaw()).value.toRaw()] = expect_ty.?; // also update RHS expr type
                },
                .map_wrong_key_type => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .map_wrong_key_type, .{}),
                .union_literal_no_fields => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .union_empty_literal, .{}),
                .union_literal_multiple_fields => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .union_literal_multiple_fields, .{}),
                .expected_enum_type => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .expected_enum_type, .{}),
                .expected_struct_type => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .expected_struct_type, .{}),
                .struct_field_count_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .struct_field_count_mismatch, .{}),
                .unknown_struct_field => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .unknown_struct_field, .{}),
                .struct_field_name_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .struct_field_name_mismatch, .{}),
                .noreturn_not_storable => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .noreturn_not_storable, .{}),
                .type_value_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .type_value_mismatch, .{}),
                .array_length_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .array_length_mismatch, .{}),
                .tuple_arity_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .tuple_arity_mismatch, .{}),
                .assign_null_to_non_optional => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .assign_null_to_non_optional, .{}),
                .pointer_type_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .pointer_type_mismatch, .{}),
                .pointer_constness_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .pointer_constness_violation, .{}),
                .expected_array_type => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .expected_array_type, .{}),
                .expected_tuple_type => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .expected_tuple_type, .{}),
                .expected_map_type => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .expected_map_type, .{}),
                .expected_pointer_type => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .expected_pointer_type, .{}),
                .expected_integer_type => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .expected_integer_type, .{}),
                .expected_float_type => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .expected_float_type, .{}),
                .failure => try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .type_annotation_mismatch, .{}),
            }
        }
    }

    fn checkStmt(self: *Checker, sid: ast.StmtId) !?types.TypeId {
        switch (self.ast_unit.stmts.index.kinds.items[sid.toRaw()]) {
            .Expr => {
                const row = self.ast_unit.stmts.get(.Expr, sid);
                // Statement expression: no value required
                try self.pushValueReq(false);
                defer self.popValueReq();
                _ = try self.checkExpr(row.expr);
                return null;
            },
            .Decl => {
                const row = self.ast_unit.stmts.get(.Decl, sid);
                try self.checkDecl(row.decl);
                if (self.inFunction()) {
                    // record local decl for purity tracking
                    const idx = self.func_stack.items.len - 1;
                    _ = self.func_stack.items[idx].locals.put(self.gpa, row.decl.toRaw(), {}) catch {};
                }
            },
            .Assign => {
                const row = self.ast_unit.stmts.get(.Assign, sid);
                // Pattern-shaped LHS support: tuple/struct/array destructuring
                const lkind = self.ast_unit.exprs.index.kinds.items[row.left.toRaw()];
                if (lkind == .TupleLit or lkind == .StructLit or lkind == .ArrayLit) {
                    // RHS of assignment should be checked in value context
                    try self.pushValueReq(true);
                    const rv_ty = try self.checkExpr(row.right);
                    self.popValueReq();
                    if (rv_ty != null) {
                        const shape_ok = pattern_matching.checkPatternShapeForAssignExpr(self, row.left, rv_ty.?);
                        switch (shape_ok) {
                            .ok => {},
                            .tuple_arity_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tuple_arity_mismatch, .{}),
                            .struct_field_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .struct_pattern_field_mismatch, .{}),
                            .shape_mismatch => try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .pattern_shape_mismatch, .{}),
                        }
                    }
                } else {
                    const lt = try self.checkExpr(row.left);
                    // RHS of assignment should be checked in value context
                    try self.pushValueReq(true);
                    const rt = try self.checkExpr(row.right);
                    self.popValueReq();
                    if (lt != null and rt != null and (self.assignable(rt.?, lt.?) != .success)) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .type_annotation_mismatch, .{});
                    }
                }
                // Purity: assignment writes inside pure functions are allowed only to locals
                if (self.inFunction()) {
                    const fctx = self.currentFunc().?;
                    if (fctx.require_pure) {
                        const root = self.lvalueRootKind(row.left);
                        switch (root) {
                            .LocalDecl => {},
                            .Param, .NonLocalDecl, .Unknown => {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .purity_violation, .{});
                                self.func_stack.items[self.func_stack.items.len - 1].pure = false;
                            },
                        }
                    }
                }
            },
            .Insert => {
                const row = self.ast_unit.stmts.get(.Insert, sid);
                if (!self.warned_meta) {
                    _ = self.diags.addNote(self.ast_unit.exprs.locs.get(row.loc), .checker_insert_not_expanded, .{}) catch {};
                    self.warned_meta = true;
                }
                _ = try self.checkExpr(row.expr);
            },
            .Return => {
                const row = self.ast_unit.stmts.get(.Return, sid);
                return try self.checkReturn(row);
            },
            .Break => {
                const row = self.ast_unit.stmts.get(.Break, sid);
                if (!self.inLoop())
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .break_outside_loop, .{});
                if (!row.value.isNone()) {
                    // Break value must be computed in value context
                    try self.pushValueReq(true);
                    const vt = try self.checkExpr(row.value.unwrap());
                    self.popValueReq();
                    if (vt == null) return null;
                    if (self.loopCtxForLabel(row.label)) |ctx| {
                        if (ctx.result_ty) |rt| {
                            if (rt.toRaw() != vt.?.toRaw()) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .loop_break_value_type_conflict, .{});
                                return null;
                            }
                        } else {
                            ctx.result_ty = vt.?;
                        }
                    }
                }
            },
            .Continue => {
                const row = self.ast_unit.stmts.get(.Continue, sid);
                if (!self.inLoop())
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .continue_outside_loop, .{});
            },
            .Unreachable => {},
            .Defer => {
                const row = self.ast_unit.stmts.get(.Defer, sid);
                _ = try self.checkDefer(row);
            },
            .ErrDefer => {
                const row = self.ast_unit.stmts.get(.ErrDefer, sid);
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
        const k = self.ast_unit.exprs.index.kinds.items[id.toRaw()];

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
            .FieldAccess => self.checkFieldAccess(id),
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
                const row = self.ast_unit.exprs.get(.Return, id);
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
                const row = self.ast_unit.exprs.get(.Defer, id);
                break :blk try self.checkDefer(row);
            },
            .ErrDefer => blk: {
                const row = self.ast_unit.exprs.get(.ErrDefer, id);
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
                const row = self.ast_unit.exprs.get(.MapType, id);
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
        const lit = self.ast_unit.exprs.get(.Literal, id);
        return switch (lit.kind) {
            .int => blk: {
                const s = self.ast_unit.exprs.strs.get(lit.value.unwrap());
                if (std.fmt.parseInt(i64, s, 10) catch null == null) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(lit.loc), .invalid_integer_literal, .{});
                    return null;
                }
                break :blk self.type_info.store.tI64();
            },
            .float => blk: {
                // try parsing the float literal
                const s = self.ast_unit.exprs.strs.get(lit.value.unwrap());
                if (std.fmt.parseFloat(f64, s) catch null == null) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(lit.loc), .invalid_float_literal, .{});
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
        const row = self.ast_unit.exprs.get(.Ident, id);
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
        const br = self.ast_unit.exprs.get(.Block, id);
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
                    const se = self.ast_unit.stmts.get(.Expr, stmts[i]).expr;
                    if (self.ast_unit.exprs.index.kinds.items[se.toRaw()] == .Break) after_break = true;
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
                const se = self.ast_unit.stmts.get(.Expr, stmts[i]).expr;
                if (self.ast_unit.exprs.index.kinds.items[se.toRaw()] == .Break) after_break = true;
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
            const row = self.ast_unit.stmts.get(.Expr, last);
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
                const row = self.ast_unit.stmts.get(.Expr, sid);
                break :blk self.exprLoc(row.expr);
            },
            .Decl => blk2: {
                const row = self.ast_unit.stmts.get(.Decl, sid);
                const d = self.ast_unit.exprs.Decl.get(row.decl.toRaw());
                break :blk2 self.ast_unit.exprs.locs.get(d.loc);
            },
            .Assign => blk3: {
                const row = self.ast_unit.stmts.get(.Assign, sid);
                break :blk3 self.ast_unit.exprs.locs.get(row.loc);
            },
            .Insert => blk4: {
                const row = self.ast_unit.stmts.get(.Insert, sid);
                break :blk4 self.ast_unit.exprs.locs.get(row.loc);
            },
            .Return => blk5: {
                const row = self.ast_unit.stmts.get(.Return, sid);
                break :blk5 self.ast_unit.exprs.locs.get(row.loc);
            },
            .Break => blk6: {
                const row = self.ast_unit.stmts.get(.Break, sid);
                break :blk6 self.ast_unit.exprs.locs.get(row.loc);
            },
            .Continue => blk7: {
                const row = self.ast_unit.stmts.get(.Continue, sid);
                break :blk7 self.ast_unit.exprs.locs.get(row.loc);
            },
            .Unreachable => blk8: {
                const row = self.ast_unit.stmts.get(.Unreachable, sid);
                break :blk8 self.ast_unit.exprs.locs.get(row.loc);
            },
            .Defer => blk9: {
                const row = self.ast_unit.stmts.get(.Defer, sid);
                break :blk9 self.ast_unit.exprs.locs.get(row.loc);
            },
            .ErrDefer => blk10: {
                const row = self.ast_unit.stmts.get(.ErrDefer, sid);
                break :blk10 self.ast_unit.exprs.locs.get(row.loc);
            },
        };
    }

    fn exprLoc(self: *Checker, eid: ast.ExprId) Loc {
        const k = self.ast_unit.exprs.index.kinds.items[eid.toRaw()];
        return switch (k) {
            inline else => |x| self.ast_unit.exprs.locs.get(self.ast_unit.exprs.get(x, eid).loc),
        };
    }

    fn checkBinary(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const bin: ast.Rows.Binary = self.ast_unit.exprs.get(.Binary, id);
        const lt = try self.checkExpr(bin.left);
        const rt = try self.checkExpr(bin.right);
        if (lt == null or rt == null) return null;

        const l = lt.?;
        const r = rt.?;
        const lhs_kind = self.type_info.store.index.kinds.items[l.toRaw()];
        const rhs_kind = self.type_info.store.index.kinds.items[r.toRaw()];

        switch (bin.op) {
            .add, .sub, .mul, .div, .mod, .bit_and, .bit_or, .bit_xor, .shl, .shr => {
                if (bin.op == .div) try self.checkDivByZero(bin.right, self.ast_unit.exprs.locs.get(bin.loc));
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
                        try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                        return null;
                    }
                    if (check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind))
                        try self.checkIntZeroLiteral(bin.right, self.ast_unit.exprs.locs.get(bin.loc));
                }
                if (!check_types.isNumericKind(self, lhs_kind) or !check_types.isNumericKind(self, rhs_kind)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                    return null;
                }
                if (l.toRaw() == r.toRaw()) return l;
                try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                return null;
            },
            .eq, .neq, .lt, .lte, .gt, .gte => {
                const both_numeric = check_types.isNumericKind(self, lhs_kind) and check_types.isNumericKind(self, rhs_kind);
                const both_bool = lhs_kind == .Bool and rhs_kind == .Bool;
                if (l.toRaw() != r.toRaw() or !(both_numeric or both_bool)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                    return null;
                }
                return self.type_info.store.tBool();
            },
            .logical_and, .logical_or => {
                if (l.toRaw() == self.type_info.store.tBool().toRaw() and
                    r.toRaw() == self.type_info.store.tBool().toRaw())
                    return self.type_info.store.tBool();
                try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                return null;
            },
            .@"orelse" => {
                if (check_types.isOptional(self, l)) |elem| {
                    if (self.assignable(elem, r) == .success) {
                        return elem;
                    } else return {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                        return null;
                    };
                }
                try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_use_of_orelse_on_non_optional, .{});
                return null;
            },
        }
        return null;
    }

    fn checkUnary(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const unary_expr = self.ast_unit.exprs.get(.Unary, id);
        const expr_ty = try self.checkExpr(unary_expr.expr);
        if (expr_ty == null) return null;
        const t = expr_ty.?;
        const type_kind = self.type_info.store.index.kinds.items[t.toRaw()];
        switch (unary_expr.op) {
            .plus, .minus => {
                if (!check_types.isNumericKind(self, type_kind)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(unary_expr.loc), .invalid_unary_op_operand, .{});
                    return null;
                }
                return t;
            },
            .logical_not => {
                // Accept bool or any
                if (t.toRaw() != self.type_info.store.tBool().toRaw() and t.toRaw() != self.type_info.store.tAny().toRaw()) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(unary_expr.loc), .invalid_unary_op_operand, .{});
                    return null;
                }
                return self.type_info.store.tBool();
            },
            .address_of => return self.type_info.store.mkPtr(t, false),
        }
    }

    fn checkFunctionLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const fnr = self.ast_unit.exprs.get(.FunctionLit, id);
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
                            try self.diags.addError(self.ast_unit.exprs.locs.get(fnr.loc), .tuple_arity_mismatch, .{});
                            return null;
                        },
                        .struct_field_mismatch => {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(fnr.loc), .struct_pattern_field_mismatch, .{});
                            return null;
                        },
                        .shape_mismatch => {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(fnr.loc), .pattern_shape_mismatch, .{});
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
        // Determine purity: 'fn' is pure by definition; 'proc' purity inferred from body
        const ctx = self.currentFunc().?;
        // Extern procs are considered impure; otherwise proc purity comes from body analysis.
        const is_pure = if (fnr.flags.is_proc) (ctx.pure and !fnr.flags.is_extern) else true;
        const final_ty = self.type_info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic, is_pure);
        self.type_info.expr_types.items[id.toRaw()] = final_ty;
        return final_ty;
    }

    fn checkTupleLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const tuple_lit = self.ast_unit.exprs.get(.TupleLit, id);
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
        const array_lit = self.ast_unit.exprs.get(.ArrayLit, id);
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
                try self.diags.addError(self.ast_unit.exprs.locs.get(array_lit.loc), .heterogeneous_array_elements, .{});
                return null;
            }
        }
        return self.type_info.store.mkArray(first_ty, elems.len);
    }

    fn checkMapLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const row = self.ast_unit.exprs.get(.MapLit, id);
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
                try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .map_mixed_key_types, .{});
                return null;
            }
            if (vt == null or vt.?.toRaw() != val_ty.?.toRaw()) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .map_mixed_value_types, .{});
                return null;
            }
        }
        return self.type_info.store.mkMap(key_ty.?, val_ty.?);
    }

    fn checkIndexAccess(self: *Checker, id: ast.ExprId) ?types.TypeId {
        const index_expr = self.ast_unit.exprs.get(.IndexAccess, id);
        const col_ty = self.checkExpr(index_expr.collection) catch
            return null;
        if (col_ty == null) return null;
        const col_kind = self.type_info.store.index.kinds.items[col_ty.?.toRaw()];
        switch (col_kind) {
            .Array, .Slice => return self.indexElemTypeFromArrayLike(col_ty.?, index_expr.index, self.ast_unit.exprs.locs.get(index_expr.loc)),
            .Map => {
                const m = self.type_info.store.Map.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
                const it = self.checkExpr(index_expr.index) catch return null;
                if (it) |iid| {
                    if (iid.toRaw() != m.key.toRaw()) {
                        _ = self.diags.addError(self.ast_unit.exprs.locs.get(index_expr.loc), .map_wrong_key_type, .{}) catch {};
                        return null;
                    }
                }
                return m.value;
            },

            .String => {
                const it = self.checkExpr(index_expr.index) catch return null;
                if (it) |iid| {
                    if (!check_types.isIntegerKind(self, self.type_info.store.index.kinds.items[iid.toRaw()])) {
                        _ = self.diags.addError(self.ast_unit.exprs.locs.get(index_expr.loc), .non_integer_index, .{}) catch {};
                        return null;
                    }
                }
                return self.type_info.store.tU8();
            },
            else => {
                _ = self.diags.addError(self.ast_unit.exprs.locs.get(index_expr.loc), .not_indexable, .{}) catch {};
            },
        }
        return null;
    }

    fn indexElemTypeFromArrayLike(self: *Checker, col_ty: types.TypeId, idx_expr: ast.ExprId, loc: Loc) ?types.TypeId {
        const col_kind = self.type_info.store.index.kinds.items[col_ty.toRaw()];
        std.debug.assert(col_kind == .Array or col_kind == .Slice);
        const idx_kind = self.ast_unit.exprs.index.kinds.items[idx_expr.toRaw()];
        if (idx_kind == .Range) {
            _ = self.checkExpr(idx_expr) catch return null; // validate range endpoints
            return switch (col_kind) {
                .Array => blk: {
                    const r = self.type_info.store.Array.get(self.type_info.store.index.rows.items[col_ty.toRaw()]);
                    break :blk self.type_info.store.mkSlice(r.elem);
                },
                .Slice => blk2: {
                    const r = self.type_info.store.Slice.get(self.type_info.store.index.rows.items[col_ty.toRaw()]);
                    break :blk2 self.type_info.store.mkSlice(r.elem);
                },
                else => unreachable,
            };
        }
        const it = self.checkExpr(idx_expr) catch return null;
        if (it) |iid| {
            if (!check_types.isIntegerKind(self, self.type_info.store.index.kinds.items[iid.toRaw()])) {
                _ = self.diags.addError(loc, .non_integer_index, .{}) catch {};
                return null;
            }
        }
        return switch (col_kind) {
            .Array => blk3: {
                const r = self.type_info.store.Array.get(self.type_info.store.index.rows.items[col_ty.toRaw()]);
                break :blk3 r.elem;
            },
            .Slice => blk4: {
                const r = self.type_info.store.Slice.get(self.type_info.store.index.rows.items[col_ty.toRaw()]);
                break :blk4 r.elem;
            },
            else => unreachable,
        };
    }

    fn checkFieldAccess(self: *Checker, id: ast.ExprId) ?types.TypeId {
        const field_expr = self.ast_unit.exprs.get(.FieldAccess, id);
        // Special-case: module member access via import "path".member
        const parent_kind = self.ast_unit.exprs.index.kinds.items[field_expr.parent.toRaw()];
        if (parent_kind == .Import) {
            if (self.import_resolver) |_| {
                if (self.importMemberType(field_expr.parent, field_expr.field)) |mt| return mt;
            } else {
                if (self.importHasMember(field_expr.parent, field_expr.field)) return self.type_info.store.tAny();
                _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .unknown_struct_field, .{}) catch {};
                return null;
            }
        }
        // Also allow module access when parent is an identifier bound to an import declaration
        if (parent_kind == .Ident) {
            const idr = self.ast_unit.exprs.get(.Ident, field_expr.parent);
            if (self.lookup(idr.name)) |sid_sym| {
                const sym = self.symtab.syms.get(sid_sym.toRaw());
                if (!sym.origin_decl.isNone()) {
                    const did = sym.origin_decl.unwrap();
                    const drow = self.ast_unit.exprs.Decl.get(did.toRaw());
                    if (self.ast_unit.exprs.index.kinds.items[drow.value.toRaw()] == .Import) {
                        if (self.import_resolver) |_| {
                            if (self.importMemberType(drow.value, field_expr.field)) |mt| return mt;
                        } else if (self.importHasMember(drow.value, field_expr.field)) {
                            return self.type_info.store.tAny();
                        }
                        _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .unknown_struct_field, .{}) catch {};
                        return null;
                    }
                }
            }
        }
        const parent_ty = self.checkExpr(field_expr.parent) catch return null;
        if (parent_ty == null) return null;
        var ty = parent_ty.?;
        const kind = self.type_info.store.index.kinds.items[ty.toRaw()];
        switch (kind) {
            .Struct => {
                const struct_row = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                const fields = self.type_info.store.field_pool.slice(struct_row.fields);
                var i: usize = 0;
                while (i < fields.len) : (i += 1) {
                    const field = self.type_info.store.Field.get(fields[i].toRaw());
                    if (field.name.toRaw() == field_expr.field.toRaw()) {
                        return field.ty;
                    }
                }
                _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .unknown_struct_field, .{}) catch {};
                return null;
            },
            .Tuple => {
                const tuple_row = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                const fields = self.type_info.store.type_pool.slice(tuple_row.elems);
                const index = std.fmt.parseInt(usize, self.ast_unit.exprs.strs.get(field_expr.field), 10) catch {
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .expected_field_name_or_index, .{}) catch {};
                    return null;
                };
                if (index >= fields.len) {
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .tuple_index_out_of_bounds, .{}) catch {};
                    return null;
                }
                return fields[index];
            },
            .Ptr => {
                const ptr_row = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                ty = ptr_row.elem;
                const inner_kind = self.type_info.store.index.kinds.items[ty.toRaw()];
                if (inner_kind == .Struct) {
                    const struct_row = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                    const fields = self.type_info.store.field_pool.slice(struct_row.fields);
                    var i: usize = 0;
                    while (i < fields.len) : (i += 1) {
                        const field = self.type_info.store.Field.get(fields[i].toRaw());
                        if (field.name.toRaw() == field_expr.field.toRaw()) {
                            return field.ty;
                        }
                    }
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .unknown_struct_field, .{}) catch {};
                    return null;
                } else {
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .field_access_on_non_aggregate, .{}) catch {};
                    return null;
                }
            },
            .TypeType => {
                const tt = self.type_info.store.TypeType.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                ty = tt.of;
                const inner_kind = self.type_info.store.index.kinds.items[ty.toRaw()];
                if (inner_kind == .Enum) {
                    const enum_ty = self.type_info.store.Enum.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                    const enum_members = self.type_info.store.enum_member_pool.slice(enum_ty.members);
                    var i: usize = 0;
                    while (i < enum_members.len) : (i += 1) {
                        const member = self.type_info.store.EnumMember.get(enum_members[i].toRaw());
                        if (member.name.toRaw() == field_expr.field.toRaw()) {
                            // Enum tag yields value of the enum type
                            return ty;
                        }
                    }
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .unknown_enum_tag, .{}) catch {};
                    return null;
                } else if (inner_kind == .Variant) {
                    const variant_ty = self.type_info.store.Variant.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                    const variant_members = self.type_info.store.field_pool.slice(variant_ty.variants);
                    var i: usize = 0;
                    while (i < variant_members.len) : (i += 1) {
                        const member = self.type_info.store.Field.get(variant_members[i].toRaw());
                        if (member.name.toRaw() == field_expr.field.toRaw()) {
                            // In value position, selecting a variant tag without constructing:
                            // - If the payload is void, it yields a value of the variant type (tag only)
                            // - If the payload is non-void, it's a missing payload arity error
                            const pk = self.type_info.store.index.kinds.items[member.ty.toRaw()];
                            if (pk == .Void) {
                                return ty; // tag value of the variant type
                            } else {
                                _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .variant_payload_arity_mismatch, .{}) catch {};
                                return null;
                            }
                        }
                    }
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .unknown_variant_tag, .{}) catch {};
                    return null;
                } else if (inner_kind == .Error) {
                    const variant_ty = self.type_info.store.Error.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                    const variant_members = self.type_info.store.field_pool.slice(variant_ty.variants);
                    var i: usize = 0;
                    while (i < variant_members.len) : (i += 1) {
                        const member = self.type_info.store.Field.get(variant_members[i].toRaw());
                        if (member.name.toRaw() == field_expr.field.toRaw()) {
                            return ty;
                        }
                    }
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .unknown_error_tag, .{}) catch {};
                    return null;
                } else {
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .field_access_on_non_aggregate, .{}) catch {};
                    return null;
                }
            },
            else => {
                _ = self.diags.addError(self.ast_unit.exprs.locs.get(field_expr.loc), .field_access_on_non_aggregate, .{}) catch {};
                return null;
            },
        }
    }

    fn importHasMember(self: *Checker, import_eid: ast.ExprId, member: ast.StrId) bool {
        const ir = self.ast_unit.exprs.get(.Import, import_eid);
        const ek = self.ast_unit.exprs.index.kinds.items[ir.expr.toRaw()];
        if (ek != .Literal) return false;
        const lit = self.ast_unit.exprs.get(.Literal, ir.expr);
        if (lit.value.isNone()) return false;
        var path = self.ast_unit.exprs.strs.get(lit.value.unwrap());
        if (path.len >= 2 and path[0] == '"' and path[path.len - 1] == '"') {
            path = path[1 .. path.len - 1];
        }
        if (self.import_resolver) |res| return self.importMemberTypeByPath(res, path, member) != null;
        // fallback: no resolver
        return false;
    }

    fn importMemberTypeByPath(self: *Checker, res: *ImportResolver, path: []const u8, member: ast.StrId) ?types.TypeId {
        const me = res.resolve(self.import_base_dir, path) catch return null;
        const target = self.ast_unit.exprs.strs.get(member);
        if (me.syms.get(target)) |ty| {
            return check_types.translateType(self, &me.type_info.store, &self.type_info.store, ty);
        }
        return null;
    }

    fn importMemberType(self: *Checker, import_eid: ast.ExprId, member: ast.StrId) ?types.TypeId {
        if (self.import_resolver == null) return null;
        const res = self.import_resolver.?;
        const ir = self.ast_unit.exprs.get(.Import, import_eid);
        const ek = self.ast_unit.exprs.index.kinds.items[ir.expr.toRaw()];
        if (ek != .Literal) return null;
        const lit = self.ast_unit.exprs.get(.Literal, ir.expr);
        if (lit.value.isNone()) return null;
        var path = self.ast_unit.exprs.strs.get(lit.value.unwrap());
        if (path.len >= 2 and path[0] == '"' and path[path.len - 1] == '"') path = path[1 .. path.len - 1];
        return self.importMemberTypeByPath(res, path, member);
    }

    fn fileHasTopDecl(self: *Checker, abs_or_rel: []const u8, name: []const u8) bool {
        var cwd = std.fs.cwd();
        const content = cwd.readFileAlloc(self.gpa, abs_or_rel, 1 << 20) catch return false;
        defer self.gpa.free(content);
        var it = std.mem.splitScalar(u8, content, '\n');
        while (it.next()) |line| {
            var l = std.mem.trim(u8, line, " \t\r");
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
        const rr = self.ast_unit.exprs.get(.Range, id);
        if (!rr.start.isNone()) {
            const st = try self.checkExpr(rr.start.unwrap());
            if (st == null or !check_types.isIntegerKind(self, self.type_info.store.index.kinds.items[st.?.toRaw()])) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(rr.loc), .non_integer_index, .{});
                return null;
            }
        }
        if (!rr.end.isNone()) {
            const et = try self.checkExpr(rr.end.unwrap());
            if (et == null or !check_types.isIntegerKind(self, self.type_info.store.index.kinds.items[et.?.toRaw()])) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(rr.loc), .non_integer_index, .{});
                return null;
            }
        }
        return self.type_info.store.mkSlice(self.type_info.store.tUsize());
    }

    fn checkStructLit(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const struct_lit = self.ast_unit.exprs.get(.StructLit, id);
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
                try self.diags.addError(self.ast_unit.exprs.locs.get(struct_lit.loc), .struct_missing_field, .{});
                return null;
            },
            .unknown_struct_field => {
                try self.diags.addError(self.ast_unit.exprs.locs.get(struct_lit.loc), .unknown_struct_field, .{});
                return null;
            },
            .union_literal_multiple_fields => {
                try self.diags.addError(self.ast_unit.exprs.locs.get(struct_lit.loc), .union_literal_multiple_fields, .{});
                return null;
            },
            .union_literal_no_fields => {
                try self.diags.addError(self.ast_unit.exprs.locs.get(struct_lit.loc), .union_empty_literal, .{});
                return null;
            },
            else => {
                try self.diags.addError(self.ast_unit.exprs.locs.get(struct_lit.loc), .struct_field_type_mismatch, .{});
                return null;
            },
        }
        return expect_ty;
    }

    fn checkDeref(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const row = self.ast_unit.exprs.get(.Deref, id);
        const ptr_ty_opt = try self.checkExpr(row.expr);
        if (ptr_ty_opt == null) return null;
        const ptr_ty = ptr_ty_opt.?;
        const kind = self.type_info.store.index.kinds.items[ptr_ty.toRaw()];
        if (kind != .Ptr) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .deref_non_pointer, .{});
            return null;
        }
        const ptr_row = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[ptr_ty.toRaw()]);
        return ptr_row.elem;
    }

    fn checkCall(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const call_expr = self.ast_unit.exprs.get(.Call, id);
        // Module member call: (Import or Ident-of-import).field(...)
        if (self.ast_unit.exprs.index.kinds.items[call_expr.callee.toRaw()] == .FieldAccess) {
            const fr = self.ast_unit.exprs.get(.FieldAccess, call_expr.callee);
            const pk = self.ast_unit.exprs.index.kinds.items[fr.parent.toRaw()];
            var fty_opt: ?types.TypeId = null;
            if (pk == .Import) {
                fty_opt = self.importMemberType(fr.parent, fr.field);
            } else if (pk == .Ident) {
                const idr = self.ast_unit.exprs.get(.Ident, fr.parent);
                if (self.lookup(idr.name)) |sid_sym| {
                    const sym = self.symtab.syms.get(sid_sym.toRaw());
                    if (!sym.origin_decl.isNone()) {
                        const did = sym.origin_decl.unwrap();
                        const drow = self.ast_unit.exprs.Decl.get(did.toRaw());
                        if (self.ast_unit.exprs.index.kinds.items[drow.value.toRaw()] == .Import) {
                            fty_opt = self.importMemberType(drow.value, fr.field);
                        }
                    }
                }
            }
            if (fty_opt) |fty| {
                if (self.type_info.store.getKind(fty) != .Function) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .call_non_callable, .{});
                    return null;
                }
                const func = self.type_info.store.get(.Function, fty);
                const param_ids = self.type_info.store.type_pool.slice(func.params);
                const args = self.ast_unit.exprs.expr_pool.slice(call_expr.args);
                if (!func.is_variadic and args.len != param_ids.len) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                    return null;
                }
                const fixed = if (param_ids.len == 0) 0 else if (func.is_variadic) param_ids.len - 1 else param_ids.len;
                var i: usize = 0;
                while (i < args.len) : (i += 1) {
                    const at = try self.checkExpr(args[i]);
                    if (at == null) return null;
                    const pt = if (i < fixed) param_ids[i] else param_ids[fixed];
                    if (self.assignable(at.?, pt) != .success) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_type_mismatch, .{});
                        return null;
                    }
                }
                return func.result;
            }
        }
        // Handle variant/error tag constructors before evaluating callee expression.
        if (self.ast_unit.exprs.index.kinds.items[call_expr.callee.toRaw()] == .FieldAccess) {
            const fr = self.ast_unit.exprs.get(.FieldAccess, call_expr.callee);
            // Resolve the parent in type-space
            const parent_ty = try check_types.typeFromTypeExpr(self, fr.parent) orelse null;
            if (parent_ty) |pty| {
                const pk = self.type_info.store.index.kinds.items[pty.toRaw()];
                if (pk == .Variant) {
                    const vt = self.type_info.store.Variant.get(self.type_info.store.index.rows.items[pty.toRaw()]);
                    const cases = self.type_info.store.field_pool.slice(vt.variants);
                    var found: ?types.TypeId = null;
                    var ci: usize = 0;
                    while (ci < cases.len) : (ci += 1) {
                        const c = self.type_info.store.Field.get(cases[ci].toRaw());
                        if (c.name.toRaw() == fr.field.toRaw()) {
                            found = c.ty;
                            break;
                        }
                    }
                    if (found == null) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .unknown_variant_tag, .{});
                        return null;
                    }
                    const payload_ty = found.?;
                    const args = self.ast_unit.exprs.expr_pool.slice(call_expr.args);
                    const pkind = self.type_info.store.index.kinds.items[payload_ty.toRaw()];
                    switch (pkind) {
                        .Void => {
                            if (args.len != 0) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                                return null;
                            }
                            return pty;
                        },
                        .Tuple => {
                            const tup = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[payload_ty.toRaw()]);
                            const param_ids = self.type_info.store.type_pool.slice(tup.elems);
                            if (args.len < param_ids.len) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .variant_payload_arity_mismatch, .{});
                                return null;
                            }
                            if (args.len > param_ids.len) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                                return null;
                            }
                            var ai: usize = 0;
                            while (ai < args.len) : (ai += 1) {
                                const at = try self.checkExpr(args[ai]);
                                if (at == null) return null;
                                if (self.assignable(at.?, param_ids[ai]) != .success) {
                                    try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_type_mismatch, .{});
                                    return null;
                                }
                            }
                            return pty;
                        },
                        else => {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .call_non_callable, .{});
                            return null;
                        },
                    }
                } else if (pk == .Error) {
                    const et = self.type_info.store.Error.get(self.type_info.store.index.rows.items[pty.toRaw()]);
                    const cases = self.type_info.store.field_pool.slice(et.variants);
                    var found: ?types.TypeId = null;
                    var ei: usize = 0;
                    while (ei < cases.len) : (ei += 1) {
                        const c = self.type_info.store.Field.get(cases[ei].toRaw());
                        if (c.name.toRaw() == fr.field.toRaw()) {
                            found = c.ty;
                            break;
                        }
                    }
                    if (found == null) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .unknown_error_tag, .{});
                        return null;
                    }
                    const payload_ty = found.?;
                    const args = self.ast_unit.exprs.expr_pool.slice(call_expr.args);
                    const pkind = self.type_info.store.index.kinds.items[payload_ty.toRaw()];
                    switch (pkind) {
                        .Void => {
                            if (args.len != 0) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                                return null;
                            }
                            return pty;
                        },
                        .Tuple => {
                            const tup = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[payload_ty.toRaw()]);
                            const param_ids = self.type_info.store.type_pool.slice(tup.elems);
                            if (args.len < param_ids.len) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .variant_payload_arity_mismatch, .{});
                                return null;
                            }
                            if (args.len > param_ids.len) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                                return null;
                            }
                            var ai2: usize = 0;
                            while (ai2 < args.len) : (ai2 += 1) {
                                const at = try self.checkExpr(args[ai2]);
                                if (at == null) return null;
                                if (self.assignable(at.?, param_ids[ai2]) != .success) {
                                    try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_type_mismatch, .{});
                                    return null;
                                }
                            }
                            return pty;
                        },
                        else => {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .call_non_callable, .{});
                            return null;
                        },
                    }
                }
            }
        }

        const func_ty = try self.checkExpr(call_expr.callee);
        if (func_ty == null) {
            // If the callee is an unresolved identifier in the current scope, report unknown_function.
            if (self.ast_unit.exprs.index.kinds.items[call_expr.callee.toRaw()] == .Ident) {
                const idr = self.ast_unit.exprs.get(.Ident, call_expr.callee);
                if (self.lookup(idr.name) == null) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .unknown_function, .{});
                }
            }
            return null;
        }
        const func_id = func_ty.?;
        const func_kind = self.type_info.store.index.kinds.items[func_id.toRaw()];

        // Variant tag constructor call: (Type).Tag(args...)
        if (self.ast_unit.exprs.index.kinds.items[call_expr.callee.toRaw()] == .FieldAccess) {
            const fr = self.ast_unit.exprs.get(.FieldAccess, call_expr.callee);
            // Resolve the parent in type-space
            const parent_ty = try check_types.typeFromTypeExpr(self, fr.parent) orelse null;
            if (parent_ty) |pty| {
                const pk = self.type_info.store.index.kinds.items[pty.toRaw()];
                if (pk == .Variant) {
                    const vt = self.type_info.store.Variant.get(self.type_info.store.index.rows.items[pty.toRaw()]);
                    const cases = self.type_info.store.field_pool.slice(vt.variants);
                    var found: ?types.TypeId = null;
                    var ci: usize = 0;
                    while (ci < cases.len) : (ci += 1) {
                        const c = self.type_info.store.Field.get(cases[ci].toRaw());
                        if (c.name.toRaw() == fr.field.toRaw()) {
                            found = c.ty;
                            break;
                        }
                    }
                    if (found == null) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .unknown_variant_tag, .{});
                        return null;
                    }
                    const payload_ty = found.?;
                    const args = self.ast_unit.exprs.expr_pool.slice(call_expr.args);
                    const pkind = self.type_info.store.index.kinds.items[payload_ty.toRaw()];
                    switch (pkind) {
                        .Void => {
                            if (args.len != 0) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                                return null;
                            }
                            return pty;
                        },
                        .Tuple => {
                            const tup = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[payload_ty.toRaw()]);
                            const param_ids = self.type_info.store.type_pool.slice(tup.elems);
                            if (args.len < param_ids.len) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .variant_payload_arity_mismatch, .{});
                                return null;
                            }
                            if (args.len > param_ids.len) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                                return null;
                            }
                            var ai: usize = 0;
                            while (ai < args.len) : (ai += 1) {
                                const at = try self.checkExpr(args[ai]);
                                if (at == null) return null;
                                if (self.assignable(at.?, param_ids[ai]) != .success) {
                                    try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_type_mismatch, .{});
                                    return null;
                                }
                            }
                            return pty;
                        },
                        else => {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .call_non_callable, .{});
                            return null;
                        },
                    }
                } else if (pk == .Error) {
                    const et = self.type_info.store.Error.get(self.type_info.store.index.rows.items[pty.toRaw()]);
                    const cases = self.type_info.store.field_pool.slice(et.variants);
                    var found: ?types.TypeId = null;
                    var ei: usize = 0;
                    while (ei < cases.len) : (ei += 1) {
                        const c = self.type_info.store.Field.get(cases[ei].toRaw());
                        if (c.name.toRaw() == fr.field.toRaw()) {
                            found = c.ty;
                            break;
                        }
                    }
                    if (found == null) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .unknown_error_tag, .{});
                        return null;
                    }
                    const payload_ty = found.?;
                    const args = self.ast_unit.exprs.expr_pool.slice(call_expr.args);
                    const pkind = self.type_info.store.index.kinds.items[payload_ty.toRaw()];
                    switch (pkind) {
                        .Void => {
                            if (args.len != 0) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                                return null;
                            }
                            return pty;
                        },
                        .Tuple => {
                            const tup = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[payload_ty.toRaw()]);
                            const param_ids = self.type_info.store.type_pool.slice(tup.elems);
                            if (args.len < param_ids.len) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .variant_payload_arity_mismatch, .{});
                                return null;
                            }
                            if (args.len > param_ids.len) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                                return null;
                            }
                            var ai2: usize = 0;
                            while (ai2 < args.len) : (ai2 += 1) {
                                const at = try self.checkExpr(args[ai2]);
                                if (at == null) return null;
                                if (self.assignable(at.?, param_ids[ai2]) != .success) {
                                    try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_type_mismatch, .{});
                                    return null;
                                }
                            }
                            return pty;
                        },
                        else => {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .call_non_callable, .{});
                            return null;
                        },
                    }
                }
            }
        }
        if (func_kind == .Tuple) {
            // Variant Tuple Call: treat as a constructor for the tuple type.
            const tuple_ty = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[func_id.toRaw()]);
            const param_ids = self.type_info.store.type_pool.slice(tuple_ty.elems);
            const args = self.ast_unit.exprs.expr_pool.slice(call_expr.args);
            if (args.len != param_ids.len) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                return null;
            }
            var i: usize = 0;
            while (i < args.len) : (i += 1) {
                const at = try self.checkExpr(args[i]);
                if (at == null) return null;
                const atid = at.?;
                const ptid = param_ids[i];
                if (self.assignable(atid, ptid) != .success) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_type_mismatch, .{});
                    return null;
                }
            }
            return func_id;
        } else if (func_kind != .Function) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .call_non_callable, .{});
            return null;
        }
        const func = self.type_info.store.Function.get(self.type_info.store.index.rows.items[func_id.toRaw()]);
        // Purity bookkeeping: mark current function impure when calling an impure/proc callee
        if (self.inFunction()) {
            var mark_impure = !func.is_pure;
            if (!mark_impure and self.ast_unit.exprs.index.kinds.items[call_expr.callee.toRaw()] == .Ident) {
                const idr = self.ast_unit.exprs.get(.Ident, call_expr.callee);
                if (self.lookup(idr.name)) |sid_sym| {
                    const sym = self.symtab.syms.get(sid_sym.toRaw());
                    if (!sym.origin_decl.isNone()) {
                        const did = sym.origin_decl.unwrap();
                        const drow = self.ast_unit.exprs.Decl.get(did.toRaw());
                        const vk = self.ast_unit.exprs.index.kinds.items[drow.value.toRaw()];
                        if (vk == .FunctionLit) {
                            const fl = self.ast_unit.exprs.get(.FunctionLit, drow.value);
                            if (fl.flags.is_proc or fl.flags.is_extern) mark_impure = true;
                        }
                    }
                }
            }
            if (mark_impure) {
                const idx = self.func_stack.items.len - 1;
                self.func_stack.items[idx].pure = false;
            }
        }
        // Purity: disallow such calls inside a required-pure function
        if (self.inFunction()) {
            const fctx = self.currentFunc().?;
            if (fctx.require_pure) {
                var violate = !func.is_pure;
                if (!violate and self.ast_unit.exprs.index.kinds.items[call_expr.callee.toRaw()] == .Ident) {
                    const idr = self.ast_unit.exprs.get(.Ident, call_expr.callee);
                    if (self.lookup(idr.name)) |sid_sym| {
                        const sym = self.symtab.syms.get(sid_sym.toRaw());
                        if (!sym.origin_decl.isNone()) {
                            const did = sym.origin_decl.unwrap();
                            const drow = self.ast_unit.exprs.Decl.get(did.toRaw());
                            const vk = self.ast_unit.exprs.index.kinds.items[drow.value.toRaw()];
                            if (vk == .FunctionLit) {
                                const fl = self.ast_unit.exprs.get(.FunctionLit, drow.value);
                                if (fl.flags.is_proc or fl.flags.is_extern) violate = true;
                            }
                        }
                    }
                }
                if (violate) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .purity_violation, .{});
                    return null;
                }
            }
        }
        const param_ids = self.type_info.store.type_pool.slice(func.params);
        const args = self.ast_unit.exprs.expr_pool.slice(call_expr.args);
        if (!func.is_variadic) {
            if (args.len != param_ids.len) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                return null;
            }
        } else {
            // Variadic: last formal is a sentinel (e.g., 'any'), and may be omitted.
            const min_required = if (param_ids.len == 0) 0 else param_ids.len - 1;
            if (args.len < min_required) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_count_mismatch, .{});
                return null;
            }
        }
        var i: usize = 0;
        while (i < args.len) : (i += 1) {
            const at = try self.checkExpr(args[i]);
            if (at == null) return null;
            const atid = at.?;
            const ptid = if (!func.is_variadic)
                (if (i < param_ids.len) param_ids[i] else param_ids[param_ids.len - 1])
            else blk: {
                // For variadic, fixed params are all but the last; everything after uses the last formal's type.
                const fixed = if (param_ids.len == 0) 0 else param_ids.len - 1;
                break :blk if (i < fixed) param_ids[i] else param_ids[param_ids.len - 1];
            };
            if (self.assignable(atid, ptid) != .success) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(call_expr.loc), .argument_type_mismatch, .{});
                return null;
            }
        }
        return func.result;
    }

    fn checkCodeBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cb = self.ast_unit.exprs.get(.CodeBlock, id);
        if (!self.warned_code) {
            _ = self.diags.addNote(self.ast_unit.exprs.locs.get(cb.loc), .checker_code_block_not_executed, .{}) catch {};
            self.warned_code = true;
        }
        return try self.checkExpr(cb.block);
    }

    fn checkComptimeBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cb = self.ast_unit.exprs.get(.ComptimeBlock, id);
        if (!self.warned_comptime) {
            _ = self.diags.addNote(self.ast_unit.exprs.locs.get(cb.loc), .checker_comptime_not_executed, .{}) catch {};
            self.warned_comptime = true;
        }
        const t = try self.checkExpr(cb.block);
        if (t == null) return null;
        return t;
    }

    fn checkAsyncBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Treat async blocks as opaque for typing
        return self.type_info.store.tAny();
    }

    fn checkMlirBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Treat mlir blocks as opaque for typing
        return self.type_info.store.tAny();
    }

    fn checkInsert(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const r = self.ast_unit.exprs.get(.Insert, id);
        _ = try self.checkExpr(r.expr);
        return self.type_info.store.tAny();
    }

    fn checkReturn(self: *Checker, rr: ast.Rows.Return) !?types.TypeId {
        // get the expected return type from the current function context
        if (self.func_stack.items.len == 0) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(rr.loc), .return_outside_function, .{});
            return null;
        }
        const current_func = self.func_stack.items[self.func_stack.items.len - 1];
        if (current_func.has_result and rr.value.isNone()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(rr.loc), .missing_return_value, .{});
            return null;
        }
        if (!current_func.has_result and !rr.value.isNone()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(rr.loc), .return_value_in_void_function, .{});
            return null;
        }
        const expect_ty = current_func.result;
        const ret_val_ty = if (rr.value.isNone())
            self.type_info.store.tVoid()
        else blk: {
            // Return value must be evaluated in value context even in statement bodies
            try self.pushValueReq(true);
            const t = try self.checkExpr(rr.value.unwrap());
            self.popValueReq();
            break :blk t;
        };
        // check if the return value type matches the expected return type
        if (ret_val_ty == null) return null;
        if (self.assignable(ret_val_ty.?, expect_ty) != .success) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(rr.loc), .return_type_mismatch, .{});
            return null;
        }
        return ret_val_ty;
    }

    fn checkIf(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const if_expr = self.ast_unit.exprs.get(.If, id);
        const cond = try self.checkExpr(if_expr.cond);
        if (cond == null or cond.?.toRaw() != self.type_info.store.tBool().toRaw()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(if_expr.loc), .non_boolean_condition, .{});
            return null;
        }
        const value_required = self.isValueReq();
        if (!value_required) {
            // Statement context: type-check branches, no else required
            _ = try self.checkExpr(if_expr.then_block);
            if (!if_expr.else_block.isNone()) {
                _ = try self.checkExpr(if_expr.else_block.unwrap());
            }
            return self.type_info.store.tVoid();
        }
        // Value context: else required, and branches must match
        const then_ty = try self.checkExpr(if_expr.then_block);
        if (then_ty == null) return null;
        if (if_expr.else_block.isNone()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(if_expr.loc), .if_expression_requires_else, .{});
            return null;
        }
        const else_ty = try self.checkExpr(if_expr.else_block.unwrap());
        if (else_ty == null) return null;
        if (then_ty.?.toRaw() != else_ty.?.toRaw()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(if_expr.loc), .if_branch_type_mismatch, .{});
            return null;
        }
        return then_ty;
    }

    fn checkWhile(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const wr = self.ast_unit.exprs.get(.While, id);
        // C-like while loop
        if (!wr.cond.isNone() and wr.pattern.isNone()) {
            const cond = try self.checkExpr(wr.cond.unwrap());
            if (cond == null) return null;
            const ct = cond.?;
            if (ct.toRaw() != self.type_info.store.tBool().toRaw() and ct.toRaw() != self.type_info.store.tAny().toRaw()) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(wr.loc), .non_boolean_condition, .{});
                return null;
            }
        }
        // Pattern-matching while loop
        else if (!wr.cond.isNone() and !wr.pattern.isNone()) {
            const expr_ty = try self.checkExpr(wr.cond.unwrap());
            if (expr_ty == null) return null;
            if (!try pattern_matching.checkPattern(self, wr.pattern.unwrap(), expr_ty.?, true)) {
                return null;
            }
            // Set loop pattern context for identifier type inference within body
            self.current_loop_pat = wr.pattern;
            self.current_loop_subject_ty = expr_ty.?;
        }
        // Infinite loop
        else if (wr.cond.isNone() and wr.pattern.isNone()) {} else unreachable;

        try self.pushLoop(wr.label);
        defer self.popLoop();
        defer {
            self.current_loop_pat = ast.OptPatternId.none();
            self.current_loop_subject_ty = null;
        }
        const body_ty = try self.checkExpr(wr.body);
        // If loop used as a value, return the loop's result type (set by labeled breaks)
        if (self.isValueReq()) {
            const lc = self.loopCtxForLabel(wr.label);
            if (lc) |ctx| return ctx.result_ty;
        }
        return body_ty;
    }

    fn checkUnreachable(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.type_info.store.tAny();
    }

    fn checkFor(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const fr = self.ast_unit.exprs.get(.For, id);
        const it = try self.checkExpr(fr.iterable);
        if (it == null) return null;
        const kind = self.type_info.store.index.kinds.items[it.?.toRaw()];
        switch (kind) {
            .Array, .Slice, .DynArray => {
                const pat_kind = self.ast_unit.pats.index.kinds.items[fr.pattern.toRaw()];
                const subject_ty: types.TypeId = switch (pat_kind) {
                    .Slice => it.?,
                    else => if (kind == .Array)
                        self.type_info.store.Array.get(self.type_info.store.index.rows.items[it.?.toRaw()]).elem
                    else if (kind == .Slice)
                        self.type_info.store.Slice.get(self.type_info.store.index.rows.items[it.?.toRaw()]).elem
                    else
                        self.type_info.store.DynArray.get(self.type_info.store.index.rows.items[it.?.toRaw()]).elem,
                };
                if (!try pattern_matching.checkPattern(self, fr.pattern, subject_ty, true)) {
                    return null;
                }
                // Set loop pattern context for identifier type inference within body
                self.current_loop_pat = ast.OptPatternId.some(fr.pattern);
                self.current_loop_subject_ty = subject_ty;
            },
            else => {
                try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .non_iterable_in_for, .{});
                return null;
            },
        }
        // Body must type-check
        try self.pushLoop(fr.label);
        defer self.popLoop();
        defer {
            self.current_loop_pat = ast.OptPatternId.none();
            self.current_loop_subject_ty = null;
        }
        const body_ty = try self.checkExpr(fr.body);
        // If loop used as a value, return the loop's result type (set by labeled breaks)
        if (self.isValueReq()) {
            const lc = self.loopCtxForLabel(fr.label);
            if (lc) |ctx| return ctx.result_ty;
        }
        return body_ty;
    }

    fn castable(self: *Checker, got: types.TypeId, expect: types.TypeId) bool {
        if (got.toRaw() == expect.toRaw()) return true;
        const gk = self.type_info.store.index.kinds.items[got.toRaw()];
        const ek = self.type_info.store.index.kinds.items[expect.toRaw()];
        // Allow numeric casts
        const num_ok = switch (gk) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize => true,
            else => false,
        } and switch (ek) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize => true,
            else => false,
        };
        if (num_ok) return true;
        // Allow pointer-to-pointer casts
        if (gk == .Ptr and ek == .Ptr) return true;
        return false;
    }

    fn checkBreak(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const br = self.ast_unit.exprs.get(.Break, id);
        if (!self.inLoop()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(br.loc), .break_outside_loop, .{});
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
                        try self.diags.addError(self.ast_unit.exprs.locs.get(br.loc), .loop_break_value_type_conflict, .{});
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
        if (!self.inFunction()) try self.diags.addError(self.ast_unit.exprs.locs.get(defer_expr.loc), .defer_outside_function, .{});
        const dt = try self.checkExpr(defer_expr.expr);
        if (dt == null) return null;
        return self.type_info.store.tVoid();
    }

    fn checkErrDefer(self: *Checker, errdefer_expr: ast.Rows.ErrDefer) !?types.TypeId {
        if (!self.inFunction()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(errdefer_expr.loc), .errdefer_outside_function, .{});
            return null;
        }
        // get current function's error set type
        const current_func = self.currentFunc().?;
        if (!current_func.has_result or self.type_info.store.index.kinds.items[current_func.result.toRaw()] != .ErrorSet) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(errdefer_expr.loc), .errdefer_in_non_error_function, .{});
            return null;
        }
        const edt = try self.checkExpr(errdefer_expr.expr);
        if (edt == null) return null;
        return self.type_info.store.tVoid();
    }

    fn checkErrUnwrap(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const eur = self.ast_unit.exprs.get(.ErrUnwrap, id);
        const et = try self.checkExpr(eur.expr);
        if (et == null) return null;
        if (self.type_info.store.index.kinds.items[et.?.toRaw()] != .ErrorSet) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(eur.loc), .error_propagation_on_non_error, .{});
            return null;
        }
        const er = self.type_info.store.ErrorSet.get(self.type_info.store.index.rows.items[et.?.toRaw()]);

        // Ensure we are inside a function whose result type is also an error set (to allow propagation)
        if (!self.inFunction()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(eur.loc), .error_propagation_mismatched_function_result, .{});
            return null;
        }
        const fctx = self.currentFunc().?;
        const fk = self.type_info.store.index.kinds.items[fctx.result.toRaw()];
        if (fk != .ErrorSet) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(eur.loc), .error_propagation_mismatched_function_result, .{});
            return null;
        }
        // Optional: verify error/value types compatibility between operand and function result
        const fr = self.type_info.store.ErrorSet.get(self.type_info.store.index.rows.items[fctx.result.toRaw()]);
        if (self.assignable(er.error_ty, fr.error_ty) != .success or self.assignable(er.value_ty, fr.value_ty) != .success) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(eur.loc), .error_propagation_mismatched_function_result, .{});
            return null;
        }
        return er.value_ty;
    }

    fn checkOptionalUnwrap(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const our = self.ast_unit.exprs.get(.OptionalUnwrap, id);
        const ot = try self.checkExpr(our.expr);
        if (ot == null) return null;
        if (self.type_info.store.index.kinds.items[ot.?.toRaw()] != .Optional) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(our.loc), .invalid_optional_unwrap_target, .{});
            return null;
        }
        const ore = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[ot.?.toRaw()]);
        return ore.elem;
    }

    fn checkAwait(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Await is a no-op in the checker
        return self.type_info.store.tAny();
    }

    fn checkClosure(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cr = self.ast_unit.exprs.get(.Closure, id);
        const params = self.ast_unit.exprs.param_pool.slice(cr.params);
        var param_tys = try self.type_info.store.gpa.alloc(types.TypeId, params.len);
        defer self.type_info.store.gpa.free(param_tys);
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = self.ast_unit.exprs.Param.get(params[i].toRaw());
            if (p.ty.isNone()) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(p.loc), .type_annotation_mismatch, .{});
                return null;
            }
            const pt = try check_types.typeFromTypeExpr(self, p.ty.unwrap());
            if (pt == null) return null;
            param_tys[i] = pt.?;
        }
        const body_ty = try self.checkExpr(cr.body);
        if (body_ty == null) return null;
        const fty = self.type_info.store.mkFunction(param_tys, body_ty.?, false, true);
        // if (expect.ty) |et| {
        //     if (self.assignable(fty, et) != .success) {
        //         try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .type_annotation_mismatch, .{});
        //         return null;
        //     }
        // }
        return fty;
    }

    fn checkCast(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cr = self.ast_unit.exprs.get(.Cast, id);
        const et = try check_types.typeFromTypeExpr(self, cr.ty) orelse {
            try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .cast_target_not_type, .{});
            return null;
        };
        const vt = try self.checkExpr(cr.expr);
        if (vt == null) return null;
        const vk = self.type_info.store.index.kinds.items[vt.?.toRaw()];
        const ek = self.type_info.store.index.kinds.items[et.toRaw()];

        switch (cr.kind) {
            .normal => {
                // A normal cast allows assignable types or types that are generally castable (e.g., numeric to numeric, pointer to pointer)
                if (self.assignable(vt.?, et) != .success and !self.castable(vt.?, et)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .invalid_cast, .{});
                    return null;
                }
            },
            .bitcast => {
                const gsize = check_types.typeSize(self, vt.?);
                const tsize = check_types.typeSize(self, et);
                if (gsize == null or tsize == null) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .invalid_bitcast, .{});
                    return null;
                }
                if (gsize.? != tsize.?) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .invalid_bitcast, .{});
                    return null;
                }
            },
            .saturate, .wrap => {
                // Saturating and wrapping casts are for numeric types only.
                if (!check_types.isNumericKind(self, vk) or !check_types.isNumericKind(self, ek)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .numeric_cast_on_non_numeric, .{});
                    return null;
                }
            },
            .checked => {
                // Checked casts are similar to normal casts but might imply runtime checks.
                // For type checking, we can use the same rules as 'normal' for now,
                // but with a specific error message if it fails.
                if (self.assignable(vt.?, et) != .success and !self.castable(vt.?, et)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .invalid_checked_cast, .{});
                    return null;
                }
            },
        }

        return et;
    }

    fn checkCatch(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const cr = self.ast_unit.exprs.get(.Catch, id);
        const vt = try self.checkExpr(cr.expr);
        if (vt == null) return null;
        if (self.type_info.store.index.kinds.items[vt.?.toRaw()] != .ErrorSet) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .catch_on_non_error, .{});
            return null;
        }
        const er = self.type_info.store.ErrorSet.get(self.type_info.store.index.rows.items[vt.?.toRaw()]);
        const value_required = self.isValueReq();
        // Always type-check the handler body
        const ht = try self.checkExpr(cr.handler);
        if (ht == null) return null;
        if (!value_required) {
            // Used as a statement: no value produced
            return self.type_info.store.tVoid();
        }
        // In value position, ensure handler yields the value type of the error set
        if (self.assignable(ht.?, er.value_ty) != .success) {
            // Reuse if-branch mismatch diagnostic for now
            try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .if_branch_type_mismatch, .{});
            return null;
        }
        return er.value_ty;
    }

    fn checkImport(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const ir = self.ast_unit.exprs.get(.Import, id);
        const k = self.ast_unit.exprs.index.kinds.items[ir.expr.toRaw()];
        if (k != .Literal) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(ir.loc), .invalid_import_operand, .{});
            return null;
        }
        const lit = self.ast_unit.exprs.get(.Literal, ir.expr);
        if (lit.kind != .string or lit.value.isNone()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(ir.loc), .invalid_import_operand, .{});
            return null;
        }
        // Successful import expression is a module value; keep it as 'any' for now.
        return self.type_info.store.tAny();
    }

    // =========================================================
    // Misc helpers
    // =========================================================
    fn checkDivByZero(self: *Checker, rhs: ast.ExprId, loc: Loc) !void {
        if (self.ast_unit.exprs.index.kinds.items[rhs.toRaw()] == .Literal) {
            const lit = self.ast_unit.exprs.get(.Literal, rhs);
            switch (lit.kind) {
                .int => {
                    if (!lit.value.isNone()) {
                        const sval = self.ast_unit.exprs.strs.get(lit.value.unwrap());
                        if (std.mem.eql(u8, sval, "0")) try self.diags.addError(loc, .division_by_zero, .{});
                    }
                },
                .float => {
                    if (!lit.value.isNone()) {
                        const sval = self.ast_unit.exprs.strs.get(lit.value.unwrap());
                        const f = std.fmt.parseFloat(f64, sval) catch 1.0;
                        if (f == 0.0) try self.diags.addError(loc, .division_by_zero, .{});
                    }
                },
                else => {},
            }
        }
    }
    fn checkIntZeroLiteral(self: *Checker, rhs: ast.ExprId, loc: Loc) !void {
        if (self.ast_unit.exprs.index.kinds.items[rhs.toRaw()] == .Literal) {
            const lit = self.ast_unit.exprs.get(.Literal, rhs);
            if (lit.kind == .int and !lit.value.isNone()) {
                const sval = self.ast_unit.exprs.strs.get(lit.value.unwrap());
                if (std.mem.eql(u8, sval, "0")) try self.diags.addError(loc, .division_by_zero, .{});
            }
        }
    }

    const LvalueRootKind = enum { LocalDecl, Param, NonLocalDecl, Unknown };
    fn lvalueRootKind(self: *Checker, expr: ast.ExprId) LvalueRootKind {
        const kind = self.ast_unit.exprs.index.kinds.items[expr.toRaw()];
        switch (kind) {
            .Ident => {
                const idr = self.ast_unit.exprs.get(.Ident, expr);
                // Discard assignment '_' is considered local
                if (std.mem.eql(u8, self.ast_unit.exprs.strs.get(idr.name), "_")) return .LocalDecl;
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
                const dr = self.ast_unit.exprs.get(.Deref, expr);
                return self.lvalueRootKind(dr.expr);
            },
            .FieldAccess => {
                const fr = self.ast_unit.exprs.get(.FieldAccess, expr);
                return self.lvalueRootKind(fr.parent);
            },
            .IndexAccess => {
                const ir = self.ast_unit.exprs.get(.IndexAccess, expr);
                return self.lvalueRootKind(ir.collection);
            },
            else => return .Unknown,
        }
    }
};
