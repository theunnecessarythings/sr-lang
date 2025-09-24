const std = @import("std");
const ast = @import("ast.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const diag = @import("diagnostics.zig");
const Loc = @import("lexer.zig").Token.Loc;
const symbols = @import("symbols.zig");
const types = @import("types.zig");
const TypeInfo = types.TypeInfo;

pub const Checker = struct {
    gpa: std.mem.Allocator,
    diags: *Diagnostics,
    ast_unit: *const ast.Ast,
    type_info: TypeInfo,

    symtab: symbols.SymbolStore = undefined,

    func_stack: std.ArrayListUnmanaged(FunctionCtx) = .{},
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},
    value_ctx: std.ArrayListUnmanaged(bool) = .{},
    warned_meta: bool = false,
    warned_comptime: bool = false,
    warned_code: bool = false,

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
    const LoopCtx = struct { label: ast.OptStrId };

    fn bindDeclPattern(self: *Checker, did: ast.DeclId, d: ast.Rows.Decl) !void {
        if (d.pattern.isNone()) return;
        const name_opt = self.primaryNameOfPattern(d.pattern.unwrap());
        if (name_opt.isNone()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .invalid_binding_name_in_at_pattern, .{});
            return;
        }
        _ = try self.symtab.declare(.{
            .name = name_opt.unwrap(),
            .kind = .Var,
            .loc = d.loc,
            .origin_decl = ast.OptDeclId.some(did),
            .origin_param = ast.OptParamId.none(),
        });
    }

    fn bindParamPattern(self: *Checker, pid: ast.ParamId, p: ast.Rows.Param) !void {
        if (p.pat.isNone()) return;
        const name_opt = self.primaryNameOfPattern(p.pat.unwrap());
        if (name_opt.isNone()) return;
        _ = try self.symtab.declare(.{
            .name = name_opt.unwrap(),
            .kind = .Param,
            .loc = p.loc,
            .origin_decl = ast.OptDeclId.none(),
            .origin_param = ast.OptParamId.some(pid),
        });
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
        try self.loop_stack.append(self.gpa, .{ .label = label });
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
    fn isValueReq(self: *const Checker) bool {
        if (self.value_ctx.items.len == 0) return true; // default: value required
        return self.value_ctx.items[self.value_ctx.items.len - 1];
    }

    fn lookup(self: *Checker, name: ast.StrId) ?symbols.SymbolId {
        return self.symtab.lookup(self.ast_unit, self.symtab.currentId(), name);
    }

    fn primaryNameOfPattern(self: *Checker, pid: ast.PatternId) ast.OptStrId {
        const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
        return switch (k) {
            .Binding => ast.OptStrId.some(self.ast_unit.pats.get(.Binding, pid).name),
            .Path => blk: {
                const p = self.ast_unit.pats.get(.Path, pid);
                const segs = self.ast_unit.pats.seg_pool.slice(p.segments);
                if (segs.len == 0) break :blk ast.OptStrId.none();
                break :blk ast.OptStrId.some(self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw()).name);
            },
            else => ast.OptStrId.none(),
        };
    }

    // --------- type helpers
    fn isNumericKind(_: *const Checker, k: types.TypeKind) bool {
        return switch (k) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize, .Tensor, .Simd, .Complex => true,
            else => false,
        };
    }
    fn isIntegerKind(_: *const Checker, k: types.TypeKind) bool {
        return switch (k) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
            else => false,
        };
    }

    fn typeSize(self: *Checker, ty_id: types.TypeId) ?usize {
        const k = self.type_info.store.index.kinds.items[ty_id.toRaw()];
        return switch (k) {
            .I8, .U8 => 1,
            .I16, .U16 => 2,
            .I32, .U32, .F32 => 4,
            .I64, .U64, .F64, .Usize => 8, // Assuming usize is 8 bytes for 64-bit
            .Bool => 1, // Typically 1 byte
            .Ptr => 8, // Assuming 64-bit pointers
            .Void => 0, // No size
            .Any => null, // Unknown size
            .String => 8, // Assuming string is a pointer (8 bytes) for 64-bit (TODO: more complex)
            .Array => {
                const arr = self.type_info.store.Array.get(self.type_info.store.index.rows.items[ty_id.toRaw()]);
                const elem_size = self.typeSize(arr.elem) orelse return null;
                return elem_size * arr.len;
            },
            .Slice => 16, // Pointer + length (assuming 64-bit)
            .Optional => {
                const opt = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[ty_id.toRaw()]);
                const elem_size = self.typeSize(opt.elem) orelse return null;
                return elem_size + 1; // Element size + 1 byte for discriminant
            },
            // TODO: Implement for other aggregate types like Struct, Tuple, Union, etc.
            else => null, // Unknown or complex size
        };
    }

    fn isOptional(self: *Checker, id: types.TypeId) ?types.TypeId {
        const k = self.type_info.store.index.kinds.items[id.toRaw()];
        if (k != .Optional) return null;
        const opt = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[id.toRaw()]);
        return opt.elem;
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

    fn assignable(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
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
                if (!self.isIntegerKind(got_kind)) return .expected_integer_type;
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
            try self.typeFromTypeExpr(decl.ty.unwrap());
        const rhs_ty = try self.checkExpr(decl.value);
        // const rhs_kind = if (rhs_ty != null) self.type_info.store.index.kinds.items[rhs_ty.?.toRaw()] else null;
        // const expect_kind = if (expect_ty != null) self.type_info.store.index.kinds.items[expect_ty.?.toRaw()] else null;
        // std.debug.print("Decl @ {d}, expect={?}, rhs={?}\n", .{ decl.loc.toRaw(), expect_kind, rhs_kind });
        if (rhs_ty == null)
            return;
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
                const lt = try self.checkExpr(row.left);
                const rt = try self.checkExpr(row.right);
                if (lt != null and rt != null and (self.assignable(rt.?, lt.?) != .success)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .type_annotation_mismatch, .{});
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
                if (!row.value.isNone())
                    _ = try self.checkExpr(row.value.unwrap());
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
    fn checkExpr(self: *Checker, id: ast.ExprId) anyerror!?types.TypeId {
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
            .Match => try self.checkMatch(id),
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
            .TypeOf => try self.checkTypeOf(id),
            .NullLit => self.type_info.store.mkOptional(self.type_info.store.tAny()),

            .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => blk: {
                const ty = try self.typeFromTypeExpr(id);
                if (ty == null) break :blk null;
                break :blk self.type_info.store.mkTypeType(ty.?);
            },
            .MapType => blk_mt_expr: {
                // Try to interpret as a type expression first
                const row = self.ast_unit.exprs.get(.MapType, id);
                const key_ty = try self.typeFromTypeExpr(row.key);
                const val_ty = try self.typeFromTypeExpr(row.value);
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
                if (self.type_info.decl_types.items[srow.origin_decl.unwrap().toRaw()]) |dt|
                    return dt;
            }
            // Param-originated symbol?
            if (!srow.origin_param.isNone()) {
                const pid = srow.origin_param.unwrap();
                const p = self.ast_unit.exprs.Param.get(pid.toRaw());
                if (!p.ty.isNone()) {
                    const pt = (try self.typeFromTypeExpr(p.ty.unwrap())) orelse return null;
                    return pt;
                } else {
                    // Unannotated param currently treated as 'any'
                    return self.type_info.store.tAny();
                }
            }
        }
        return null;
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

    fn checkBlock(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const br = self.ast_unit.exprs.get(.Block, id);
        const stmts = self.ast_unit.stmts.stmt_pool.slice(br.items);
        var i: usize = 0;
        _ = try self.symtab.push(self.symtab.currentId());
        defer self.symtab.pop();

        if (stmts.len == 0) return self.type_info.store.tVoid();
        const value_required = self.isValueReq();
        if (!value_required) {
            // Statement context: just type-check children, no value produced
            while (i < stmts.len) : (i += 1) {
                _ = try self.checkStmt(stmts[i]);
            }
            return self.type_info.store.tVoid();
        }
        // Value context: the last line must be an expression to produce a value
        while (i < stmts.len - 1) : (i += 1) {
            _ = try self.checkStmt(stmts[i]);
        }
        // If last is an expression, evaluate it in value context directly
        const last = stmts[stmts.len - 1];
        const last_kind = self.ast_unit.stmts.index.kinds.items[last.toRaw()];
        if (last_kind == .Expr) {
            const row = self.ast_unit.stmts.get(.Expr, last);
            return try self.checkExpr(row.expr);
        }
        // Otherwise, type-check the statement and treat as void
        _ = try self.checkStmt(last);
        return self.type_info.store.tVoid();
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
                    if (self.isIntegerKind(lhs_kind) and self.isIntegerKind(rhs_kind))
                        try self.checkIntZeroLiteral(bin.right, self.ast_unit.exprs.locs.get(bin.loc));
                }
                if (!self.isNumericKind(lhs_kind) or !self.isNumericKind(rhs_kind)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                    return null;
                }
                if (l.toRaw() == r.toRaw()) return l;
                try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                return null;
            },
            .eq, .neq, .lt, .lte, .gt, .gte => {
                const both_numeric = self.isNumericKind(lhs_kind) and self.isNumericKind(rhs_kind);
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
                if (self.isOptional(l)) |elem| {
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
                if (!self.isNumericKind(type_kind)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(unary_expr.loc), .invalid_unary_op_operand, .{});
                    return null;
                }
                return t;
            },
            .logical_not => {
                if (t.toRaw() != self.type_info.store.tBool().toRaw()) {
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
            (try self.typeFromTypeExpr(fnr.result_ty.unwrap()))
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
                const pt = (try self.typeFromTypeExpr(p.ty.unwrap())) orelse return null;
                pbuf[i] = pt;
            } else {
                pbuf[i] = self.type_info.store.tAny();
            }
            // store in symbol table
            try self.bindParamPattern(params[i], p);
        }

        // Temporarily record a function type (purity will be finalized after body analysis)
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
            .Array => {
                const idx_kind = self.ast_unit.exprs.index.kinds.items[index_expr.index.toRaw()];
                if (idx_kind == .Range) {
                    _ = self.checkExpr(index_expr.index) catch return null;
                    const r = self.type_info.store.Array.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
                    return self.type_info.store.mkSlice(r.elem);
                }

                const it = self.checkExpr(index_expr.index) catch return null;
                if (it) |iid| {
                    if (!self.isIntegerKind(self.type_info.store.index.kinds.items[iid.toRaw()])) {
                        _ = self.diags.addError(self.ast_unit.exprs.locs.get(index_expr.loc), .non_integer_index, .{}) catch {};
                        return null;
                    }
                }
                const r = self.type_info.store.Array.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
                return r.elem;
            },
            .Slice => {
                const idx_kind = self.ast_unit.exprs.index.kinds.items[index_expr.index.toRaw()];
                if (idx_kind == .Range) {
                    _ = self.checkExpr(index_expr.index) catch return null;
                    const r = self.type_info.store.Slice.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
                    return self.type_info.store.mkSlice(r.elem);
                }

                const it = self.checkExpr(index_expr.index) catch return null;
                if (it) |iid| {
                    if (!self.isIntegerKind(self.type_info.store.index.kinds.items[iid.toRaw()])) {
                        _ = self.diags.addError(self.ast_unit.exprs.locs.get(index_expr.loc), .non_integer_index, .{}) catch {};
                        return null;
                    }
                }
                const r = self.type_info.store.Slice.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
                return r.elem;
            },
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
                    if (!self.isIntegerKind(self.type_info.store.index.kinds.items[iid.toRaw()])) {
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

    fn checkFieldAccess(self: *Checker, id: ast.ExprId) ?types.TypeId {
        const field_expr = self.ast_unit.exprs.get(.FieldAccess, id);
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

    fn checkRange(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const rr = self.ast_unit.exprs.get(.Range, id);
        if (!rr.start.isNone()) {
            const st = try self.checkExpr(rr.start.unwrap());
            if (st == null or !self.isIntegerKind(self.type_info.store.index.kinds.items[st.?.toRaw()])) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(rr.loc), .non_integer_index, .{});
                return null;
            }
        }
        if (!rr.end.isNone()) {
            const et = try self.checkExpr(rr.end.unwrap());
            if (et == null or !self.isIntegerKind(self.type_info.store.index.kinds.items[et.?.toRaw()])) {
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
        const expect_ty = try self.typeFromTypeExpr(lit_ty) orelse
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

    fn checkCall(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const call_expr = self.ast_unit.exprs.get(.Call, id);
        // Handle variant/error tag constructors before evaluating callee expression.
        if (self.ast_unit.exprs.index.kinds.items[call_expr.callee.toRaw()] == .FieldAccess) {
            const fr = self.ast_unit.exprs.get(.FieldAccess, call_expr.callee);
            // Resolve the parent in type-space
            const parent_ty = try self.typeFromTypeExpr(fr.parent) orelse null;
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
            const parent_ty = try self.typeFromTypeExpr(fr.parent) orelse null;
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
        else
            try self.checkExpr(rr.value.unwrap());
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
            if (cond == null or cond.?.toRaw() != self.type_info.store.tBool().toRaw()) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(wr.loc), .non_boolean_condition, .{});
                return null;
            }
        }
        // Pattern-matching while loop
        else if (!wr.cond.isNone() and !wr.pattern.isNone()) {
            const expr_ty = try self.checkExpr(wr.cond.unwrap());
            if (expr_ty == null) return null;
            if (!try self.checkPattern(wr.pattern.unwrap(), expr_ty.?, true)) {
                return null;
            }
        }
        // Infinite loop
        else if (wr.cond.isNone() and wr.pattern.isNone()) {} else unreachable;

        try self.pushLoop(wr.label);
        defer self.popLoop();
        return self.checkExpr(wr.body);
    }

    fn checkMatch(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const mr = self.ast_unit.exprs.get(.Match, id);
        const mt = try self.checkExpr(mr.expr);
        if (mt == null) return null;
        var result_ty: ?types.TypeId = null;
        const arms = self.ast_unit.exprs.arm_pool.slice(mr.arms);
        var i: usize = 0;
        while (i < arms.len) : (i += 1) {
            const arm = self.ast_unit.exprs.MatchArm.get(arms[i].toRaw());
            if (!try self.checkPattern(arm.pattern, mt.?, false)) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(arm.loc), .pattern_shape_mismatch, .{});
                return null;
            }
            const at = try self.checkExpr(arm.body);
            if (at == null) return null;
            if (result_ty == null) result_ty = at else if (result_ty.?.toRaw() != at.?.toRaw()) {
                result_ty = self.type_info.store.tAny();
            }
            i += 1;
        }
        if (result_ty == null) return self.type_info.store.tVoid();
        return result_ty;
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
            .Array, .Slice => {
                const elem_ty = if (kind == .Array)
                    self.type_info.store.Array.get(self.type_info.store.index.rows.items[it.?.toRaw()]).elem
                else
                    self.type_info.store.Slice.get(self.type_info.store.index.rows.items[it.?.toRaw()]).elem;
                if (!try self.checkPattern(fr.pattern, elem_ty, true)) {
                    return null;
                }
            },
            else => {
                try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .non_iterable_in_for, .{});
                return null;
            },
        }
        // Body must type-check
        try self.pushLoop(fr.label);
        defer self.popLoop();
        return self.checkExpr(fr.body);
    }

    fn checkPattern(self: *Checker, pid: ast.PatternId, value_ty: types.TypeId, top_level: bool) !bool {
        _ = top_level;
        const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];

        switch (k) {
            .Or, .At, .Range, .VariantStruct, .VariantTuple => unreachable,
            .Binding => {
                const bp = self.ast_unit.pats.get(.Binding, pid);
                // Declare the bound name in the symbol table
                _ = try self.symtab.declare(.{
                    .name = bp.name,
                    .kind = .Var, // Or appropriate kind
                    .loc = bp.loc,
                    .origin_decl = ast.OptDeclId.none(),
                    .origin_param = ast.OptParamId.none(),
                });
                // If there's a sub-pattern, check it recursively
                // if (!bp.pattern.isNone()) {
                //     return self.checkPattern(bp.pattern.unwrap(), value_ty, top_level);
                // }
                return true;
            },
            .Wildcard => return true,
            .Literal => {
                const lp = self.ast_unit.pats.get(.Literal, pid);
                const pattern_loc = self.ast_unit.exprs.locs.get(lp.loc);
                const lit_expr_id = lp.expr;
                const lit_ty = (try self.checkExpr(lit_expr_id)) orelse return false;
                if (self.assignable(value_ty, lit_ty) != .success) {
                    try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                    return false;
                }
                // TODO: For literal patterns, if not top_level, we might need to check the actual value for equality.
                // This would involve evaluating the literal expression and comparing it with the value being matched.
                // For now, only type compatibility is checked.
                return true;
            },
            .Tuple => {
                const tp = self.ast_unit.pats.get(.Tuple, pid);
                const pattern_loc = self.ast_unit.exprs.locs.get(tp.loc);
                const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
                if (value_kind != .Tuple) {
                    try self.diags.addError(pattern_loc, .pattern_shape_mismatch, .{});
                    return false;
                }
                const value_tuple_ty = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
                const pattern_elems = self.ast_unit.pats.pat_pool.slice(tp.elems);
                const value_elems = self.type_info.store.type_pool.slice(value_tuple_ty.elems);

                if (pattern_elems.len != value_elems.len) {
                    try self.diags.addError(pattern_loc, .tuple_arity_mismatch, .{});
                    return false;
                }

                for (pattern_elems, 0..) |pat_elem_id, i| {
                    if (!(try self.checkPattern(pat_elem_id, value_elems[i], false))) {
                        return false;
                    }
                }
                return true;
            },
            .Slice => {
                const ap = self.ast_unit.pats.get(.Slice, pid);
                const pattern_loc = self.ast_unit.exprs.locs.get(ap.loc);
                const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
                if (value_kind != .Array) {
                    try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                    return false;
                }
                const value_array_ty = self.type_info.store.Array.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
                const pattern_elems = self.ast_unit.pats.pat_pool.slice(ap.elems);

                if (pattern_elems.len != value_array_ty.len) {
                    try self.diags.addError(pattern_loc, .array_length_mismatch, .{});
                    return false;
                }

                for (pattern_elems) |pat_elem_id| {
                    if (!(try self.checkPattern(pat_elem_id, value_array_ty.elem, false))) {
                        return false;
                    }
                }
                return true;
            },
            .Struct => {
                const sp = self.ast_unit.pats.get(.Struct, pid);
                const pattern_loc = self.ast_unit.exprs.locs.get(sp.loc);
                const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
                if (value_kind != .Struct) {
                    try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                    return false;
                }
                const value_struct_ty = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
                const pattern_fields = self.ast_unit.pats.field_pool.slice(sp.fields);
                const value_fields = self.type_info.store.field_pool.slice(value_struct_ty.fields);

                // For each pattern field, find a matching field in the value type and check recursively
                for (pattern_fields) |pat_field_id| {
                    const pat_field = self.ast_unit.pats.StructField.get(pat_field_id.toRaw());
                    var found_match = false;
                    for (value_fields) |val_field_id| {
                        const val_field = self.type_info.store.Field.get(val_field_id.toRaw());
                        if (pat_field.name.toRaw() == val_field.name.toRaw()) {
                            found_match = true;
                            if (!(try self.checkPattern(pat_field.pattern, val_field.ty, false))) {
                                return false;
                            }
                            break;
                        }
                    }
                    if (!found_match) {
                        try self.diags.addError(pattern_loc, .unknown_struct_field, .{});
                        return false;
                    }
                }
                return true;
            },
            // .Enum => {
            //     const ep = self.ast_unit.pats.get(.Enum, pid);
            //     const pattern_loc = self.ast_unit.exprs.locs.get(ep.loc);
            //     const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
            //     if (value_kind != .Enum) {
            //         try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
            //         return false;
            //     }
            //     const value_enum_ty = self.type_info.store.Enum.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            //     const pattern_tag_name = self.ast_unit.exprs.strs.get(ep.tag);
            //
            //     var found_tag = false;
            //     for (self.type_info.store.enum_member_pool.slice(value_enum_ty.members)) |member_id| {
            //         const member = self.type_info.store.EnumMember.get(member_id.toRaw());
            //         if (std.mem.eql(u8, pattern_tag_name, member.name)) {
            //             found_tag = true;
            //             break;
            //         }
            //     }
            //     if (!found_tag) {
            //         try self.diags.addError(pattern_loc, .unknown_enum_tag, .{});
            //         return false;
            //     }
            //     // Enum patterns don't have sub-patterns for their values, just the tag.
            //     return true;
            // },
            // .Variant => {
            //     const vp = self.ast_unit.pats.get(.Variant, pid);
            //     const pattern_loc = self.ast_unit.exprs.locs.get(vp.loc);
            //     const value_kind = self.type_info.store.index.kinds.items[value_ty.toRaw()];
            //     if (value_kind != .Variant) {
            //         try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
            //         return false;
            //     }
            //     const value_variant_ty = self.type_info.store.Variant.get(self.type_info.store.index.rows.items[value_ty.toRaw()]);
            //     const pattern_tag_name = self.ast_unit.exprs.strs.get(vp.tag);
            //
            //     var found_tag_and_matched_payload = false;
            //     for (self.type_info.store.field_pool.slice(value_variant_ty.variants)) |variant_field_id| {
            //         const variant_field = self.type_info.store.Field.get(variant_field_id.toRaw());
            //         if (std.mem.eql(u8, pattern_tag_name, self.ast_unit.exprs.strs.get(variant_field.name))) {
            //             // Found the matching variant tag
            //             if (!vp.pattern.isNone()) {
            //                 // If there's a payload pattern, check it against the variant's payload type
            //                 if (try self.checkPattern(vp.pattern.unwrap(), variant_field.ty, false)) {
            //                     found_tag_and_matched_payload = true;
            //                 }
            //             } else {
            //                 // No payload pattern, just tag match is enough
            //                 found_tag_and_matched_payload = true;
            //             }
            //             break;
            //         }
            //     }
            //     if (!found_tag_and_matched_payload) {
            //         try self.diags.addError(pattern_loc, .unknown_variant_tag, .{});
            //         return false;
            //     }
            //     return true;
            // },
            .Path => {
                const pp = self.ast_unit.pats.get(.Path, pid);
                const pattern_loc = self.ast_unit.exprs.locs.get(pp.loc);
                const segments = self.ast_unit.pats.seg_pool.slice(pp.segments);
                if (segments.len == 0) {
                    try self.diags.addError(pattern_loc, .empty_path_pattern, .{});
                    return false;
                }

                // Resolve the path to a type or a specific enum/variant member
                // This is a simplified approach; a full implementation would involve symbol resolution
                // across modules/scopes. For now, assume it refers to an enum or variant member.

                // Get the type of the first segment (e.g., `Enum` in `Enum.Member`)
                const first_seg_name = self.ast_unit.pats.PathSeg.get(segments[0].toRaw()).name;
                const first_seg_str = self.ast_unit.exprs.strs.get(first_seg_name);

                // Try to resolve the first segment as a type
                // This is a very basic lookup, a real compiler would have a more robust type resolution system
                var current_ty: ?types.TypeId = blk: {
                    if (std.mem.eql(u8, first_seg_str, "bool")) break :blk self.type_info.store.tBool();
                    if (std.mem.eql(u8, first_seg_str, "i8")) break :blk self.type_info.store.tI8();
                    if (std.mem.eql(u8, first_seg_str, "i16")) break :blk self.type_info.store.tI16();
                    if (std.mem.eql(u8, first_seg_str, "i32")) break :blk self.type_info.store.tI32();
                    if (std.mem.eql(u8, first_seg_str, "i64")) break :blk self.type_info.store.tI64();
                    if (std.mem.eql(u8, first_seg_str, "u8")) break :blk self.type_info.store.tU8();
                    if (std.mem.eql(u8, first_seg_str, "u16")) break :blk self.type_info.store.tU16();
                    if (std.mem.eql(u8, first_seg_str, "u32")) break :blk self.type_info.store.tU32();
                    if (std.mem.eql(u8, first_seg_str, "u64")) break :blk self.type_info.store.tU64();
                    if (std.mem.eql(u8, first_seg_str, "f32")) break :blk self.type_info.store.tF32();
                    if (std.mem.eql(u8, first_seg_str, "f64")) break :blk self.type_info.store.tF64();
                    if (std.mem.eql(u8, first_seg_str, "usize")) break :blk self.type_info.store.tUsize();
                    if (std.mem.eql(u8, first_seg_str, "char")) break :blk self.type_info.store.tU32();
                    if (std.mem.eql(u8, first_seg_str, "string")) break :blk self.type_info.store.tString();
                    if (std.mem.eql(u8, first_seg_str, "void")) break :blk self.type_info.store.tVoid();
                    if (std.mem.eql(u8, first_seg_str, "any")) break :blk self.type_info.store.tAny();

                    if (self.lookup(first_seg_name)) |sid| {
                        const sym = self.symtab.syms.get(sid.toRaw());
                        if (!sym.origin_decl.isNone()) {
                            if (self.type_info.decl_types.items[sym.origin_decl.unwrap().toRaw()]) |ty| {
                                if (self.type_info.store.index.kinds.items[ty.toRaw()] == .TypeType) {
                                    const tt = self.type_info.store.TypeType.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                                    break :blk tt.of;
                                } else {
                                    break :blk ty;
                                }
                            }
                        }
                    }
                    break :blk null;
                };

                if (current_ty == null) {
                    try self.diags.addError(pattern_loc, .unknown_type_in_path, .{});
                    return false;
                }

                // Traverse the rest of the path
                var i: usize = 1;
                while (i < segments.len) : (i += 1) {
                    const seg = self.ast_unit.pats.PathSeg.get(segments[i].toRaw());
                    const current_kind = self.type_info.store.index.kinds.items[current_ty.?.toRaw()];

                    if (current_kind == .Enum) {
                        const enum_ty = self.type_info.store.Enum.get(self.type_info.store.index.rows.items[current_ty.?.toRaw()]);
                        var found_member = false;
                        for (self.type_info.store.enum_member_pool.slice(enum_ty.members)) |member_id| {
                            const member = self.type_info.store.EnumMember.get(member_id.toRaw());
                            if (seg.name.toRaw() == member.name.toRaw()) {
                                // The path refers to an enum member. The type of the path pattern is the enum itself.
                                // So, we check if the value_ty is assignable to the enum type.
                                if (self.assignable(value_ty, current_ty.?) != .success) {
                                    try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                                    return false;
                                }
                                found_member = true;
                                break;
                            }
                        }
                        if (!found_member) {
                            try self.diags.addError(pattern_loc, .unknown_enum_tag, .{});
                            return false;
                        }
                        return true; // Path fully resolved to an enum member
                    } else if (current_kind == .Variant) {
                        const variant_ty = self.type_info.store.Variant.get(self.type_info.store.index.rows.items[current_ty.?.toRaw()]);
                        var found_case = false;
                        for (self.type_info.store.field_pool.slice(variant_ty.variants)) |variant_field_id| {
                            const variant_field = self.type_info.store.Field.get(variant_field_id.toRaw());
                            if (seg.name.toRaw() == variant_field.name.toRaw()) {
                                // The path refers to a variant case. The type of the path pattern is the variant itself.
                                // So, we check if the value_ty is assignable to the variant type.
                                if (self.assignable(value_ty, current_ty.?) != .success) {
                                    try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                                    return false;
                                }
                                found_case = true;
                                break;
                            }
                        }
                        if (!found_case) {
                            try self.diags.addError(pattern_loc, .unknown_variant_tag, .{});
                            return false;
                        }
                        return true; // Path fully resolved to a variant case
                    } else {
                        try self.diags.addError(pattern_loc, .field_access_on_non_aggregate, .{});
                        return false;
                    }
                }
                // If we reached here, it means the path was just a single identifier that resolved to a type.
                // In this case, the pattern matches if the value_ty is assignable to the resolved type.
                if (self.assignable(value_ty, current_ty.?) != .success) {
                    try self.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                    return false;
                }
                return true;
            },
        }
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
        _ = id;
        return self.type_info.store.tVoid();
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
            const pt = try self.typeFromTypeExpr(p.ty.unwrap());
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
        const et = try self.typeFromTypeExpr(cr.ty) orelse {
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
                const gsize = self.typeSize(vt.?);
                const tsize = self.typeSize(et);
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
                if (!self.isNumericKind(vk) or !self.isNumericKind(ek)) {
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
        return er.value_ty;
    }

    fn checkImport(self: *Checker, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.type_info.store.tAny();
    }

    fn checkTypeOf(self: *Checker, id: ast.ExprId) !?types.TypeId {
        const tr = self.ast_unit.exprs.get(.TypeOf, id);
        const tt = try self.typeFromTypeExpr(tr.expr) orelse {
            try self.diags.addError(self.ast_unit.exprs.locs.get(tr.loc), .could_not_resolve_type, .{});
            return null;
        };
        return self.type_info.store.mkTypeType(tt);
    }

    // =========================================================
    // Type expressions
    // =========================================================
    fn typeFromTypeExpr(self: *Checker, id: ast.ExprId) anyerror!?types.TypeId {
        const k = self.ast_unit.exprs.index.kinds.items[id.toRaw()];
        return switch (k) {
            .Ident => blk_ident: {
                const name = self.ast_unit.exprs.get(.Ident, id).name;
                const s = self.ast_unit.exprs.strs.get(name);
                if (std.mem.eql(u8, s, "bool")) break :blk_ident self.type_info.store.tBool();
                if (std.mem.eql(u8, s, "i8")) break :blk_ident self.type_info.store.tI8();
                if (std.mem.eql(u8, s, "i16")) break :blk_ident self.type_info.store.tI16();
                if (std.mem.eql(u8, s, "i32")) break :blk_ident self.type_info.store.tI32();
                if (std.mem.eql(u8, s, "i64")) break :blk_ident self.type_info.store.tI64();
                if (std.mem.eql(u8, s, "u8")) break :blk_ident self.type_info.store.tU8();
                if (std.mem.eql(u8, s, "u16")) break :blk_ident self.type_info.store.tU16();
                if (std.mem.eql(u8, s, "u32")) break :blk_ident self.type_info.store.tU32();
                if (std.mem.eql(u8, s, "u64")) break :blk_ident self.type_info.store.tU64();
                if (std.mem.eql(u8, s, "f32")) break :blk_ident self.type_info.store.tF32();
                if (std.mem.eql(u8, s, "f64")) break :blk_ident self.type_info.store.tF64();
                if (std.mem.eql(u8, s, "usize")) break :blk_ident self.type_info.store.tUsize();
                if (std.mem.eql(u8, s, "char")) break :blk_ident self.type_info.store.tU32();
                if (std.mem.eql(u8, s, "string")) break :blk_ident self.type_info.store.tString();
                if (std.mem.eql(u8, s, "void")) break :blk_ident self.type_info.store.tVoid();
                if (std.mem.eql(u8, s, "any")) break :blk_ident self.type_info.store.tAny();

                if (self.lookup(name)) |sid| {
                    const sym = self.symtab.syms.get(sid.toRaw());
                    if (!sym.origin_decl.isNone()) {
                        if (self.type_info.decl_types.items[sym.origin_decl.unwrap().toRaw()]) |ty| {
                            if (self.type_info.store.index.kinds.items[ty.toRaw()] == .TypeType) {
                                const tt = self.type_info.store.TypeType.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                                return tt.of;
                            }
                            return ty;
                        }
                    }
                }

                break :blk_ident null;
            },
            .TupleType => blk_tt: {
                const row = self.ast_unit.exprs.get(.TupleType, id);
                const ids = self.ast_unit.exprs.expr_pool.slice(row.elems);
                var buf = try self.type_info.store.gpa.alloc(types.TypeId, ids.len);
                defer self.type_info.store.gpa.free(buf);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) buf[i] = (try self.typeFromTypeExpr(ids[i])) orelse break :blk_tt null;
                break :blk_tt self.type_info.store.mkTuple(buf);
            },
            .TupleLit => blk_ttl: {
                const row = self.ast_unit.exprs.get(.TupleLit, id);
                const ids = self.ast_unit.exprs.expr_pool.slice(row.elems);
                var buf = try self.type_info.store.gpa.alloc(types.TypeId, ids.len);
                defer self.type_info.store.gpa.free(buf);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) buf[i] = (try self.typeFromTypeExpr(ids[i])) orelse break :blk_ttl null;
                break :blk_ttl self.type_info.store.mkTuple(buf);
            },
            .MapType => blk_mt: {
                const row = self.ast_unit.exprs.get(.MapType, id);
                const key = (try self.typeFromTypeExpr(row.key)) orelse break :blk_mt null;
                const val = (try self.typeFromTypeExpr(row.value)) orelse break :blk_mt null;
                break :blk_mt self.type_info.store.mkMap(key, val);
            },
            .ArrayType => blk_at: {
                const row = self.ast_unit.exprs.get(.ArrayType, id);
                const elem = (try self.typeFromTypeExpr(row.elem)) orelse break :blk_at null;
                var len_val: usize = 0;
                if (self.ast_unit.exprs.index.kinds.items[row.size.toRaw()] == .Literal) {
                    const lit = self.ast_unit.exprs.get(.Literal, row.size);
                    if (lit.kind == .int and !lit.value.isNone()) {
                        len_val = std.fmt.parseInt(usize, self.ast_unit.exprs.strs.get(lit.value.unwrap()), 10) catch 0;
                    } else {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .array_size_not_integer_literal, .{});
                        return null;
                    }
                } else return error.InvalidArraySize;
                break :blk_at self.type_info.store.mkArray(elem, len_val);
            },
            .DynArrayType => blk_dt: {
                const row = self.ast_unit.exprs.get(.DynArrayType, id);
                const elem = (try self.typeFromTypeExpr(row.elem)) orelse break :blk_dt null;
                break :blk_dt self.type_info.store.mkDynArray(elem);
            },
            .SliceType => blk_st: {
                const row = self.ast_unit.exprs.get(.SliceType, id);
                const elem = (try self.typeFromTypeExpr(row.elem)) orelse break :blk_st null;
                break :blk_st self.type_info.store.mkSlice(elem);
            },
            .OptionalType => blk_ot: {
                const row = self.ast_unit.exprs.get(.OptionalType, id);
                const elem = (try self.typeFromTypeExpr(row.elem)) orelse break :blk_ot null;
                break :blk_ot self.type_info.store.mkOptional(elem);
            },
            .PointerType => blk_pt: {
                const row = self.ast_unit.exprs.get(.PointerType, id);
                const elem = (try self.typeFromTypeExpr(row.elem)) orelse break :blk_pt null;
                break :blk_pt self.type_info.store.mkPtr(elem, row.is_const);
            },
            .SimdType => blk_simd: {
                const row = self.ast_unit.exprs.get(.SimdType, id);
                // element type must be numeric (int or float)
                const elem_ty = (try self.typeFromTypeExpr(row.elem)) orelse break :blk_simd null;
                const ek = self.type_info.store.index.kinds.items[elem_ty.toRaw()];
                if (!self.isNumericKind(ek)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_invalid_element_type, .{});
                    break :blk_simd null;
                }
                // lanes must be an integer literal
                const lk = self.ast_unit.exprs.index.kinds.items[row.lanes.toRaw()];
                if (lk != .Literal) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                    break :blk_simd null;
                }
                const lit = self.ast_unit.exprs.get(.Literal, row.lanes);
                if (lit.kind != .int) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                    break :blk_simd null;
                }
                // Accept the type (we don't model concrete simd in TypeStore yet)
                break :blk_simd self.type_info.store.tAny();
            },
            .TensorType => blk_tensor: {
                const row = self.ast_unit.exprs.get(.TensorType, id);
                // Validate shape dimensions are integer literals
                const dims = self.ast_unit.exprs.expr_pool.slice(row.shape);
                var i: usize = 0;
                while (i < dims.len) : (i += 1) {
                    const dk = self.ast_unit.exprs.index.kinds.items[dims[i].toRaw()];
                    if (dk != .Literal) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                        break :blk_tensor null;
                    }
                    const dl = self.ast_unit.exprs.get(.Literal, dims[i]);
                    if (dl.kind != .int) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                        break :blk_tensor null;
                    }
                }
                // Validate element type present and resolvable
                const ety = try self.typeFromTypeExpr(row.elem);
                if (ety == null) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_missing_arguments, .{});
                    break :blk_tensor null;
                }
                break :blk_tensor self.type_info.store.tAny();
            },
            .StructType => blk_sty: {
                const row = self.ast_unit.exprs.get(.StructType, id);
                const sfs = self.ast_unit.exprs.sfield_pool.slice(row.fields);
                var buf = try self.type_info.store.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
                defer self.type_info.store.gpa.free(buf);
                var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
                defer seen.deinit(self.gpa);
                var i: usize = 0;
                while (i < sfs.len) : (i += 1) {
                    const f = self.ast_unit.exprs.StructField.get(sfs[i].toRaw());
                    const gop = try seen.getOrPut(self.gpa, f.name.toRaw());
                    if (gop.found_existing) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(f.loc), .duplicate_field, .{});
                        return null;
                    }
                    const ft = (try self.typeFromTypeExpr(f.ty)) orelse break :blk_sty null;
                    buf[i] = .{ .name = f.name, .ty = ft };
                }
                break :blk_sty self.type_info.store.mkStruct(buf);
            },
            .UnionType => blk_un: {
                const row = self.ast_unit.exprs.get(.UnionType, id);
                const sfs = self.ast_unit.exprs.sfield_pool.slice(row.fields);
                var buf = try self.type_info.store.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
                defer self.type_info.store.gpa.free(buf);
                var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
                defer seen.deinit(self.gpa);
                var i: usize = 0;
                while (i < sfs.len) : (i += 1) {
                    const sf = self.ast_unit.exprs.StructField.get(sfs[i].toRaw());
                    const gop = try seen.getOrPut(self.gpa, sf.name.toRaw());
                    if (gop.found_existing) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(sf.loc), .duplicate_field, .{});
                        return null;
                    }
                    // Validate field types resolve
                    const ft = (try self.typeFromTypeExpr(sf.ty)) orelse break :blk_un null;
                    buf[i] = .{ .name = sf.name, .ty = ft };
                }
                break :blk_un self.type_info.store.mkUnion(buf);
            },
            .EnumType => blk_en: {
                const row = self.ast_unit.exprs.get(.EnumType, id);
                const efs = self.ast_unit.exprs.efield_pool.slice(row.fields);

                const tag_ty = if (row.discriminant.isNone())
                    self.type_info.store.tI32()
                else
                    (try self.typeFromTypeExpr(row.discriminant.unwrap())) orelse return null;

                var member_buf = try self.gpa.alloc(types.TypeStore.EnumMemberArg, efs.len);
                defer self.gpa.free(member_buf);

                var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
                defer seen.deinit(self.gpa);

                var next_value: u64 = 0;
                var i: usize = 0;
                while (i < efs.len) : (i += 1) {
                    const enum_field = self.ast_unit.exprs.EnumField.get(efs[i].toRaw());
                    const name = self.ast_unit.exprs.strs.get(enum_field.name);

                    const gop = try seen.getOrPut(self.gpa, enum_field.name.toRaw());
                    if (gop.found_existing) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .duplicate_enum_field, .{});
                        return null;
                    }

                    var current_value: u64 = next_value;
                    if (!enum_field.value.isNone()) {
                        const val_id = enum_field.value.unwrap();
                        const val_kind = self.ast_unit.exprs.index.kinds.items[val_id.toRaw()];
                        if (val_kind != .Literal) {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                            return null;
                        }
                        const lit = self.ast_unit.exprs.get(.Literal, val_id);
                        if (lit.kind != .int or lit.value.isNone()) {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                            return null;
                        }
                        const val_str = self.ast_unit.exprs.strs.get(lit.value.unwrap());
                        current_value = try std.fmt.parseInt(u64, val_str, 10);
                    }

                    member_buf[i] = .{ .name = name, .value = current_value };
                    next_value = current_value + 1;
                }
                break :blk_en self.type_info.store.mkEnum(member_buf, tag_ty);
            },
            .ErrorType => blk_err: {
                const row = self.ast_unit.exprs.get(.ErrorType, id);
                const vfs = self.ast_unit.exprs.vfield_pool.slice(row.fields);
                var case_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
                defer self.gpa.free(case_buf);

                var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
                defer seen.deinit(self.gpa);

                var i: usize = 0;
                while (i < vfs.len) : (i += 1) {
                    const vf = self.ast_unit.exprs.VariantField.get(vfs[i].toRaw());
                    const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                    if (gop.found_existing) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(vf.loc), .duplicate_error_variant, .{});
                        return null;
                    }

                    const payload_ty = switch (vf.payload_kind) {
                        .none => self.type_info.store.tVoid(),
                        .tuple => blk_tuple: {
                            if (vf.payload_elems.isNone()) {
                                break :blk_tuple self.type_info.store.tVoid();
                            }
                            const elems = self.ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                            var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                            defer self.gpa.free(elem_buf);
                            var j: usize = 0;
                            while (j < elems.len) : (j += 1) {
                                elem_buf[j] = (try self.typeFromTypeExpr(elems[j])) orelse return null;
                            }
                            break :blk_tuple self.type_info.store.mkTuple(elem_buf);
                        },
                        .@"struct" => blk_struct: {
                            if (vf.payload_fields.isNone()) {
                                break :blk_struct self.type_info.store.tVoid();
                            }
                            const fields = self.ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                            var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                            defer self.gpa.free(field_buf);
                            var j: usize = 0;
                            while (j < fields.len) : (j += 1) {
                                const sf = self.ast_unit.exprs.StructField.get(fields[j].toRaw());
                                field_buf[j] = .{
                                    .name = sf.name,
                                    .ty = (try self.typeFromTypeExpr(sf.ty)) orelse return null,
                                };
                            }
                            break :blk_struct self.type_info.store.mkStruct(field_buf);
                        },
                    };
                    case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
                }
                break :blk_err self.type_info.store.mkError(case_buf);
            },
            .ErrorSetType => blk_est: {
                const row = self.ast_unit.exprs.get(.ErrorSetType, id);
                const val_ty = try self.typeFromTypeExpr(row.value);
                const err_ty = try self.typeFromTypeExpr(row.err);
                if (val_ty == null or err_ty == null) break :blk_est null;
                break :blk_est self.type_info.store.mkErrorSet(val_ty.?, err_ty.?);
            },
            .VariantType => blk_var: {
                const row = self.ast_unit.exprs.get(.VariantType, id);
                const vfs = self.ast_unit.exprs.vfield_pool.slice(row.fields);
                var case_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
                defer self.gpa.free(case_buf);

                var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
                defer seen.deinit(self.gpa);

                var i: usize = 0;
                while (i < vfs.len) : (i += 1) {
                    const vf = self.ast_unit.exprs.VariantField.get(vfs[i].toRaw());
                    const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                    if (gop.found_existing) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(vf.loc), .duplicate_variant, .{});
                        return null;
                    }

                    const payload_ty = switch (vf.payload_kind) {
                        .none => self.type_info.store.tVoid(),
                        .tuple => blk_tuple: {
                            if (vf.payload_elems.isNone()) {
                                break :blk_tuple self.type_info.store.tVoid();
                            }
                            const elems = self.ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                            var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                            defer self.gpa.free(elem_buf);
                            var j: usize = 0;
                            while (j < elems.len) : (j += 1) {
                                elem_buf[j] = (try self.typeFromTypeExpr(elems[j])) orelse return null;
                            }
                            break :blk_tuple self.type_info.store.mkTuple(elem_buf);
                        },
                        .@"struct" => blk_struct: {
                            if (vf.payload_fields.isNone()) {
                                break :blk_struct self.type_info.store.tVoid();
                            }
                            const fields = self.ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                            var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                            defer self.gpa.free(field_buf);
                            var j: usize = 0;
                            while (j < fields.len) : (j += 1) {
                                const sf = self.ast_unit.exprs.StructField.get(fields[j].toRaw());
                                field_buf[j] = .{
                                    .name = sf.name,
                                    .ty = (try self.typeFromTypeExpr(sf.ty)) orelse return null,
                                };
                            }
                            break :blk_struct self.type_info.store.mkStruct(field_buf);
                        },
                    };
                    case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
                }
                break :blk_var self.type_info.store.mkVariant(case_buf);
            },

            .FunctionLit => blk_fn: {
                // function type in type position
                const fnr = self.ast_unit.exprs.get(.FunctionLit, id);
                const params = self.ast_unit.exprs.param_pool.slice(fnr.params);
                var pbuf = try self.gpa.alloc(types.TypeId, params.len);
                defer self.gpa.free(pbuf);
                var i: usize = 0;
                while (i < params.len) : (i += 1) {
                    const p = self.ast_unit.exprs.Param.get(params[i].toRaw());
                    if (p.ty.isNone()) break :blk_fn null;
                    const pt = (try self.typeFromTypeExpr(p.ty.unwrap())) orelse break :blk_fn null;
                    pbuf[i] = pt;
                }
                const res = if (!fnr.result_ty.isNone()) (try self.typeFromTypeExpr(fnr.result_ty.unwrap())) else self.type_info.store.tVoid();
                if (res == null) break :blk_fn null;
                const is_pure = !fnr.flags.is_proc;
                break :blk_fn self.type_info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic, is_pure);
            },
            .FieldAccess => blk_fa: {
                const fr = self.ast_unit.exprs.get(.FieldAccess, id);
                const parent_ty = (try self.typeFromTypeExpr(fr.parent)) orelse break :blk_fa null;
                const parent_kind = self.type_info.store.index.kinds.items[parent_ty.toRaw()];
                switch (parent_kind) {
                    .Struct => {
                        const st = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[parent_ty.toRaw()]);
                        const fields = self.type_info.store.field_pool.slice(st.fields);
                        var i: usize = 0;
                        while (i < fields.len) : (i += 1) {
                            const f = fields[i];
                            const field = self.type_info.store.Field.get(f.toRaw());
                            if (field.name.toRaw() == fr.field.toRaw()) return field.ty;
                        }
                        try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{});
                        break :blk_fa null;
                    },
                    // NEW: handle Variant directly (e.g., V2.C in type position).
                    .Variant => {
                        const vt = self.type_info.store.Variant.get(self.type_info.store.index.rows.items[parent_ty.toRaw()]);
                        const cases = self.type_info.store.field_pool.slice(vt.variants);
                        var i: usize = 0;
                        while (i < cases.len) : (i += 1) {
                            const vc = self.type_info.store.Field.get(cases[i].toRaw());
                            if (vc.name.toRaw() == fr.field.toRaw()) {
                                // Return the payload type of the chosen variant (struct/tuple/void).
                                return vc.ty;
                            }
                        }
                        try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_variant_tag, .{});
                        break :blk_fa null;
                    },
                    .TypeType => {
                        // Back-compat in case a type value ever appears here:
                        const tt = self.type_info.store.TypeType.get(self.type_info.store.index.rows.items[parent_ty.toRaw()]);
                        const inner_kind = self.type_info.store.index.kinds.items[tt.of.toRaw()];
                        if (inner_kind == .Variant) {
                            const vt = self.type_info.store.Variant.get(self.type_info.store.index.rows.items[tt.of.toRaw()]);
                            const cases = self.type_info.store.field_pool.slice(vt.variants);
                            var i: usize = 0;
                            while (i < cases.len) : (i += 1) {
                                const vc = self.type_info.store.Field.get(cases[i].toRaw());
                                if (vc.name.toRaw() == fr.field.toRaw()) return vc.ty;
                            }
                            try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_variant_tag, .{});
                            break :blk_fa null;
                        } else {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .field_access_on_non_aggregate, .{});
                            break :blk_fa null;
                        }
                    },
                    else => {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .field_access_on_non_aggregate, .{});
                        break :blk_fa null;
                    },
                }
            },
            .AnyType => self.type_info.store.tAny(),
            .TypeType => self.type_info.store.tType(),
            .NoreturnType => self.type_info.store.tNoReturn(),
            else => null,
        };
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
