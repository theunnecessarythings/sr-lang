const std = @import("std");
const ast = @import("ast_v2.zig");
const Diagnostics = @import("diagnostics_v2.zig").Diagnostics;
const diag = @import("diagnostics_v2.zig");
const Loc = @import("lexer.zig").Token.Loc;
const symbols = @import("symbols_v2.zig");
const types = @import("types_v2.zig");
const TypeInfoV2 = types.TypeInfoV2;

pub const CheckerV2 = CheckerV3;
pub const CheckerV3 = struct {
    gpa: std.mem.Allocator,
    diags: *Diagnostics,
    ast_unit: *const ast.Ast,
    type_info: TypeInfoV2,

    symtab: symbols.SymbolStore = undefined,

    func_stack: std.ArrayListUnmanaged(FunctionCtx) = .{},
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},
    warned_meta: bool = false,
    warned_comptime: bool = false,
    warned_code: bool = false,

    pub fn init(
        gpa: std.mem.Allocator,
        diags: *Diagnostics,
        unit: *const ast.Ast,
    ) CheckerV3 {
        return .{
            .gpa = gpa,
            .diags = diags,
            .ast_unit = unit,
            .symtab = symbols.SymbolStore.init(gpa),
            .type_info = TypeInfoV2.init(gpa),
        };
    }
    pub fn deinit(self: *CheckerV3) void {
        self.func_stack.deinit(self.gpa);
        self.loop_stack.deinit(self.gpa);
        self.symtab.deinit();
    }

    pub fn run(self: *CheckerV3) !void {
        var info = try self.runWithTypes();
        info.deinit();
    }

    pub fn runWithTypes(self: *CheckerV3) !TypeInfoV2 {

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
    const FunctionCtx = struct { has_result: bool };
    const LoopCtx = struct { label: ast.OptStrId };
    const MapExpectation = struct { key: types.TypeId, value: types.TypeId, loc: Loc };
    const Expectation = struct {
        ty: ?types.TypeId = null,
        map: ?MapExpectation = null,
        suppress_null_assign: bool = false,
        enum_decl: ?ast.DeclId = null,
        error_decl: ?ast.DeclId = null,
    };
    const DeclExpectation = struct { ty: ?types.TypeId, ctx: Expectation };

    inline fn expectNone() Expectation {
        return .{};
    }
    inline fn expectTy(ty: types.TypeId) Expectation {
        return .{ .ty = ty };
    }
    inline fn expectTySuppressNull(ty: types.TypeId) Expectation {
        return .{ .ty = ty, .suppress_null_assign = true };
    }
    inline fn expectMap(key: types.TypeId, value: types.TypeId, loc: Loc) Expectation {
        return .{ .map = .{ .key = key, .value = value, .loc = loc } };
    }

    fn bindDeclPattern(self: *CheckerV3, did: ast.DeclId, d: ast.Rows.Decl) !void {
        if (d.pattern.isNone()) return;
        const name_opt = self.primaryNameOfPattern(d.pattern.unwrap());
        if (name_opt.isNone()) return;
        _ = try self.symtab.declare(.{ .name = name_opt.unwrap(), .kind = .Var, .loc = d.loc, .origin_decl = ast.OptDeclId.some(did), .origin_param = ast.OptParamId.none() });
    }

    fn prepareDeclExpectation(
        self: *CheckerV3,
        d: ast.Rows.Decl,
    ) !?DeclExpectation {
        var result = DeclExpectation{ .ty = null, .ctx = expectNone() };
        if (d.ty.isNone()) return result;

        const annot_id = d.ty.unwrap();
        const annot_kind = self.ast_unit.exprs.index.kinds.items[annot_id.toRaw()];
        var array_size_invalid = false;
        const resolved_ty = self.typeFromTypeExpr(annot_id) catch |err| switch (err) {
            error.InvalidArraySize => blk: {
                array_size_invalid = true;
                break :blk null;
            },
            else => return err,
        };

        if (array_size_invalid) {
            const loc_id = switch (annot_kind) {
                .ArrayType => self.ast_unit.exprs.get(.ArrayType, annot_id).loc,
                else => d.loc,
            };
            try self.diags.addError(self.ast_unit.exprs.locs.get(loc_id), .array_size_not_integer_literal, .{});
            return null;
        }

        result.ty = resolved_ty;
        if (result.ty) |et| {
            result.ctx = expectTy(et);
        } else if (annot_kind == .MapType) {
            const map_ty = self.ast_unit.exprs.get(.MapType, annot_id);
            const key_expect = try self.typeFromTypeExpr(map_ty.key);
            const value_expect = try self.typeFromTypeExpr(map_ty.value);
            if (key_expect != null and value_expect != null) {
                result.ctx = expectMap(key_expect.?, value_expect.?, self.ast_unit.exprs.locs.get(d.loc));
            }
        } else if (annot_kind == .TypeType) {
            // Expect a type value on RHS
            const any_t = self.type_info.store.tAny();
            const tt = self.type_info.store.mkTypeType(any_t);
            result.ty = tt;
            result.ctx = expectTy(tt);
        }
        if (self.enumDeclByExpr(annot_id)) |did| {
            result.ctx.enum_decl = did;
        }
        if (annot_kind == .ErrorSetType) {
            const est = self.ast_unit.exprs.get(.ErrorSetType, annot_id);
            if (self.variantDeclByExpr(est.err)) |edid| result.ctx.error_decl = edid;
        }
        return result;
    }

    fn finalizeDeclType(
        self: *CheckerV3,
        did: ast.DeclId,
        d: ast.Rows.Decl,
        rhs_ty: ?types.TypeId,
        expect_ty: ?types.TypeId,
    ) !void {
        if (expect_ty) |et| {
            const ekind = self.type_info.store.index.kinds.items[et.toRaw()];
            if (ekind == .TypeType) {
                // RHS must be a type expression; resolve it and store TypeType(of)
                const resolved = try self.typeFromTypeExpr(d.value);
                if (resolved == null) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .type_value_mismatch, .{});
                    return;
                }
                const tt = self.type_info.store.mkTypeType(resolved.?);
                self.type_info.decl_types.items[did.toRaw()] = tt;
                return;
            }
            if (rhs_ty) |rt| {
                // Immediate pointer constness downcast check: *const T -> *T
                const k_rt0 = self.type_info.store.index.kinds.items[rt.toRaw()];
                const k_et0 = self.type_info.store.index.kinds.items[et.toRaw()];
                if (k_rt0 == .Ptr and k_et0 == .Ptr) {
                    const pr = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[rt.toRaw()]);
                    const pe = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[et.toRaw()]);
                    if (pr.is_const and !pe.is_const) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .pointer_constness_violation, .{});
                        return;
                    }
                }
                var ok = self.assignable(rt, et, true);
                if (!ok) {
                    if (self.isOptional(et)) |inner| {
                        ok = self.assignable(rt, inner, true) or rt.toRaw() == inner.toRaw();
                    }
                }
                if (!ok) {
                    const gk = self.type_info.store.index.kinds.items[rt.toRaw()];
                    const ek = self.type_info.store.index.kinds.items[et.toRaw()];
                    if (gk == .Ptr and ek == .Ptr) {
                        const gr = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[rt.toRaw()]);
                        const er = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[et.toRaw()]);
                        if (gr.is_const and !er.is_const) {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .pointer_constness_violation, .{});
                        } else {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .type_annotation_mismatch, .{});
                        }
                    } else {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .type_annotation_mismatch, .{});
                    }
                } else self.type_info.decl_types.items[did.toRaw()] = et;
            } else {
                self.type_info.decl_types.items[did.toRaw()] = et;
            }
        } else if (rhs_ty) |rt| {
            self.type_info.decl_types.items[did.toRaw()] = rt;
        }
    }

    fn pushFunc(self: *CheckerV3, has_result: bool) !void {
        try self.func_stack.append(self.gpa, .{ .has_result = has_result });
    }
    fn popFunc(self: *CheckerV3) void {
        if (self.func_stack.items.len > 0) _ = self.func_stack.pop();
    }
    fn inFunction(self: *const CheckerV3) bool {
        return self.func_stack.items.len > 0;
    }
    fn currentFunc(self: *const CheckerV3) ?FunctionCtx {
        if (self.func_stack.items.len == 0) return null;
        return self.func_stack.items[self.func_stack.items.len - 1];
    }

    fn pushLoop(self: *CheckerV3, label: ast.OptStrId) !void {
        try self.loop_stack.append(self.gpa, .{ .label = label });
    }
    fn popLoop(self: *CheckerV3) void {
        if (self.loop_stack.items.len > 0) _ = self.loop_stack.pop();
    }
    fn inLoop(self: *const CheckerV3) bool {
        return self.loop_stack.items.len > 0;
    }

    fn lookup(self: *CheckerV3, name: ast.StrId) ?symbols.SymbolId {
        return self.symtab.lookup(self.ast_unit, self.symtab.currentId(), name);
    }

    // no forward-decl scan; rely on scoped lookup only

    fn primaryNameOfPattern(self: *CheckerV3, pid: ast.PatternId) ast.OptStrId {
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
    fn isNumericKind(_: *const CheckerV3, k: types.TypeKind) bool {
        return switch (k) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize, .Tensor, .Simd, .Complex => true,
            else => false,
        };
    }
    fn isIntegerKind(_: *const CheckerV3, k: types.TypeKind) bool {
        return switch (k) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
            else => false,
        };
    }

    fn isOptional(self: *CheckerV3, id: types.TypeId) ?types.TypeId {
        const k = self.type_info.store.index.kinds.items[id.toRaw()];
        if (k != .Optional) return null;
        const opt = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[id.toRaw()]);
        return opt.elem;
    }

    fn assignable(self: *CheckerV3, got: types.TypeId, expect: types.TypeId) bool {
        if (got.toRaw() == expect.toRaw()) return true;
        const got_kind = self.type_info.store.index.kinds.items[got.toRaw()];
        const expected_kind = self.type_info.store.index.kinds.items[expect.toRaw()];
        if (expected_kind == .Any or got_kind == .Any) return true;

        switch (expected_kind) {
            .Array => {
                if (got_kind != .Array) return false;
                const expected_ty = self.type_info.store.Array.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Array.get(self.type_info.store.index.rows.items[got.toRaw()]);
                const elem_ok = self.assignable(got_ty.elem, expected_ty.elem);
                const size_ok = expected_ty.len == got_ty.len;
                return elem_ok and size_ok;
            },
            .DynArray => {
                if (got_kind != .Array) return false;
                const expected_ty = self.type_info.store.DynArray.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Array.get(self.type_info.store.index.rows.items[got.toRaw()]);
                return self.assignable(got_ty.elem, expected_ty.elem);
            },
            .Tuple => {
                if (got_kind != .Tuple) return false;
                const expected_ty = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[got.toRaw()]);
                if (expected_ty.elems.len != got_ty.elems.len) return false;
                const got_elems = self.type_info.store.type_pool.slice(got_ty.elems);
                const expected_elems = self.type_info.store.type_pool.slice(expected_ty.elems);
                for (expected_elems, 0..) |et, i| {
                    const gt = got_elems[i];
                    if (!self.assignable(gt, et)) return false;
                }
                return true;
            },
            .Map => {
                if (got_kind == .Array) {
                    const got_ty = self.type_info.store.Array.get(self.type_info.store.index.rows.items[got.toRaw()]);
                    if (got_ty.len != 0) return false;
                    return true; // empty array can be assigned to any map type
                }
                // Could be a degenerate case, single key value pair that looks like a map type
                if (got_kind == .TypeType) {}
                if (got_kind != .Map) return false;
                const expected_ty = self.type_info.store.Map.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                const got_ty = self.type_info.store.Map.get(self.type_info.store.index.rows.items[got.toRaw()]);
                const key_ok = self.assignable(got_ty.key, expected_ty.key);
                const value_ok = self.assignable(got_ty.value, expected_ty.value);
                return key_ok and value_ok;
            },
            .Optional => {
                const expected_ty = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[expect.toRaw()]);
                if (got_kind == .Optional) {
                    const got_ty = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[got.toRaw()]);
                    return self.assignable(got_ty.elem, expected_ty.elem);
                }
                return self.assignable(got, expected_ty.elem);
            },
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => {
                if (!self.isIntegerKind(got_kind)) return false;
                return true;
            },
            .F32, .F64 => {
                if (got_kind != .F32 and got_kind != .F64) return false;
                return true;
            },
            else => {},
        }

        // if (got_kind == .Ptr and expected_kind == .Ptr) {
        //     const gr = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[got.toRaw()]);
        //     const er = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[expect.toRaw()]);
        //     const const_ok = (er.is_const or (!er.is_const and !gr.is_const));
        //     return const_ok and self.assignable(gr.elem, er.elem);
        // }
        // // Error-union assignability:
        // if (expected_kind == .ErrorSet) {
        //     const er = self.type_info.store.ErrorSet.get(self.type_info.store.index.rows.items[expect.toRaw()]);
        //     // assigning error value to error-union
        //     if (got_kind == .ErrorSet) {
        //         const gr = self.type_info.store.ErrorSet.get(self.type_info.store.index.rows.items[got.toRaw()]);
        //         if (gr.payload == null) return true;
        //         // both are error-union types; require identical
        //         return got.toRaw() == expect.toRaw();
        //     }
        //     // assigning underlying value to error-union
        //     if (er.payload) |pv| {
        //         if (got.toRaw() == pv.toRaw()) return true;
        //     }
        // }
        return false;
    }

    // =========================================================
    // Declarations & Statements
    // =========================================================
    fn checkDecl(self: *CheckerV3, decl_id: ast.DeclId) !void {
        const decl = self.ast_unit.exprs.Decl.get(decl_id.toRaw());
        if (decl.pattern.isNone()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(decl.loc), .unexpected_token, .{});
            return;
        }
        try self.bindDeclPattern(decl_id, decl);
        const expect_ty = if (decl.ty.isNone())
            null
        else
            try self.typeFromTypeExpr(decl.ty.unwrap());
        const rhs_ty = try self.checkExpr(decl.value, expectNone());
        if (rhs_ty == null)
            return;
        try self.tryTypeCoercion(decl_id, rhs_ty.?, expect_ty);
    }

    fn tryTypeCoercion(
        self: *CheckerV2,
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
        } else if (!self.assignable(rhs_ty, expect_ty.?)) {
            const d = self.ast_unit.exprs.Decl.get(decl.toRaw());
            try self.diags.addError(self.ast_unit.exprs.locs.get(d.loc), .type_annotation_mismatch, .{});
        } else {
            self.type_info.decl_types.items[decl.toRaw()] = expect_ty.?;
            self.type_info.expr_types.items[self.ast_unit.exprs.Decl.get(decl.toRaw()).value.toRaw()] = expect_ty.?; // also update RHS expr type
        }
    }

    fn checkStmt(self: *CheckerV3, sid: ast.StmtId) !void {
        switch (self.ast_unit.stmts.index.kinds.items[sid.toRaw()]) {
            .Expr => {
                const row = self.ast_unit.stmts.get(.Expr, sid);
                _ = try self.checkExpr(row.expr, expectNone());
            },
            .Decl => {
                const row = self.ast_unit.stmts.get(.Decl, sid);
                try self.checkDecl(row.decl);
            },
            .Assign => {
                const row = self.ast_unit.stmts.get(.Assign, sid);
                const lt = try self.checkExpr(row.left, expectNone());
                const rt = try self.checkExpr(row.right, if (lt) |lt_ty| expectTy(lt_ty) else expectNone());
                if (lt != null and rt != null and !self.assignable(rt.?, lt.?)) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .type_annotation_mismatch, .{});
                }
            },
            .Insert => {
                const row = self.ast_unit.stmts.get(.Insert, sid);
                if (!self.warned_meta) {
                    _ = self.diags.addNote(self.ast_unit.exprs.locs.get(row.loc), .checker_insert_not_expanded, .{}) catch {};
                    self.warned_meta = true;
                }
                _ = try self.checkExpr(row.expr, expectNone());
            },
            .Return => {
                const row = self.ast_unit.stmts.get(.Return, sid);
                if (!self.inFunction()) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .return_outside_function, .{});
                } else {
                    const f = self.currentFunc().?;
                    if (!f.has_result and !row.value.isNone())
                        try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .return_value_in_void_function, .{});
                    if (f.has_result and row.value.isNone())
                        try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .missing_return_value, .{});
                    if (!row.value.isNone()) _ = try self.checkExpr(row.value.unwrap(), expectNone());
                }
            },
            .Break => {
                const row = self.ast_unit.stmts.get(.Break, sid);
                if (!self.inLoop()) try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .break_outside_loop, .{});
                if (!row.value.isNone()) _ = try self.checkExpr(row.value.unwrap(), expectNone());
            },
            .Continue => {
                const row = self.ast_unit.stmts.get(.Continue, sid);
                if (!self.inLoop()) try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .continue_outside_loop, .{});
            },
            .Unreachable => {},
            .Defer => {
                const row = self.ast_unit.stmts.get(.Defer, sid);
                if (!self.inFunction()) try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .defer_outside_function, .{});
                _ = try self.checkExpr(row.expr, expectNone());
            },
            .ErrDefer => {
                const row = self.ast_unit.stmts.get(.ErrDefer, sid);
                if (!self.inFunction()) try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .errdefer_outside_function, .{});
                _ = try self.checkExpr(row.expr, expectNone());
            },
        }
    }

    // =========================================================
    // Expressions
    // =========================================================
    fn checkExpr(self: *CheckerV3, id: ast.ExprId, expect: Expectation) anyerror!?types.TypeId {
        if (self.type_info.expr_types.items[id.toRaw()]) |cached| return cached;
        const k = self.ast_unit.exprs.index.kinds.items[id.toRaw()];
        var tid: ?types.TypeId = null;

        switch (k) {
            .Literal => tid = self.checkLiteral(id),
            .Ident => tid = self.checkIdent(id),
            .Binary => tid = try self.checkBinary(id),
            .Unary => tid = try self.checkUnary(id),
            .FunctionLit => tid = try self.checkFunctionLit(id),
            .ArrayLit => tid = try self.checkArrayLit(id),
            .TupleLit => tid = try self.checkTupleLit(id),
            .MapLit => tid = try self.checkMapLit(id),
            .IndexAccess => tid = self.checkIndexAccess(id),
            .FieldAccess => tid = self.checkFieldAccess(id, expect),
            .StructLit => tid = try self.checkStructLit(id, expect),
            .Range => tid = try self.checkRange(id),

            // still default to any for the following kinds (can be implemented later)
            .Deref => tid = try self.checkDeref(id),
            .VariantLit => tid = try self.checkVariantLit(id),
            .EnumLit => tid = try self.checkEnumLit(id, expect),
            .Call => tid = try self.checkCall(id, expect),
            .ComptimeBlock => tid = try self.checkComptimeBlock(id),
            .CodeBlock => tid = try self.checkCodeBlock(id, expect),
            .AsyncBlock => tid = try self.checkAsyncBlock(id),
            .MlirBlock => tid = try self.checkMlirBlock(id),
            .Insert => tid = try self.checkInsert(id),
            .Return => tid = try self.checkReturn(id),
            .If => tid = try self.checkIf(id),
            .While => tid = try self.checkWhile(id),
            .For => tid = try self.checkFor(id),
            .Match => tid = try self.checkMatch(id),
            .Break => tid = try self.checkBreak(id),
            .Continue => tid = try self.checkContinue(id),
            .Unreachable => tid = try self.checkUnreachable(id),
            .UndefLit => tid = self.type_info.store.tAny(),

            .Block => tid = try self.checkBlock(id, expect),
            .Defer => tid = try self.checkDefer(id),
            .ErrDefer => tid = try self.checkErrDefer(id),
            .ErrUnwrap => tid = try self.checkErrUnwrap(id),
            .OptionalUnwrap => tid = try self.checkOptionalUnwrap(id),
            .Await => tid = try self.checkAwait(id),
            .Closure => tid = try self.checkClosure(id, expect),
            .Cast => tid = try self.checkCast(id),
            .Catch => tid = try self.checkCatch(id),
            .Import => tid = try self.checkImport(id),
            .TypeOf => tid = try self.checkTypeOf(id),
            .NullLit => tid = self.type_info.store.mkOptional(self.type_info.store.tAny()),

            .TupleType, .ArrayType, .DynArrayType, .MapType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => {
                var array_size_invalid = false;
                const resolved = self.typeFromTypeExpr(id) catch |err| switch (err) {
                    error.InvalidArraySize => blk: {
                        array_size_invalid = true;
                        break :blk null;
                    },
                    else => return err,
                };
                if (array_size_invalid) {
                    if (k == .ArrayType) {
                        const row = self.ast_unit.exprs.get(.ArrayType, id);
                        try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .array_size_not_integer_literal, .{});
                    }
                    return null;
                }
                tid = resolved orelse self.type_info.store.tAny();
            },
        }

        // if (expect.map) |exp| {
        //     switch (k) {
        //         .MapLit => {},
        //         .ArrayLit => {
        //             const arr = self.ast_unit.exprs.get(.ArrayLit, id);
        //             if (self.ast_unit.exprs.expr_pool.slice(arr.elems).len != 0) {
        //                 try self.diags.addError(exp.loc, .type_annotation_mismatch, .{});
        //                 return null;
        //             }
        //         },
        //         .NullLit => {},
        //         else => {
        //             try self.diags.addError(exp.loc, .type_annotation_mismatch, .{});
        //             return null;
        //         },
        //     }
        // }

        if (tid) |t| self.type_info.expr_types.items[id.toRaw()] = t;
        return tid;
    }

    fn checkLiteral(self: *CheckerV3, id: ast.ExprId) ?types.TypeId {
        const lit = self.ast_unit.exprs.get(.Literal, id);
        return switch (lit.kind) {
            .int => self.type_info.store.tI64(),
            .float => self.type_info.store.tF64(),
            .bool => self.type_info.store.tBool(),
            .string => self.type_info.store.tString(),
            .char => self.type_info.store.tU32(),
        };
    }
    fn checkIdent(self: *CheckerV3, id: ast.ExprId) ?types.TypeId {
        const row = self.ast_unit.exprs.get(.Ident, id);
        if (self.lookup(row.name)) |sid| {
            const srow = self.symtab.syms.get(sid.toRaw());
            if (!srow.origin_decl.isNone()) if (self.type_info.decl_types.items[srow.origin_decl.unwrap().toRaw()]) |dt| return dt;
        }
        return null;
    }

    fn checkDeref(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const row = self.ast_unit.exprs.get(.Deref, id);
        const ptr_ty_opt = try self.checkExpr(row.expr, expectNone());
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

    fn checkBlock(self: *CheckerV3, id: ast.ExprId, expect: Expectation) !?types.TypeId {
        _ = expect;
        const br = self.ast_unit.exprs.get(.Block, id);
        const stmts = self.ast_unit.stmts.stmt_pool.slice(br.items);
        var i: usize = 0;
        while (i < stmts.len) : (i += 1) {
            try self.checkStmt(stmts[i]);
        }
        // Block statements currently yield void
        return self.type_info.store.tVoid();
    }

    fn checkBinary(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const bin: ast.Rows.Binary = self.ast_unit.exprs.get(.Binary, id);
        const lt = try self.checkExpr(bin.left, expectNone());
        const rt = try self.checkExpr(bin.right, expectNone());
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
                if (l.toRaw() == r.toRaw())
                    return self.type_info.store.tBool();
                try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                return null;
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
                    if (elem.toRaw() == r.toRaw()) return rt;
                    try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_binary_op_operands, .{});
                    return null;
                }
                try self.diags.addError(self.ast_unit.exprs.locs.get(bin.loc), .invalid_use_of_orelse_on_non_optional, .{});
                return null;
            },
        }
        return null;
    }

    fn checkUnary(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const unary_expr = self.ast_unit.exprs.get(.Unary, id);
        const expr_ty = try self.checkExpr(unary_expr.expr, expectNone());
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

    fn checkFunctionLit(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const fnr = self.ast_unit.exprs.get(.FunctionLit, id);
        const params = self.ast_unit.exprs.param_pool.slice(fnr.params);
        var pbuf = try self.gpa.alloc(types.TypeId, params.len);
        defer self.gpa.free(pbuf);
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = self.ast_unit.exprs.Param.get(params[i].toRaw());
            if (!p.ty.isNone()) {
                const pt = (try self.typeFromTypeExpr(p.ty.unwrap())) orelse return null;
                pbuf[i] = pt;
            } else {
                pbuf[i] = self.type_info.store.tAny();
            }
        }
        const res = if (!fnr.result_ty.isNone()) (try self.typeFromTypeExpr(fnr.result_ty.unwrap())) else self.type_info.store.tVoid();
        if (res == null) return null;
        return self.type_info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic);
    }

    fn checkTupleLit(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const tuple_lit = self.ast_unit.exprs.get(.TupleLit, id);
        const elems = self.ast_unit.exprs.expr_pool.slice(tuple_lit.elems);

        var tbuf = try self.gpa.alloc(types.TypeId, elems.len);
        defer self.gpa.free(tbuf);
        var i: usize = 0;
        while (i < elems.len) : (i += 1) {
            const ety = try self.checkExpr(elems[i], expectNone());
            if (ety == null) return null;
            tbuf[i] = ety.?;
        }
        return self.type_info.store.mkTuple(tbuf);
    }

    fn checkArrayLit(
        self: *CheckerV3,
        id: ast.ExprId,
    ) !?types.TypeId {
        const array_lit = self.ast_unit.exprs.get(.ArrayLit, id);
        const elems = self.ast_unit.exprs.expr_pool.slice(array_lit.elems);

        // infer from first element, homogeneous requirement
        if (elems.len == 0) {
            return self.type_info.store.mkArray(self.type_info.store.tAny(), 0);
        }
        const first_ty = (try self.checkExpr(elems[0], expectNone())) orelse return null;
        var i: usize = 1;
        while (i < elems.len) : (i += 1) {
            const ety = try self.checkExpr(elems[i], expectTySuppressNull(first_ty));
            if (ety == null or ety.?.toRaw() != first_ty.toRaw()) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(array_lit.loc), .heterogeneous_array_elements, .{});
                return null;
            }
        }
        return self.type_info.store.mkArray(first_ty, elems.len);
    }

    fn checkMapLit(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const row = self.ast_unit.exprs.get(.MapLit, id);
        const kvs = self.ast_unit.exprs.kv_pool.slice(row.entries);

        if (kvs.len == 0) {
            return self.type_info.store.mkMap(self.type_info.store.tAny(), self.type_info.store.tAny());
        }
        const first = self.ast_unit.exprs.KeyValue.get(kvs[0].toRaw());
        const key_ty = try self.checkExpr(first.key, expectNone());
        const val_ty = try self.checkExpr(first.value, expectNone());
        if (key_ty == null or val_ty == null) return null;

        var i: usize = 1;
        while (i < kvs.len) : (i += 1) {
            const kv = self.ast_unit.exprs.KeyValue.get(kvs[i].toRaw());
            const kt = try self.checkExpr(kv.key, expectNone());
            const vt = try self.checkExpr(kv.value, expectNone());
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

    fn checkIndexAccess(self: *CheckerV3, id: ast.ExprId) ?types.TypeId {
        const index_expr = self.ast_unit.exprs.get(.IndexAccess, id);
        const col_ty = self.checkExpr(index_expr.collection, expectNone()) catch
            return null;

        const col_kind = self.type_info.store.index.kinds.items[col_ty.?.toRaw()];
        switch (col_kind) {
            .Array => {
                const idx_kind = self.ast_unit.exprs.index.kinds.items[index_expr.index.toRaw()];
                if (idx_kind == .Range) {
                    _ = self.checkExpr(index_expr.index, expectNone()) catch return null;
                    const r = self.type_info.store.Array.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
                    return self.type_info.store.mkSlice(r.elem);
                }

                const it = self.checkExpr(index_expr.index, expectNone()) catch return null;
                if (it) |iid| {
                    if (!self.isIntegerKind(self.type_info.store.index.kinds.items[iid.toRaw()])) {
                        _ = self.diags.addError(self.ast_unit.exprs.locs.get(index_expr.loc), .non_integer_index, .{}) catch {};
                        return null;
                    }
                }
                const r = self.type_info.store.Array.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
                return r.elem;
            },
            .Map => {
                const m = self.type_info.store.Map.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
                const it = self.checkExpr(index_expr.index, expectNone()) catch return null;
                if (it) |iid| {
                    if (iid.toRaw() != m.key.toRaw()) {
                        _ = self.diags.addError(self.ast_unit.exprs.locs.get(index_expr.loc), .map_wrong_key_type, .{}) catch {};
                        return null;
                    }
                }
                return m.value;
            },
            // .Slice => {
            //     const idx_kind = self.ast_unit.exprs.index.kinds.items[index_expr.index.toRaw()];
            //     if (idx_kind == .Range) {
            //         _ = self.checkExpr(index_expr.index, expectNone()) catch return null;
            //         const r = self.type_info.store.Slice.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
            //         return self.type_info.store.mkSlice(r.elem);
            //     }
            //
            //     const it = self.checkExpr(index_expr.index, expectNone()) catch return null;
            //     if (it) |iid| {
            //         if (!self.isIntegerKind(self.type_info.store.index.kinds.items[iid.toRaw()])) {
            //             _ = self.diags.addError(self.ast_unit.exprs.locs.get(index_expr.loc), .non_integer_index, .{}) catch {};
            //             return null;
            //         }
            //     }
            //     const r = self.type_info.store.Slice.get(self.type_info.store.index.rows.items[col_ty.?.toRaw()]);
            //     return r.elem;
            // },
            .String => {
                const it = self.checkExpr(index_expr.index, expectNone()) catch return null;
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

    fn checkFieldAccess(self: *CheckerV3, id: ast.ExprId, expect: Expectation) ?types.TypeId {
        const fr = self.ast_unit.exprs.get(.FieldAccess, id);
        const enum_decl_opt = if (!fr.is_tuple) self.enumDeclByExpr(fr.parent) else null;
        const variant_decl_opt = if (!fr.is_tuple) self.variantDeclByExpr(fr.parent) else null;
        const pt = self.checkExpr(fr.parent, expectNone()) catch return null;
        if (pt == null) {
            // Try struct typed literal context
            if (!fr.is_tuple and self.ast_unit.exprs.index.kinds.items[fr.parent.toRaw()] == .StructLit) {
                return self.structFieldTypeFromLiteralContext(fr);
            }
            if (enum_decl_opt) |did| {
                return self.handleEnumFieldAccess(fr, expect, did);
            }
            if (variant_decl_opt) |vdid| {
                // Accessing a variant tag without constructor: only ok for no-payload cases
                const decl = self.ast_unit.exprs.Decl.get(vdid.toRaw());
                const is_error = (self.ast_unit.exprs.index.kinds.items[decl.value.toRaw()] == .ErrorType);
                const vt = if (!is_error) self.ast_unit.exprs.get(.VariantType, decl.value) else self.ast_unit.exprs.get(.ErrorType, decl.value);
                const fields = self.ast_unit.exprs.vfield_pool.slice(vt.fields);
                var i: usize = 0;
                while (i < fields.len) : (i += 1) {
                    const vf = self.ast_unit.exprs.VariantField.get(fields[i].toRaw());
                    if (std.mem.eql(u8, self.ast_unit.exprs.strs.get(vf.name), self.ast_unit.exprs.strs.get(fr.field))) {
                        if (is_error) {
                            if (expect.error_decl) |ed| {
                                if (ed.toRaw() != vdid.toRaw()) {
                                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_error_tag, .{}) catch {};
                                    return null;
                                }
                            }
                        }
                        switch (vf.payload_kind) {
                            .none => return self.type_info.store.mkErrorSet(null),
                            .tuple, .@"struct" => {
                                _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .variant_payload_arity_mismatch, .{}) catch {};
                                return null;
                            },
                        }
                    }
                }
                if (is_error) {
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_error_tag, .{}) catch {};
                } else {
                    _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_enum_tag, .{}) catch {};
                }
                return null;
            }
            return null;
        }
        var t = pt.?;
        if (self.type_info.store.index.kinds.items[t.toRaw()] == .Ptr)
            t = self.type_info.store.Ptr.get(self.type_info.store.index.rows.items[t.toRaw()]).elem;

        if (enum_decl_opt != null and t.toRaw() == self.type_info.store.tAny().toRaw()) {
            return self.handleEnumFieldAccess(fr, expect, enum_decl_opt.?);
        }
        if (variant_decl_opt != null and t.toRaw() == self.type_info.store.tAny().toRaw()) {
            // Same as above: plain tag access on variant context
            const vdid = variant_decl_opt.?;
            const decl = self.ast_unit.exprs.Decl.get(vdid.toRaw());
            const is_error = (self.ast_unit.exprs.index.kinds.items[decl.value.toRaw()] == .ErrorType);
            const vt = if (!is_error) self.ast_unit.exprs.get(.VariantType, decl.value) else self.ast_unit.exprs.get(.ErrorType, decl.value);
            const fields = self.ast_unit.exprs.vfield_pool.slice(vt.fields);
            var i: usize = 0;
            while (i < fields.len) : (i += 1) {
                const vf = self.ast_unit.exprs.VariantField.get(fields[i].toRaw());
                if (std.mem.eql(u8, self.ast_unit.exprs.strs.get(vf.name), self.ast_unit.exprs.strs.get(fr.field))) {
                    if (is_error) {
                        if (expect.error_decl) |ed| {
                            if (ed.toRaw() != vdid.toRaw()) {
                                _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_error_tag, .{}) catch {};
                                return null;
                            }
                        }
                    }
                    switch (vf.payload_kind) {
                        .none => return self.type_info.store.mkErrorSet(null),
                        .tuple, .@"struct" => {
                            _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .variant_payload_arity_mismatch, .{}) catch {};
                            return null;
                        },
                    }
                }
            }
            if (is_error) {
                _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_error_tag, .{}) catch {};
            } else {
                _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_enum_tag, .{}) catch {};
            }
            return null;
        }

        if (self.type_info.store.index.kinds.items[t.toRaw()] == .Tuple) {
            if (fr.is_tuple) {
                const rowt = self.type_info.store.Tuple.get(self.type_info.store.index.rows.items[t.toRaw()]);
                const idx = std.fmt.parseInt(usize, self.ast_unit.exprs.strs.get(fr.field), 10) catch return null;
                const ids = self.type_info.store.type_pool.slice(rowt.elems);
                if (idx < ids.len) return ids[idx];
                _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .tuple_index_out_of_bounds, .{}) catch {};
                return null;
            } else {
                _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .expected_field_name_or_index, .{}) catch {};
                return null;
            }
        }
        if (self.type_info.store.index.kinds.items[t.toRaw()] == .Struct) {
            const rowt = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[t.toRaw()]);
            const fids = self.type_info.store.field_pool.slice(rowt.fields);
            var i: usize = 0;
            while (i < fids.len) : (i += 1) {
                const f = self.type_info.store.Field.get(fids[i].toRaw());
                if (std.mem.eql(u8, self.type_info.store.strs.get(f.name), self.ast_unit.exprs.strs.get(fr.field))) {
                    return f.ty;
                }
            }
            _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{}) catch {};
            return null;
        }
        return null;
    }

    fn checkRange(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const rr = self.ast_unit.exprs.get(.Range, id);
        if (!rr.start.isNone()) {
            const st = try self.checkExpr(rr.start.unwrap(), expectNone());
            if (st == null or !self.isIntegerKind(self.type_info.store.index.kinds.items[st.?.toRaw()])) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(rr.loc), .non_integer_index, .{});
                return null;
            }
        }
        if (!rr.end.isNone()) {
            const et = try self.checkExpr(rr.end.unwrap(), expectNone());
            if (et == null or !self.isIntegerKind(self.type_info.store.index.kinds.items[et.?.toRaw()])) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(rr.loc), .non_integer_index, .{});
                return null;
            }
        }
        return self.type_info.store.mkSlice(self.type_info.store.tUsize());
    }

    fn checkVariantLit(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const vl = self.ast_unit.exprs.get(.VariantLit, id);
        if (vl.value.isNone()) return self.type_info.store.tAny();
        const pt = try self.checkExpr(vl.value.unwrap(), expectNone());
        if (pt == null) return null;
        return self.type_info.store.mkVariant(pt.?);
    }

    fn checkEnumLit(self: *CheckerV3, id: ast.ExprId, expect: Expectation) !?types.TypeId {
        // In the current lowering, enum tags appear as FieldAccess, not EnumLit.
        // Accept and yield 'any' here to compile; real enum typing happens via FieldAccess.
        _ = expect;
        _ = id;
        return self.type_info.store.tAny();
    }

    fn checkCall(self: *CheckerV3, id: ast.ExprId, expect: Expectation) !?types.TypeId {
        _ = expect;
        const cr = self.ast_unit.exprs.get(.Call, id);
        const callee_kind = self.ast_unit.exprs.index.kinds.items[cr.callee.toRaw()];
        if (callee_kind == .FieldAccess) {
            const fr = self.ast_unit.exprs.get(.FieldAccess, cr.callee);
            if (self.variantDeclByExpr(fr.parent)) |_| {
                const args = self.ast_unit.exprs.expr_pool.slice(cr.args);
                return try self.handleVariantCtorCall(fr, args);
            }
        }
        const ft = try self.checkExpr(cr.callee, expectNone());
        if (ft == null) {
            // If the callee is an unresolved identifier in the current scope, report unknown_function.
            if (self.ast_unit.exprs.index.kinds.items[cr.callee.toRaw()] == .Ident) {
                const idr = self.ast_unit.exprs.get(.Ident, cr.callee);
                if (self.lookup(idr.name) == null) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .unknown_function, .{});
                }
            }
            return null;
        }
        const f = ft.?;
        const fk = self.type_info.store.index.kinds.items[f.toRaw()];
        if (fk != .Function) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .call_non_callable, .{});
            return null;
        }
        const fr = self.type_info.store.Function.get(self.type_info.store.index.rows.items[f.toRaw()]);
        const param_ids = self.type_info.store.type_pool.slice(fr.params);
        const args = self.ast_unit.exprs.expr_pool.slice(cr.args);
        if (!fr.is_variadic) {
            if (args.len != param_ids.len) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .argument_count_mismatch, .{});
                return null;
            }
        } else {
            // Variadic: last formal is a sentinel (e.g., 'any'), and may be omitted.
            const min_required = if (param_ids.len == 0) 0 else param_ids.len - 1;
            if (args.len < min_required) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .argument_count_mismatch, .{});
                return null;
            }
        }
        var i: usize = 0;
        while (i < args.len) : (i += 1) {
            const at = try self.checkExpr(args[i], expectNone());
            if (at == null) return null;
            const atid = at.?;
            const ptid = if (!fr.is_variadic)
                (if (i < param_ids.len) param_ids[i] else param_ids[param_ids.len - 1])
            else blk: {
                // For variadic, fixed params are all but the last; everything after uses the last formal's type.
                const fixed = if (param_ids.len == 0) 0 else param_ids.len - 1;
                break :blk if (i < fixed) param_ids[i] else param_ids[param_ids.len - 1];
            };
            // Special-case: passing 'null' to a non-optional pointer parameter
            if (self.ast_unit.exprs.index.kinds.items[args[i].toRaw()] == .NullLit) {
                const pk = self.type_info.store.index.kinds.items[ptid.toRaw()];
                if (pk == .Ptr) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .null_to_non_optional_param, .{});
                    return null;
                }
                if (pk == .Optional) {
                    const pr = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[ptid.toRaw()]);
                    const inner_k = self.type_info.store.index.kinds.items[pr.elem.toRaw()];
                    if (inner_k == .Ptr) {
                        // ok: null allowed for optional pointer
                        continue;
                    }
                }
            }
            if (!self.assignable(atid, ptid)) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .argument_type_mismatch, .{});
                return null;
            }
        }
        return fr.result;
    }

    fn checkCodeBlock(self: *CheckerV3, id: ast.ExprId, expect: Expectation) !?types.TypeId {
        const cb = self.ast_unit.exprs.get(.CodeBlock, id);
        if (!self.warned_code) {
            _ = self.diags.addNote(self.ast_unit.exprs.locs.get(cb.loc), .checker_code_block_not_executed, .{}) catch {};
            self.warned_code = true;
        }
        return try self.checkExpr(cb.block, expect);
    }

    fn checkComptimeBlock(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const cb = self.ast_unit.exprs.get(.ComptimeBlock, id);
        if (!self.warned_comptime) {
            _ = self.diags.addNote(self.ast_unit.exprs.locs.get(cb.loc), .checker_comptime_not_executed, .{}) catch {};
            self.warned_comptime = true;
        }
        const t = try self.checkExpr(cb.block, expectNone());
        if (t == null) return null;
        return t;
    }

    fn checkAsyncBlock(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Treat async blocks as opaque for typing
        return self.type_info.store.tAny();
    }

    fn checkMlirBlock(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Treat mlir blocks as opaque for typing
        return self.type_info.store.tAny();
    }

    fn checkInsert(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const r = self.ast_unit.exprs.get(.Insert, id);
        _ = try self.checkExpr(r.expr, expectNone());
        return self.type_info.store.tAny();
    }

    fn checkReturn(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const rr = self.ast_unit.exprs.get(.Return, id);
        if (rr.value.isNone()) return self.type_info.store.tVoid();
        const et = try self.checkExpr(rr.value.unwrap(), expectNone());
        return et;
    }

    fn checkIf(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const ir = self.ast_unit.exprs.get(.If, id);
        const cond = try self.checkExpr(ir.cond, expectNone());
        if (cond == null or cond.?.toRaw() != self.type_info.store.tBool().toRaw()) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(ir.loc), .non_boolean_condition, .{});
            return null;
        }
        const then_ty = try self.checkExpr(ir.then_block, expectNone());
        if (then_ty == null) return null;
        var else_ty: ?types.TypeId = null;
        if (!ir.else_block.isNone()) {
            else_ty = try self.checkExpr(ir.else_block.unwrap(), expectNone());
            if (else_ty == null) return null;
        }
        if (else_ty == null) return then_ty;
        if (then_ty.?.toRaw() == else_ty.?.toRaw()) return then_ty;
        return self.type_info.store.tAny();
    }

    fn checkWhile(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const wr = self.ast_unit.exprs.get(.While, id);
        if (!wr.cond.isNone()) {
            const cond = try self.checkExpr(wr.cond.unwrap(), expectNone());
            if (cond == null or cond.?.toRaw() != self.type_info.store.tBool().toRaw()) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(wr.loc), .non_boolean_condition, .{});
                return null;
            }
        }
        const bt = try self.checkExpr(wr.body, expectNone());
        if (bt == null) return null;
        return self.type_info.store.tVoid();
    }

    fn checkMatch(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const mr = self.ast_unit.exprs.get(.Match, id);
        const mt = try self.checkExpr(mr.expr, expectNone());
        if (mt == null) return null;
        var result_ty: ?types.TypeId = null;
        const arms = self.ast_unit.exprs.arm_pool.slice(mr.arms);
        var i: usize = 0;
        while (i < arms.len) : (i += 1) {
            const arm = self.ast_unit.exprs.MatchArm.get(arms[i].toRaw());
            if (!self.checkPattern(arm.pattern, mt.?, false)) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(arm.loc), .pattern_shape_mismatch, .{});
                return null;
            }
            const at = try self.checkExpr(arm.body, expectNone());
            if (at == null) return null;
            if (result_ty == null) result_ty = at else if (result_ty.?.toRaw() != at.?.toRaw()) {
                result_ty = self.type_info.store.tAny();
            }
            i += 1;
        }
        if (result_ty == null) return self.type_info.store.tVoid();
        return result_ty;
    }

    fn checkUnreachable(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.type_info.store.tAny();
    }

    fn checkFor(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const fr = self.ast_unit.exprs.get(.For, id);
        const it = try self.checkExpr(fr.iterable, expectNone());
        if (it == null) return null;
        const k = self.type_info.store.index.kinds.items[it.?.toRaw()];
        switch (k) {
            .Array, .Slice, .String => {},
            else => {
                try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .non_iterable_in_for, .{});
                return null;
            },
        }
        // Body must type-check
        _ = try self.checkExpr(fr.body, expectNone());
        return self.type_info.store.tVoid();
    }

    fn checkPattern(self: *CheckerV3, pid: ast.PatternId, value_ty: types.TypeId, top_level: bool) bool {
        _ = self;
        _ = pid;
        _ = value_ty;
        _ = top_level;
        // TODO: implement proper pattern checking
        return true;
    }

    fn castable(self: *CheckerV3, got: types.TypeId, expect: types.TypeId) bool {
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

    fn checkBreak(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.type_info.store.tVoid();
    }

    fn checkContinue(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.type_info.store.tVoid();
    }

    fn checkDefer(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const dr = self.ast_unit.exprs.get(.Defer, id);
        const dt = try self.checkExpr(dr.expr, expectNone());
        if (dt == null) return null;
        return self.type_info.store.tVoid();
    }

    fn checkErrDefer(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const edr = self.ast_unit.exprs.get(.ErrDefer, id);
        const edt = try self.checkExpr(edr.expr, expectNone());
        if (edt == null) return null;
        return self.type_info.store.tVoid();
    }

    fn checkErrUnwrap(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const eur = self.ast_unit.exprs.get(.ErrUnwrap, id);
        const et = try self.checkExpr(eur.expr, expectNone());
        if (et == null) return null;
        if (self.type_info.store.index.kinds.items[et.?.toRaw()] != .ErrorSet) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(eur.loc), .error_propagation_on_non_error, .{});
            return null;
        }
        const er = self.type_info.store.ErrorSet.get(self.type_info.store.index.rows.items[et.?.toRaw()]);
        if (er.payload == null) return self.type_info.store.tVoid();
        return er.payload.?;
    }

    fn checkOptionalUnwrap(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const our = self.ast_unit.exprs.get(.OptionalUnwrap, id);
        const ot = try self.checkExpr(our.expr, expectNone());
        if (ot == null) return null;
        if (self.type_info.store.index.kinds.items[ot.?.toRaw()] != .Optional) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(our.loc), .invalid_optional_unwrap_target, .{});
            return null;
        }
        const ore = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[ot.?.toRaw()]);
        return ore.elem;
    }

    fn checkAwait(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        _ = id;
        // Await is a no-op in the checker
        return self.type_info.store.tAny();
    }

    fn checkClosure(self: *CheckerV3, id: ast.ExprId, expect: Expectation) !?types.TypeId {
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
        const body_ty = try self.checkExpr(cr.body, expectNone());
        if (body_ty == null) return null;
        const fty = self.type_info.store.mkFunction(param_tys, body_ty.?, false);
        if (expect.ty) |et| {
            if (!self.assignable(fty, et)) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .type_annotation_mismatch, .{});
                return null;
            }
        }
        return fty;
    }

    fn checkCast(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const cr = self.ast_unit.exprs.get(.Cast, id);
        const et = try self.typeFromTypeExpr(cr.expr) orelse {
            try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .could_not_resolve_type, .{});
            return null;
        };
        const vt = try self.checkExpr(cr.expr, expectNone());
        if (vt == null) return null;
        if (!self.castable(vt.?, et)) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .invalid_checked_cast, .{});
            return null;
        }
        return et;
    }

    fn checkCatch(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const cr = self.ast_unit.exprs.get(.Catch, id);
        const vt = try self.checkExpr(cr.expr, expectNone());
        if (vt == null) return null;
        if (self.type_info.store.index.kinds.items[vt.?.toRaw()] != .ErrorSet) {
            try self.diags.addError(self.ast_unit.exprs.locs.get(cr.loc), .catch_on_non_error, .{});
            return null;
        }
        const er = self.type_info.store.ErrorSet.get(self.type_info.store.index.rows.items[vt.?.toRaw()]);
        if (er.payload == null) return self.type_info.store.tVoid();
        return er.payload.?;
    }

    fn checkImport(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        _ = id;
        return self.type_info.store.tAny();
    }

    fn checkTypeOf(self: *CheckerV3, id: ast.ExprId) !?types.TypeId {
        const tr = self.ast_unit.exprs.get(.TypeOf, id);
        const tt = try self.typeFromTypeExpr(tr.expr) orelse {
            try self.diags.addError(self.ast_unit.exprs.locs.get(tr.loc), .could_not_resolve_type, .{});
            return null;
        };
        return self.type_info.store.mkTypeType(tt);
    }

    fn checkStructLit(self: *CheckerV3, id: ast.ExprId, expect: Expectation) !?types.TypeId {
        const sl = self.ast_unit.exprs.get(.StructLit, id);
        const lit_fields = self.ast_unit.exprs.sfv_pool.slice(sl.fields);

        // 1) Prefer explicit type on the literal head
        if (!sl.ty.isNone()) {
            const te = sl.ty.unwrap();
            // Variant case head: enforce with variant payload diagnostics
            if (self.ast_unit.exprs.index.kinds.items[te.toRaw()] == .FieldAccess) {
                if (try self.collectStructFieldsFromTypeExpr(te)) |expv| {
                    defer self.gpa.free(expv);
                    try self.enforceVariantStructPayloadAgainstExpected(self.ast_unit.exprs.locs.get(sl.loc), lit_fields, expv);
                    return self.type_info.store.mkVariant(self.type_info.store.tAny());
                }
            }
            // Union head: enforce union literal semantics
            const te_kind = self.ast_unit.exprs.index.kinds.items[te.toRaw()];
            if (te_kind == .UnionType or te_kind == .Ident or te_kind == .FieldAccess) {
                var union_fields_opt: ?[]ExpectedStructField = null;
                if (te_kind == .UnionType) {
                    const r = self.ast_unit.exprs.get(.UnionType, te).fields;
                    const sfs = self.ast_unit.exprs.sfield_pool.slice(r);
                    var out = try self.gpa.alloc(ExpectedStructField, sfs.len);
                    var i: usize = 0;
                    while (i < sfs.len) : (i += 1) {
                        const f = self.ast_unit.exprs.StructField.get(sfs[i].toRaw());
                        const ft = (try self.typeFromTypeExpr(f.ty)) orelse {
                            self.gpa.free(out);
                            return null;
                        };
                        out[i] = .{ .name = self.ast_unit.exprs.strs.get(f.name), .ty = ft };
                    }
                    union_fields_opt = out;
                } else if (self.unionDeclByExpr(te)) |udid| {
                    const decl = self.ast_unit.exprs.Decl.get(udid.toRaw());
                    const ur = self.ast_unit.exprs.get(.UnionType, decl.value);
                    const sfs = self.ast_unit.exprs.sfield_pool.slice(ur.fields);
                    var out = try self.gpa.alloc(ExpectedStructField, sfs.len);
                    var i: usize = 0;
                    while (i < sfs.len) : (i += 1) {
                        const f = self.ast_unit.exprs.StructField.get(sfs[i].toRaw());
                        const ft = (try self.typeFromTypeExpr(f.ty)) orelse {
                            self.gpa.free(out);
                            return null;
                        };
                        out[i] = .{ .name = self.ast_unit.exprs.strs.get(f.name), .ty = ft };
                    }
                    union_fields_opt = out;
                }
                if (union_fields_opt) |exp_u| {
                    try self.enforceUnionLiteralAgainstExpected(self.ast_unit.exprs.locs.get(sl.loc), lit_fields, exp_u);
                    return null;
                }
            }
            if (try self.collectStructFieldsFromTypeExpr(te)) |exp| {
                try self.enforceStructFieldsAgainstExpected(self.ast_unit.exprs.locs.get(sl.loc), lit_fields, exp);
                // If type expression resolves to a concrete TypeId, return it.
                if (try self.typeFromTypeExpr(te)) |tt| return tt;
                return null;
            }
        }

        // 2) Otherwise, if we have an expected Struct TypeId, use it
        if (expect.ty) |et| {
            if (self.type_info.store.index.kinds.items[et.toRaw()] == .Struct) {
                const exp = try self.collectStructFieldsFromTypeId(et);
                try self.enforceStructFieldsAgainstExpected(self.ast_unit.exprs.locs.get(sl.loc), lit_fields, exp);
                return et;
            }
        }

        // 3) Nothing to enforce against
        return null;
    }

    const ExpectedStructField = struct { name: []const u8, ty: types.TypeId };

    fn enumDeclByExpr(self: *CheckerV3, expr: ast.ExprId) ?ast.DeclId {
        const kind = self.ast_unit.exprs.index.kinds.items[expr.toRaw()];
        switch (kind) {
            .Ident => {
                const ident = self.ast_unit.exprs.get(.Ident, expr);
                if (self.lookup(ident.name)) |sid| {
                    const sym = self.symtab.syms.get(sid.toRaw());
                    if (!sym.origin_decl.isNone()) {
                        const did = sym.origin_decl.unwrap();
                        const decl = self.ast_unit.exprs.Decl.get(did.toRaw());
                        if (self.ast_unit.exprs.index.kinds.items[decl.value.toRaw()] == .EnumType) return did;
                    }
                }
                const target = self.ast_unit.exprs.strs.get(ident.name);
                const decl_ids = self.ast_unit.exprs.decl_pool.slice(self.ast_unit.unit.decls);
                var i: usize = 0;
                while (i < decl_ids.len) : (i += 1) {
                    const did = decl_ids[i];
                    const d = self.ast_unit.exprs.Decl.get(did.toRaw());
                    if (d.pattern.isNone()) continue;
                    const pname = self.primaryNameOfPattern(d.pattern.unwrap());
                    if (pname.isNone()) continue;
                    if (!std.mem.eql(u8, self.ast_unit.exprs.strs.get(pname.unwrap()), target)) continue;
                    if (self.ast_unit.exprs.index.kinds.items[d.value.toRaw()] == .EnumType) return did;
                }
            },
            else => {},
        }
        return null;
    }

    fn handleEnumFieldAccess(
        self: *CheckerV3,
        fr: ast.Rows.FieldAccess,
        expect: Expectation,
        enum_decl: ast.DeclId,
    ) ?types.TypeId {
        const decl = self.ast_unit.exprs.Decl.get(enum_decl.toRaw());
        const en = self.ast_unit.exprs.get(.EnumType, decl.value);
        const fields = self.ast_unit.exprs.efield_pool.slice(en.fields);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const ef = self.ast_unit.exprs.EnumField.get(fields[i].toRaw());
            if (std.mem.eql(u8, self.ast_unit.exprs.strs.get(ef.name), self.ast_unit.exprs.strs.get(fr.field))) {
                if (expect.enum_decl) |expected| {
                    if (expected.toRaw() != enum_decl.toRaw()) {
                        _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .enum_tag_type_mismatch, .{}) catch {};
                        return null;
                    }
                }
                return null;
            }
        }
        _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_enum_tag, .{}) catch {};
        return null;
    }

    fn variantDeclByExpr(self: *CheckerV3, expr: ast.ExprId) ?ast.DeclId {
        const kind = self.ast_unit.exprs.index.kinds.items[expr.toRaw()];
        switch (kind) {
            .Ident => {
                const ident = self.ast_unit.exprs.get(.Ident, expr);
                if (self.lookup(ident.name)) |sid| {
                    const sym = self.symtab.syms.get(sid.toRaw());
                    if (!sym.origin_decl.isNone()) {
                        const did = sym.origin_decl.unwrap();
                        const decl = self.ast_unit.exprs.Decl.get(did.toRaw());
                        const k = self.ast_unit.exprs.index.kinds.items[decl.value.toRaw()];
                        if (k == .VariantType or k == .ErrorType) return did;
                    }
                }
                const target = self.ast_unit.exprs.strs.get(ident.name);
                const decl_ids = self.ast_unit.exprs.decl_pool.slice(self.ast_unit.unit.decls);
                var i: usize = 0;
                while (i < decl_ids.len) : (i += 1) {
                    const did = decl_ids[i];
                    const d = self.ast_unit.exprs.Decl.get(did.toRaw());
                    if (d.pattern.isNone()) continue;
                    const pname = self.primaryNameOfPattern(d.pattern.unwrap());
                    if (pname.isNone()) continue;
                    if (!std.mem.eql(u8, self.ast_unit.exprs.strs.get(pname.unwrap()), target)) continue;
                    const k = self.ast_unit.exprs.index.kinds.items[d.value.toRaw()];
                    if (k == .VariantType or k == .ErrorType) return did;
                }
            },
            else => {},
        }
        return null;
    }

    fn handleVariantCtorCall(
        self: *CheckerV3,
        fr: ast.Rows.FieldAccess,
        args: []const ast.ExprId,
    ) !?types.TypeId {
        const did = self.variantDeclByExpr(fr.parent) orelse return null;
        const decl = self.ast_unit.exprs.Decl.get(did.toRaw());
        const vk = self.ast_unit.exprs.index.kinds.items[decl.value.toRaw()];
        if (vk != .VariantType and vk != .ErrorType) return null;
        const vt = self.ast_unit.exprs.get(.VariantType, decl.value);
        const fields = self.ast_unit.exprs.vfield_pool.slice(vt.fields);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const vf = self.ast_unit.exprs.VariantField.get(fields[i].toRaw());
            if (!std.mem.eql(u8, self.ast_unit.exprs.strs.get(vf.name), self.ast_unit.exprs.strs.get(fr.field))) continue;
            switch (vf.payload_kind) {
                .none => {
                    if (args.len != 0) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .variant_payload_arity_mismatch, .{});
                        return null;
                    }
                    return self.type_info.store.mkVariant(self.type_info.store.tVoid());
                },
                .tuple => {
                    const expected_len: usize = if (!vf.payload_elems.isNone()) self.ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange()).len else 0;
                    if (args.len != expected_len) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .variant_payload_arity_mismatch, .{});
                        return null;
                    }
                    if (expected_len > 0) {
                        const elems = self.ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var j: usize = 0;
                        while (j < elems.len) : (j += 1) {
                            const et = (try self.typeFromTypeExpr(elems[j])) orelse {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .variant_payload_mismatch, .{});
                                return null;
                            };
                            const at = try self.checkExpr(args[j], expectTy(et));
                            if (at == null or !self.assignable(at.?, et)) {
                                try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .variant_payload_mismatch, .{});
                                return null;
                            }
                        }
                    }
                    return self.type_info.store.mkVariant(self.type_info.store.tAny());
                },
                .@"struct" => {
                    // Struct-like payload should be provided via typed struct literal: V.C{...}
                    // A call form is invalid arity.
                    try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .variant_payload_arity_mismatch, .{});
                    return null;
                },
            }
        }
        // Unknown tag
        _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_enum_tag, .{}) catch {};
        return null;
    }

    fn collectStructFieldsFromTypeExpr(self: *CheckerV3, te: ast.ExprId) !?[]ExpectedStructField {
        var fields_range_opt: ?ast.RangeField = null;
        _ = switch (self.ast_unit.exprs.index.kinds.items[te.toRaw()]) {
            .StructType => fields_range_opt = self.ast_unit.exprs.get(.StructType, te).fields,
            .UnionType => fields_range_opt = self.ast_unit.exprs.get(.UnionType, te).fields,
            .FieldAccess => blk_fa: {
                const fr = self.ast_unit.exprs.get(.FieldAccess, te);
                if (self.variantDeclByExpr(fr.parent)) |did| {
                    const decl = self.ast_unit.exprs.Decl.get(did.toRaw());
                    const vt = self.ast_unit.exprs.get(.VariantType, decl.value);
                    const vfs = self.ast_unit.exprs.vfield_pool.slice(vt.fields);
                    var i: usize = 0;
                    while (i < vfs.len) : (i += 1) {
                        const vf = self.ast_unit.exprs.VariantField.get(vfs[i].toRaw());
                        if (!std.mem.eql(u8, self.ast_unit.exprs.strs.get(vf.name), self.ast_unit.exprs.strs.get(fr.field))) continue;
                        if (vf.payload_kind != .@"struct" or vf.payload_fields.isNone()) break :blk_fa null;
                        const fields = self.ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var out = try self.gpa.alloc(ExpectedStructField, fields.len);
                        var j: usize = 0;
                        while (j < fields.len) : (j += 1) {
                            const sf = self.ast_unit.exprs.StructField.get(fields[j].toRaw());
                            const ft = (try self.typeFromTypeExpr(sf.ty)) orelse {
                                self.gpa.free(out);
                                return null;
                            };
                            out[j] = .{ .name = self.ast_unit.exprs.strs.get(sf.name), .ty = ft };
                        }
                        return out;
                    }
                }
                return null;
            },
            .Ident => {
                const nm = self.ast_unit.exprs.get(.Ident, te).name;
                if (self.lookup(nm)) |sid| {
                    const srow = self.symtab.syms.get(sid.toRaw());
                    if (!srow.origin_decl.isNone()) {
                        const od = self.ast_unit.exprs.Decl.get(srow.origin_decl.unwrap().toRaw());
                        if (self.ast_unit.exprs.index.kinds.items[od.value.toRaw()] == .StructType)
                            fields_range_opt = self.ast_unit.exprs.get(.StructType, od.value).fields;
                    }
                } else {
                    // top-level scan
                    const decl_ids = self.ast_unit.exprs.decl_pool.slice(self.ast_unit.unit.decls);
                    var ii: usize = 0;
                    while (ii < decl_ids.len) : (ii += 1) {
                        const d2 = self.ast_unit.exprs.Decl.get(decl_ids[ii].toRaw());
                        if (!d2.pattern.isNone()) {
                            const name2 = self.primaryNameOfPattern(d2.pattern.unwrap());
                            if (!name2.isNone() and std.mem.eql(u8, self.ast_unit.exprs.strs.get(name2.unwrap()), self.ast_unit.exprs.strs.get(nm))) {
                                if (self.ast_unit.exprs.index.kinds.items[d2.value.toRaw()] == .StructType) {
                                    fields_range_opt = self.ast_unit.exprs.get(.StructType, d2.value).fields;
                                    break;
                                }
                            }
                        }
                    }
                }
            },
            else => {},
        };
        if (fields_range_opt == null) return null;

        const r = fields_range_opt.?;
        const sfs = self.ast_unit.exprs.sfield_pool.slice(r);
        var out = try self.gpa.alloc(ExpectedStructField, sfs.len);
        var i: usize = 0;
        while (i < sfs.len) : (i += 1) {
            const f = self.ast_unit.exprs.StructField.get(sfs[i].toRaw());
            const ft = (try self.typeFromTypeExpr(f.ty)) orelse {
                self.gpa.free(out);
                return null;
            };
            out[i] = .{ .name = self.ast_unit.exprs.strs.get(f.name), .ty = ft };
        }
        return out;
    }

    fn collectStructFieldsFromTypeId(self: *CheckerV3, tid: types.TypeId) ![]ExpectedStructField {
        const row = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[tid.toRaw()]);
        const fids = self.type_info.store.field_pool.slice(row.fields);
        var out = try self.gpa.alloc(ExpectedStructField, fids.len);
        var i: usize = 0;
        while (i < fids.len) : (i += 1) {
            const f = self.type_info.store.Field.get(fids[i].toRaw());
            out[i] = .{ .name = self.type_info.store.strs.get(f.name), .ty = f.ty };
        }
        return out;
    }

    fn enforceStructFieldsAgainstExpected(
        self: *CheckerV3,
        loc: Loc,
        lit_fields: []const ast.StructFieldValueId,
        expected: []const ExpectedStructField,
    ) anyerror!void {
        defer self.gpa.free(expected);

        // 1) extra fields?
        var i: usize = 0;
        while (i < lit_fields.len) : (i += 1) {
            const lf = self.ast_unit.exprs.StructFieldValue.get(lit_fields[i].toRaw());
            if (lf.name.isNone()) continue;
            const lname = self.ast_unit.exprs.strs.get(lf.name.unwrap());
            var found = false;
            var j: usize = 0;
            while (j < expected.len) : (j += 1) {
                if (std.mem.eql(u8, expected[j].name, lname)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                try self.diags.addError(loc, .unknown_struct_field, .{});
                return;
            }
        }

        // 2) every expected present with correct type
        var j: usize = 0;
        while (j < expected.len) : (j += 1) {
            const exp_name = expected[j].name;
            const exp_ty = expected[j].ty;

            var found_val: ?ast.ExprId = null;
            var k: usize = 0;
            while (k < lit_fields.len) : (k += 1) {
                const lf = self.ast_unit.exprs.StructFieldValue.get(lit_fields[k].toRaw());
                if (!lf.name.isNone() and std.mem.eql(u8, self.ast_unit.exprs.strs.get(lf.name.unwrap()), exp_name)) {
                    found_val = lf.value;
                    break;
                }
            }
            if (found_val == null) {
                try self.diags.addError(loc, .struct_missing_field, .{});
                return;
            }

            const val_id = found_val.?;
            const val_kind = self.ast_unit.exprs.index.kinds.items[val_id.toRaw()];

            if (val_kind == .NullLit) {
                // null only allowed if target is Optional
                const ek = self.type_info.store.index.kinds.items[exp_ty.toRaw()];
                if (ek != .Optional) {
                    try self.diags.addError(loc, .struct_field_type_mismatch, .{});
                    return;
                }
                continue;
            }

            // nested struct literal: recurse with expected field type if it's a struct
            if (val_kind == .StructLit) {
                const ek = self.type_info.store.index.kinds.items[exp_ty.toRaw()];
                if (ek == .Struct) {
                    _ = try self.checkStructLit(val_id, expectTy(exp_ty));
                    continue;
                }
            }

            const got_ty = (try self.checkExpr(val_id, expectTy(exp_ty))) orelse {
                try self.diags.addError(loc, .struct_field_type_mismatch, .{});
                return;
            };
            if (got_ty.toRaw() != exp_ty.toRaw()) {
                try self.diags.addError(loc, .struct_field_type_mismatch, .{});
                return;
            }
        }
    }

    fn structFieldTypeFromLiteralContext(self: *CheckerV3, fr: ast.Rows.FieldAccess) ?types.TypeId {
        const parent = self.ast_unit.exprs.get(.StructLit, fr.parent);
        if (!parent.ty.isNone()) {
            const te = parent.ty.unwrap();
            if (self.collectStructFieldsFromTypeExpr(te) catch null) |exp| {
                defer self.gpa.free(exp);
                var i: usize = 0;
                while (i < exp.len) : (i += 1) {
                    if (std.mem.eql(u8, exp[i].name, self.ast_unit.exprs.strs.get(fr.field))) return exp[i].ty;
                }
                _ = self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{}) catch {};
            }
        }
        return null;
    }

    fn enforceVariantStructPayloadAgainstExpected(
        self: *CheckerV3,
        loc: Loc,
        lit_fields: []const ast.StructFieldValueId,
        expected: []const ExpectedStructField,
    ) !void {
        // extra fields
        var i: usize = 0;
        while (i < lit_fields.len) : (i += 1) {
            const lf = self.ast_unit.exprs.StructFieldValue.get(lit_fields[i].toRaw());
            if (lf.name.isNone()) continue;
            const lname = self.ast_unit.exprs.strs.get(lf.name.unwrap());
            var found = false;
            var j: usize = 0;
            while (j < expected.len) : (j += 1) {
                if (std.mem.eql(u8, expected[j].name, lname)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                try self.diags.addError(loc, .variant_payload_field_mismatch, .{});
                return;
            }
        }
        // required fields present and typed
        var j: usize = 0;
        while (j < expected.len) : (j += 1) {
            const exp_name = expected[j].name;
            const exp_ty = expected[j].ty;
            var found_val: ?ast.ExprId = null;
            var k: usize = 0;
            while (k < lit_fields.len) : (k += 1) {
                const lf = self.ast_unit.exprs.StructFieldValue.get(lit_fields[k].toRaw());
                if (!lf.name.isNone() and std.mem.eql(u8, self.ast_unit.exprs.strs.get(lf.name.unwrap()), exp_name)) {
                    found_val = lf.value;
                    break;
                }
            }
            if (found_val == null) {
                try self.diags.addError(loc, .variant_payload_field_mismatch, .{});
                return;
            }
            const val_id = found_val.?;
            const val_kind = self.ast_unit.exprs.index.kinds.items[val_id.toRaw()];
            if (val_kind == .NullLit) {
                const ek = self.type_info.store.index.kinds.items[exp_ty.toRaw()];
                if (ek != .Optional) {
                    try self.diags.addError(loc, .variant_payload_field_requires_non_null, .{});
                    return;
                }
                continue;
            }
            const got_ty = (try self.checkExpr(val_id, expectTy(exp_ty))) orelse {
                try self.diags.addError(loc, .variant_payload_field_type_mismatch, .{});
                return;
            };
            if (got_ty.toRaw() != exp_ty.toRaw()) {
                try self.diags.addError(loc, .variant_payload_field_type_mismatch, .{});
                return;
            }
        }
    }

    fn unionDeclByExpr(self: *CheckerV3, expr: ast.ExprId) ?ast.DeclId {
        const kind = self.ast_unit.exprs.index.kinds.items[expr.toRaw()];
        switch (kind) {
            .Ident => {
                const ident = self.ast_unit.exprs.get(.Ident, expr);
                if (self.lookup(ident.name)) |sid| {
                    const sym = self.symtab.syms.get(sid.toRaw());
                    if (!sym.origin_decl.isNone()) {
                        const did = sym.origin_decl.unwrap();
                        const decl = self.ast_unit.exprs.Decl.get(did.toRaw());
                        if (self.ast_unit.exprs.index.kinds.items[decl.value.toRaw()] == .UnionType) return did;
                    }
                }
                const target = self.ast_unit.exprs.strs.get(ident.name);
                const decl_ids = self.ast_unit.exprs.decl_pool.slice(self.ast_unit.unit.decls);
                var i: usize = 0;
                while (i < decl_ids.len) : (i += 1) {
                    const did = decl_ids[i];
                    const d = self.ast_unit.exprs.Decl.get(did.toRaw());
                    if (d.pattern.isNone()) continue;
                    const pname = self.primaryNameOfPattern(d.pattern.unwrap());
                    if (pname.isNone()) continue;
                    if (!std.mem.eql(u8, self.ast_unit.exprs.strs.get(pname.unwrap()), target)) continue;
                    if (self.ast_unit.exprs.index.kinds.items[d.value.toRaw()] == .UnionType) return did;
                }
            },
            else => {},
        }
        return null;
    }

    fn enforceUnionLiteralAgainstExpected(
        self: *CheckerV3,
        loc: Loc,
        lit_fields: []const ast.StructFieldValueId,
        expected: []const ExpectedStructField,
    ) !void {
        defer self.gpa.free(expected);
        // must specify exactly one field
        var specified: usize = 0;
        var chosen_name: []const u8 = &[_]u8{};
        var chosen_expr: ?ast.ExprId = null;
        var i: usize = 0;
        while (i < lit_fields.len) : (i += 1) {
            const lf = self.ast_unit.exprs.StructFieldValue.get(lit_fields[i].toRaw());
            if (!lf.name.isNone()) {
                specified += 1;
                chosen_name = self.ast_unit.exprs.strs.get(lf.name.unwrap());
                chosen_expr = lf.value;
            }
        }
        if (specified == 0) {
            try self.diags.addError(loc, .union_empty_literal, .{});
            return;
        }
        if (specified > 1) {
            try self.diags.addError(loc, .union_literal_multiple_fields, .{});
            return;
        }
        // validate chosen field exists and type matches
        var found = false;
        var exp_ty: ?types.TypeId = null;
        var j: usize = 0;
        while (j < expected.len) : (j += 1) {
            if (std.mem.eql(u8, expected[j].name, chosen_name)) {
                found = true;
                exp_ty = expected[j].ty;
                break;
            }
        }
        if (!found) {
            try self.diags.addError(loc, .unknown_union_field, .{});
            return;
        }
        const ce = chosen_expr.?;
        const ck = self.ast_unit.exprs.index.kinds.items[ce.toRaw()];
        if (ck == .NullLit) {
            if (self.type_info.store.index.kinds.items[exp_ty.?.toRaw()] != .Optional) {
                try self.diags.addError(loc, .union_field_requires_non_null, .{});
                return;
            }
            return; // ok
        }
        const got = (try self.checkExpr(ce, expectTy(exp_ty.?))) orelse {
            try self.diags.addError(loc, .union_field_type_mismatch, .{});
            return;
        };
        if (!self.assignable(got, exp_ty.?)) {
            try self.diags.addError(loc, .union_field_type_mismatch, .{});
            return;
        }
    }

    // =========================================================
    // Type expressions
    // =========================================================
    fn typeFromTypeExpr(self: *CheckerV3, id: ast.ExprId) anyerror!?types.TypeId {
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
                var i: usize = 0;
                while (i < sfs.len) : (i += 1) {
                    const f = self.ast_unit.exprs.StructField.get(sfs[i].toRaw());
                    const ft = (try self.typeFromTypeExpr(f.ty)) orelse break :blk_sty null;
                    buf[i] = .{ .name = self.ast_unit.exprs.strs.get(f.name), .ty = ft };
                }
                break :blk_sty self.type_info.store.mkStruct(buf);
            },
            .EnumType => blk_en: {
                const row = self.ast_unit.exprs.get(.EnumType, id);
                const efs = self.ast_unit.exprs.efield_pool.slice(row.fields);
                var seen = std.StringHashMapUnmanaged(void){};
                defer seen.deinit(self.gpa);
                var i: usize = 0;
                while (i < efs.len) : (i += 1) {
                    const ef = self.ast_unit.exprs.EnumField.get(efs[i].toRaw());
                    const name = self.ast_unit.exprs.strs.get(ef.name);
                    const gop = try seen.getOrPut(self.gpa, name);
                    if (gop.found_existing) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(ef.loc), .duplicate_enum_field, .{});
                        return null;
                    }
                    if (!ef.value.isNone()) {
                        const val_id = ef.value.unwrap();
                        const val_kind = self.ast_unit.exprs.index.kinds.items[val_id.toRaw()];
                        if (val_kind != .Literal) {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(ef.loc), .enum_discriminant_not_integer, .{});
                            return null;
                        }
                        const lit = self.ast_unit.exprs.get(.Literal, val_id);
                        if (lit.kind != .int) {
                            try self.diags.addError(self.ast_unit.exprs.locs.get(ef.loc), .enum_discriminant_not_integer, .{});
                            return null;
                        }
                    }
                }
                break :blk_en null;
            },
            .ErrorType => blk_err: {
                const row = self.ast_unit.exprs.get(.ErrorType, id);
                const vfs = self.ast_unit.exprs.vfield_pool.slice(row.fields);
                var seen = std.StringHashMapUnmanaged(void){};
                defer seen.deinit(self.gpa);
                var i: usize = 0;
                while (i < vfs.len) : (i += 1) {
                    const vf = self.ast_unit.exprs.VariantField.get(vfs[i].toRaw());
                    const name = self.ast_unit.exprs.strs.get(vf.name);
                    const gop = try seen.getOrPut(self.gpa, name);
                    if (gop.found_existing) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(vf.loc), .duplicate_error_variant, .{});
                        return null;
                    }
                }
                break :blk_err null;
            },
            .ErrorSetType => blk_est: {
                const row = self.ast_unit.exprs.get(.ErrorSetType, id);
                const val = (try self.typeFromTypeExpr(row.value)) orelse break :blk_est null;
                break :blk_est self.type_info.store.mkErrorSet(val);
            },
            .VariantType => blk_var: {
                const row = self.ast_unit.exprs.get(.VariantType, id);
                const vfs = self.ast_unit.exprs.vfield_pool.slice(row.fields);
                var seen = std.StringHashMapUnmanaged(void){};
                defer seen.deinit(self.gpa);
                var i: usize = 0;
                while (i < vfs.len) : (i += 1) {
                    const vf = self.ast_unit.exprs.VariantField.get(vfs[i].toRaw());
                    const name = self.ast_unit.exprs.strs.get(vf.name);
                    const gop = try seen.getOrPut(self.gpa, name);
                    if (gop.found_existing) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(vf.loc), .duplicate_variant, .{});
                        return null;
                    }
                    switch (vf.payload_kind) {
                        .none => {},
                        .tuple => {
                            if (!vf.payload_elems.isNone()) {
                                const elems = self.ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                                var j: usize = 0;
                                while (j < elems.len) : (j += 1) {
                                    _ = try self.typeFromTypeExpr(elems[j]);
                                }
                            }
                        },
                        .@"struct" => {
                            if (!vf.payload_fields.isNone()) {
                                const fields = self.ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                                var j: usize = 0;
                                while (j < fields.len) : (j += 1) {
                                    const sf = self.ast_unit.exprs.StructField.get(fields[j].toRaw());
                                    const ft = try self.typeFromTypeExpr(sf.ty);
                                    if (ft == null) return null;
                                }
                            }
                        },
                    }
                }
                break :blk_var null;
            },
            .UnionType => blk_un: {
                const row = self.ast_unit.exprs.get(.UnionType, id);
                const sfs = self.ast_unit.exprs.sfield_pool.slice(row.fields);
                var seen = std.StringHashMapUnmanaged(void){};
                defer seen.deinit(self.gpa);
                var i: usize = 0;
                while (i < sfs.len) : (i += 1) {
                    const sf = self.ast_unit.exprs.StructField.get(sfs[i].toRaw());
                    const name = self.ast_unit.exprs.strs.get(sf.name);
                    const gop = try seen.getOrPut(self.gpa, name);
                    if (gop.found_existing) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(sf.loc), .duplicate_field, .{});
                        return null;
                    }
                    // Validate field types resolve
                    _ = (try self.typeFromTypeExpr(sf.ty)) orelse null;
                }
                break :blk_un null;
            },
            .FunctionLit => blk_fn: {
                // function type in type position
                const fnr = self.ast_unit.exprs.get(.FunctionLit, id);
                const params = self.ast_unit.exprs.param_pool.slice(fnr.params);
                var pbuf = try self.type_info.store.gpa.alloc(types.TypeId, params.len);
                defer self.type_info.store.gpa.free(pbuf);
                var i: usize = 0;
                while (i < params.len) : (i += 1) {
                    const p = self.ast_unit.exprs.Param.get(params[i].toRaw());
                    if (p.ty.isNone()) break :blk_fn null;
                    const pt = (try self.typeFromTypeExpr(p.ty.unwrap())) orelse break :blk_fn null;
                    pbuf[i] = pt;
                }
                const res = if (!fnr.result_ty.isNone()) (try self.typeFromTypeExpr(fnr.result_ty.unwrap())) else self.type_info.store.tVoid();
                if (res == null) break :blk_fn null;
                break :blk_fn self.type_info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic);
            },
            .AnyType => self.type_info.store.tAny(),
            .TypeType => null,
            else => null,
        };
    }

    // =========================================================
    // Misc helpers
    // =========================================================
    fn checkDivByZero(self: *CheckerV3, rhs: ast.ExprId, loc: Loc) !void {
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
    fn checkIntZeroLiteral(self: *CheckerV3, rhs: ast.ExprId, loc: Loc) !void {
        if (self.ast_unit.exprs.index.kinds.items[rhs.toRaw()] == .Literal) {
            const lit = self.ast_unit.exprs.get(.Literal, rhs);
            if (lit.kind == .int and !lit.value.isNone()) {
                const sval = self.ast_unit.exprs.strs.get(lit.value.unwrap());
                if (std.mem.eql(u8, sval, "0")) try self.diags.addError(loc, .division_by_zero, .{});
            }
        }
    }
};
