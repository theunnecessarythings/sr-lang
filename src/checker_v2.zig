const std = @import("std");
const ast = @import("ast_v2.zig");
const infer = @import("infer_v2.zig");
const Diagnostics = @import("diagnostics_v2.zig").Diagnostics;
const diag = @import("diagnostics_v2.zig");
const Loc = @import("lexer.zig").Token.Loc;
const symbols = @import("symbols_v2.zig");
const types = @import("types_v2.zig");

/// ------------------------------------------------------------
/// CheckerV3 — refactor of the previous CheckerV2
///  - Node-specific checks (no more giant visitDecl).
///  - Small helpers for assignability / optionals / zero checks.
///  - Reuses TypeStore from types.zig (no duplicate type tables).
/// ------------------------------------------------------------
pub const CheckerV2 = CheckerV3; // alias for compatibility
pub const CheckerV3 = struct {
    gpa: std.mem.Allocator,
    diags: *Diagnostics,

    symtab: symbols.SymbolStore = undefined,

    // cached builtins
    t_bool: types.TypeId = undefined,
    t_i32: types.TypeId = undefined,
    t_f64: types.TypeId = undefined,
    t_string: types.TypeId = undefined,
    t_void: types.TypeId = undefined,
    t_any: types.TypeId = undefined,

    func_stack: std.ArrayListUnmanaged(FunctionCtx) = .{},
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},
    warned_meta: bool = false,

    pub fn init(gpa: std.mem.Allocator, diags: *Diagnostics) CheckerV3 {
        return .{ .gpa = gpa, .diags = diags, .symtab = symbols.SymbolStore.init(gpa) };
    }
    pub fn deinit(self: *CheckerV3) void {
        self.func_stack.deinit(self.gpa);
        self.loop_stack.deinit(self.gpa);
        self.symtab.deinit();
    }

    pub fn run(self: *CheckerV3, a: *const ast.Ast) !void {
        var info = try self.runWithTypes(a);
        info.deinit();
    }

    pub fn runWithTypes(self: *CheckerV3, a: *const ast.Ast) !infer.TypeInfoV2 {
        var info = infer.TypeInfoV2.init(self.gpa);
        errdefer info.deinit();

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

        _ = try self.symtab.push(null);
        defer self.symtab.pop();

        const decl_ids = a.exprs.decl_pool.slice(a.unit.decls);
        for (decl_ids) |did| {
            try self.checkDecl(&info, a, did);
        }
        return info;
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

    fn bindDeclPattern(self: *CheckerV3, a: *const ast.Ast, did: ast.DeclId, d: ast.Rows.Decl) !void {
        if (d.pattern.isNone()) return;
        const name_opt = self.primaryNameOfPattern(a, d.pattern.unwrap());
        if (name_opt.isNone()) return;
        _ = try self.symtab.declare(.{ .name = name_opt.unwrap(), .kind = .Var, .loc = d.loc, .origin_decl = ast.OptDeclId.some(did), .origin_param = ast.OptParamId.none() });
    }

    fn prepareDeclExpectation(
        self: *CheckerV3,
        info: *infer.TypeInfoV2,
        a: *const ast.Ast,
        d: ast.Rows.Decl,
    ) !?DeclExpectation {
        var result = DeclExpectation{ .ty = null, .ctx = expectNone() };
        if (d.ty.isNone()) return result;

        const annot_id = d.ty.unwrap();
        const annot_kind = a.exprs.index.kinds.items[annot_id.toRaw()];
        var array_size_invalid = false;
        const resolved_ty = self.typeFromTypeExpr(info, a, annot_id) catch |err| switch (err) {
            error.InvalidArraySize => blk: {
                array_size_invalid = true;
                break :blk null;
            },
            else => return err,
        };

        if (array_size_invalid) {
            const loc_id = switch (annot_kind) {
                .ArrayType => a.exprs.get(.ArrayType, annot_id).loc,
                else => d.loc,
            };
            try self.diags.addError(a.exprs.locs.get(loc_id), .array_size_not_integer_literal, .{});
            return null;
        }

        result.ty = resolved_ty;
        if (result.ty) |et| {
            result.ctx = expectTy(et);
        } else if (annot_kind == .MapType) {
            const map_ty = a.exprs.get(.MapType, annot_id);
            const key_expect = try self.typeFromTypeExpr(info, a, map_ty.key);
            const value_expect = try self.typeFromTypeExpr(info, a, map_ty.value);
            if (key_expect != null and value_expect != null) {
                result.ctx = expectMap(key_expect.?, value_expect.?, a.exprs.locs.get(d.loc));
            }
        }
        if (self.enumDeclByExpr(a, annot_id)) |did| {
            result.ctx.enum_decl = did;
        }
        return result;
    }

    fn finalizeDeclType(
        self: *CheckerV3,
        info: *infer.TypeInfoV2,
        a: *const ast.Ast,
        did: ast.DeclId,
        d: ast.Rows.Decl,
        rhs_ty: ?types.TypeId,
        expect_ty: ?types.TypeId,
    ) !void {
        if (expect_ty) |et| {
            if (rhs_ty) |rt| {
                var ok = self.assignable(info, rt, et, true);
                if (!ok) {
                    if (self.isOptional(info, et)) |inner| {
                        ok = self.assignable(info, rt, inner, true) or rt.toRaw() == inner.toRaw();
                    }
                }
                if (!ok) {
                    try self.diags.addError(a.exprs.locs.get(d.loc), .type_annotation_mismatch, .{});
                } else info.decl_types.items[did.toRaw()] = et;
            } else {
                info.decl_types.items[did.toRaw()] = et;
            }
        } else if (rhs_ty) |rt| {
            info.decl_types.items[did.toRaw()] = rt;
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

    fn lookup(self: *CheckerV3, a: *const ast.Ast, name: ast.StrId) ?symbols.SymbolId {
        return self.symtab.lookup(a, self.symtab.currentId(), name);
    }

    fn primaryNameOfPattern(self: *CheckerV3, a: *const ast.Ast, pid: ast.PatternId) ast.OptStrId {
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

    // --------- type helpers
    fn isNumericKind(_: *const CheckerV3, k: types.TypeKind) bool {
        return switch (k) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize => true,
            else => false,
        };
    }
    fn isIntegerKind(_: *const CheckerV3, k: types.TypeKind) bool {
        return switch (k) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
            else => false,
        };
    }
    fn isOptional(self: *CheckerV3, info: *infer.TypeInfoV2, id: types.TypeId) ?types.TypeId {
        _ = self;
        const k = info.store.index.kinds.items[id.toRaw()];
        if (k != .Optional) return null;
        const row = info.store.Optional.get(info.store.index.rows.items[id.toRaw()]);
        return row.elem;
    }
    fn assignable(self: *CheckerV3, info: *infer.TypeInfoV2, got: types.TypeId, expect: types.TypeId, allow_numeric_coerce: bool) bool {
        if (got.toRaw() == expect.toRaw()) return true;
        if (!allow_numeric_coerce) return false;
        const gk = info.store.index.kinds.items[got.toRaw()];
        const ek = info.store.index.kinds.items[expect.toRaw()];
        return self.isNumericKind(gk) and self.isNumericKind(ek);
    }

    // =========================================================
    // Declarations & Statements
    // =========================================================
    fn checkDecl(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, did: ast.DeclId) !void {
        const d = a.exprs.Decl.get(did.toRaw());
        try self.bindDeclPattern(a, did, d);
        const decl_expect = (try self.prepareDeclExpectation(info, a, d)) orelse return;
        const rhs_ty = try self.checkExpr(info, a, d.value, decl_expect.ctx);
        try self.finalizeDeclType(info, a, did, d, rhs_ty, decl_expect.ty);
    }

    fn checkStmt(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, sid: ast.StmtId) !void {
        switch (a.stmts.index.kinds.items[sid.toRaw()]) {
            .Expr => {
                const row = a.stmts.get(.Expr, sid);
                _ = try self.checkExpr(info, a, row.expr, expectNone());
            },
            .Decl => {
                const row = a.stmts.get(.Decl, sid);
                try self.checkDecl(info, a, row.decl);
            },
            .Assign => {
                const row = a.stmts.get(.Assign, sid);
                const lt = try self.checkExpr(info, a, row.left, expectNone());
                const rt = try self.checkExpr(info, a, row.right, if (lt) |lt_ty| expectTy(lt_ty) else expectNone());
                if (lt != null and rt != null and !self.assignable(info, rt.?, lt.?, true)) {
                    try self.diags.addError(a.exprs.locs.get(row.loc), .type_annotation_mismatch, .{});
                }
            },
            .Insert => {
                const row = a.stmts.get(.Insert, sid);
                if (!self.warned_meta) {
                    _ = self.diags.addNote(a.exprs.locs.get(row.loc), .checker_insert_not_expanded, .{}) catch {};
                    self.warned_meta = true;
                }
                _ = try self.checkExpr(info, a, row.expr, expectNone());
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
                    if (!row.value.isNone()) _ = try self.checkExpr(info, a, row.value.unwrap(), expectNone());
                }
            },
            .Break => {
                const row = a.stmts.get(.Break, sid);
                if (!self.inLoop()) try self.diags.addError(a.exprs.locs.get(row.loc), .break_outside_loop, .{});
                if (!row.value.isNone()) _ = try self.checkExpr(info, a, row.value.unwrap(), expectNone());
            },
            .Continue => {
                const row = a.stmts.get(.Continue, sid);
                if (!self.inLoop()) try self.diags.addError(a.exprs.locs.get(row.loc), .continue_outside_loop, .{});
            },
            .Unreachable => {},
            .Defer => {
                const row = a.stmts.get(.Defer, sid);
                if (!self.inFunction()) try self.diags.addError(a.exprs.locs.get(row.loc), .defer_outside_function, .{});
                _ = try self.checkExpr(info, a, row.expr, expectNone());
            },
            .ErrDefer => {
                const row = a.stmts.get(.ErrDefer, sid);
                if (!self.inFunction()) try self.diags.addError(a.exprs.locs.get(row.loc), .errdefer_outside_function, .{});
                _ = try self.checkExpr(info, a, row.expr, expectNone());
            },
        }
    }

    // =========================================================
    // Expressions
    // =========================================================
    fn checkExpr(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId, expect: Expectation) anyerror!?types.TypeId {
        if (info.expr_types.items[id.toRaw()]) |cached| return cached;
        const k = a.exprs.index.kinds.items[id.toRaw()];
        var tid: ?types.TypeId = null;

        switch (k) {
            .Literal => tid = self.checkLiteral(info, a, id),
            .Ident => tid = self.checkIdent(info, a, id),
            .Binary => tid = try self.checkBinary(info, a, id),
            .Unary => tid = try self.checkUnary(info, a, id),
            .FunctionLit => tid = try self.checkFunctionLit(info, a, id),
            .ArrayLit => tid = try self.checkArrayLit(info, a, id, expect),
            .TupleLit => tid = try self.checkTupleLit(info, a, id, expect),
            .MapLit => tid = try self.checkMapLit(info, a, id, expect),
            .IndexAccess => tid = self.checkIndexAccess(info, a, id),
            .FieldAccess => tid = self.checkFieldAccess(info, a, id, expect),
            .StructLit => tid = try self.checkStructLit(info, a, id, expect),
            .Range => tid = try self.checkRange(info, a, id),

            // still default to any for the following kinds (can be implemented later)
            .VariantLit => {
                std.debug.print("VariantLit expr {d}\n", .{id.toRaw()});
                tid = self.t_any;
            },
            .EnumLit, .Call, .ComptimeBlock, .CodeBlock, .AsyncBlock, .MlirBlock, .Insert, .Return, .If, .While, .For, .Match, .Break, .Continue, .Unreachable, .UndefLit => tid = self.t_any,

            .Block, .Defer, .ErrDefer, .ErrUnwrap, .OptionalUnwrap, .Await, .Closure, .Cast, .Catch, .Import, .TypeOf => std.debug.panic("TODO: checkExpr kind not implemented: {}", .{k}),

            .NullLit => {
                if (expect.map) |exp| {
                    try self.diags.addError(exp.loc, .type_annotation_mismatch, .{});
                    return null;
                }
                if (expect.ty) |et| {
                    const inner = self.isOptional(info, et);
                    if (inner != null) {
                        tid = et;
                    } else {
                        if (expect.suppress_null_assign) {
                            tid = info.store.mkOptional(info.store.tAny());
                        } else {
                            const loc = a.exprs.locs.get(a.exprs.get(.NullLit, id).loc);
                            const kind = info.store.index.kinds.items[et.toRaw()];
                            switch (kind) {
                                .Slice, .Array, .Struct, .Tuple, .Function, .Ptr => try self.diags.addError(loc, .type_annotation_mismatch, .{}),
                                else => try self.diags.addError(loc, .assign_null_to_non_optional, .{}),
                            }
                            return null;
                        }
                    }
                } else tid = info.store.mkOptional(info.store.tAny());
            },

            .TupleType, .ArrayType, .DynArrayType, .MapType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => {
                var array_size_invalid = false;
                const resolved = self.typeFromTypeExpr(info, a, id) catch |err| switch (err) {
                    error.InvalidArraySize => blk: {
                        array_size_invalid = true;
                        break :blk null;
                    },
                    else => return err,
                };
                if (array_size_invalid) {
                    if (k == .ArrayType) {
                        const row = a.exprs.get(.ArrayType, id);
                        try self.diags.addError(a.exprs.locs.get(row.loc), .array_size_not_integer_literal, .{});
                    }
                    return null;
                }
                tid = resolved orelse self.t_any;
            },
            else => std.debug.panic("TODO: checkExpr kind not implemented: {}", .{k}),
        }

        if (expect.map) |exp| {
            switch (k) {
                .MapLit => {},
                .ArrayLit => {
                    const arr = a.exprs.get(.ArrayLit, id);
                    if (a.exprs.expr_pool.slice(arr.elems).len != 0) {
                        try self.diags.addError(exp.loc, .type_annotation_mismatch, .{});
                        return null;
                    }
                },
                .NullLit => {},
                else => {
                    try self.diags.addError(exp.loc, .type_annotation_mismatch, .{});
                    return null;
                },
            }
        }

        if (tid) |t| info.expr_types.items[id.toRaw()] = t;
        return tid;
    }

    fn checkLiteral(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) ?types.TypeId {
        const lit = a.exprs.get(.Literal, id);
        return switch (lit.kind) {
            .int => self.t_i32,
            .float => self.t_f64,
            .bool => self.t_bool,
            .string => self.t_string,
            .char => info.store.tU32(),
        };
    }
    fn checkIdent(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) ?types.TypeId {
        const row = a.exprs.get(.Ident, id);
        if (self.lookup(a, row.name)) |sid| {
            const srow = self.symtab.syms.get(sid.toRaw());
            if (!srow.origin_decl.isNone()) if (info.decl_types.items[srow.origin_decl.unwrap().toRaw()]) |dt| return dt;
        }
        return null;
    }

    fn checkBinary(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) !?types.TypeId {
        const row = a.exprs.get(.Binary, id);
        const lt = try self.checkExpr(info, a, row.left, expectNone());
        const rt = try self.checkExpr(info, a, row.right, expectNone());
        if (lt == null or rt == null) return null;

        const l = lt.?;
        const r = rt.?;
        const lk = info.store.index.kinds.items[l.toRaw()];
        const rk = info.store.index.kinds.items[r.toRaw()];

        switch (row.op) {
            .add, .sub, .mul, .div, .mod, .bit_and, .bit_or, .bit_xor, .shl, .shr => {
                if (row.op == .div) try self.checkDivByZero(info, a, row.right, a.exprs.locs.get(row.loc));
                if (row.op == .mod) {
                    const left_is_float = switch (lk) {
                        .F32, .F64 => true,
                        else => false,
                    };
                    const right_is_float = switch (rk) {
                        .F32, .F64 => true,
                        else => false,
                    };
                    if (left_is_float or right_is_float) {
                        try self.diags.addError(a.exprs.locs.get(row.loc), .invalid_binary_op_operands, .{});
                        return null;
                    }
                    if (self.isIntegerKind(lk) and self.isIntegerKind(rk))
                        try self.checkIntZeroLiteral(info, a, row.right, a.exprs.locs.get(row.loc));
                }
                const both_numeric = self.isNumericKind(lk) and self.isNumericKind(rk);
                const both_integer = self.isIntegerKind(lk) and self.isIntegerKind(rk);
                const same = l.toRaw() == r.toRaw();
                const ok = (both_numeric and (row.op == .add or row.op == .sub or row.op == .mul or row.op == .div) and same) or (both_integer and (row.op == .mod or row.op == .bit_and or row.op == .bit_or or row.op == .bit_xor or row.op == .shl or row.op == .shr) and same);
                if (ok) return lt;
                try self.diags.addError(a.exprs.locs.get(row.loc), .invalid_binary_op_operands, .{});
                return null;
            },
            .eq, .neq, .lt, .lte, .gt, .gte => {
                if (l.toRaw() == r.toRaw()) {
                    if (row.op == .eq or row.op == .neq) return self.t_bool;
                    if (self.isNumericKind(lk)) return self.t_bool;
                }
                try self.diags.addError(a.exprs.locs.get(row.loc), .invalid_binary_op_operands, .{});
                return null;
            },
            .logical_and, .logical_or => {
                if (l.toRaw() == self.t_bool.toRaw() and r.toRaw() == self.t_bool.toRaw()) return self.t_bool;
                try self.diags.addError(a.exprs.locs.get(row.loc), .invalid_binary_op_operands, .{});
                return null;
            },
            .@"orelse" => {
                if (self.isOptional(info, l)) |elem| if (elem.toRaw() == r.toRaw()) return rt;
                try self.diags.addError(a.exprs.locs.get(row.loc), .could_not_resolve_type, .{});
                return null;
            },
        }
        return null;
    }

    fn checkUnary(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) !?types.TypeId {
        const ur = a.exprs.get(.Unary, id);
        const et = try self.checkExpr(info, a, ur.expr, expectNone());
        if (et == null) return null;
        const t = et.?;
        const tk = info.store.index.kinds.items[t.toRaw()];
        switch (ur.op) {
            .plus, .minus => {
                if (!self.isNumericKind(tk)) {
                    try self.diags.addError(a.exprs.locs.get(ur.loc), .invalid_unary_op_operand, .{});
                    return null;
                }
                return t;
            },
            .logical_not => {
                if (t.toRaw() != self.t_bool.toRaw()) {
                    try self.diags.addError(a.exprs.locs.get(ur.loc), .invalid_unary_op_operand, .{});
                    return null;
                }
                return self.t_bool;
            },
            .address_of => return info.store.mkPtr(t, false),
        }
    }

    fn checkFunctionLit(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) !?types.TypeId {
        const fnr = a.exprs.get(.FunctionLit, id);
        const params = a.exprs.param_pool.slice(fnr.params);
        var pbuf = try self.gpa.alloc(types.TypeId, params.len);
        defer self.gpa.free(pbuf);
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = a.exprs.Param.get(params[i].toRaw());
            if (!p.ty.isNone()) {
                const pt = (try self.typeFromTypeExpr(info, a, p.ty.unwrap())) orelse return null;
                pbuf[i] = pt;
            } else {
                pbuf[i] = info.store.tAny();
            }
        }
        const res = if (!fnr.result_ty.isNone()) (try self.typeFromTypeExpr(info, a, fnr.result_ty.unwrap())) else info.store.tVoid();
        if (res == null) return null;
        return info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic);
    }

    fn checkTupleLit(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId, expect: Expectation) !?types.TypeId {
        const row = a.exprs.get(.TupleLit, id);
        const elems = a.exprs.expr_pool.slice(row.elems);

        if (expect.ty) |et| {
            if (info.store.index.kinds.items[et.toRaw()] == .Tuple) {
                const at = info.store.Tuple.get(info.store.index.rows.items[et.toRaw()]);
                const a_elems = info.store.type_pool.slice(at.elems);
                if (a_elems.len != elems.len) {
                    try self.diags.addError(a.exprs.locs.get(row.loc), .tuple_arity_mismatch, .{});
                    return null;
                }
                var ok = true;
                var i: usize = 0;
                while (i < elems.len) : (i += 1) {
                    const got = try self.checkExpr(info, a, elems[i], expectTy(a_elems[i]));
                    if (got == null or !self.assignable(info, got.?, a_elems[i], false)) {
                        ok = false;
                        break;
                    }
                }
                if (!ok) {
                    try self.diags.addError(a.exprs.locs.get(row.loc), .type_annotation_mismatch, .{});
                    return null;
                }
                return et;
            }
        }

        var tbuf = try self.gpa.alloc(types.TypeId, elems.len);
        defer self.gpa.free(tbuf);
        var i: usize = 0;
        while (i < elems.len) : (i += 1) {
            const ety = try self.checkExpr(info, a, elems[i], expectNone());
            if (ety == null) return null;
            tbuf[i] = ety.?;
        }
        return info.store.mkTuple(tbuf);
    }

    fn checkArrayLit(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId, expect: Expectation) !?types.TypeId {
        const row = a.exprs.get(.ArrayLit, id);
        const elems = a.exprs.expr_pool.slice(row.elems);

        if (expect.map) |_| {
            if (elems.len == 0) return null;
            try self.diags.addError(a.exprs.locs.get(row.loc), .type_annotation_mismatch, .{});
            return null;
        }

        // With a concrete expected array/slice element type, enforce elements (and length for arrays).
        if (expect.ty) |et| {
            switch (info.store.index.kinds.items[et.toRaw()]) {
                .Array => {
                    const er = info.store.Array.get(info.store.index.rows.items[et.toRaw()]);
                    if (er.len != elems.len) {
                        try self.diags.addError(a.exprs.locs.get(row.loc), .array_length_mismatch, .{});
                        return null;
                    }
                    var i: usize = 0;
                    var ok = true;
                    while (i < elems.len) : (i += 1) {
                        const gt = try self.checkExpr(info, a, elems[i], expectTySuppressNull(er.elem));
                        if (gt == null or !self.assignable(info, gt.?, er.elem, true)) {
                            ok = false;
                            break;
                        }
                    }
                    if (!ok) {
                        try self.diags.addError(a.exprs.locs.get(row.loc), .type_annotation_mismatch, .{});
                        return null;
                    }
                    return et;
                },
                .Slice => {
                    const er = info.store.Slice.get(info.store.index.rows.items[et.toRaw()]);
                    var i: usize = 0;
                    var ok = true;
                    while (i < elems.len) : (i += 1) {
                        const gt = try self.checkExpr(info, a, elems[i], expectTySuppressNull(er.elem));
                        if (gt == null or !self.assignable(info, gt.?, er.elem, true)) {
                            ok = false;
                            break;
                        }
                    }
                    if (!ok) {
                        try self.diags.addError(a.exprs.locs.get(row.loc), .type_annotation_mismatch, .{});
                        return null;
                    }
                    return et;
                },
                else => {},
            }
        }

        if (elems.len == 0) {
            // unannotated [] is ambiguous (could be map init in this language)
            try self.diags.addError(a.exprs.locs.get(row.loc), .ambiguous_empty_map, .{});
            return null;
        }

        // infer from first element, homogeneous requirement
        const first_ty = (try self.checkExpr(info, a, elems[0], expectNone())) orelse return null;
        var i: usize = 1;
        while (i < elems.len) : (i += 1) {
            const ety = try self.checkExpr(info, a, elems[i], expectTySuppressNull(first_ty));
            if (ety == null or ety.?.toRaw() != first_ty.toRaw()) {
                try self.diags.addError(a.exprs.locs.get(row.loc), .heterogeneous_array_elements, .{});
                return null;
            }
        }
        return info.store.mkArray(first_ty, elems.len);
    }

    fn checkMapLit(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId, expect: Expectation) !?types.TypeId {
        const row = a.exprs.get(.MapLit, id);
        const kvs = a.exprs.kv_pool.slice(row.entries);

        if (expect.map) |exp| {
            var saw_key_mismatch = false;
            var saw_value_mismatch = false;
            var i: usize = 0;
            while (i < kvs.len) : (i += 1) {
                const kv = a.exprs.KeyValue.get(kvs[i].toRaw());
                const kt = try self.checkExpr(info, a, kv.key, expectNone());
                if (!saw_key_mismatch) {
                    if (kt == null or !self.assignable(info, kt.?, exp.key, false)) {
                        saw_key_mismatch = true;
                    }
                }
                const vt = try self.checkExpr(info, a, kv.value, expectTySuppressNull(exp.value));
                if (!saw_value_mismatch) {
                    if (vt == null or !self.assignable(info, vt.?, exp.value, false)) {
                        saw_value_mismatch = true;
                    }
                }
                if (saw_key_mismatch and saw_value_mismatch) {
                    break;
                }
            }
            if (saw_key_mismatch) {
                try self.diags.addError(a.exprs.locs.get(row.loc), .map_wrong_key_type, .{});
            }
            if (saw_value_mismatch) {
                try self.diags.addError(a.exprs.locs.get(row.loc), .type_annotation_mismatch, .{});
            }
            return null;
        }

        var key_ty: ?types.TypeId = null;
        var val_ty: ?types.TypeId = null;
        var i: usize = 0;
        while (i < kvs.len) : (i += 1) {
            const kv = a.exprs.KeyValue.get(kvs[i].toRaw());
            const kt = try self.checkExpr(info, a, kv.key, expectNone());
            const vt = try self.checkExpr(info, a, kv.value, expectNone());
            if (kt != null) {
                if (key_ty == null) key_ty = kt else if (key_ty.?.toRaw() != kt.?.toRaw()) {
                    try self.diags.addError(a.exprs.locs.get(row.loc), .map_mixed_key_types, .{});
                    break;
                }
            }
            if (vt != null) {
                if (val_ty == null) val_ty = vt else if (val_ty.?.toRaw() != vt.?.toRaw()) {
                    try self.diags.addError(a.exprs.locs.get(row.loc), .map_mixed_value_types, .{});
                    break;
                }
            }
        }
        return null; // construction deferred, just do checks
    }

    fn checkIndexAccess(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) ?types.TypeId {
        const row = a.exprs.get(.IndexAccess, id);
        const ct = self.checkExpr(info, a, row.collection, expectNone()) catch return null;

        // Map literal special-case
        if (a.exprs.index.kinds.items[row.collection.toRaw()] == .MapLit) {
            const m = a.exprs.get(.MapLit, row.collection);
            const kvs = a.exprs.kv_pool.slice(m.entries);
            if (kvs.len > 0) {
                const first = a.exprs.KeyValue.get(kvs[0].toRaw());
                const key_ty = self.checkExpr(info, a, first.key, expectNone()) catch null;
                const idx_ty = self.checkExpr(info, a, row.index, expectNone()) catch null;
                if (key_ty != null and idx_ty != null and key_ty.?.toRaw() != idx_ty.?.toRaw()) {
                    _ = self.diags.addError(a.exprs.locs.get(row.loc), .map_wrong_key_type, .{}) catch {};
                    return null;
                }
                return self.checkExpr(info, a, first.value, expectNone()) catch null;
            }
            return null;
        }

        if (ct) |t| {
            const k = info.store.index.kinds.items[t.toRaw()];
            switch (k) {
                .Array => {
                    const idx_kind = a.exprs.index.kinds.items[row.index.toRaw()];
                    if (idx_kind == .Range) {
                        _ = self.checkExpr(info, a, row.index, expectNone()) catch return null;
                        const r = info.store.Array.get(info.store.index.rows.items[t.toRaw()]);
                        return info.store.mkSlice(r.elem);
                    }

                    const it = self.checkExpr(info, a, row.index, expectNone()) catch return null;
                    if (it) |iid| {
                        if (!self.isIntegerKind(info.store.index.kinds.items[iid.toRaw()])) {
                            _ = self.diags.addError(a.exprs.locs.get(row.loc), .non_integer_index, .{}) catch {};
                            return null;
                        }
                    }
                    const r = info.store.Array.get(info.store.index.rows.items[t.toRaw()]);
                    return r.elem;
                },
                .Slice => {
                    const idx_kind = a.exprs.index.kinds.items[row.index.toRaw()];
                    if (idx_kind == .Range) {
                        _ = self.checkExpr(info, a, row.index, expectNone()) catch return null;
                        const r = info.store.Slice.get(info.store.index.rows.items[t.toRaw()]);
                        return info.store.mkSlice(r.elem);
                    }

                    const it = self.checkExpr(info, a, row.index, expectNone()) catch return null;
                    if (it) |iid| {
                        if (!self.isIntegerKind(info.store.index.kinds.items[iid.toRaw()])) {
                            _ = self.diags.addError(a.exprs.locs.get(row.loc), .non_integer_index, .{}) catch {};
                            return null;
                        }
                    }
                    const r = info.store.Slice.get(info.store.index.rows.items[t.toRaw()]);
                    return r.elem;
                },
                .String => {
                    const it = self.checkExpr(info, a, row.index, expectNone()) catch return null;
                    if (it) |iid| {
                        if (!self.isIntegerKind(info.store.index.kinds.items[iid.toRaw()])) {
                            _ = self.diags.addError(a.exprs.locs.get(row.loc), .non_integer_index, .{}) catch {};
                            return null;
                        }
                    }
                    return info.store.tU8();
                },
                else => {
                    _ = self.diags.addError(a.exprs.locs.get(row.loc), .not_indexable, .{}) catch {};
                },
            }
        }
        return null;
    }

    fn checkFieldAccess(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId, expect: Expectation) ?types.TypeId {
        const fr = a.exprs.get(.FieldAccess, id);
        const enum_decl_opt = if (!fr.is_tuple) self.enumDeclByExpr(a, fr.parent) else null;
        const pt = self.checkExpr(info, a, fr.parent, expectNone()) catch return null;
        if (pt == null) {
            // Try struct typed literal context
            if (!fr.is_tuple and a.exprs.index.kinds.items[fr.parent.toRaw()] == .StructLit) {
                return self.structFieldTypeFromLiteralContext(info, a, fr);
            }
            if (enum_decl_opt) |did| {
                return self.handleEnumFieldAccess(a, fr, expect, did);
            }
            return null;
        }
        var t = pt.?;
        if (info.store.index.kinds.items[t.toRaw()] == .Ptr)
            t = info.store.Ptr.get(info.store.index.rows.items[t.toRaw()]).elem;

        if (enum_decl_opt != null and t.toRaw() == self.t_any.toRaw()) {
            return self.handleEnumFieldAccess(a, fr, expect, enum_decl_opt.?);
        }

        if (info.store.index.kinds.items[t.toRaw()] == .Tuple) {
            if (fr.is_tuple) {
                const rowt = info.store.Tuple.get(info.store.index.rows.items[t.toRaw()]);
                const idx = std.fmt.parseInt(usize, a.exprs.strs.get(fr.field), 10) catch return null;
                const ids = info.store.type_pool.slice(rowt.elems);
                if (idx < ids.len) return ids[idx];
                _ = self.diags.addError(a.exprs.locs.get(fr.loc), .tuple_index_out_of_bounds, .{}) catch {};
                return null;
            } else {
                _ = self.diags.addError(a.exprs.locs.get(fr.loc), .expected_field_name_or_index, .{}) catch {};
                return null;
            }
        }
        if (info.store.index.kinds.items[t.toRaw()] == .Struct) {
            const rowt = info.store.Struct.get(info.store.index.rows.items[t.toRaw()]);
            const fids = info.store.field_pool.slice(rowt.fields);
            var i: usize = 0;
            while (i < fids.len) : (i += 1) {
                const f = info.store.Field.get(fids[i].toRaw());
                if (std.mem.eql(u8, info.store.strs.get(f.name), a.exprs.strs.get(fr.field))) {
                    return f.ty;
                }
            }
            _ = self.diags.addError(a.exprs.locs.get(fr.loc), .unknown_struct_field, .{}) catch {};
            return null;
        }
        return null;
    }

    fn checkRange(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) !?types.TypeId {
        const rr = a.exprs.get(.Range, id);
        if (!rr.start.isNone()) {
            const st = try self.checkExpr(info, a, rr.start.unwrap(), expectNone());
            if (st == null or !self.isIntegerKind(info.store.index.kinds.items[st.?.toRaw()])) {
                try self.diags.addError(a.exprs.locs.get(rr.loc), .non_integer_index, .{});
                return null;
            }
        }
        if (!rr.end.isNone()) {
            const et = try self.checkExpr(info, a, rr.end.unwrap(), expectNone());
            if (et == null or !self.isIntegerKind(info.store.index.kinds.items[et.?.toRaw()])) {
                try self.diags.addError(a.exprs.locs.get(rr.loc), .non_integer_index, .{});
                return null;
            }
        }
        return info.store.mkSlice(info.store.tUsize());
    }

    // =========================================================
    // Struct literal checks (moved out of visitDecl)
    // =========================================================
    fn checkStructLit(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId, expect: Expectation) !?types.TypeId {
        const sl = a.exprs.get(.StructLit, id);
        const lit_fields = a.exprs.sfv_pool.slice(sl.fields);

        // 1) Prefer explicit type on the literal head
        if (!sl.ty.isNone()) {
            const te = sl.ty.unwrap();
            if (try self.collectStructFieldsFromTypeExpr(info, a, te)) |exp| {
                try self.enforceStructFieldsAgainstExpected(info, a, a.exprs.locs.get(sl.loc), lit_fields, exp);
                // If type expression resolves to a concrete TypeId, return it.
                if (try self.typeFromTypeExpr(info, a, te)) |tt| return tt;
                return null;
            }
        }

        // 2) Otherwise, if we have an expected Struct TypeId, use it
        if (expect.ty) |et| {
            if (info.store.index.kinds.items[et.toRaw()] == .Struct) {
                const exp = try self.collectStructFieldsFromTypeId(info, et);
                try self.enforceStructFieldsAgainstExpected(info, a, a.exprs.locs.get(sl.loc), lit_fields, exp);
                return et;
            }
        }

        // 3) Nothing to enforce against
        return null;
    }

    const ExpectedStructField = struct { name: []const u8, ty: types.TypeId };

    fn enumDeclByExpr(self: *CheckerV3, a: *const ast.Ast, expr: ast.ExprId) ?ast.DeclId {
        const kind = a.exprs.index.kinds.items[expr.toRaw()];
        switch (kind) {
            .Ident => {
                const ident = a.exprs.get(.Ident, expr);
                if (self.lookup(a, ident.name)) |sid| {
                    const sym = self.symtab.syms.get(sid.toRaw());
                    if (!sym.origin_decl.isNone()) {
                        const did = sym.origin_decl.unwrap();
                        const decl = a.exprs.Decl.get(did.toRaw());
                        if (a.exprs.index.kinds.items[decl.value.toRaw()] == .EnumType) return did;
                    }
                }
                const target = a.exprs.strs.get(ident.name);
                const decl_ids = a.exprs.decl_pool.slice(a.unit.decls);
                var i: usize = 0;
                while (i < decl_ids.len) : (i += 1) {
                    const did = decl_ids[i];
                    const d = a.exprs.Decl.get(did.toRaw());
                    if (d.pattern.isNone()) continue;
                    const pname = self.primaryNameOfPattern(a, d.pattern.unwrap());
                    if (pname.isNone()) continue;
                    if (!std.mem.eql(u8, a.exprs.strs.get(pname.unwrap()), target)) continue;
                    if (a.exprs.index.kinds.items[d.value.toRaw()] == .EnumType) return did;
                }
            },
            else => {},
        }
        return null;
    }

    fn handleEnumFieldAccess(
        self: *CheckerV3,
        a: *const ast.Ast,
        fr: ast.Rows.FieldAccess,
        expect: Expectation,
        enum_decl: ast.DeclId,
    ) ?types.TypeId {
        const decl = a.exprs.Decl.get(enum_decl.toRaw());
        const en = a.exprs.get(.EnumType, decl.value);
        const fields = a.exprs.efield_pool.slice(en.fields);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const ef = a.exprs.EnumField.get(fields[i].toRaw());
            if (std.mem.eql(u8, a.exprs.strs.get(ef.name), a.exprs.strs.get(fr.field))) {
                if (expect.enum_decl) |expected| {
                    if (expected.toRaw() != enum_decl.toRaw()) {
                        _ = self.diags.addError(a.exprs.locs.get(fr.loc), .enum_tag_type_mismatch, .{}) catch {};
                        return null;
                    }
                }
                return null;
            }
        }
        _ = self.diags.addError(a.exprs.locs.get(fr.loc), .unknown_enum_tag, .{}) catch {};
        return null;
    }

    fn collectStructFieldsFromTypeExpr(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, te: ast.ExprId) !?[]ExpectedStructField {
        var fields_range_opt: ?ast.RangeField = null;
        switch (a.exprs.index.kinds.items[te.toRaw()]) {
            .StructType => fields_range_opt = a.exprs.get(.StructType, te).fields,
            .Ident => {
                const nm = a.exprs.get(.Ident, te).name;
                if (self.lookup(a, nm)) |sid| {
                    const srow = self.symtab.syms.get(sid.toRaw());
                    if (!srow.origin_decl.isNone()) {
                        const od = a.exprs.Decl.get(srow.origin_decl.unwrap().toRaw());
                        if (a.exprs.index.kinds.items[od.value.toRaw()] == .StructType)
                            fields_range_opt = a.exprs.get(.StructType, od.value).fields;
                    }
                } else {
                    // top-level scan
                    const decl_ids = a.exprs.decl_pool.slice(a.unit.decls);
                    var ii: usize = 0;
                    while (ii < decl_ids.len) : (ii += 1) {
                        const d2 = a.exprs.Decl.get(decl_ids[ii].toRaw());
                        if (!d2.pattern.isNone()) {
                            const name2 = self.primaryNameOfPattern(a, d2.pattern.unwrap());
                            if (!name2.isNone() and std.mem.eql(u8, a.exprs.strs.get(name2.unwrap()), a.exprs.strs.get(nm))) {
                                if (a.exprs.index.kinds.items[d2.value.toRaw()] == .StructType) {
                                    fields_range_opt = a.exprs.get(.StructType, d2.value).fields;
                                    break;
                                }
                            }
                        }
                    }
                }
            },
            else => {},
        }
        if (fields_range_opt == null) return null;

        const r = fields_range_opt.?;
        const sfs = a.exprs.sfield_pool.slice(r);
        var out = try self.gpa.alloc(ExpectedStructField, sfs.len);
        var i: usize = 0;
        while (i < sfs.len) : (i += 1) {
            const f = a.exprs.StructField.get(sfs[i].toRaw());
            const ft = (try self.typeFromTypeExpr(info, a, f.ty)) orelse {
                self.gpa.free(out);
                return null;
            };
            out[i] = .{ .name = a.exprs.strs.get(f.name), .ty = ft };
        }
        return out;
    }

    fn collectStructFieldsFromTypeId(self: *CheckerV3, info: *infer.TypeInfoV2, tid: types.TypeId) ![]ExpectedStructField {
        const row = info.store.Struct.get(info.store.index.rows.items[tid.toRaw()]);
        const fids = info.store.field_pool.slice(row.fields);
        var out = try self.gpa.alloc(ExpectedStructField, fids.len);
        var i: usize = 0;
        while (i < fids.len) : (i += 1) {
            const f = info.store.Field.get(fids[i].toRaw());
            out[i] = .{ .name = info.store.strs.get(f.name), .ty = f.ty };
        }
        return out;
    }

    fn enforceStructFieldsAgainstExpected(
        self: *CheckerV3,
        info: *infer.TypeInfoV2,
        a: *const ast.Ast,
        loc: Loc,
        lit_fields: []const ast.StructFieldValueId,
        expected: []const ExpectedStructField,
    ) anyerror!void {
        defer self.gpa.free(expected);

        // 1) extra fields?
        var i: usize = 0;
        while (i < lit_fields.len) : (i += 1) {
            const lf = a.exprs.StructFieldValue.get(lit_fields[i].toRaw());
            if (lf.name.isNone()) continue;
            const lname = a.exprs.strs.get(lf.name.unwrap());
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
                const lf = a.exprs.StructFieldValue.get(lit_fields[k].toRaw());
                if (!lf.name.isNone() and std.mem.eql(u8, a.exprs.strs.get(lf.name.unwrap()), exp_name)) {
                    found_val = lf.value;
                    break;
                }
            }
            if (found_val == null) {
                try self.diags.addError(loc, .struct_missing_field, .{});
                return;
            }

            const val_id = found_val.?;
            const val_kind = a.exprs.index.kinds.items[val_id.toRaw()];

            if (val_kind == .NullLit) {
                // null only allowed if target is Optional
                const ek = info.store.index.kinds.items[exp_ty.toRaw()];
                if (ek != .Optional) {
                    try self.diags.addError(loc, .struct_field_type_mismatch, .{});
                    return;
                }
                continue;
            }

            // nested struct literal: recurse with expected field type if it's a struct
            if (val_kind == .StructLit) {
                const ek = info.store.index.kinds.items[exp_ty.toRaw()];
                if (ek == .Struct) {
                    _ = try self.checkStructLit(info, a, val_id, expectTy(exp_ty));
                    continue;
                }
            }

            const got_ty = (try self.checkExpr(info, a, val_id, expectTy(exp_ty))) orelse {
                try self.diags.addError(loc, .struct_field_type_mismatch, .{});
                return;
            };
            if (got_ty.toRaw() != exp_ty.toRaw()) {
                try self.diags.addError(loc, .struct_field_type_mismatch, .{});
                return;
            }
        }
    }

    fn structFieldTypeFromLiteralContext(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, fr: ast.Rows.FieldAccess) ?types.TypeId {
        const parent = a.exprs.get(.StructLit, fr.parent);
        if (!parent.ty.isNone()) {
            const te = parent.ty.unwrap();
            if (self.collectStructFieldsFromTypeExpr(info, a, te) catch null) |exp| {
                defer self.gpa.free(exp);
                var i: usize = 0;
                while (i < exp.len) : (i += 1) {
                    if (std.mem.eql(u8, exp[i].name, a.exprs.strs.get(fr.field))) return exp[i].ty;
                }
                _ = self.diags.addError(a.exprs.locs.get(fr.loc), .unknown_struct_field, .{}) catch {};
            }
        }
        return null;
    }

    // =========================================================
    // Type expressions
    // =========================================================
    fn typeFromTypeExpr(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) anyerror!?types.TypeId {
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
                if (std.mem.eql(u8, s, "char")) break :blk_ident info.store.tU32();
                if (std.mem.eql(u8, s, "string")) break :blk_ident info.store.tString();
                if (std.mem.eql(u8, s, "void")) break :blk_ident info.store.tVoid();
                if (std.mem.eql(u8, s, "any")) break :blk_ident info.store.tAny();
                break :blk_ident null;
            },
            .TupleType => blk_tt: {
                const row = a.exprs.get(.TupleType, id);
                const ids = a.exprs.expr_pool.slice(row.elems);
                var buf = try info.store.gpa.alloc(types.TypeId, ids.len);
                defer info.store.gpa.free(buf);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) buf[i] = (try self.typeFromTypeExpr(info, a, ids[i])) orelse break :blk_tt null;
                break :blk_tt info.store.mkTuple(buf);
            },
            .TupleLit => blk_ttl: {
                const row = a.exprs.get(.TupleLit, id);
                const ids = a.exprs.expr_pool.slice(row.elems);
                var buf = try info.store.gpa.alloc(types.TypeId, ids.len);
                defer info.store.gpa.free(buf);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) buf[i] = (try self.typeFromTypeExpr(info, a, ids[i])) orelse break :blk_ttl null;
                break :blk_ttl info.store.mkTuple(buf);
            },
            .ArrayType => blk_at: {
                const row = a.exprs.get(.ArrayType, id);
                const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_at null;
                var len_val: usize = 0;
                if (a.exprs.index.kinds.items[row.size.toRaw()] == .Literal) {
                    const lit = a.exprs.get(.Literal, row.size);
                    if (lit.kind == .int and !lit.value.isNone()) {
                        len_val = std.fmt.parseInt(usize, a.exprs.strs.get(lit.value.unwrap()), 10) catch 0;
                    } else return error.InvalidArraySize;
                } else return error.InvalidArraySize;
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
                var buf = try info.store.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
                defer info.store.gpa.free(buf);
                var i: usize = 0;
                while (i < sfs.len) : (i += 1) {
                    const f = a.exprs.StructField.get(sfs[i].toRaw());
                    const ft = (try self.typeFromTypeExpr(info, a, f.ty)) orelse break :blk_sty null;
                    buf[i] = .{ .name = a.exprs.strs.get(f.name), .ty = ft };
                }
                break :blk_sty info.store.mkStruct(buf);
            },
            .EnumType => blk_en: {
                const row = a.exprs.get(.EnumType, id);
                const efs = a.exprs.efield_pool.slice(row.fields);
                var seen = std.StringHashMapUnmanaged(void){};
                defer seen.deinit(self.gpa);
                var i: usize = 0;
                while (i < efs.len) : (i += 1) {
                    const ef = a.exprs.EnumField.get(efs[i].toRaw());
                    const name = a.exprs.strs.get(ef.name);
                    const gop = try seen.getOrPut(self.gpa, name);
                    if (gop.found_existing) {
                        try self.diags.addError(a.exprs.locs.get(ef.loc), .duplicate_enum_field, .{});
                        return null;
                    }
                    if (!ef.value.isNone()) {
                        const val_id = ef.value.unwrap();
                        const val_kind = a.exprs.index.kinds.items[val_id.toRaw()];
                        if (val_kind != .Literal) {
                            try self.diags.addError(a.exprs.locs.get(ef.loc), .enum_discriminant_not_integer, .{});
                            return null;
                        }
                        const lit = a.exprs.get(.Literal, val_id);
                        if (lit.kind != .int) {
                            try self.diags.addError(a.exprs.locs.get(ef.loc), .enum_discriminant_not_integer, .{});
                            return null;
                        }
                    }
                }
                break :blk_en null;
            },
            .VariantType => blk_var: {
                const row = a.exprs.get(.VariantType, id);
                const vfs = a.exprs.vfield_pool.slice(row.fields);
                var seen = std.StringHashMapUnmanaged(void){};
                defer seen.deinit(self.gpa);
                var i: usize = 0;
                while (i < vfs.len) : (i += 1) {
                    const vf = a.exprs.VariantField.get(vfs[i].toRaw());
                    const name = a.exprs.strs.get(vf.name);
                    const gop = try seen.getOrPut(self.gpa, name);
                    if (gop.found_existing) {
                        try self.diags.addError(a.exprs.locs.get(vf.loc), .duplicate_variant, .{});
                        return null;
                    }
                    switch (vf.payload_kind) {
                        .none => {},
                        .tuple => {
                            if (!vf.payload_elems.isNone()) {
                                const elems = a.exprs.expr_pool.slice(vf.payload_elems.asRange());
                                var j: usize = 0;
                                while (j < elems.len) : (j += 1) {
                                    _ = try self.typeFromTypeExpr(info, a, elems[j]);
                                }
                            }
                        },
                        .@"struct" => {
                            if (!vf.payload_fields.isNone()) {
                                const fields = a.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                                var j: usize = 0;
                                while (j < fields.len) : (j += 1) {
                                    const sf = a.exprs.StructField.get(fields[j].toRaw());
                                    const ft = try self.typeFromTypeExpr(info, a, sf.ty);
                                    if (ft == null) return null;
                                }
                            }
                        },
                    }
                }
                break :blk_var null;
            },
            .FunctionLit => blk_fn: {
                // function type in type position
                const fnr = a.exprs.get(.FunctionLit, id);
                const params = a.exprs.param_pool.slice(fnr.params);
                var pbuf = try info.store.gpa.alloc(types.TypeId, params.len);
                defer info.store.gpa.free(pbuf);
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

    // =========================================================
    // Misc helpers
    // =========================================================
    fn checkDivByZero(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, rhs: ast.ExprId, loc: Loc) !void {
        _ = info;
        if (a.exprs.index.kinds.items[rhs.toRaw()] == .Literal) {
            const lit = a.exprs.get(.Literal, rhs);
            if (lit.kind == .int) {
                const sval = if (!lit.value.isNone()) a.exprs.strs.get(lit.value.unwrap()) else "";
                if (std.mem.eql(u8, sval, "0")) try self.diags.addError(loc, .division_by_zero, .{});
            } else if (lit.kind == .float) {
                if (!lit.value.isNone()) {
                    const sval = a.exprs.strs.get(lit.value.unwrap());
                    const f = std.fmt.parseFloat(f64, sval) catch 1.0;
                    if (f == 0.0) try self.diags.addError(loc, .division_by_zero, .{});
                }
            }
        }
    }
    fn checkIntZeroLiteral(self: *CheckerV3, info: *infer.TypeInfoV2, a: *const ast.Ast, rhs: ast.ExprId, loc: Loc) !void {
        _ = info;
        if (a.exprs.index.kinds.items[rhs.toRaw()] == .Literal) {
            const lit = a.exprs.get(.Literal, rhs);
            if (lit.kind == .int) {
                const sval = if (!lit.value.isNone()) a.exprs.strs.get(lit.value.unwrap()) else "";
                if (std.mem.eql(u8, sval, "0")) try self.diags.addError(loc, .division_by_zero, .{});
            }
        }
    }
};

// If you want this to be a drop-in replacement without touching imports:
// pub const CheckerV2 = CheckerV3;
