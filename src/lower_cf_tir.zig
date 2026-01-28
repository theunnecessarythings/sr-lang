const LowerTir = @import("lower_tir.zig");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const std = @import("std");
const call_resolution = @import("call_resolution.zig");
const codegen = @import("codegen_main.zig");
const List = std.ArrayList;
const ValueBinding = LowerTir.ValueBinding;
const check_pattern_matching = @import("check_pattern_matching.zig");

// ============================
// Context structs
// ============================
const ContinueInfo = union(enum) {
    none,
    range: struct {
        update_block: tir.BlockId,
        idx_value: tir.ValueId,
    },
};

pub const DeferEntry = struct {
    expr: ast.ExprId,
    is_err: bool,
};

pub const LoopCtx = struct {
    label: ast.OptStrId,
    break_block: tir.BlockId,
    continue_block: tir.BlockId,
    join_block: tir.BlockId,
    res_ty: ?types.TypeId,
    has_result: bool,
    res_param: tir.OptValueId,
    continue_info: ContinueInfo,
    defer_len_at_entry: u32,
};

pub const Env = struct {
    map: std.AutoArrayHashMapUnmanaged(ast.StrId, ValueBinding) = .{},
    bindings: List(LowerTir.EnvBindingSnapshot) = .{},
    defers: List(DeferEntry) = .{},
    marks: List(u32) = .{},
    binding_marks: List(u32) = .{},

    pub fn deinit(self: *Env, gpa: std.mem.Allocator) void {
        self.map.deinit(gpa);
        self.bindings.deinit(gpa);
        self.defers.deinit(gpa);
        self.marks.deinit(gpa);
        self.binding_marks.deinit(gpa);
    }

    pub fn bind(self: *Env, gpa: std.mem.Allocator, name: tir.StrId, vb: ValueBinding, builder: *tir.Builder, blk: *tir.Builder.BlockFrame, loc: tir.OptLocId) !void {
        if (self.binding_marks.items.len > 0) {
            try self.bindings.append(gpa, .{ .name = name, .prev = self.map.get(name) });
        }
        try self.map.put(gpa, name, vb);

        if (codegen.enable_debug_info) {
            try blk.instrs.append(gpa, builder.t.instrs.add(.DbgDeclare, .{
                .result = builder.freshValue(),
                .ty = vb.ty,
                .value = vb.value,
                .name = name,
                .loc = loc,
            }));
        }
    }

    pub fn lookup(self: *Env, s: ast.StrId) ?ValueBinding {
        return self.map.get(s);
    }

    pub fn restoreBinding(self: *Env, gpa: std.mem.Allocator, name: ast.StrId, prev: ?ValueBinding) !void {
        if (prev) |val| {
            try self.map.put(gpa, name, val);
        } else {
            _ = self.map.swapRemove(name);
        }
    }

    pub fn pushScope(self: *Env, gpa: std.mem.Allocator) !void {
        try self.marks.append(gpa, @intCast(self.defers.items.len));
        try self.binding_marks.append(gpa, @intCast(self.bindings.items.len));
    }

    pub fn popScope(self: *Env, gpa: std.mem.Allocator) u32 {
        if (self.marks.items.len == 0) return 0;
        const mark = self.marks.pop().?;
        self.defers.items.len = mark;

        if (self.binding_marks.pop()) |bmark| {
            var i: usize = self.bindings.items.len;
            const items = self.bindings.items;
            // Restore bindings in reverse order
            while (i > bmark) : (i -= 1) {
                const entry = items[i - 1];
                if (entry.prev) |val| {
                    self.map.put(gpa, entry.name, val) catch {};
                } else {
                    _ = self.map.swapRemove(entry.name);
                }
            }
            self.bindings.items.len = bmark;
        }
        return mark;
    }
};

pub fn runNormalDefersFrom(self: *LowerTir, ctx: *LowerTir.LowerContext, a: *ast.Ast, env: *Env, f: *tir.Builder.FunctionFrame, blk: *tir.Builder.BlockFrame, from: u32) !void {
    var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
    const items = env.defers.items;
    while (j >= 0 and @as(u32, @intCast(j)) >= from) : (j -= 1) {
        const ent = items[@intCast(j)];
        if (!ent.is_err) _ = try self.lowerExpr(ctx, a, env, f, blk, ent.expr, null, .rvalue);
    }
    env.defers.items.len = from;
}

pub fn hasErrDefersFrom(_: *LowerTir, env: *Env, from: u32) bool {
    var i: usize = env.defers.items.len;
    const items = env.defers.items;
    while (i > from) : (i -= 1) {
        if (items[i - 1].is_err) return true;
    }
    return false;
}

pub fn emitDefers(self: *LowerTir, ctx: *LowerTir.LowerContext, a: *ast.Ast, env: *Env, f: *tir.Builder.FunctionFrame, blk: *tir.Builder.BlockFrame, slice: []const DeferEntry, want_err: bool) !void {
    var j: isize = @as(isize, @intCast(slice.len)) - 1;
    while (j >= 0) : (j -= 1) {
        const ent = slice[@intCast(j)];
        if (ent.is_err == want_err) _ = try self.lowerExpr(ctx, a, env, f, blk, ent.expr, null, .rvalue);
    }
}

fn runDefersForLoopExit(self: *LowerTir, ctx: *LowerTir.LowerContext, a: *ast.Ast, env: *Env, f: *tir.Builder.FunctionFrame, blk: *tir.Builder.BlockFrame, lc: LoopCtx) !void {
    var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
    const items = env.defers.items;
    while (j >= 0 and @as(u32, @intCast(j)) >= lc.defer_len_at_entry) : (j -= 1) {
        const ent = items[@intCast(j)];
        if (!ent.is_err) _ = try self.lowerExpr(ctx, a, env, f, blk, ent.expr, null, .rvalue);
    }
    env.defers.items.len = lc.defer_len_at_entry;
}

fn loopCtxForLabel(_: *LowerTir, ctx: *LowerTir.LowerContext, want: ast.OptStrId) ?*LoopCtx {
    if (ctx.loop_stack.items.len == 0) return null;
    var i: isize = @as(isize, @intCast(ctx.loop_stack.items.len)) - 1;
    const items = ctx.loop_stack.items;
    while (i >= 0) : (i -= 1) {
        const lc = &items[@intCast(i)];
        if (want.isNone() or (!lc.label.isNone() and lc.label.unwrap().eq(want.unwrap()))) return lc;
    }
    return null;
}

pub fn lowerIf(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.If, id);
    const loc = LowerTir.optLoc(a, id);
    const ts = self.context.type_store;

    // Evaluate Condition
    const cond_ty = self.getExprType(ctx, a, row.cond);
    const cond_kind = ts.getKind(cond_ty);
    const cond_v = try self.lowerExpr(ctx, a, env, f, blk, row.cond, ts.tBool(), .rvalue);

    const out_ty_guess = expected_ty orelse self.getExprType(ctx, a, id);
    const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

    // If lowering would introduce control-flow with tensor/simd results, prefer select.
    // This is primarily for Triton/GPU targets where divergence is expensive and
    // execution is masked. For CPU, we must avoid eager evaluation of side effects.
    const is_triton = f.builder.t.funcs.Function.get(f.id).is_triton_fn;
    const out_kind = ts.getKind(out_ty_guess);
    const wants_select = is_triton and produce_value and (out_kind == .Tensor or out_kind == .Simd);

    if (wants_select) {
        const cond_for_select = blk_sel: {
            if (cond_kind == .Tensor or cond_kind == .Simd) break :blk_sel cond_v;

            const bool_cond = self.forceLocalCond(blk, cond_v, loc);
            if (out_kind == .Tensor) {
                const ten = ts.get(.Tensor, out_ty_guess);
                const cond_t = ts.mkTensor(ts.tBool(), ten.dims[0..ten.rank]);
                break :blk_sel blk.builder.tirValue(.Broadcast, blk, cond_t, loc, .{ .value = bool_cond });
            }
            if (out_kind == .Simd) {
                const simd = ts.get(.Simd, out_ty_guess);
                const cond_t = ts.mkSimd(ts.tBool(), simd.lanes);
                break :blk_sel blk.builder.tirValue(.Broadcast, blk, cond_t, loc, .{ .value = bool_cond });
            }
            break :blk_sel bool_cond;
        };

        var v_then = try self.lowerBlockExprValue(ctx, a, env, f, blk, row.then_block, out_ty_guess);
        if (expected_ty) |want| v_then = self.emitCoerce(blk, v_then, self.getExprType(ctx, a, row.then_block), want, loc);

        var v_else: tir.ValueId = undefined;
        if (!row.else_block.isNone()) {
            v_else = try self.lowerBlockExprValue(ctx, a, env, f, blk, row.else_block.unwrap(), out_ty_guess);
            if (expected_ty) |want| v_else = self.emitCoerce(blk, v_else, self.getExprType(ctx, a, row.else_block.unwrap()), want, loc);
        } else {
            v_else = self.safeUndef(blk, out_ty_guess, loc);
        }

        return blk.builder.tirValue(.Select, blk, out_ty_guess, loc, .{
            .cond = cond_for_select,
            .then_value = v_then,
            .else_value = v_else,
        });
    }

    // Statement if: try to lower tensor/simd assignment into a select to avoid dominance issues.
    if (is_triton and !produce_value) {
        if (try lowerTensorIfAssignAsSelect(self, ctx, a, env, f, blk, row, cond_v, cond_kind, loc)) {
            return self.safeUndef(blk, ts.tAny(), loc);
        }
    }

    var then_blk = try f.builder.beginBlock(f);
    var else_blk = try f.builder.beginBlock(f);
    const br_cond = self.forceLocalCond(blk, cond_v, loc);
    try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{}, loc);
    try f.builder.endBlock(f, blk.*);

    if (produce_value) {
        var join_blk = try f.builder.beginBlock(f);
        const res_param = try f.builder.addBlockParam(&join_blk, null, out_ty_guess);

        // Then Branch (Value)
        if (then_blk.term.isNone()) {
            var v_then = try self.lowerBlockExprValue(ctx, a, env, f, &then_blk, row.then_block, out_ty_guess);
            if (expected_ty) |want| v_then = self.emitCoerce(&then_blk, v_then, self.getExprType(ctx, a, row.then_block), want, loc);
            try f.builder.br(&then_blk, join_blk.id, &.{v_then}, loc);
        }
        try f.builder.endBlock(f, then_blk);

        // Else Branch (Value)
        if (!row.else_block.isNone()) {
            if (else_blk.term.isNone()) {
                var v_else = try self.lowerBlockExprValue(ctx, a, env, f, &else_blk, row.else_block.unwrap(), out_ty_guess);
                if (expected_ty) |want| v_else = self.emitCoerce(&else_blk, v_else, self.getExprType(ctx, a, row.else_block.unwrap()), want, loc);
                try f.builder.br(&else_blk, join_blk.id, &.{v_else}, loc);
            }
        } else {
            if (else_blk.term.isNone()) try f.builder.br(&else_blk, join_blk.id, &.{self.safeUndef(&else_blk, out_ty_guess, loc)}, loc);
        }
        try f.builder.endBlock(f, else_blk);

        blk.* = join_blk;
        return res_param;
    } else {
        const exit_blk = try f.builder.beginBlock(f);

        // Then Branch (Statement: Use Scope)
        try env.pushScope(self.gpa);
        try self.lowerExprAsStmtList(ctx, a, env, f, &then_blk, row.then_block);
        _ = env.popScope(self.gpa);
        if (then_blk.term.isNone()) try f.builder.br(&then_blk, exit_blk.id, &.{}, loc);
        try f.builder.endBlock(f, then_blk);

        // Else Branch (Statement: Use Scope)
        try env.pushScope(self.gpa);
        if (!row.else_block.isNone()) try self.lowerExprAsStmtList(ctx, a, env, f, &else_blk, row.else_block.unwrap());
        _ = env.popScope(self.gpa);
        if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{}, loc);
        try f.builder.endBlock(f, else_blk);

        blk.* = exit_blk;
        return self.safeUndef(blk, self.context.type_store.tAny(), loc);
    }
}

fn lowerTensorIfAssignAsSelect(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    row: ast.Rows.If,
    cond_v: tir.ValueId,
    cond_kind: types.TypeKind,
    loc: tir.OptLocId,
) !bool {
    const ts = self.context.type_store;

    const assign_then = extractAssignBlockInfo(a, row.then_block) orelse return false;
    const assign_else = if (!row.else_block.isNone()) extractAssignBlockInfo(a, row.else_block.unwrap()) else null;

    if (assign_else) |ae| {
        if (!ae.name.eq(assign_then.name)) return false;
    }

    const var_ty = resolveIdentType(self, a, env, assign_then.ident_expr) orelse return false;
    const var_kind = ts.getKind(var_ty);
    if (var_kind != .Tensor and var_kind != .Simd) return false;

    const ptr = try self.lowerIdentAddrByName(a, env, f, blk, assign_then.name, var_ty, var_ty, loc);
    const cur_val = try self.lowerIdent(ctx, a, env, f, blk, assign_then.ident_expr, var_ty, .rvalue);
    try env.pushScope(self.gpa);
    defer _ = env.popScope(self.gpa);
    for (assign_then.pre_stmts) |sid| try self.lowerStmt(ctx, a, env, f, blk, sid);
    var then_val = try self.lowerExpr(ctx, a, env, f, blk, assign_then.rhs, var_ty, .rvalue);
    if (!self.getExprType(ctx, a, assign_then.rhs).eq(var_ty)) {
        then_val = self.emitCoerce(blk, then_val, self.getExprType(ctx, a, assign_then.rhs), var_ty, loc);
    }

    var else_val: tir.ValueId = cur_val;
    if (assign_else) |ae| {
        try env.pushScope(self.gpa);
        defer _ = env.popScope(self.gpa);
        for (ae.pre_stmts) |sid| try self.lowerStmt(ctx, a, env, f, blk, sid);
        else_val = try self.lowerExpr(ctx, a, env, f, blk, ae.rhs, var_ty, .rvalue);
        if (!self.getExprType(ctx, a, ae.rhs).eq(var_ty)) {
            else_val = self.emitCoerce(blk, else_val, self.getExprType(ctx, a, ae.rhs), var_ty, loc);
        }
    }

    const cond_for_select = blk_sel: {
        if (cond_kind == .Tensor or cond_kind == .Simd) break :blk_sel cond_v;

        const bool_cond = self.forceLocalCond(blk, cond_v, loc);
        if (var_kind == .Tensor) {
            const ten = ts.get(.Tensor, var_ty);
            const cond_t = ts.mkTensor(ts.tBool(), ten.dims[0..ten.rank]);
            break :blk_sel blk.builder.tirValue(.Broadcast, blk, cond_t, loc, .{ .value = bool_cond });
        }
        if (var_kind == .Simd) {
            const simd = ts.get(.Simd, var_ty);
            const cond_t = ts.mkSimd(ts.tBool(), simd.lanes);
            break :blk_sel blk.builder.tirValue(.Broadcast, blk, cond_t, loc, .{ .value = bool_cond });
        }
        break :blk_sel bool_cond;
    };

    const sel = blk.builder.tirValue(.Select, blk, var_ty, loc, .{
        .cond = cond_for_select,
        .then_value = then_val,
        .else_value = else_val,
    });
    _ = f.builder.tirValue(.Store, blk, var_ty, loc, .{ .ptr = ptr, .value = sel, .@"align" = 0 });
    return true;
}

fn resolveIdentType(_: *LowerTir, a: *ast.Ast, env: *Env, ident_expr: ast.ExprId) ?types.TypeId {
    const row = a.exprs.get(.Ident, ident_expr);
    if (env.lookup(row.name)) |bnd| return bnd.ty;
    if (call_resolution.findDeclId(a, row.name)) |did| {
        return LowerTir.getDeclType(a, did);
    }
    const raw = ident_expr.toRaw();
    if (raw < a.type_info.expr_types.items.len) {
        return a.type_info.expr_types.items[raw];
    }
    return null;
}

fn extractAssignBlockInfo(a: *ast.Ast, expr: ast.ExprId) ?struct { name: ast.StrId, ident_expr: ast.ExprId, rhs: ast.ExprId, pre_stmts: []const ast.StmtId } {
    if (a.kind(expr) != .Block) return null;
    const b = a.exprs.get(.Block, expr);
    const stmts = a.stmts.stmt_pool.slice(b.items);
    if (stmts.len == 0) return null;
    const last = stmts[stmts.len - 1];
    if (a.kind(last) != .Assign) return null;
    const as = a.stmts.get(.Assign, last);
    switch (as.left) {
        .expr => |left_expr| {
            if (a.kind(left_expr) != .Ident) return null;
            const name = a.exprs.get(.Ident, left_expr).name;
            var i: usize = 0;
            while (i + 1 < stmts.len) : (i += 1) {
                if (a.kind(stmts[i]) != .Decl) return null;
            }
            return .{ .name = name, .ident_expr = left_expr, .rhs = as.right, .pre_stmts = stmts[0 .. stmts.len - 1] };
        },
        else => return null,
    }
}

pub fn lowerBreak(self: *LowerTir, ctx: *LowerTir.LowerContext, a: *ast.Ast, env: *Env, f: *tir.Builder.FunctionFrame, blk: *tir.Builder.BlockFrame, sid: ast.StmtId) !void {
    const br = a.stmts.get(.Break, sid);
    try lowerBreakCommon(self, ctx, a, env, f, blk, br.label, br.value, LowerTir.optLoc(a, sid));
}

pub fn lowerBreakCommon(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    label: ast.OptStrId,
    value: ast.OptExprId,
    loc: tir.OptLocId,
) !void {
    var i: isize = @as(isize, @intCast(ctx.loop_stack.items.len)) - 1;
    const loop_items = ctx.loop_stack.items;
    const strs = a.exprs.strs;

    while (i >= 0) : (i -= 1) {
        const lc = loop_items[@intCast(i)];
        if (label.isNone() or (!lc.label.isNone() and std.mem.eql(u8, strs.get(lc.label.unwrap()), strs.get(label.unwrap())))) {
            try runDefersForLoopExit(self, ctx, a, env, f, blk, lc);
            if (lc.has_result) {
                const v = if (!value.isNone()) try self.lowerExpr(ctx, a, env, f, blk, value.unwrap(), lc.res_ty, .rvalue) else self.safeUndef(blk, lc.res_ty.?, loc);
                try f.builder.br(blk, lc.join_block, &.{v}, loc);
            } else {
                try f.builder.br(blk, lc.break_block, &.{}, loc);
            }
            return;
        }
    }
    return error.LoweringBug;
}

pub fn lowerContinue(self: *LowerTir, ctx: *LowerTir.LowerContext, a: *ast.Ast, env: *Env, f: *tir.Builder.FunctionFrame, blk: *tir.Builder.BlockFrame, sid: ast.StmtId) !void {
    try lowerContinueCommon(self, ctx, a, env, f, blk, a.stmts.get(.Continue, sid).label, LowerTir.optLoc(a, sid));
}

pub fn lowerContinueCommon(self: *LowerTir, ctx: *LowerTir.LowerContext, a: *ast.Ast, env: *Env, f: *tir.Builder.FunctionFrame, blk: *tir.Builder.BlockFrame, label: ast.OptStrId, loc: tir.OptLocId) !void {
    const lc = loopCtxForLabel(self, ctx, label) orelse return error.LoweringBug;
    try runDefersForLoopExit(self, ctx, a, env, f, blk, lc.*);
    switch (lc.continue_info) {
        .none => try f.builder.br(blk, lc.continue_block, &.{}, loc),
        .range => |info| try f.builder.br(blk, info.update_block, &.{info.idx_value}, loc),
    }
}

fn typeIdForName(ts: *types.TypeStore, name: ast.StrId) ?types.TypeId {
    const s = ts.strs.get(name);
    // Optimized length switch
    switch (s.len) {
        2 => {
            if (std.mem.eql(u8, s, "i8")) return ts.tI8();
            if (std.mem.eql(u8, s, "u8")) return ts.tU8();
        },
        3 => {
            if (std.mem.eql(u8, s, "i16")) return ts.tI16();
            if (std.mem.eql(u8, s, "u16")) return ts.tU16();
            if (std.mem.eql(u8, s, "i32")) return ts.tI32();
            if (std.mem.eql(u8, s, "u32")) return ts.tU32();
            if (std.mem.eql(u8, s, "i64")) return ts.tI64();
            if (std.mem.eql(u8, s, "u64")) return ts.tU64();
            if (std.mem.eql(u8, s, "f32")) return ts.tF32();
            if (std.mem.eql(u8, s, "f64")) return ts.tF64();
            if (std.mem.eql(u8, s, "any")) return ts.tAny();
        },
        4 => {
            if (std.mem.eql(u8, s, "bool")) return ts.tBool();
            if (std.mem.eql(u8, s, "char")) return ts.tU32();
            if (std.mem.eql(u8, s, "type")) return ts.mkTypeType(ts.tAny());
        },
        5 => if (std.mem.eql(u8, s, "usize")) return ts.tUsize(),
        6 => if (std.mem.eql(u8, s, "string")) return ts.tString(),
        else => {},
    }
    return null;
}

pub fn matchPattern(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    pid: ast.PatternId,
    scrut: tir.ValueId,
    scrut_ty: types.TypeId,
    loc: tir.OptLocId,
) !tir.ValueId {
    const ts = self.context.type_store;
    const t_bool = ts.tBool();

    switch (a.kind(pid)) {
        .Wildcard => return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = true }),
        .Binding => {
            const br = a.pats.get(.Binding, pid);
            if (ts.getKind(scrut_ty) == .TypeType) {
                if (typeIdForName(ts, br.name)) |want_ty| {
                    const want = f.builder.tirValue(.ConstInt, blk, scrut_ty, loc, .{ .value = @as(u64, @intCast(want_ty.toRaw())) });
                    return blk.builder.binBool(blk, .CmpEq, scrut, want, loc);
                }
            }
            return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = true });
        },
        .Literal => {
            const pr = a.pats.get(.Literal, pid);
            if (a.kind(pr.expr) == .Range) {
                const range = a.exprs.get(.Range, pr.expr);
                return matchRangeBounds(self, ctx, a, env, f, blk, range.start, range.end, range.inclusive_right, scrut, scrut_ty, loc);
            }
            const litv = try self.lowerExpr(ctx, a, env, f, blk, pr.expr, scrut_ty, .rvalue);
            if (ts.getKind(scrut_ty) == .String) {
                return try self.emitStringEq(f, blk, scrut, litv, loc, true);
            }
            return blk.builder.binBool(blk, .CmpEq, scrut, litv, loc);
        },
        .VariantTuple => {
            const vt = a.pats.get(.VariantTuple, pid);
            const segs = a.pats.seg_pool.slice(vt.path);
            if (segs.len > 0) {
                const last = a.pats.PathSeg.get(segs[segs.len - 1]);
                if (self.tagIndexForCase(scrut_ty, last.name)) |idx| {
                    const tag = blk.builder.extractField(blk, ts.tI32(), scrut, 0, loc);
                    const want = f.builder.tirValue(.ConstInt, blk, ts.tI32(), loc, .{ .value = @as(u64, @intCast(idx)) });
                    return blk.builder.binBool(blk, .CmpEq, tag, want, loc);
                }
            }
            return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = false });
        },
        .At => return try matchPattern(self, ctx, a, env, f, blk, a.pats.get(.At, pid).pattern, scrut, scrut_ty, loc),
        .VariantStruct => {
            const vs = a.pats.get(.VariantStruct, pid);
            if (ts.getKind(scrut_ty) == .Struct) {
                const pat_fields = a.pats.field_pool.slice(vs.fields);
                const value_fields = ts.field_pool.slice(ts.get(.Struct, scrut_ty).fields);
                var all_match = blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = true });

                for (pat_fields) |pat_field_id| {
                    const pat_field = a.pats.StructField.get(pat_field_id);
                    var found = false;
                    for (value_fields, 0..) |vf_id, j| {
                        const val_field = ts.Field.get(vf_id);
                        if (pat_field.name.eq(val_field.name)) {
                            const field_val = blk.builder.extractField(blk, val_field.ty, scrut, @intCast(j), loc);
                            const field_match = try matchPattern(self, ctx, a, env, f, blk, pat_field.pattern, field_val, val_field.ty, loc);
                            all_match = blk.builder.binBool(blk, .LogicalAnd, all_match, field_match, loc);
                            found = true;
                            break;
                        }
                    }
                    if (!found) return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = false });
                }
                return all_match;
            }
            const segs = a.pats.seg_pool.slice(vs.path);
            if (segs.len > 0) {
                const last = a.pats.PathSeg.get(segs[segs.len - 1]);
                if (self.tagIndexForCase(scrut_ty, last.name)) |idx| {
                    const tag = blk.builder.extractField(blk, ts.tI32(), scrut, 0, loc);
                    const want = f.builder.tirValue(.ConstInt, blk, ts.tI32(), loc, .{ .value = @as(u64, @intCast(idx)) });
                    return blk.builder.binBool(blk, .CmpEq, tag, want, loc);
                }
            }
            return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = false });
        },
        .Path => {
            const pp = a.pats.get(.Path, pid);
            const segs = a.pats.seg_pool.slice(pp.segments);
            if (segs.len > 0) {
                const last = a.pats.PathSeg.get(segs[segs.len - 1]);
                if (self.enumMemberValue(scrut_ty, last.name)) |val| {
                    return blk.builder.binBool(blk, .CmpEq, scrut, f.builder.tirValue(.ConstInt, blk, scrut_ty, loc, .{ .value = val }), loc);
                }
                if (self.tagIndexForCase(scrut_ty, last.name)) |idx| {
                    const tag = blk.builder.extractField(blk, ts.tI32(), scrut, 0, loc);
                    const want = f.builder.tirValue(.ConstInt, blk, ts.tI32(), loc, .{ .value = @as(u64, @intCast(idx)) });
                    return blk.builder.binBool(blk, .CmpEq, tag, want, loc);
                }
            }
            return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = false });
        },
        .Slice => {
            const sl = a.pats.get(.Slice, pid);
            const elems = a.pats.pat_pool.slice(sl.elems);
            const usize_ty = ts.tUsize();

            var len_val: tir.ValueId = undefined;
            var elem_ty: types.TypeId = undefined;

            if (ts.getKind(scrut_ty) == .Array) {
                const arr = ts.get(.Array, scrut_ty);
                len_val = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = arr.len });
                elem_ty = arr.elem;
            } else {
                len_val = blk.builder.extractFieldNamed(blk, usize_ty, scrut, f.builder.intern("len"), loc);
                elem_ty = ts.get(.Slice, scrut_ty).elem;
            }

            const req_val = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = elems.len });
            const len_ok = if (sl.has_rest) blk.builder.binBool(blk, .CmpGe, len_val, req_val, loc) else blk.builder.binBool(blk, .CmpEq, len_val, req_val, loc);
            var match_accum = len_ok;

            for (elems, 0..) |pat_elem, i| {
                const idx = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = @as(u64, @intCast(i)) });
                const elem_val = blk.builder.indexOp(blk, elem_ty, scrut, idx, .none());
                const sub_match = try matchPattern(self, ctx, a, env, f, blk, pat_elem, elem_val, elem_ty, loc);
                match_accum = blk.builder.binBool(blk, .LogicalAnd, match_accum, sub_match, loc);
            }
            return match_accum;
        },
        .Or => {
            const alts = a.pats.pat_pool.slice(a.pats.get(.Or, pid).alts);
            if (alts.len == 0) return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = false });
            var result = try matchPattern(self, ctx, a, env, f, blk, alts[0], scrut, scrut_ty, loc);
            for (alts[1..]) |alt| {
                result = blk.builder.binBool(blk, .LogicalOr, result, try matchPattern(self, ctx, a, env, f, blk, alt, scrut, scrut_ty, loc), loc);
            }
            return result;
        },
        .Range => {
            const r = a.pats.get(.Range, pid);
            return matchRangeBounds(self, ctx, a, env, f, blk, r.start, r.end, r.inclusive_right, scrut, scrut_ty, loc);
        },
        .Tuple => {
            if (ts.getKind(scrut_ty) != .Tuple) return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = false });
            const elems = a.pats.pat_pool.slice(a.pats.get(.Tuple, pid).elems);
            const val_elems = ts.type_pool.slice(ts.get(.Tuple, scrut_ty).elems);
            if (elems.len != val_elems.len) return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = false });

            var all_match = blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = true });
            for (elems, 0..) |pat, i| {
                const eval = blk.builder.extractField(blk, val_elems[i], scrut, @intCast(i), loc);
                all_match = blk.builder.binBool(blk, .LogicalAnd, all_match, try matchPattern(self, ctx, a, env, f, blk, pat, eval, val_elems[i], loc), loc);
            }
            return all_match;
        },
        .Struct => {
            if (ts.getKind(scrut_ty) != .Struct) return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = false });
            const fields = a.pats.field_pool.slice(a.pats.get(.Struct, pid).fields);
            const val_fields = ts.field_pool.slice(ts.get(.Struct, scrut_ty).fields);
            var all_match = blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = true });

            for (fields) |fid| {
                const pf = a.pats.StructField.get(fid);
                var found = false;
                for (val_fields, 0..) |vfid, j| {
                    const vf = ts.Field.get(vfid);
                    if (pf.name.eq(vf.name)) {
                        const eval = blk.builder.extractField(blk, vf.ty, scrut, @intCast(j), loc);
                        all_match = blk.builder.binBool(blk, .LogicalAnd, all_match, try matchPattern(self, ctx, a, env, f, blk, pf.pattern, eval, vf.ty, loc), loc);
                        found = true;
                        break;
                    }
                }
                if (!found) return blk.builder.tirValue(.ConstBool, blk, t_bool, loc, .{ .value = false });
            }
            return all_match;
        },
    }
}

fn matchRangeBounds(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    start: ast.OptExprId,
    end: ast.OptExprId,
    inclusive_right: bool,
    scrut: tir.ValueId,
    scrut_ty: types.TypeId,
    loc: tir.OptLocId,
) !tir.ValueId {
    var result = blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = true });

    if (!start.isNone()) {
        const val = try self.lowerExpr(ctx, a, env, f, blk, start.unwrap(), scrut_ty, .rvalue);
        result = blk.builder.binBool(blk, .LogicalAnd, result, blk.builder.binBool(blk, .CmpGe, scrut, val, loc), loc);
    }
    if (!end.isNone()) {
        const val = try self.lowerExpr(ctx, a, env, f, blk, end.unwrap(), scrut_ty, .rvalue);
        const upper_ok = if (inclusive_right)
            blk.builder.binBool(blk, .CmpLe, scrut, val, loc)
        else
            blk.builder.binBool(blk, .CmpLt, scrut, val, loc);
        result = blk.builder.binBool(blk, .LogicalAnd, result, upper_ok, loc);
    }
    return result;
}

pub fn lowerOptionalUnwrap(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.OptionalUnwrap, id);
    const opt_ty = self.getExprType(ctx, a, row.expr);
    const ts = self.context.type_store;
    if (ts.getKind(opt_ty) != .Optional) return error.LoweringBug;

    const loc = LowerTir.optLoc(a, id);
    const opt_val = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);

    var then_blk = try f.builder.beginBlock(f);
    var none_blk = try f.builder.beginBlock(f);
    var join_blk = try f.builder.beginBlock(f);

    const elem_ty = ts.get(.Optional, opt_ty).elem;
    const then_param = try f.builder.addBlockParam(&then_blk, null, elem_ty);
    const res_param = try f.builder.addBlockParam(&join_blk, null, expected_ty orelse self.getExprType(ctx, a, id));

    try f.builder.condBr(blk, self.optionalFlag(blk, opt_ty, opt_val, loc), then_blk.id, &.{self.optionalPayload(blk, opt_ty, opt_val, loc)}, none_blk.id, &.{}, loc);
    try f.builder.endBlock(f, blk.*);

    var unwrapped = then_param;
    if (expected_ty) |want| unwrapped = self.emitCoerce(&then_blk, unwrapped, elem_ty, want, loc);
    try f.builder.br(&then_blk, join_blk.id, &.{unwrapped}, loc);
    try f.builder.endBlock(f, then_blk);

    const panic_str = none_blk.builder.tirValue(.ConstString, &none_blk, ts.tString(), loc, .{ .text = f.builder.intern("unwrap of null optional") });
    _ = none_blk.builder.call(&none_blk, ts.tVoid(), f.builder.intern("rt_panic"), &.{ none_blk.builder.extractField(&none_blk, ts.mkPtr(ts.tU8(), true), panic_str, 0, loc), none_blk.builder.extractField(&none_blk, ts.tUsize(), panic_str, 1, loc) }, loc);
    try f.builder.setUnreachable(&none_blk, loc);
    try f.builder.endBlock(f, none_blk);

    blk.* = join_blk;
    return res_param;
}

pub fn lowerErrUnwrap(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.ErrUnwrap, id);
    const ts = self.context.type_store;
    const es_ty = self.getExprType(ctx, a, row.expr);
    if (ts.getKind(es_ty) != .ErrorSet) return error.LoweringBug;
    const es = ts.get(.ErrorSet, es_ty);
    const loc = LowerTir.optLoc(a, id);
    const expr_loc = LowerTir.optLoc(a, row.expr);

    const es_val = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    const tag_ty = ts.tI32();
    const is_ok = blk.builder.binBool(blk, .CmpEq, blk.builder.extractField(blk, tag_ty, es_val, 0, expr_loc), blk.builder.tirValue(.ConstInt, blk, tag_ty, expr_loc, .{ .value = 0 }), expr_loc);

    var then_blk = try f.builder.beginBlock(f);
    var else_blk = try f.builder.beginBlock(f);
    var join_blk = try f.builder.beginBlock(f);

    const res_ty = expected_ty orelse self.getExprType(ctx, a, id);
    try self.noteExprType(ctx, id, res_ty);

    const value_is_void = self.isVoid(es.value_ty);
    const res_param = if (!value_is_void) try f.builder.addBlockParam(&join_blk, null, res_ty) else undefined;

    try f.builder.condBr(blk, self.forceLocalCond(blk, is_ok, expr_loc), then_blk.id, &.{}, else_blk.id, &.{}, loc);
    try f.builder.endBlock(f, blk.*);

    // Ok path
    if (value_is_void) {
        try f.builder.br(&then_blk, join_blk.id, &.{}, loc);
    } else {
        const payload_union_ty = ts.mkUnion(&.{ .{ .name = f.builder.intern("Ok"), .ty = es.value_ty }, .{ .name = f.builder.intern("Err"), .ty = es.error_ty } });
        var ok_val = then_blk.builder.tirValue(.UnionField, &then_blk, es.value_ty, loc, .{ .base = then_blk.builder.extractField(&then_blk, payload_union_ty, es_val, 1, expr_loc), .field_index = 0 });
        if (expected_ty) |want| ok_val = self.emitCoerce(&then_blk, ok_val, es.value_ty, want, loc);
        try f.builder.br(&then_blk, join_blk.id, &.{ok_val}, loc);
    }
    try f.builder.endBlock(f, then_blk);

    // Err path
    const expect = f.builder.t.funcs.Function.get(f.id).result;
    const ret_val = if (!self.isVoid(expect) and !expect.eq(es_ty)) self.emitCoerce(&else_blk, es_val, es_ty, expect, loc) else es_val;
    try f.builder.setReturnVal(&else_blk, ret_val, loc);
    try f.builder.endBlock(f, else_blk);

    blk.* = join_blk;
    return if (value_is_void) self.safeUndef(&join_blk, ts.tBool(), loc) else res_param;
}

fn isAllIntMatch(_: *LowerTir, a: *ast.Ast, arms_slice: []const ast.MatchArmId, values_buf: []u64) bool {
    if (arms_slice.len != values_buf.len) return false;
    for (arms_slice, 0..) |arm_id, i| {
        const arm = a.exprs.MatchArm.get(arm_id);
        if (!arm.guard.isNone() or a.kind(arm.pattern) != .Literal) return false;
        const plit = a.pats.get(.Literal, arm.pattern);
        if (a.kind(plit.expr) != .Literal) return false;
        const lit = a.exprs.get(.Literal, plit.expr);
        if (lit.kind != .int) return false;
        const info = if (lit.data == .int) lit.data.int else return false;
        if (!info.valid) return false;
        values_buf[i] = std.math.cast(u64, info.value) orelse return false;
    }
    return true;
}

pub fn lowerMatch(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Match, id);
    const loc = LowerTir.optLoc(a, id);
    const scrut = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);

    const out_ty_guess = expected_ty orelse self.getExprType(ctx, a, id);
    const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess) and self.context.type_store.getKind(out_ty_guess) != .Any;
    const res_ty = out_ty_guess;

    if (produce_value) {
        var join_blk = try f.builder.beginBlock(f);
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
        const arms = a.exprs.arm_pool.slice(row.arms);

        if (arms.len == 0) {
            try f.builder.br(blk, join_blk.id, &.{self.safeUndef(blk, res_ty, loc)}, loc);
            blk.* = join_blk;
            return res_param;
        }

        const values = try self.gpa.alloc(u64, arms.len);
        defer self.gpa.free(values);

        if (isAllIntMatch(self, a, arms, values)) {
            var case_dests = try self.gpa.alloc(tir.Builder.SwitchDest, arms.len);
            defer self.gpa.free(case_dests);
            var bodies = try self.gpa.alloc(@TypeOf(try f.builder.beginBlock(f)), arms.len);
            defer self.gpa.free(bodies);

            var default_blk = try f.builder.beginBlock(f);
            for (bodies) |*b| b.* = try f.builder.beginBlock(f);
            for (bodies, 0..) |b, i| case_dests[i] = .{ .dest = b.id, .args = &.{} };

            try f.builder.switchInt(blk, scrut, values, case_dests, default_blk.id, &.{}, loc);

            for (bodies, 0..) |b, i| {
                const arm = a.exprs.MatchArm.get(arms[i]);
                try self.lowerExprAsStmtList(ctx, a, env, f, &bodies[i], arm.body);
                if (b.term.isNone()) {
                    var v = try self.lowerBlockExprValue(ctx, a, env, f, &bodies[i], arm.body, res_ty);
                    v = self.emitCoerce(&bodies[i], v, self.getExprType(ctx, a, arm.body), res_ty, loc);
                    try f.builder.br(&bodies[i], join_blk.id, &.{v}, loc);
                }
                try f.builder.endBlock(f, b);
            }

            try f.builder.br(&default_blk, join_blk.id, &.{self.safeUndef(&default_blk, res_ty, loc)}, loc);
            try f.builder.endBlock(f, default_blk);

            blk.* = join_blk;
            return res_param;
        }

        // Chained tests (Value)
        const binding_names = &ctx.pattern_binding_names;
        const saved = &ctx.binding_snapshots;
        var cur = blk.*;
        const scrut_ty = self.getExprType(ctx, a, row.expr);

        for (arms, 0..) |arm_id, j| {
            binding_names.clearRetainingCapacity();
            saved.clearRetainingCapacity();
            const arm = a.exprs.MatchArm.get(arm_id);
            var test_blk = try f.builder.beginBlock(f);
            var body_blk = try f.builder.beginBlock(f);
            const next_blk = if (j + 1 < arms.len) try f.builder.beginBlock(f) else join_blk;
            const else_args = if (next_blk.id.eq(join_blk.id)) &.{self.safeUndef(&test_blk, res_ty, loc)} else &.{};

            try f.builder.br(&cur, test_blk.id, &.{}, loc);
            try f.builder.endBlock(f, cur);

            const ok = try matchPattern(self, ctx, a, env, f, &test_blk, arm.pattern, scrut, scrut_ty, loc);
            try check_pattern_matching.collectPatternBindings(self.chk, a, arm.pattern, binding_names);
            try saved.ensureTotalCapacity(self.gpa, binding_names.items.len);
            for (binding_names.items) |name| try saved.append(self.gpa, .{ .name = name, .prev = env.lookup(name) });

            if (!arm.guard.isNone()) {
                var guard_blk = try f.builder.beginBlock(f);
                try f.builder.condBr(&test_blk, self.forceLocalCond(&test_blk, ok, loc), guard_blk.id, &.{}, next_blk.id, else_args, loc);
                try f.builder.endBlock(f, test_blk);

                try bindPattern(self, ctx, a, env, f, &guard_blk, arm.pattern, scrut, scrut_ty);
                const guard_id = arm.guard.unwrap();
                const guard_val = try self.lowerExpr(ctx, a, env, f, &guard_blk, guard_id, self.context.type_store.tBool(), .rvalue);
                try self.restoreBindings(env, saved.items);
                try f.builder.condBr(&guard_blk, self.forceLocalCond(&guard_blk, guard_val, LowerTir.optLoc(a, guard_id)), body_blk.id, &.{}, next_blk.id, else_args, loc);
                try f.builder.endBlock(f, guard_blk);
            } else {
                try f.builder.condBr(&test_blk, self.forceLocalCond(&test_blk, ok, loc), body_blk.id, &.{}, next_blk.id, else_args, loc);
                try f.builder.endBlock(f, test_blk);
            }

            try bindPattern(self, ctx, a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);
            if (body_blk.term.isNone()) {
                var v2 = try self.lowerBlockExprValue(ctx, a, env, f, &body_blk, arm.body, res_ty);
                v2 = self.emitCoerce(&body_blk, v2, self.getExprType(ctx, a, arm.body), res_ty, loc);
                try f.builder.br(&body_blk, join_blk.id, &.{v2}, loc);
            }
            try self.restoreBindings(env, saved.items);
            try f.builder.endBlock(f, body_blk);
            cur = next_blk;
        }

        blk.* = join_blk;
        return res_param;
    } else {
        // Statement path
        const exit_blk = try f.builder.beginBlock(f);
        const arms = a.exprs.arm_pool.slice(row.arms);
        if (arms.len == 0) {
            try f.builder.br(blk, exit_blk.id, &.{}, loc);
            blk.* = exit_blk;
            return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
        }

        const values = try self.gpa.alloc(u64, arms.len);
        defer self.gpa.free(values);
        const scrut_ty = self.getExprType(ctx, a, row.expr);

        if (isAllIntMatch(self, a, arms, values)) {
            var case_dests = try self.gpa.alloc(tir.Builder.SwitchDest, arms.len);
            defer self.gpa.free(case_dests);
            var bodies = try self.gpa.alloc(@TypeOf(try f.builder.beginBlock(f)), arms.len);
            defer self.gpa.free(bodies);

            var default_blk = try f.builder.beginBlock(f);
            for (bodies) |*b| b.* = try f.builder.beginBlock(f);
            for (bodies, 0..) |b, i| case_dests[i] = .{ .dest = b.id, .args = &.{} };

            try f.builder.switchInt(blk, scrut, values, case_dests, default_blk.id, &.{}, loc);

            for (bodies, 0..) |b, i| {
                const arm = a.exprs.MatchArm.get(arms[i]);
                try self.lowerExprAsStmtList(ctx, a, env, f, &bodies[i], arm.body);
                if (b.term.isNone()) try f.builder.br(&bodies[i], exit_blk.id, &.{}, loc);
                try f.builder.endBlock(f, b);
            }
            try f.builder.br(&default_blk, exit_blk.id, &.{}, loc);
            try f.builder.endBlock(f, default_blk);

            blk.* = exit_blk;
            return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
        }

        // Chained tests (Stmt)
        const binding_names = &ctx.pattern_binding_names;
        const saved = &ctx.binding_snapshots;
        var cur = blk.*;

        for (arms, 0..) |arm_id, l| {
            binding_names.clearRetainingCapacity();
            saved.clearRetainingCapacity();
            const arm = a.exprs.MatchArm.get(arm_id);
            var test_blk = try f.builder.beginBlock(f);
            var body_blk = try f.builder.beginBlock(f);
            const next_blk = if (l + 1 < arms.len) try f.builder.beginBlock(f) else exit_blk;

            try f.builder.br(&cur, test_blk.id, &.{}, loc);
            try f.builder.endBlock(f, cur);

            const ok = try matchPattern(self, ctx, a, env, f, &test_blk, arm.pattern, scrut, scrut_ty, loc);

            if (!arm.guard.isNone()) {
                var guard_blk = try f.builder.beginBlock(f);
                try f.builder.condBr(&test_blk, self.forceLocalCond(&test_blk, ok, loc), guard_blk.id, &.{}, next_blk.id, &.{}, loc);
                try f.builder.endBlock(f, test_blk);

                try check_pattern_matching.collectPatternBindings(self.chk, a, arm.pattern, binding_names);
                try saved.ensureTotalCapacity(self.gpa, binding_names.items.len);
                for (binding_names.items) |name| try saved.append(self.gpa, .{ .name = name, .prev = env.lookup(name) });

                try bindPattern(self, ctx, a, env, f, &guard_blk, arm.pattern, scrut, scrut_ty);
                const guard_id = arm.guard.unwrap();
                const guard_val = try self.lowerExpr(ctx, a, env, f, &guard_blk, guard_id, self.context.type_store.tBool(), .rvalue);
                try self.restoreBindings(env, saved.items);
                try f.builder.condBr(&guard_blk, self.forceLocalCond(&guard_blk, guard_val, LowerTir.optLoc(a, guard_id)), body_blk.id, &.{}, next_blk.id, &.{}, loc);
                try f.builder.endBlock(f, guard_blk);
            } else {
                try f.builder.condBr(&test_blk, self.forceLocalCond(&test_blk, ok, loc), body_blk.id, &.{}, next_blk.id, &.{}, loc);
                try f.builder.endBlock(f, test_blk);
            }

            try bindPattern(self, ctx, a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);
            try self.lowerExprAsStmtList(ctx, a, env, f, &body_blk, arm.body);
            if (body_blk.term.isNone()) try f.builder.br(&body_blk, exit_blk.id, &.{}, loc);
            try f.builder.endBlock(f, body_blk);
            cur = next_blk;
        }

        blk.* = exit_blk;
        return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
    }
}

pub fn lowerWhile(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.While, id);
    var header = try f.builder.beginBlock(f);
    var body = try f.builder.beginBlock(f);
    const loc = LowerTir.optLoc(a, id);

    const out_ty_guess = expected_ty orelse self.getExprType(ctx, a, id);
    const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

    var exit_blk = try f.builder.beginBlock(f);
    var join_blk = if (produce_value) try f.builder.beginBlock(f) else exit_blk;
    const res_param = if (produce_value) try f.builder.addBlockParam(&join_blk, null, out_ty_guess) else undefined;

    try f.builder.br(blk, header.id, &.{}, loc);
    try f.builder.endBlock(f, blk.*);

    try ctx.loop_stack.append(self.gpa, .{
        .label = row.label,
        .continue_block = header.id,
        .break_block = exit_blk.id,
        .has_result = produce_value,
        .join_block = join_blk.id,
        .res_param = if (produce_value) .some(res_param) else .none(),
        .res_ty = if (produce_value) out_ty_guess else null,
        .continue_info = .none,
        .defer_len_at_entry = @intCast(env.defers.items.len),
    });

    if (row.is_pattern and !row.pattern.isNone() and !row.cond.isNone()) {
        const subj = try self.lowerExpr(ctx, a, env, f, &header, row.cond.unwrap(), null, .rvalue);
        const subj_ty = self.getExprType(ctx, a, row.cond.unwrap());
        const ok = try matchPattern(self, ctx, a, env, f, &header, row.pattern.unwrap(), subj, subj_ty, loc);
        try f.builder.condBr(&header, self.forceLocalCond(&header, ok, loc), body.id, &.{}, exit_blk.id, &.{}, loc);
        try bindPattern(self, ctx, a, env, f, &body, row.pattern.unwrap(), subj, subj_ty);
    } else {
        const cond_loc = if (!row.cond.isNone()) LowerTir.optLoc(a, row.cond.unwrap()) else loc;
        const cond_v = if (!row.cond.isNone()) try self.lowerExpr(ctx, a, env, f, &header, row.cond.unwrap(), self.context.type_store.tBool(), .rvalue) else f.builder.tirValue(.ConstBool, &header, self.context.type_store.tBool(), cond_loc, .{ .value = true });
        try f.builder.condBr(&header, self.forceLocalCond(&header, cond_v, cond_loc), body.id, &.{}, exit_blk.id, &.{}, loc);
    }

    try self.lowerExprAsStmtList(ctx, a, env, f, &body, row.body);
    if (body.term.isNone()) try f.builder.br(&body, header.id, &.{}, loc);
    try f.builder.endBlock(f, header);
    try f.builder.endBlock(f, body);

    if (produce_value) {
        try f.builder.br(&exit_blk, join_blk.id, &.{self.safeUndef(&exit_blk, out_ty_guess, loc)}, loc);
        try f.builder.endBlock(f, exit_blk);
        blk.* = join_blk;
        return res_param;
    } else {
        blk.* = exit_blk;
        return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
    }
    _ = ctx.loop_stack.pop();
}

fn getIterableLen(self: *LowerTir, blk: *tir.Builder.BlockFrame, iterable_val: tir.ValueId, iter_ty: types.TypeId, idx_ty: types.TypeId, loc: tir.OptLocId) !tir.ValueId {
    return switch (self.context.type_store.getKind(iter_ty)) {
        .Array => blk.builder.tirValue(.ConstInt, blk, idx_ty, loc, .{ .value = @as(u64, @intCast(self.context.type_store.get(.Array, iter_ty).len)) }),
        .Slice, .DynArray => blk.builder.extractField(blk, idx_ty, iterable_val, 1, loc),
        else => error.LoweringBug,
    };
}

pub fn lowerFor(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.For, id);
    const loc = LowerTir.optLoc(a, id);
    const iterable_loc = LowerTir.optLoc(a, row.iterable);

    const out_ty_guess = expected_ty orelse self.getExprType(ctx, a, id);
    const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

    var header = try f.builder.beginBlock(f);
    var body = try f.builder.beginBlock(f);
    var exit_blk = try f.builder.beginBlock(f);
    var join_blk = if (produce_value) try f.builder.beginBlock(f) else exit_blk;
    const res_param = if (produce_value) try f.builder.addBlockParam(&join_blk, null, out_ty_guess) else undefined;

    try ctx.loop_stack.append(self.gpa, .{
        .label = row.label,
        .continue_block = header.id,
        .break_block = exit_blk.id,
        .has_result = produce_value,
        .join_block = join_blk.id,
        .res_param = if (produce_value) .some(res_param) else .none(),
        .res_ty = if (produce_value) out_ty_guess else null,
        .continue_info = .none,
        .defer_len_at_entry = @intCast(env.defers.items.len),
    });

    if (a.kind(row.iterable) == .Range) {
        const rg = a.exprs.get(.Range, row.iterable);
        const start_v = try self.lowerExpr(ctx, a, env, f, blk, rg.start.unwrap(), null, .rvalue);
        const end_v = try self.lowerExpr(ctx, a, env, f, blk, rg.end.unwrap(), null, .rvalue);
        const idx_ty = self.getExprType(ctx, a, rg.start.unwrap());
        const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);

        var update_blk = try f.builder.beginBlock(f);
        const update_param = try f.builder.addBlockParam(&update_blk, null, idx_ty);
        const next_update = update_blk.builder.bin(&update_blk, .Add, idx_ty, update_param, update_blk.builder.tirValue(.ConstInt, &update_blk, idx_ty, loc, .{ .value = 1 }), loc);
        try f.builder.br(&update_blk, header.id, &.{next_update}, loc);
        try f.builder.endBlock(f, update_blk);

        try f.builder.br(blk, header.id, &.{start_v}, loc);
        try f.builder.endBlock(f, blk.*);

        const cond = if (rg.inclusive_right) blk.builder.binBool(&header, .CmpLe, idx_param, end_v, iterable_loc) else blk.builder.binBool(&header, .CmpLt, idx_param, end_v, iterable_loc);
        try f.builder.condBr(&header, self.forceLocalCond(&header, cond, iterable_loc), body.id, &.{}, exit_blk.id, &.{}, loc);

        try bindPattern(self, ctx, a, env, f, &body, row.pattern, idx_param, idx_ty);
        ctx.loop_stack.items[ctx.loop_stack.items.len - 1].continue_info = .{ .range = .{ .update_block = update_blk.id, .idx_value = idx_param } };

        try self.lowerExprAsStmtList(ctx, a, env, f, &body, row.body);
        if (body.term.isNone()) try f.builder.br(&body, update_blk.id, &.{idx_param}, loc);
    } else {
        const arr_v = try self.lowerExpr(ctx, a, env, f, blk, row.iterable, null, .rvalue);
        const idx_ty = self.context.type_store.tUsize();
        const iter_ty = self.getExprType(ctx, a, row.iterable);
        const len_v = try getIterableLen(self, blk, arr_v, iter_ty, idx_ty, iterable_loc);

        const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);
        var update_blk = try f.builder.beginBlock(f);
        const update_param = try f.builder.addBlockParam(&update_blk, null, idx_ty);
        const next_update = update_blk.builder.bin(&update_blk, .Add, idx_ty, update_param, update_blk.builder.tirValue(.ConstInt, &update_blk, idx_ty, loc, .{ .value = 1 }), loc);
        try f.builder.br(&update_blk, header.id, &.{next_update}, loc);
        try f.builder.endBlock(f, update_blk);

        try f.builder.br(blk, header.id, &.{blk.builder.tirValue(.ConstInt, blk, idx_ty, loc, .{ .value = 0 })}, loc);
        try f.builder.endBlock(f, blk.*);

        try f.builder.condBr(&header, self.forceLocalCond(&header, blk.builder.binBool(&header, .CmpLt, idx_param, len_v, iterable_loc), iterable_loc), body.id, &.{}, exit_blk.id, &.{}, loc);

        const ts = self.context.type_store;
        const elem_ty = switch (ts.getKind(iter_ty)) {
            .Array => ts.get(.Array, iter_ty).elem,
            .Slice => ts.get(.Slice, iter_ty).elem,
            .DynArray => ts.get(.DynArray, iter_ty).elem,
            else => ts.tAny(),
        };
        try bindPattern(self, ctx, a, env, f, &body, row.pattern, blk.builder.indexOp(&body, elem_ty, arr_v, idx_param, iterable_loc), elem_ty);

        ctx.loop_stack.items[ctx.loop_stack.items.len - 1].continue_info = .{ .range = .{ .update_block = update_blk.id, .idx_value = idx_param } };

        try self.lowerExprAsStmtList(ctx, a, env, f, &body, row.body);
        if (body.term.isNone()) try f.builder.br(&body, update_blk.id, &.{idx_param}, loc);
    }

    try f.builder.endBlock(f, header);
    try f.builder.endBlock(f, body);

    if (produce_value) {
        try f.builder.br(&exit_blk, join_blk.id, &.{self.safeUndef(&exit_blk, out_ty_guess, loc)}, loc);
        try f.builder.endBlock(f, exit_blk);
        blk.* = join_blk;
        return res_param;
    } else {
        blk.* = exit_blk;
        return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
    }
    _ = ctx.loop_stack.pop();
}

pub fn bindPattern(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    pid: ast.PatternId,
    value: tir.ValueId,
    vty: types.TypeId,
) !void {
    const loc = LowerTir.optLoc(a, pid);
    switch (a.kind(pid)) {
        .Binding => try env.bind(self.gpa, a.pats.get(.Binding, pid).name, .{ .value = value, .ty = vty, .is_slot = false }, f.builder, blk, loc),
        .At => {
            const at = a.pats.get(.At, pid);
            try env.bind(self.gpa, at.binder, .{ .value = value, .ty = vty, .is_slot = false }, f.builder, blk, loc);
            try bindPattern(self, ctx, a, env, f, blk, at.pattern, value, vty);
        },
        .Tuple => {
            const elems = a.pats.pat_pool.slice(a.pats.get(.Tuple, pid).elems);
            const ts = self.context.type_store;
            const elem_tys = if (ts.getKind(vty) == .Tuple) ts.type_pool.slice(ts.get(.Tuple, vty).elems) else &.{};
            for (elems, 0..) |pe, i| try bindPattern(self, ctx, a, env, f, blk, pe, blk.builder.extractElem(blk, if (i < elem_tys.len) elem_tys[i] else ts.tAny(), value, @intCast(i), loc), if (i < elem_tys.len) elem_tys[i] else ts.tAny());
        },
        .Slice => {
            const sl = a.pats.get(.Slice, pid);
            const ts = self.context.type_store;
            const elem_ty = switch (ts.getKind(vty)) {
                .Array => ts.get(.Array, vty).elem,
                .Slice => ts.get(.Slice, vty).elem,
                else => ts.tAny(),
            };

            for (a.pats.pat_pool.slice(sl.elems), 0..) |pat_elem, i| {
                if (sl.has_rest and i == sl.rest_index) continue;
                try bindPattern(self, ctx, a, env, f, blk, pat_elem, blk.builder.indexOp(blk, elem_ty, value, blk.builder.tirValue(.ConstInt, blk, ts.tUsize(), loc, .{ .value = i }), loc), elem_ty);
            }

            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const rest = self.sliceRestValue(f, blk, value, vty, elem_ty, sl.rest_index, loc);
                try bindPattern(self, ctx, a, env, f, blk, sl.rest_binding.unwrap(), rest.val, rest.ty);
            }
        },
        .VariantTuple => {
            const pr = a.pats.get(.VariantTuple, pid);
            const segs = a.pats.seg_pool.slice(pr.path);
            if (segs.len == 0) return;
            if (self.tagIndexForCase(vty, a.pats.PathSeg.get(segs[segs.len - 1]).name)) |tag_idx| {
                const ts = self.context.type_store;
                if (self.getUnionTypeFromVariant(vty)) |union_ty| {
                    const payload_ty = ts.Field.get(ts.field_pool.slice(ts.get(.Union, union_ty).fields)[tag_idx]).ty;
                    const union_field_val = blk.builder.tirValue(.UnionField, blk, payload_ty, loc, .{ .base = blk.builder.extractField(blk, union_ty, value, 1, loc), .field_index = tag_idx });
                    const pelems = a.pats.pat_pool.slice(pr.elems);
                    if (ts.getKind(payload_ty) == .Tuple) {
                        const subtys = ts.type_pool.slice(ts.get(.Tuple, payload_ty).elems);
                        for (pelems, 0..) |pe, i| try bindPattern(self, ctx, a, env, f, blk, pe, blk.builder.extractElem(blk, if (i < subtys.len) subtys[i] else ts.tAny(), union_field_val, @intCast(i), loc), if (i < subtys.len) subtys[i] else ts.tAny());
                    } else if (pelems.len > 0) {
                        try bindPattern(self, ctx, a, env, f, blk, pelems[0], union_field_val, payload_ty);
                    }
                }
            }
        },
        .VariantStruct => {
            const vs = a.pats.get(.VariantStruct, pid);
            const ts = self.context.type_store;
            if (ts.getKind(vty) == .Struct) {
                const sfields = ts.field_pool.slice(ts.get(.Struct, vty).fields);
                for (a.pats.field_pool.slice(vs.fields)) |pfid| {
                    const pf = a.pats.StructField.get(pfid);
                    for (sfields, 0..) |sfid, i| {
                        const sf = ts.Field.get(sfid);
                        if (sf.name.eq(pf.name)) {
                            try bindPattern(self, ctx, a, env, f, blk, pf.pattern, blk.builder.extractField(blk, sf.ty, value, @intCast(i), loc), sf.ty);
                            break;
                        }
                    }
                }
            } else {
                const segs = a.pats.seg_pool.slice(vs.path);
                if (segs.len > 0) {
                    if (self.tagIndexForCase(vty, a.pats.PathSeg.get(segs[segs.len - 1]).name)) |tag_idx| {
                        if (self.getUnionTypeFromVariant(vty)) |union_ty| {
                            const payload_ty = ts.Field.get(ts.field_pool.slice(ts.get(.Union, union_ty).fields)[tag_idx]).ty;
                            const struct_val = blk.builder.tirValue(.UnionField, blk, payload_ty, loc, .{ .base = blk.builder.extractField(blk, union_ty, value, 1, loc), .field_index = tag_idx });
                            const sfields = ts.field_pool.slice(ts.get(.Struct, payload_ty).fields);
                            for (a.pats.field_pool.slice(vs.fields)) |pfid| {
                                const pf = a.pats.StructField.get(pfid);
                                for (sfields, 0..) |sfid, i| {
                                    const sf = ts.Field.get(sfid);
                                    if (sf.name.eq(pf.name)) {
                                        try bindPattern(self, ctx, a, env, f, blk, pf.pattern, blk.builder.extractField(blk, sf.ty, struct_val, @intCast(i), loc), sf.ty);
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        },
        else => {},
    }
}
