const LowerTir = @import("lower_tir.zig");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const std = @import("std");
const codegen = @import("codegen_main.zig");
const List = std.ArrayList;
const ValueBinding = LowerTir.ValueBinding;
const check_pattern_matching = @import("check_pattern_matching.zig");

// ============================
// Context structs
// ============================

/// Additional bookkeeping needed while lowering `continue` and range loops.
const ContinueInfo = union(enum) {
    /// Loop does not require special handling.
    none,
    /// Extra data required when continuing a ranged loop.
    range: struct {
        /// Block where range iteration bookkeeping runs before jumping back.
        update_block: tir.BlockId,
        /// SSA value tracking the current index in the range.
        idx_value: tir.ValueId,
    },
};

/// Represents a deferred expression that should run when the surrounding scope exits.
pub const DeferEntry = struct {
    /// AST expression to lower when the defer fires.
    expr: ast.ExprId,
    /// Whether this defer runs only during error unwinds.
    is_err: bool,
};

/// Track the active loop's jump targets, result tracking, and defers.
pub const LoopCtx = struct {
    /// Optional label supplied by the user for this loop.
    label: ast.OptStrId,
    /// Block that handles exiting the loop normally.
    break_block: tir.BlockId,
    /// Block that handles continuing the loop.
    continue_block: tir.BlockId,
    /// Block where broken-out values join with the rest of the function.
    join_block: tir.BlockId,
    /// Type expected from `break`/`return` inside this loop.
    res_ty: ?types.TypeId,
    /// Tracks whether `break`/`return` carried a value.
    has_result: bool,
    /// Block parameter used to pass the loop result to callers.
    res_param: tir.OptValueId,
    /// Additional information needed by loop `continue` handling.
    continue_info: ContinueInfo,
    /// Number of deferred expressions when the loop started (used for cleanup).
    defer_len_at_entry: u32,
};

/// Tracks local bindings, defers, and scope markers while lowering control flow constructs.
pub const Env = struct {
    /// Current binding map used for lowering variables and temporaries.
    map: std.AutoArrayHashMapUnmanaged(ast.StrId, ValueBinding) = .{},
    /// Stack of defers registered while entering statements.
    defers: List(DeferEntry) = .{},
    /// Markers that capture the defer depth for each pushed scope.
    marks: List(u32) = .{},

    /// Release allocator-backed resources owned by the environment.
    pub fn deinit(self: *Env, gpa: std.mem.Allocator) void {
        self.map.deinit(gpa);
        self.defers.deinit(gpa);
        self.marks.deinit(gpa);
    }
    /// Bind `name` to `vb` for the remainder of this scope.
    pub fn bind(self: *Env, gpa: std.mem.Allocator, name: tir.StrId, vb: ValueBinding, builder: *tir.Builder, blk: *tir.Builder.BlockFrame, loc: tir.OptLocId) !void {
        try self.map.put(gpa, name, vb);
        if (codegen.enable_debug_info) {
            const res = builder.freshValue();
            const iid = builder.t.instrs.add(.DbgDeclare, .{
                .result = res,
                .ty = vb.ty,
                .value = vb.value,
                .name = name,
                .loc = loc,
            });
            try blk.instrs.append(gpa, iid);
        }
    }
    /// Lookup the current binding for `s`, if any.
    pub fn lookup(self: *Env, s: ast.StrId) ?ValueBinding {
        return self.map.get(s);
    }
    /// Restore the previous binding for `name`, erasing or re-inserting as needed.
    pub fn restoreBinding(self: *Env, gpa: std.mem.Allocator, name: tir.StrId, prev: ?ValueBinding) !void {
        if (prev) |val| {
            try self.map.put(gpa, name, val);
        } else {
            _ = self.map.swapRemove(name);
        }
    }
    /// Start a new lexical scope by recording the current defer depth.
    pub fn pushScope(self: *Env, gpa: std.mem.Allocator) !void {
        try self.marks.append(gpa, @intCast(self.defers.items.len));
    }
    /// Exit the most recent scope, rolling back defers to the saved mark.
    pub fn popScope(self: *Env) u32 {
        if (self.marks.items.len == 0) return 0;
        const mark = self.marks.items[self.marks.items.len - 1];
        self.marks.items.len -= 1;
        self.defers.items.len = mark;
        return mark;
    }
};

/// Run "normal" (non-err) defers scheduled at or after `from`, in reverse order,
/// and then truncate the defer stack back to `from`.
pub fn runNormalDefersFrom(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    from: u32,
) !void {
    var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
    while (j >= 0 and @as(u32, @intCast(j)) >= from) : (j -= 1) {
        const ent = env.defers.items[@intCast(j)];
        if (!ent.is_err) {
            _ = try self.lowerExpr(ctx, a, env, f, blk, ent.expr, null, .rvalue);
        }
    }
    env.defers.items.len = from;
}

/// Check if error-path defers exist on or after `from`, used to include them when unwinding.
pub fn hasErrDefersFrom(_: *LowerTir, env: *Env, from: u32) bool {
    var i: usize = env.defers.items.len;
    while (i > from) : (i -= 1) {
        if (env.defers.items[i - 1].is_err) return true;
    }
    return false;
}

/// Run defers from `slice` matching `want_err`, lowering each guarded expression.
pub fn emitDefers(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    slice: []const DeferEntry,
    want_err: bool,
) !void {
    var j: isize = @as(isize, @intCast(slice.len)) - 1;
    while (j >= 0) : (j -= 1) {
        const ent = slice[@intCast(j)];
        if (ent.is_err == want_err) {
            _ = try self.lowerExpr(ctx, a, env, f, blk, ent.expr, null, .rvalue);
        }
    }
}

/// Run non-error defers that belong to `lc` as the loop exits so resources are released.
fn runDefersForLoopExit(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    lc: LoopCtx,
) !void {
    var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
    while (j >= 0 and @as(u32, @intCast(j)) >= lc.defer_len_at_entry) : (j -= 1) {
        const ent = env.defers.items[@intCast(j)];
        if (!ent.is_err) _ = try self.lowerExpr(ctx, a, env, f, blk, ent.expr, null, .rvalue);
    }
    // Defers belong to the loop/body scope being exited; drop them to avoid re-running later.
    env.defers.items.len = lc.defer_len_at_entry;
}

/// Lookup the active loop context that matches `opt_label`, if any.
fn loopCtxForLabel(_: *LowerTir, ctx: *LowerTir.LowerContext, want: ast.OptStrId) ?*LoopCtx {
    if (ctx.loop_stack.items.len == 0) return null;
    var i: isize = @as(isize, @intCast(ctx.loop_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const lc = &ctx.loop_stack.items[@intCast(i)];
        if (want.isNone()) return lc;
        if (!lc.label.isNone() and lc.label.unwrap().eq(want.unwrap())) return lc;
    }
    return null;
}

/// Lower `if` statements/expressions so both branches appropriately target `expected_ty`.
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
    var then_blk = try f.builder.beginBlock(f);
    var else_blk = try f.builder.beginBlock(f);
    const loc = LowerTir.optLoc(a, id);

    const out_ty_guess = expected_ty orelse self.getExprType(ctx, a, id);
    const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

    const cond_v = try self.lowerExpr(ctx, a, env, f, blk, row.cond, self.context.type_store.tBool(), .rvalue);

    if (produce_value) {
        var join_blk = try f.builder.beginBlock(f);
        const res_ty = out_ty_guess;
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

        const br_cond = self.forceLocalCond(blk, cond_v, loc);
        try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{}, loc);
        {
            const old = blk.*;
            try f.builder.endBlock(f, old);
        }

        // then: evaluate exactly once as value-producing block
        if (then_blk.term.isNone()) {
            var v_then = try self.lowerBlockExprValue(ctx, a, env, f, &then_blk, row.then_block, res_ty);
            if (expected_ty) |want| v_then = self.emitCoerce(&then_blk, v_then, self.getExprType(ctx, a, row.then_block), want, loc);
            try f.builder.br(&then_blk, join_blk.id, &.{v_then}, loc);
        }

        // else
        if (!row.else_block.isNone()) {
            if (else_blk.term.isNone()) {
                var v_else = try self.lowerBlockExprValue(ctx, a, env, f, &else_blk, row.else_block.unwrap(), res_ty);
                if (expected_ty) |want| v_else = self.emitCoerce(&else_blk, v_else, self.getExprType(ctx, a, row.else_block.unwrap()), want, loc);
                try f.builder.br(&else_blk, join_blk.id, &.{v_else}, loc);
            }
        } else {
            if (else_blk.term.isNone()) {
                const uv = self.safeUndef(&else_blk, res_ty, loc);
                try f.builder.br(&else_blk, join_blk.id, &.{uv}, loc);
            }
        }

        try f.builder.endBlock(f, then_blk);
        try f.builder.endBlock(f, else_blk);
        blk.* = join_blk;
        return res_param;
    } else {
        // statement-position if: no value, no phi
        const exit_blk = try f.builder.beginBlock(f);

        // Snapshot current bindings so branch-local bindings don't leak across arms.
        const saved_bindings = &ctx.binding_snapshots;
        saved_bindings.clearRetainingCapacity();
        var snap_it = env.map.iterator();
        while (snap_it.next()) |entry| {
            try saved_bindings.append(self.gpa, .{ .name = entry.key_ptr.*, .prev = entry.value_ptr.* });
        }
        const scratch_names = &ctx.pattern_binding_names;

        const br_cond = self.forceLocalCond(blk, cond_v, loc);
        try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{}, loc);
        {
            const old = blk.*;
            try f.builder.endBlock(f, old);
        }

        try self.lowerExprAsStmtList(ctx, a, env, f, &then_blk, row.then_block);
        if (then_blk.term.isNone()) try f.builder.br(&then_blk, exit_blk.id, &.{}, loc);
        try f.builder.endBlock(f, then_blk);
        try self.restoreEnvSnapshot(env, saved_bindings.items, scratch_names);

        if (!row.else_block.isNone()) {
            try self.lowerExprAsStmtList(ctx, a, env, f, &else_blk, row.else_block.unwrap());
        }
        if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{}, loc);
        try f.builder.endBlock(f, else_blk);
        try self.restoreEnvSnapshot(env, saved_bindings.items, scratch_names);

        blk.* = exit_blk;
        return self.safeUndef(blk, self.context.type_store.tAny(), loc);
    }
}

/// Lower a `break` expression by running appropriate defers and branching to the loop join block.
pub fn lowerBreak(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    const br = a.stmts.get(.Break, sid);
    const loc = LowerTir.optLoc(a, sid);
    try lowerBreakCommon(self, ctx, a, env, f, blk, br.label, br.value, loc);
}

/// Helper used by `lowerBreak` to jump through a loop's exit logic while tracking defers.
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
    var target: ?LoopCtx = null;
    var i: isize = @as(isize, @intCast(ctx.loop_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const lc = ctx.loop_stack.items[@intCast(i)];
        if (label.isNone() or (!lc.label.isNone() and std.mem.eql(u8, a.exprs.strs.get(lc.label.unwrap()), a.exprs.strs.get(label.unwrap())))) {
            target = lc;
            break;
        }
    }
    if (target) |lc| {
        try runDefersForLoopExit(self, ctx, a, env, f, blk, lc);
        if (lc.has_result) {
            const v = if (!value.isNone())
                try self.lowerExpr(ctx, a, env, f, blk, value.unwrap(), lc.res_ty, .rvalue)
            else
                self.safeUndef(blk, lc.res_ty.?, loc);
            try f.builder.br(blk, lc.join_block, &.{v}, loc);
        } else {
            try f.builder.br(blk, lc.break_block, &.{}, loc);
        }
    } else return error.LoweringBug;
}

/// Lower a `continue` statement, jumping into the loop`s continue block and honoring defers.
pub fn lowerContinue(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    const cid = a.stmts.get(.Continue, sid);
    const loc = LowerTir.optLoc(a, sid);
    try lowerContinueCommon(self, ctx, a, env, f, blk, cid.label, loc);
}

/// Shared logic for running defers and branching that powers `continue`.
pub fn lowerContinueCommon(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    env: *Env,
    f: *tir.Builder.FunctionFrame,
    blk: *tir.Builder.BlockFrame,
    label: ast.OptStrId,
    loc: tir.OptLocId,
) !void {
    const lc = loopCtxForLabel(self, ctx, label) orelse return error.LoweringBug;
    try runDefersForLoopExit(self, ctx, a, env, f, blk, lc.*);
    switch (lc.continue_info) {
        .none => try f.builder.br(blk, lc.continue_block, &.{}, loc),
        .range => |info| try f.builder.br(blk, info.update_block, &.{info.idx_value}, loc),
    }
}

/// Map a simple identifier `name` to a builtin type when possible.
fn typeIdForName(ts: *types.TypeStore, name: ast.StrId) ?types.TypeId {
    const s = ts.strs.get(name);
    if (std.mem.eql(u8, s, "bool")) return ts.tBool();
    if (std.mem.eql(u8, s, "i8")) return ts.tI8();
    if (std.mem.eql(u8, s, "i16")) return ts.tI16();
    if (std.mem.eql(u8, s, "i32")) return ts.tI32();
    if (std.mem.eql(u8, s, "i64")) return ts.tI64();
    if (std.mem.eql(u8, s, "u8")) return ts.tU8();
    if (std.mem.eql(u8, s, "u16")) return ts.tU16();
    if (std.mem.eql(u8, s, "u32")) return ts.tU32();
    if (std.mem.eql(u8, s, "u64")) return ts.tU64();
    if (std.mem.eql(u8, s, "usize")) return ts.tUsize();
    if (std.mem.eql(u8, s, "f32")) return ts.tF32();
    if (std.mem.eql(u8, s, "f64")) return ts.tF64();
    if (std.mem.eql(u8, s, "char")) return ts.tU32();
    if (std.mem.eql(u8, s, "string")) return ts.tString();
    if (std.mem.eql(u8, s, "any")) return ts.tAny();
    if (std.mem.eql(u8, s, "type")) return ts.mkTypeType(ts.tAny());
    return null;
}

/// Lower `match`/`switch` cases by testing the subject and emitting arm-specific code.
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
    switch (a.kind(pid)) {
        .Wildcard => return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = true }),
        .Binding => {
            const br = a.pats.get(.Binding, pid);
            if (self.context.type_store.getKind(scrut_ty) == .TypeType) {
                if (typeIdForName(self.context.type_store, br.name)) |want_ty| {
                    const want = f.builder.tirValue(
                        .ConstInt,
                        blk,
                        scrut_ty,
                        loc,
                        .{ .value = @as(u64, @intCast(want_ty.toRaw())) },
                    );
                    return blk.builder.binBool(blk, .CmpEq, scrut, want, loc);
                }
            }
            return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = true });
        },

        .Literal => {
            const pr = a.pats.get(.Literal, pid);
            if (a.kind(pr.expr) == .Range) {
                const range = a.exprs.get(.Range, pr.expr);
                return matchRangeBounds(
                    self,
                    ctx,
                    a,
                    env,
                    f,
                    blk,
                    range.start,
                    range.end,
                    range.inclusive_right,
                    scrut,
                    scrut_ty,
                    loc,
                );
            }
            const litv = try self.lowerExpr(ctx, a, env, f, blk, pr.expr, scrut_ty, .rvalue);
            return blk.builder.binBool(blk, .CmpEq, scrut, litv, loc);
        },
        .VariantTuple => {
            const vt = a.pats.get(.VariantTuple, pid);
            const segs = a.pats.seg_pool.slice(vt.path);
            if (segs.len == 0) return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
            const last = a.pats.PathSeg.get(segs[segs.len - 1]);
            if (self.tagIndexForCase(scrut_ty, last.name)) |idx| {
                const tag = blk.builder.extractField(blk, self.context.type_store.tI32(), scrut, 0, loc);
                const want = f.builder.tirValue(
                    .ConstInt,
                    blk,
                    self.context.type_store.tI32(),
                    loc,
                    .{ .value = @as(u64, @intCast(idx)) },
                );
                return blk.builder.binBool(blk, .CmpEq, tag, want, loc);
            }
            return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
        },
        .At => {
            const node = a.pats.get(.At, pid);
            return try matchPattern(self, ctx, a, env, f, blk, node.pattern, scrut, scrut_ty, loc);
        },
        .VariantStruct => {
            const vs = a.pats.get(.VariantStruct, pid);
            const vk = self.context.type_store.getKind(scrut_ty);
            if (vk == .Struct) {
                return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = true });
            }

            const segs = a.pats.seg_pool.slice(vs.path);
            if (segs.len == 0) return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
            const last = a.pats.PathSeg.get(segs[segs.len - 1]);
            if (self.tagIndexForCase(scrut_ty, last.name)) |idx| {
                const tag = blk.builder.extractField(blk, self.context.type_store.tI32(), scrut, 0, loc);
                const want = f.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), loc, .{ .value = @as(u64, @intCast(idx)) });
                return blk.builder.binBool(blk, .CmpEq, tag, want, loc);
            }
            return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
        },
        .Path => {
            // Tag-only variant pattern
            const pp = a.pats.get(.Path, pid);
            const segs = a.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
            const last = a.pats.PathSeg.get(segs[segs.len - 1]);

            if (self.enumMemberValue(scrut_ty, last.name)) |val| {
                const want = f.builder.tirValue(.ConstInt, blk, scrut_ty, loc, .{ .value = val });
                return blk.builder.binBool(blk, .CmpEq, scrut, want, loc);
            }

            if (self.tagIndexForCase(scrut_ty, last.name)) |idx| {
                const tag = blk.builder.extractField(blk, self.context.type_store.tI32(), scrut, 0, loc);
                const want = f.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), loc, .{ .value = @as(u64, @intCast(idx)) });
                return blk.builder.binBool(blk, .CmpEq, tag, want, loc);
            }
            return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
        },
        .Slice => {
            const sl = a.pats.get(.Slice, pid);
            const elems = a.pats.pat_pool.slice(sl.elems);
            const required_len = elems.len;

            var len_val: tir.ValueId = undefined;
            const scrut_ty_kind = self.context.type_store.getKind(scrut_ty);
            if (scrut_ty_kind == .Array) {
                const arr_ty = self.context.type_store.get(.Array, scrut_ty);
                len_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = arr_ty.len });
            } else {
                len_val = blk.builder.extractFieldNamed(blk, self.context.type_store.tUsize(), scrut, f.builder.intern("len"), loc);
            }
            const required_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = required_len });

            var len_check_result: tir.ValueId = undefined;
            if (sl.has_rest) {
                len_check_result = blk.builder.binBool(blk, .CmpGe, len_val, required_val, loc);
            } else {
                len_check_result = blk.builder.binBool(blk, .CmpEq, len_val, required_val, loc);
            }

            var all_elements_match = blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = true });

            const elem_ty = if (self.context.type_store.getKind(scrut_ty) == .Array)
                self.context.type_store.get(.Array, scrut_ty).elem
            else if (self.context.type_store.getKind(scrut_ty) == .Slice)
                self.context.type_store.get(.Slice, scrut_ty).elem
            else
                self.context.type_store.tAny();

            var i: usize = 0;
            while (i < required_len) : (i += 1) {
                const pat_elem = elems[i];
                const elem_val = blk.builder.indexOp(blk, elem_ty, scrut, blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = i }), .none());
                const elem_match = try matchPattern(self, ctx, a, env, f, blk, pat_elem, elem_val, elem_ty, loc);
                all_elements_match = blk.builder.binBool(blk, .LogicalAnd, all_elements_match, elem_match, loc);
            }

            return blk.builder.binBool(blk, .LogicalAnd, len_check_result, all_elements_match, loc);
        },
        .Or => {
            const or_pat = a.pats.get(.Or, pid);
            const alts = a.pats.pat_pool.slice(or_pat.alts);
            if (alts.len == 0) {
                return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
            }

            var result = try matchPattern(self, ctx, a, env, f, blk, alts[0], scrut, scrut_ty, loc);
            var i: usize = 1;
            while (i < alts.len) : (i += 1) {
                const next_ok = try matchPattern(self, ctx, a, env, f, blk, alts[i], scrut, scrut_ty, loc);
                result = blk.builder.binBool(blk, .LogicalOr, result, next_ok, loc);
            }
            return result;
        },
        .Range => {
            const range_pat = a.pats.get(.Range, pid);
            return matchRangeBounds(
                self,
                ctx,
                a,
                env,
                f,
                blk,
                range_pat.start,
                range_pat.end,
                range_pat.inclusive_right,
                scrut,
                scrut_ty,
                loc,
            );
        },
        .Tuple, .Struct => {
            return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = true });
        },
    }
}

/// Emit comparisons that test whether `scrut` falls between the optional `start`/`end` of a range.
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
    const bool_ty = self.context.type_store.tBool();
    var result = blk.builder.tirValue(.ConstBool, blk, bool_ty, loc, .{ .value = true });

    if (!start.isNone()) {
        const start_expr = start.unwrap();
        const start_val = try self.lowerExpr(ctx, a, env, f, blk, start_expr, scrut_ty, .rvalue);
        const cmp = blk.builder.binBool(blk, .CmpGe, scrut, start_val, loc);
        result = blk.builder.binBool(blk, .LogicalAnd, result, cmp, loc);
    }

    if (!end.isNone()) {
        const end_expr = end.unwrap();
        const end_val = try self.lowerExpr(ctx, a, env, f, blk, end_expr, scrut_ty, .rvalue);
        const cmp = if (inclusive_right)
            blk.builder.binBool(blk, .CmpLe, scrut, end_val, loc)
        else
            blk.builder.binBool(blk, .CmpLt, scrut, end_val, loc);
        result = blk.builder.binBool(blk, .LogicalAnd, result, cmp, loc);
    }

    return result;
}

/// Desugar `optional.unwrap` expressions into explicit control flow with maybes.
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
    const elem_ty = self.getExprType(ctx, a, id);
    const opt_ty = self.getExprType(ctx, a, row.expr);
    if (self.context.type_store.getKind(opt_ty) != .Optional)
        return error.LoweringBug;
    const opt_info = self.context.type_store.get(.Optional, opt_ty);
    const loc = LowerTir.optLoc(a, id);
    const expr_loc = LowerTir.optLoc(a, row.expr);

    const opt_val = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    const flag = self.optionalFlag(blk, opt_ty, opt_val, expr_loc);
    const payload = self.optionalPayload(blk, opt_ty, opt_val, expr_loc);

    var then_blk = try f.builder.beginBlock(f);
    var none_blk = try f.builder.beginBlock(f);
    var join_blk = try f.builder.beginBlock(f);

    const then_param = try f.builder.addBlockParam(&then_blk, null, opt_info.elem);
    const res_ty = expected_ty orelse elem_ty;
    const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

    try f.builder.condBr(blk, flag, then_blk.id, &.{payload}, none_blk.id, &.{}, loc);
    const orig_blk = blk.*;
    try f.builder.endBlock(f, orig_blk);

    var unwrapped = then_param;
    if (expected_ty) |want| {
        unwrapped = self.emitCoerce(&then_blk, unwrapped, elem_ty, want, loc);
    }
    try f.builder.br(&then_blk, join_blk.id, &.{unwrapped}, loc);
    try f.builder.endBlock(f, then_blk);

    const panic_msg = "unwrap of null optional";
    const panic_str = none_blk.builder.tirValue(
        .ConstString,
        &none_blk,
        self.context.type_store.tString(),
        loc,
        .{ .text = f.builder.intern(panic_msg) },
    );
    const panic_fn = f.builder.intern("rt_panic");
    const ptr_ty = self.context.type_store.mkPtr(self.context.type_store.tU8(), true);
    const str_ptr = none_blk.builder.extractField(&none_blk, ptr_ty, panic_str, 0, loc);
    const str_len = none_blk.builder.extractField(&none_blk, self.context.type_store.tUsize(), panic_str, 1, loc);
    _ = none_blk.builder.call(&none_blk, self.context.type_store.tVoid(), panic_fn, &.{ str_ptr, str_len }, loc);
    try f.builder.setUnreachable(&none_blk, loc);
    try f.builder.endBlock(f, none_blk);

    blk.* = join_blk;
    return res_param;
}

/// Lower `try`/`?` unwraps so error propagation defers can fire correctly.
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
    const result_ty = self.getExprType(ctx, a, id);
    const loc = LowerTir.optLoc(a, id);
    const expr_loc = LowerTir.optLoc(a, row.expr);

    // Lower the error-union expression
    const es_val = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    const es_ty = self.getExprType(ctx, a, row.expr);
    if (self.context.type_store.getKind(es_ty) != .ErrorSet)
        return error.LoweringBug;
    const es = self.context.type_store.get(.ErrorSet, es_ty);

    // Extract tag and branch
    const tag_ty = self.context.type_store.tI32();
    const tag = blk.builder.extractField(blk, tag_ty, es_val, 0, expr_loc);
    const zero = blk.builder.tirValue(.ConstInt, blk, tag_ty, expr_loc, .{ .value = 0 });
    const is_ok = blk.builder.binBool(blk, .CmpEq, tag, zero, expr_loc);

    var then_blk = try f.builder.beginBlock(f); // ok path
    var else_blk = try f.builder.beginBlock(f); // err path
    var join_blk = try f.builder.beginBlock(f);

    const res_ty = expected_ty orelse result_ty;
    try self.noteExprType(ctx, id, res_ty);
    const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

    const br_cond = self.forceLocalCond(blk, is_ok, expr_loc);
    try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{}, loc);
    {
        const old = blk.*;
        try f.builder.endBlock(f, old);
    }

    // Ok path: extract Ok payload from union and jump to join
    const payload_union_ty = self.context.type_store.mkUnion(&.{
        .{ .name = f.builder.intern("Ok"), .ty = es.value_ty },
        .{ .name = f.builder.intern("Err"), .ty = es.error_ty },
    });
    const payload_union_ok = then_blk.builder.extractField(&then_blk, payload_union_ty, es_val, 1, expr_loc);
    var ok_val = then_blk.builder.tirValue(.UnionField, &then_blk, es.value_ty, loc, .{
        .base = payload_union_ok,
        .field_index = 0,
    });
    if (expected_ty) |want| ok_val = self.emitCoerce(&then_blk, ok_val, es.value_ty, want, loc);
    try f.builder.br(&then_blk, join_blk.id, &.{ok_val}, loc);
    try f.builder.endBlock(f, then_blk);

    // Err path: early-return the error to the caller
    // Coerce to current function's expected result type if needed
    const frow = f.builder.t.funcs.Function.get(f.id);
    const expect = frow.result;
    var ret_val = es_val;
    if (!self.isVoid(expect) and !expect.eq(es_ty)) {
        ret_val = self.emitCoerce(&else_blk, es_val, es_ty, expect, loc);
    }
    try f.builder.setReturnVal(&else_blk, ret_val, loc);
    try f.builder.endBlock(f, else_blk);

    // Continue after join with the unwrapped value
    blk.* = join_blk;
    return res_param;
}

/// Check whether every match arm is an integer literal, recording their values in `values_buf`.
fn isAllIntMatch(_: *LowerTir, a: *ast.Ast, arms_slice: []const ast.MatchArmId, values_buf: []u64) bool {
    if (arms_slice.len != values_buf.len) return false;
    for (arms_slice, 0..) |arm_id, i| {
        const arm = a.exprs.MatchArm.get(arm_id);
        if (!arm.guard.isNone()) return false;
        if (a.kind(arm.pattern) != .Literal) return false;
        const plit = a.pats.get(.Literal, arm.pattern);
        if (a.kind(plit.expr) != .Literal) return false;
        const lit = a.exprs.get(.Literal, plit.expr);
        if (lit.kind != .int) return false;
        const info = switch (lit.data) {
            .int => |int_info| int_info,
            else => return false,
        };
        if (!info.valid) return false;
        const value = std.math.cast(u64, info.value) orelse return false;
        values_buf[i] = value;
    }
    return true;
}

/// Lower the high-level `match` expression into a chain of basic blocks and comparisons.
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

    // Scrutinee value
    const scrut = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);

    // Decide if this match-expression needs to produce a value
    const out_ty_guess = expected_ty orelse self.getExprType(ctx, a, id);
    const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess) and self.context.type_store.getKind(out_ty_guess) != .Any;

    if (produce_value) {
        // ------- value-producing path -------
        const res_ty = out_ty_guess;

        // Join block (phi-like param carries the match result)
        var join_blk = try f.builder.beginBlock(f);
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

        const arms = a.exprs.arm_pool.slice(row.arms);
        const scrut_ty = self.getExprType(ctx, a, row.expr);
        if (arms.len == 0) {
            const uv = self.safeUndef(blk, res_ty, loc);
            try f.builder.br(blk, join_blk.id, &.{uv}, loc);
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

            var i: usize = 0;
            while (i < arms.len) : (i += 1) bodies[i] = try f.builder.beginBlock(f);
            var default_blk = try f.builder.beginBlock(f);

            try f.builder.switchInt(blk, scrut, values, blk: {
                i = 0;
                while (i < arms.len) : (i += 1) case_dests[i] = .{ .dest = bodies[i].id, .args = &.{} };
                break :blk case_dests;
            }, default_blk.id, &.{}, loc);

            // Fill bodies
            i = 0;
            while (i < arms.len) : (i += 1) {
                const arm = a.exprs.MatchArm.get(arms[i]);
                try self.lowerExprAsStmtList(ctx, a, env, f, &bodies[i], arm.body);
                if (bodies[i].term.isNone()) {
                    var v = try self.lowerBlockExprValue(ctx, a, env, f, &bodies[i], arm.body, res_ty);
                    v = self.emitCoerce(&bodies[i], v, self.getExprType(ctx, a, arm.body), res_ty, loc);
                    try f.builder.br(&bodies[i], join_blk.id, &.{v}, loc);
                }
                try f.builder.endBlock(f, bodies[i]);
            }

            const uv = self.safeUndef(&default_blk, res_ty, loc);
            try f.builder.br(&default_blk, join_blk.id, &.{uv}, loc);
            try f.builder.endBlock(f, default_blk);

            blk.* = join_blk;
            return res_param;
        }

        // -------- General path: chained tests with optional guards --------
        const binding_names = &ctx.pattern_binding_names;
        const saved = &ctx.binding_snapshots;

        var cur = blk.*;

        var j: usize = 0;
        while (j < arms.len) : (j += 1) {
            binding_names.clearRetainingCapacity();
            saved.clearRetainingCapacity();

            const arm_id = arms[j];
            const arm = a.exprs.MatchArm.get(arm_id);

            var test_blk = try f.builder.beginBlock(f);
            var body_blk = try f.builder.beginBlock(f);
            const next_blk = if (j + 1 < arms.len) try f.builder.beginBlock(f) else join_blk;

            try f.builder.br(&cur, test_blk.id, &.{}, loc);
            try f.builder.endBlock(f, cur);

            const ok = try matchPattern(self, ctx, a, env, f, &test_blk, arm.pattern, scrut, scrut_ty, loc);

            const else_args = if (next_blk.id.eq(join_blk.id)) blkargs: {
                const uv = self.safeUndef(&test_blk, res_ty, loc);
                break :blkargs &.{uv};
            } else &.{};

            try check_pattern_matching.collectPatternBindings(self.chk, a, arm.pattern, binding_names);
            try saved.ensureTotalCapacity(self.gpa, binding_names.items.len);
            for (binding_names.items) |name| {
                try saved.append(self.gpa, .{ .name = name, .prev = env.lookup(name) });
            }

            if (!arm.guard.isNone()) {
                var guard_blk = try f.builder.beginBlock(f);
                const br_cond = self.forceLocalCond(&test_blk, ok, loc);
                try f.builder.condBr(&test_blk, br_cond, guard_blk.id, &.{}, next_blk.id, else_args, loc);
                try f.builder.endBlock(f, test_blk);

                try bindPattern(self, ctx, a, env, f, &guard_blk, arm.pattern, scrut, scrut_ty);
                const guard_id = arm.guard.unwrap();
                const guard_loc = LowerTir.optLoc(a, guard_id);
                const guard_val = try self.lowerExpr(ctx, a, env, f, &guard_blk, guard_id, self.context.type_store.tBool(), .rvalue);
                const guard_cond = self.forceLocalCond(&guard_blk, guard_val, guard_loc);
                try self.restoreBindings(env, saved.items);
                try f.builder.condBr(&guard_blk, guard_cond, body_blk.id, &.{}, next_blk.id, else_args, guard_loc);
                try f.builder.endBlock(f, guard_blk);
            } else {
                const br_cond = self.forceLocalCond(&test_blk, ok, loc);
                try f.builder.condBr(&test_blk, br_cond, body_blk.id, &.{}, next_blk.id, else_args, loc);
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
        // ------- statement-position path (no value) -------
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

            var i: usize = 0;
            while (i < arms.len) : (i += 1) bodies[i] = try f.builder.beginBlock(f);
            var default_blk = try f.builder.beginBlock(f);

            try f.builder.switchInt(blk, scrut, values, blk: {
                i = 0;
                while (i < arms.len) : (i += 1) case_dests[i] = .{ .dest = bodies[i].id, .args = &.{} };
                break :blk case_dests;
            }, default_blk.id, &.{}, loc);

            i = 0;
            while (i < arms.len) : (i += 1) {
                const arm = a.exprs.MatchArm.get(arms[i]);
                try self.lowerExprAsStmtList(ctx, a, env, f, &bodies[i], arm.body);
                if (bodies[i].term.isNone()) try f.builder.br(&bodies[i], exit_blk.id, &.{}, loc);
                try f.builder.endBlock(f, bodies[i]);
            }

            try f.builder.br(&default_blk, exit_blk.id, &.{}, loc);
            try f.builder.endBlock(f, default_blk);

            blk.* = exit_blk;
            return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
        }

        // General path (no value): chained tests, fallthrough to exit
        const binding_names = &ctx.pattern_binding_names;
        const saved = &ctx.binding_snapshots;

        var cur = blk.*;
        var l: usize = 0;
        while (l < arms.len) : (l += 1) {
            binding_names.clearRetainingCapacity();
            saved.clearRetainingCapacity();

            const arm_id = arms[l];
            const arm = a.exprs.MatchArm.get(arm_id);

            var test_blk = try f.builder.beginBlock(f);
            var body_blk = try f.builder.beginBlock(f);
            const next_blk = if (l + 1 < arms.len) try f.builder.beginBlock(f) else exit_blk;

            try f.builder.br(&cur, test_blk.id, &.{}, loc);
            try f.builder.endBlock(f, cur);

            const ok = try matchPattern(self, ctx, a, env, f, &test_blk, arm.pattern, scrut, scrut_ty, loc);

            if (!arm.guard.isNone()) {
                var guard_blk = try f.builder.beginBlock(f);
                const br_cond = self.forceLocalCond(&test_blk, ok, loc);
                try f.builder.condBr(&test_blk, br_cond, guard_blk.id, &.{}, next_blk.id, &.{}, loc);
                try f.builder.endBlock(f, test_blk);

                try check_pattern_matching.collectPatternBindings(self.chk, a, arm.pattern, binding_names);
                try saved.ensureTotalCapacity(self.gpa, binding_names.items.len);
                for (binding_names.items) |name| {
                    try saved.append(self.gpa, .{ .name = name, .prev = env.lookup(name) });
                }

                try bindPattern(self, ctx, a, env, f, &guard_blk, arm.pattern, scrut, scrut_ty);
                const guard_id = arm.guard.unwrap();
                const guard_loc = LowerTir.optLoc(a, guard_id);
                const guard_val = try self.lowerExpr(ctx, a, env, f, &guard_blk, guard_id, self.context.type_store.tBool(), .rvalue);
                const guard_cond = self.forceLocalCond(&guard_blk, guard_val, guard_loc);
                try self.restoreBindings(env, saved.items);
                try f.builder.condBr(&guard_blk, guard_cond, body_blk.id, &.{}, next_blk.id, &.{}, guard_loc);
                try f.builder.endBlock(f, guard_blk);
            } else {
                const br_cond = self.forceLocalCond(&test_blk, ok, loc);
                try f.builder.condBr(&test_blk, br_cond, body_blk.id, &.{}, next_blk.id, &.{}, loc);
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

/// Lower a `while` loop by lowering its condition, body, and associated defers/continuations.
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
    const res_ty = out_ty_guess;

    var exit_blk = try f.builder.beginBlock(f);
    var join_blk = exit_blk;
    var res_param: tir.ValueId = undefined;
    if (produce_value) {
        join_blk = try f.builder.beginBlock(f);
        res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
    }

    try f.builder.br(blk, header.id, &.{}, loc);
    {
        const old = blk.*;
        try f.builder.endBlock(f, old);
    }

    try f.builder.br(blk, header.id, &.{}, loc);
    {
        const old = blk.*;
        try f.builder.endBlock(f, old);
    }

    try f.builder.br(blk, header.id, &.{}, loc);
    {
        const old = blk.*;
        try f.builder.endBlock(f, old);
    }

    try ctx.loop_stack.append(self.gpa, .{
        .label = row.label,
        .continue_block = header.id,
        .break_block = exit_blk.id,
        .has_result = produce_value,
        .join_block = join_blk.id,
        .res_param = if (produce_value) .some(res_param) else .none(),
        .res_ty = if (produce_value) res_ty else null,
        .continue_info = .none,
        .defer_len_at_entry = @intCast(env.defers.items.len),
    });

    if (row.is_pattern and !row.pattern.isNone() and !row.cond.isNone()) {
        const subj = try self.lowerExpr(ctx, a, env, f, &header, row.cond.unwrap(), null, .rvalue);
        const subj_ty = self.getExprType(ctx, a, row.cond.unwrap());

        const ok = try matchPattern(self, ctx, a, env, f, &header, row.pattern.unwrap(), subj, subj_ty, loc);

        const br_cond = self.forceLocalCond(&header, ok, loc);
        try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{}, loc);

        try bindPattern(self, ctx, a, env, f, &body, row.pattern.unwrap(), subj, subj_ty);
    } else {
        const cond_loc = if (!row.cond.isNone()) LowerTir.optLoc(a, row.cond.unwrap()) else loc;
        const cond_v = if (!row.cond.isNone())
            try self.lowerExpr(ctx, a, env, f, &header, row.cond.unwrap(), self.context.type_store.tBool(), .rvalue)
        else
            f.builder.tirValue(.ConstBool, &header, self.context.type_store.tBool(), cond_loc, .{ .value = true });

        const br_cond = self.forceLocalCond(&header, cond_v, cond_loc);
        try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{}, loc);
    }

    try self.lowerExprAsStmtList(ctx, a, env, f, &body, row.body);
    if (body.term.isNone()) try f.builder.br(&body, header.id, &.{}, loc);
    try f.builder.endBlock(f, header);
    try f.builder.endBlock(f, body);

    if (produce_value) {
        const uv = self.safeUndef(&exit_blk, res_ty, loc);
        try f.builder.br(&exit_blk, join_blk.id, &.{uv}, loc);
        try f.builder.endBlock(f, exit_blk);

        _ = ctx.loop_stack.pop();
        blk.* = join_blk;
        return res_param;
    } else {
        _ = ctx.loop_stack.pop();
        blk.* = exit_blk;
        return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
    }
}

/// Produce the iteration count for `iterable_val`, either from a constant array size or slice length.
fn getIterableLen(
    self: *LowerTir,
    blk: *tir.Builder.BlockFrame,
    iterable_val: tir.ValueId,
    iter_ty: types.TypeId,
    idx_ty: types.TypeId,
    loc: tir.OptLocId,
) !tir.ValueId {
    return switch (self.context.type_store.getKind(iter_ty)) {
        .Array => blk: {
            const at = self.context.type_store.get(.Array, iter_ty);
            break :blk blk.builder.tirValue(.ConstInt, blk, idx_ty, loc, .{ .value = @as(u64, @intCast(at.len)) });
        },
        .Slice, .DynArray => blk: {
            const v = blk.builder.extractField(blk, idx_ty, iterable_val, 1, loc);
            break :blk v;
        },
        else => return error.LoweringBug,
    };
}

/// Lower a `for` loop by iterating over the subject and mapping its body to blocks.
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
    const res_ty = out_ty_guess;

    var header = try f.builder.beginBlock(f);
    var body = try f.builder.beginBlock(f);

    var exit_blk = try f.builder.beginBlock(f);
    var join_blk = exit_blk;
    var res_param: tir.ValueId = undefined;
    if (produce_value) {
        join_blk = try f.builder.beginBlock(f);
        res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
    }

    try ctx.loop_stack.append(self.gpa, .{
        .label = row.label,
        .continue_block = header.id,
        .break_block = exit_blk.id,
        .has_result = produce_value,
        .join_block = join_blk.id,
        .res_param = if (produce_value) .some(res_param) else .none(),
        .res_ty = if (produce_value) res_ty else null,
        .continue_info = .none,
        .defer_len_at_entry = @intCast(env.defers.items.len),
    });

    if (a.kind(row.iterable) == .Range) {
        const rg = a.exprs.get(.Range, row.iterable);
        if (rg.start.isNone() or rg.end.isNone()) return error.LoweringBug;

        const start_v = try self.lowerExpr(ctx, a, env, f, blk, rg.start.unwrap(), null, .rvalue);
        const end_v = try self.lowerExpr(ctx, a, env, f, blk, rg.end.unwrap(), null, .rvalue);
        const idx_ty = self.getExprType(ctx, a, rg.start.unwrap());

        const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);

        var update_blk = try f.builder.beginBlock(f);
        const update_param = try f.builder.addBlockParam(&update_blk, null, idx_ty);
        const one_update = update_blk.builder.tirValue(.ConstInt, &update_blk, idx_ty, loc, .{ .value = 1 });
        const next_update = update_blk.builder.bin(&update_blk, .Add, idx_ty, update_param, one_update, loc);
        const update_block_id = update_blk.id;
        try f.builder.br(&update_blk, header.id, &.{next_update}, loc);
        try f.builder.endBlock(f, update_blk);

        try f.builder.br(blk, header.id, &.{start_v}, loc);
        {
            const old = blk.*;
            try f.builder.endBlock(f, old);
        }

        const cond = if (rg.inclusive_right)
            blk.builder.binBool(&header, .CmpLe, idx_param, end_v, iterable_loc)
        else
            blk.builder.binBool(&header, .CmpLt, idx_param, end_v, iterable_loc);

        const br_cond = self.forceLocalCond(&header, cond, iterable_loc);
        try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{}, loc);

        try bindPattern(self, ctx, a, env, f, &body, row.pattern, idx_param, idx_ty);

        var lc = &ctx.loop_stack.items[ctx.loop_stack.items.len - 1];
        lc.continue_block = update_block_id;
        lc.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

        try self.lowerExprAsStmtList(ctx, a, env, f, &body, row.body);
        if (body.term.isNone())
            try f.builder.br(&body, update_block_id, &.{idx_param}, loc);
    } else {
        const arr_v = try self.lowerExpr(ctx, a, env, f, blk, row.iterable, null, .rvalue);
        const idx_ty = self.context.type_store.tUsize();
        const iter_ty = self.getExprType(ctx, a, row.iterable);
        const len_v = try getIterableLen(self, blk, arr_v, iter_ty, idx_ty, iterable_loc);

        const zero = blk.builder.tirValue(.ConstInt, blk, idx_ty, loc, .{ .value = 0 });
        const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);

        var update_blk = try f.builder.beginBlock(f);
        const update_param = try f.builder.addBlockParam(&update_blk, null, idx_ty);
        const one_update = update_blk.builder.tirValue(.ConstInt, &update_blk, idx_ty, loc, .{ .value = 1 });
        const next_update = update_blk.builder.bin(&update_blk, .Add, idx_ty, update_param, one_update, loc);
        const update_block_id = update_blk.id;
        try f.builder.br(&update_blk, header.id, &.{next_update}, loc);
        try f.builder.endBlock(f, update_blk);

        try f.builder.br(blk, header.id, &.{zero}, loc);
        {
            const old = blk.*;
            try f.builder.endBlock(f, old);
        }

        const cond = blk.builder.binBool(&header, .CmpLt, idx_param, len_v, iterable_loc);
        const br_cond = self.forceLocalCond(&header, cond, iterable_loc);
        try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{}, loc);

        var elem_ty = self.context.type_store.tAny();
        const ik = self.context.type_store.getKind(iter_ty);
        if (ik == .Array)
            elem_ty = self.context.type_store.get(.Array, iter_ty).elem
        else if (ik == .Slice)
            elem_ty = self.context.type_store.get(.Slice, iter_ty).elem
        else if (ik == .DynArray)
            elem_ty = self.context.type_store.get(.DynArray, iter_ty).elem;
        const elem = blk.builder.indexOp(&body, elem_ty, arr_v, idx_param, iterable_loc);
        try bindPattern(self, ctx, a, env, f, &body, row.pattern, elem, elem_ty);

        var lc2 = &ctx.loop_stack.items[ctx.loop_stack.items.len - 1];
        lc2.continue_block = update_block_id;
        lc2.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

        try self.lowerExprAsStmtList(ctx, a, env, f, &body, row.body);
        if (body.term.isNone())
            try f.builder.br(&body, update_block_id, &.{idx_param}, loc);
    }

    try f.builder.endBlock(f, header);
    try f.builder.endBlock(f, body);

    if (produce_value) {
        const uv = self.safeUndef(&exit_blk, res_ty, loc);
        try f.builder.br(&exit_blk, join_blk.id, &.{uv}, loc);
        try f.builder.endBlock(f, exit_blk);

        _ = ctx.loop_stack.pop();
        blk.* = join_blk;
        return res_param;
    } else {
        _ = ctx.loop_stack.pop();
        blk.* = exit_blk;
        return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
    }
}
/// Lower a pattern binding during `match` or `for` lowering and record introduced symbols.
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
        .Binding => {
            const nm = a.pats.get(.Binding, pid).name;
            try env.bind(self.gpa, nm, .{ .value = value, .ty = vty, .is_slot = false }, f.builder, blk, loc);
        },
        .At => {
            const at = a.pats.get(.At, pid);
            try env.bind(self.gpa, at.binder, .{ .value = value, .ty = vty, .is_slot = false }, f.builder, blk, loc);
            try bindPattern(self, ctx, a, env, f, blk, at.pattern, value, vty);
        },
        .Tuple => {
            const row = a.pats.get(.Tuple, pid);
            const elems = a.pats.pat_pool.slice(row.elems);
            var elem_tys: []const types.TypeId = &.{};
            if (self.context.type_store.getKind(vty) == .Tuple) {
                const tr = self.context.type_store.get(.Tuple, vty);
                elem_tys = self.context.type_store.type_pool.slice(tr.elems);
            }
            for (elems, 0..) |pe, i| {
                const ety = if (i < elem_tys.len) elem_tys[i] else self.context.type_store.tAny();
                const ev = blk.builder.extractElem(blk, ety, value, @intCast(i), loc);
                try bindPattern(self, ctx, a, env, f, blk, pe, ev, ety);
            }
        },
        .Slice => {
            const sl = a.pats.get(.Slice, pid);
            const elems = a.pats.pat_pool.slice(sl.elems);
            const elem_ty = if (self.context.type_store.getKind(vty) == .Array)
                self.context.type_store.get(.Array, vty).elem
            else if (self.context.type_store.getKind(vty) == .Slice)
                self.context.type_store.get(.Slice, vty).elem
            else
                self.context.type_store.tAny();

            for (elems, 0..) |pat_elem, i| {
                if (sl.has_rest and i == sl.rest_index) continue;
                const index_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = i });
                const elem_val = blk.builder.indexOp(blk, elem_ty, value, index_val, loc);
                try bindPattern(self, ctx, a, env, f, blk, pat_elem, elem_val, elem_ty);
            }

            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const rest_pat = sl.rest_binding.unwrap();
                const vty_kind = self.context.type_store.getKind(vty);
                const slice_const = if (vty_kind == .Slice)
                    self.context.type_store.get(.Slice, vty).is_const
                else
                    false;
                const slice_ty = self.context.type_store.mkSlice(elem_ty, slice_const);
                const start = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = sl.rest_index });

                var len_val: tir.ValueId = undefined;
                if (vty_kind == .Array) {
                    const arr_ty = self.context.type_store.get(.Array, vty);
                    len_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = arr_ty.len });
                } else {
                    len_val = blk.builder.extractFieldNamed(blk, self.context.type_store.tUsize(), value, f.builder.intern("len"), loc);
                }

                const range_ty = self.context.type_store.mkSlice(self.context.type_store.tUsize(), false);
                const inclusive = blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
                const range_val = blk.builder.rangeMake(blk, range_ty, start, len_val, inclusive, loc);
                const rest_slice = blk.builder.indexOp(blk, slice_ty, value, range_val, loc);
                try bindPattern(self, ctx, a, env, f, blk, rest_pat, rest_slice, slice_ty);
            }
        },
        .VariantTuple => {
            // Pattern like Some(x, y, ...)
            const pr = a.pats.get(.VariantTuple, pid);
            const segs = a.pats.seg_pool.slice(pr.path);
            if (segs.len == 0) return;
            const case_name = a.pats.PathSeg.get(segs[segs.len - 1]).name;

            const tag_idx = self.tagIndexForCase(vty, case_name) orelse return;

            // Build the union type that sits at field #1 of the runtime variant value
            const union_ty = self.getUnionTypeFromVariant(vty) orelse return;

            // Grab the union payload aggregate from the variant value
            const union_agg = blk.builder.extractField(blk, union_ty, value, 1, loc);

            // Determine the concrete payload type for this case
            const payload_fields = self.context.type_store.field_pool.slice(
                self.context.type_store.get(.Union, union_ty).fields,
            );
            const fld = self.context.type_store.Field.get(payload_fields[tag_idx]);
            const payload_ty = fld.ty;

            const pelems = a.pats.pat_pool.slice(pr.elems);

            if (self.context.type_store.getKind(payload_ty) == .Tuple) {
                // Read the whole tuple payload value, then destructure
                const tuple_val = blk.builder.tirValue(.UnionField, blk, payload_ty, loc, .{
                    .base = union_agg,
                    .field_index = tag_idx,
                });

                const tr = self.context.type_store.get(.Tuple, payload_ty);
                const subtys = self.context.type_store.type_pool.slice(tr.elems);

                for (pelems, 0..) |pe, i| {
                    const ety = if (i < subtys.len) subtys[i] else self.context.type_store.tAny();
                    const ev = blk.builder.extractElem(blk, ety, tuple_val, @intCast(i), loc);
                    try bindPattern(self, ctx, a, env, f, blk, pe, ev, ety);
                }
            } else {
                // Single non-tuple payload
                const pv = blk.builder.tirValue(.UnionField, blk, payload_ty, loc, .{
                    .base = union_agg,
                    .field_index = tag_idx,
                });
                if (pelems.len > 0) {
                    try bindPattern(self, ctx, a, env, f, blk, pelems[0], pv, payload_ty);
                }
            }
        },
        .VariantStruct => {
            const vs = a.pats.get(.VariantStruct, pid);
            const vk = self.context.type_store.getKind(vty);
            if (vk == .Struct) {
                const pfields = a.pats.field_pool.slice(vs.fields);
                for (pfields) |pfid| {
                    const pf = a.pats.StructField.get(pfid);
                    const struct_ty = self.context.type_store.get(.Struct, vty);
                    const sfields = self.context.type_store.field_pool.slice(struct_ty.fields);
                    for (sfields, 0..) |sfid, i| {
                        const sf = self.context.type_store.Field.get(sfid);
                        if (sf.name.eq(pf.name)) {
                            const field_val = blk.builder.extractField(blk, sf.ty, value, @intCast(i), loc);
                            try bindPattern(self, ctx, a, env, f, blk, pf.pattern, field_val, sf.ty);
                            break;
                        }
                    }
                }
                return;
            }

            const segs = a.pats.seg_pool.slice(vs.path);
            if (segs.len == 0) return;
            const case_name = a.pats.PathSeg.get(segs[segs.len - 1]).name;

            const tag_idx = self.tagIndexForCase(vty, case_name) orelse return;

            const union_ty = self.getUnionTypeFromVariant(vty) orelse return;
            const union_agg = blk.builder.extractField(blk, union_ty, value, 1, loc);

            const payload_fields = self.context.type_store.field_pool.slice(
                self.context.type_store.get(.Union, union_ty).fields,
            );
            const fld = self.context.type_store.Field.get(payload_fields[tag_idx]);
            const payload_ty = fld.ty;

            const struct_val = blk.builder.tirValue(.UnionField, blk, payload_ty, loc, .{
                .base = union_agg,
                .field_index = tag_idx,
            });

            const pfields = a.pats.field_pool.slice(vs.fields);
            for (pfields) |pfid| {
                const pf = a.pats.StructField.get(pfid);
                const struct_ty = self.context.type_store.get(.Struct, payload_ty);
                const sfields = self.context.type_store.field_pool.slice(struct_ty.fields);
                for (sfields, 0..) |sfid, i| {
                    const sf = self.context.type_store.Field.get(sfid);
                    if (sf.name.eq(pf.name)) {
                        const field_val = blk.builder.extractField(blk, sf.ty, struct_val, @intCast(i), loc);
                        try bindPattern(self, ctx, a, env, f, blk, pf.pattern, field_val, sf.ty);
                        break;
                    }
                }
            }
        },
        // Other pattern forms can be added as needed.
        else => {},
    }
}
