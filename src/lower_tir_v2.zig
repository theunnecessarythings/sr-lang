const std = @import("std");
const ast = @import("ast_v2.zig");
const tir = @import("tir_v2.zig");
const types = @import("types_v2.zig");

const StrId = @import("cst_v2.zig").StrId;
const OptStrId = @import("cst_v2.zig").OptStrId;

pub const LowerTirV2 = struct {
    gpa: std.mem.Allocator,
    info: *types.TypeInfoV2,
    // Simple loop stack to support break/continue in While/For
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},

    pub fn init(gpa: std.mem.Allocator, info: *types.TypeInfoV2) LowerTirV2 {
        return .{ .gpa = gpa, .info = info };
    }

    pub fn run(self: *@This(), a: *const ast.Ast) !tir.TIR {
        var t = tir.TIR.init(self.gpa, &self.info.store);
        var b = Builder.init(self.gpa, &t);

        // Lower top-level decls: functions and globals
        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        for (decls) |did| try self.lowerTopDecl(a, &b, did);

        return t;
    }

    fn lowerTopDecl(self: *@This(), a: *const ast.Ast, b: *Builder, did: ast.DeclId) !void {
        const d = a.exprs.Decl.get(did.toRaw());
        const kind = a.exprs.index.kinds.items[d.value.toRaw()];
        if (kind == .FunctionLit and !a.exprs.get(.FunctionLit, d.value).flags.is_extern) {
            const name = if (!d.pattern.isNone()) self.bindingNameOfPattern(a, d.pattern.unwrap()) else null;
            if (name) |nm| {
                try self.lowerFunction(a, b, nm, d.value);
            }
            return;
        }
        // Global: only record type for now
        if (!d.pattern.isNone()) {
            const nm = self.bindingNameOfPattern(a, d.pattern.unwrap()) orelse return;
            const ty = self.getDeclType(did) orelse return;
            const sid = b.intern(a.exprs.strs.get(nm));
            _ = b.addGlobal(sid, ty);
        }
    }

    fn lowerFunction(self: *@This(), a: *const ast.Ast, b: *Builder, name: StrId, fun_eid: ast.ExprId) !void {
        const fid = self.getExprType(fun_eid) orelse return;
        // Expect a function type
        if (self.info.store.index.kinds.items[fid.toRaw()] != .Function) return;
        const fnty = self.info.store.Function.get(self.info.store.index.rows.items[fid.toRaw()]);

        const fname = b.intern(a.exprs.strs.get(name));
        var f = try b.beginFunction(fname, fnty.result);

        const fnr = a.exprs.get(.FunctionLit, fun_eid);
        // Params
        const params = a.exprs.param_pool.slice(fnr.params);
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = a.exprs.Param.get(params[i].toRaw());
            const pty = self.info.store.type_pool.slice(fnty.params)[i];
            const pname = if (!p.pat.isNone()) self.bindingNameOfPattern(a, p.pat.unwrap()) else null;
            _ = try b.addParam(&f, pname, pty);
        }

        // Entry block
        var blk = try b.beginBlock(&f);
        var env = Env.init(self.gpa);
        defer env.deinit(self.gpa);

        // Bind params in env
        i = 0;
        const param_vals = f.param_vals.items;
        while (i < params.len) : (i += 1) {
            const p = a.exprs.Param.get(params[i].toRaw());
            if (!p.pat.isNone()) {
                const pname = self.bindingNameOfPattern(a, p.pat.unwrap()) orelse continue;
                try env.bind(self.gpa, a, pname, .{ .value = param_vals[i], .is_slot = false });
            }
        }

        // Body is an ExprId to a Block
        if (!fnr.body.isNone()) {
            const body_id = fnr.body.unwrap();
            // function-level defer scope
            try env.pushScope(self.gpa);
            try self.lowerExprAsStmtList(a, &env, &f, &blk, body_id);
            _ = env.popScope();
        }

        // If no terminator, add void return
        if (blk.term.value == 0) {
            try b.setReturn(&blk, tir.OptValueId.none());
        }

        try b.endBlock(&f, blk);
        try b.endFunction(f);
    }

    fn lowerExprAsStmtList(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId) !void {
        if (a.exprs.index.kinds.items[id.toRaw()] == .Block) {
            const b = a.exprs.get(.Block, id);
            const stmts = a.stmts.stmt_pool.slice(b.items);
            try env.pushScope(self.gpa);
            for (stmts) |sid| try self.lowerStmt(a, env, f, blk, sid);
            _ = env.popScope();
        } else {
            // Single expression statement
            _ = try self.lowerExpr(a, env, f, blk, id);
        }
    }

    fn lowerStmt(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, sid: ast.StmtId) !void {
        const k = a.stmts.index.kinds.items[sid.toRaw()];
        switch (k) {
            .Expr => {
                const e = a.stmts.get(.Expr, sid).expr;
                _ = try self.lowerExpr(a, env, f, blk, e);
            },
            .Defer => {
                const d = a.stmts.get(.Defer, sid);
                try env.defers.append(self.gpa, .{ .expr = d.expr, .is_err = false });
            },
            .ErrDefer => {
                const d = a.stmts.get(.ErrDefer, sid);
                try env.defers.append(self.gpa, .{ .expr = d.expr, .is_err = true });
            },
            .Break => {
                const br = a.stmts.get(.Break, sid);
                // find nearest loop; ignore label for now except if provided and matches
                var target: ?LoopCtx = null;
                var i: isize = @as(isize, @intCast(self.loop_stack.items.len)) - 1;
                while (i >= 0) : (i -= 1) {
                    const lc = self.loop_stack.items[@intCast(i)];
                    if (br.label.isNone() or (lc.label != null and std.mem.eql(u8, lc.label.?, a.exprs.strs.get(br.label.unwrap())))) {
                        target = lc;
                        break;
                    }
                }
                if (target) |lc| {
                    // run normal defers from current down to loop entry
                    var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
                    while (j >= 0 and @as(u32, @intCast(j)) >= lc.defer_len_at_entry) : (j -= 1) {
                        const ent = env.defers.items[@intCast(j)];
                        if (!ent.is_err) _ = try self.lowerExpr(a, env, f, blk, ent.expr);
                    }
                    if (lc.has_result) {
                        const v = if (!br.value.isNone()) try self.lowerExpr(a, env, f, blk, br.value.unwrap()) else f.builder.constUndef(blk, lc.res_ty);
                        try f.builder.br(blk, lc.join_block, &.{v});
                    } else {
                        try f.builder.br(blk, lc.break_block, &.{});
                    }
                } else {
                    return error.OutOfMemory; // no loop context
                }
            },
            .Continue => {
                const lc = if (self.loop_stack.items.len > 0) self.loop_stack.items[self.loop_stack.items.len - 1] else return error.OutOfMemory;
                // run normal defers from current down to loop entry
                var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
                while (j >= 0 and @as(u32, @intCast(j)) >= lc.defer_len_at_entry) : (j -= 1) {
                    const ent = env.defers.items[@intCast(j)];
                    if (!ent.is_err) _ = try self.lowerExpr(a, env, f, blk, ent.expr);
                }
                try f.builder.br(blk, lc.continue_block, &.{});
            },
            .Decl => {
                const drow = a.stmts.get(.Decl, sid);
                const d = a.exprs.Decl.get(drow.decl.toRaw());
                const val = try self.lowerExpr(a, env, f, blk, d.value);
                if (!d.pattern.isNone()) {
                    const nm = self.bindingNameOfPattern(a, d.pattern.unwrap()) orelse return;
                    if (d.flags.is_const) {
                        try env.bind(self.gpa, a, nm, .{ .value = val, .is_slot = false });
                    } else {
                        const vty = self.getExprType(d.value) orelse return;
                        const slot_ty = self.info.store.mkPtr(vty, false);
                        const slot = f.builder.alloca(blk, slot_ty, tir.OptValueId.none(), 0);
                        _ = f.builder.store(blk, vty, slot, val, 0);
                        try env.bind(self.gpa, a, nm, .{ .value = slot, .is_slot = true });
                    }
                }
            },
            .Assign => {
                const as = a.stmts.get(.Assign, sid);
                const lhs_ptr = try self.lowerAddress(a, env, f, blk, as.left);
                const rhs = try self.lowerExpr(a, env, f, blk, as.right);
                const rty = self.getExprType(as.right) orelse return;
                _ = f.builder.store(blk, rty, lhs_ptr, rhs, 0);
            },
            .Return => {
                const r = a.stmts.get(.Return, sid);
                // run normal defers (ignore err-only for now)
                var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
                while (j >= 0) : (j -= 1) {
                    const ent = env.defers.items[@intCast(j)];
                    if (!ent.is_err) {
                        _ = try self.lowerExpr(a, env, f, blk, ent.expr);
                    }
                }
                if (!r.value.isNone()) {
                    const v = try self.lowerExpr(a, env, f, blk, r.value.unwrap());
                    // If we have err-defer entries, run them conditionally based on builtin.err.is_err(v)
                    var has_err_defer = false;
                    for (env.defers.items) |ent2| {
                        if (ent2.is_err) {
                            has_err_defer = true;
                            break;
                        }
                    }
                    if (has_err_defer) {
                        var then_blk = try f.builder.beginBlock(f);
                        var cont_blk = try f.builder.beginBlock(f);
                        const is_err_name = f.builder.intern("builtin.err.is_err");
                        const is_err = blk.builder.call(blk, self.info.store.tBool(), is_err_name, &.{v});
                        try f.builder.condBr(blk, is_err, then_blk.id, &.{}, cont_blk.id, &.{});
                        // then: run err-only defers, then return
                        var kk: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
                        while (kk >= 0) : (kk -= 1) {
                            const ent3 = env.defers.items[@intCast(kk)];
                            if (ent3.is_err) _ = try self.lowerExpr(a, env, f, &then_blk, ent3.expr);
                        }
                        try f.builder.setReturnVal(&then_blk, v);
                        try f.builder.endBlock(f, then_blk);
                        // else: return directly
                        try f.builder.setReturnVal(&cont_blk, v);
                        blk.* = cont_blk;
                    } else {
                        try f.builder.setReturnVal(blk, v);
                    }
                } else {
                    try f.builder.setReturnVoid(blk);
                }
            },
            .Unreachable => {
                try f.builder.setUnreachable(blk);
            },
            else => {},
        }
    }

    fn lowerExpr(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId) anyerror!tir.ValueId {
        const k = a.exprs.index.kinds.items[id.toRaw()];
        switch (k) {
            .Literal => {
                const lit = a.exprs.get(.Literal, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                return switch (lit.kind) {
                    .int => blk.builder.constInt(blk, ty, try std.fmt.parseInt(i64, a.exprs.strs.get(lit.value.unwrap()), 10)),
                    .float => blk.builder.constFloat(blk, ty, try std.fmt.parseFloat(f64, a.exprs.strs.get(lit.value.unwrap()))),
                    .bool => blk.builder.constBool(blk, ty, lit.bool_value),
                    .string => blk.builder.constString(blk, ty, a.exprs.strs.get(lit.value.unwrap())),
                    .char => blk.builder.constInt(blk, ty, @as(i64, @intCast(lit.char_value))),
                };
            },
            .NullLit => {
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                return blk.builder.constNull(blk, ty);
            },
            .UndefLit => {
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                return blk.builder.constUndef(blk, ty);
            },
            .Unary => {
                const row = a.exprs.get(.Unary, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const v = try self.lowerExpr(a, env, f, blk, row.expr);
                return switch (row.op) {
                    .plus => v,
                    .minus => blk.builder.bin(blk, .Sub, ty, blk.builder.constInt(blk, ty, 0), v),
                    .logical_not => blk.builder.un1(blk, .LogicalNot, self.info.store.tBool(), v),
                    .address_of => blk.builder.addressOf(blk, self.info.store.mkPtr(ty, false), v),
                };
            },
            .Range => {
                const row = a.exprs.get(.Range, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const start_v = if (!row.start.isNone()) try self.lowerExpr(a, env, f, blk, row.start.unwrap()) else blk.builder.constUndef(blk, ty);
                const end_v = if (!row.end.isNone()) try self.lowerExpr(a, env, f, blk, row.end.unwrap()) else blk.builder.constUndef(blk, ty);
                const incl = blk.builder.constBool(blk, self.info.store.tBool(), row.inclusive_right);
                const make = blk.builder.intern("builtin.range.make");
                return blk.builder.call(blk, ty, make, &.{ start_v, end_v, incl });
            },
            .Deref => {
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const row = a.exprs.get(.Deref, id);
                const ptr = try self.lowerExpr(a, env, f, blk, row.expr);
                return blk.builder.load(blk, ty, ptr, 0);
            },
            .TupleLit => {
                const row = a.exprs.get(.TupleLit, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const ids = a.exprs.expr_pool.slice(row.elems);
                var vals = try self.gpa.alloc(tir.ValueId, ids.len);
                defer self.gpa.free(vals);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) vals[i] = try self.lowerExpr(a, env, f, blk, ids[i]);
                return blk.builder.tupleMake(blk, ty, vals);
            },
            .ArrayLit => {
                const row = a.exprs.get(.ArrayLit, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const ids = a.exprs.expr_pool.slice(row.elems);
                var vals = try self.gpa.alloc(tir.ValueId, ids.len);
                defer self.gpa.free(vals);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) vals[i] = try self.lowerExpr(a, env, f, blk, ids[i]);
                return blk.builder.arrayMake(blk, ty, vals);
            },
            .StructLit => {
                const row = a.exprs.get(.StructLit, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const fids = a.exprs.sfv_pool.slice(row.fields);
                var fields = try self.gpa.alloc(tir.Rows.StructFieldInit, fids.len);
                defer self.gpa.free(fields);
                var i: usize = 0;
                while (i < fids.len) : (i += 1) {
                    const sfv = a.exprs.StructFieldValue.get(fids[i].toRaw());
                    const v = try self.lowerExpr(a, env, f, blk, sfv.value);
                    var name_opt = OptStrId.none();
                    if (!sfv.name.isNone()) {
                        const nm = a.exprs.strs.get(sfv.name.unwrap());
                        name_opt = OptStrId.some(blk.builder.intern(nm));
                    }
                    fields[i] = .{ .index = @intCast(i), .name = name_opt, .value = v };
                }
                return blk.builder.structMake(blk, ty, fields);
            },
            .MapLit => {
                const row = a.exprs.get(.MapLit, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const kv_ids = a.exprs.kv_pool.slice(row.entries);
                var vals = try self.gpa.alloc(tir.ValueId, kv_ids.len * 2);
                defer self.gpa.free(vals);
                var j: usize = 0;
                for (kv_ids) |kid| {
                    const kv = a.exprs.KeyValue.get(kid.toRaw());
                    vals[j] = try self.lowerExpr(a, env, f, blk, kv.key);
                    j += 1;
                    vals[j] = try self.lowerExpr(a, env, f, blk, kv.value);
                    j += 1;
                }
                const make = blk.builder.intern("builtin.map.from_kv");
                return blk.builder.call(blk, ty, make, vals);
            },
            .IndexAccess => {
                const row = a.exprs.get(.IndexAccess, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const base = try self.lowerExpr(a, env, f, blk, row.collection);
                const idx = try self.lowerExpr(a, env, f, blk, row.index);
                return blk.builder.indexOp(blk, ty, base, idx);
            },
            .FieldAccess => {
                const row = a.exprs.get(.FieldAccess, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const base = try self.lowerExpr(a, env, f, blk, row.parent);
                if (row.is_tuple) {
                    const idx = try std.fmt.parseInt(u32, a.exprs.strs.get(row.field), 10);
                    return blk.builder.extractElem(blk, ty, base, idx);
                } else {
                    // best-effort: field index unresolved -> use 0
                    return blk.builder.extractField(blk, ty, base, 0);
                }
            },
            .Block => {
                const res_ty = self.getExprType(id) orelse self.info.store.tVoid();
                return try self.lowerBlockExprValue(a, env, f, blk, id, res_ty);
            },
            .Ident => {
                const row = a.exprs.get(.Ident, id);
                const name = a.exprs.strs.get(row.name);
                const bnd = env.lookup(name) orelse return error.OutOfMemory;
                if (bnd.is_slot) {
                    const ety = self.getExprType(id) orelse return error.OutOfMemory;
                    return blk.builder.load(blk, ety, bnd.value, 0);
                } else return bnd.value;
            },
            .Binary => {
                const row = a.exprs.get(.Binary, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const l = try self.lowerExpr(a, env, f, blk, row.left);
                const r = try self.lowerExpr(a, env, f, blk, row.right);
                return switch (row.op) {
                    .add => blk.builder.bin(blk, .Add, ty, l, r),
                    .sub => blk.builder.bin(blk, .Sub, ty, l, r),
                    .mul => blk.builder.bin(blk, .Mul, ty, l, r),
                    .div => blk.builder.bin(blk, .Div, ty, l, r),
                    .mod => blk.builder.bin(blk, .Mod, ty, l, r),
                    .shl => blk.builder.bin(blk, .Shl, ty, l, r),
                    .shr => blk.builder.bin(blk, .Shr, ty, l, r),
                    .bit_and => blk.builder.bin(blk, .BitAnd, ty, l, r),
                    .bit_or => blk.builder.bin(blk, .BitOr, ty, l, r),
                    .bit_xor => blk.builder.bin(blk, .BitXor, ty, l, r),
                    .eq => blk.builder.binBool(blk, .CmpEq, l, r),
                    .neq => blk.builder.binBool(blk, .CmpNe, l, r),
                    .lt => blk.builder.binBool(blk, .CmpLt, l, r),
                    .lte => blk.builder.binBool(blk, .CmpLe, l, r),
                    .gt => blk.builder.binBool(blk, .CmpGt, l, r),
                    .gte => blk.builder.binBool(blk, .CmpGe, l, r),
                    .logical_and => blk.builder.binBool(blk, .LogicalAnd, l, r),
                    .logical_or => blk.builder.binBool(blk, .LogicalOr, l, r),
                    .@"orelse" => blk: {
                        // optional-or-else: if lhs is some -> unwrap, else rhs
                        // Build CFG: then=unwrap(lhs), else=rhs, join with result param
                        var then_blk = try f.builder.beginBlock(f);
                        var else_blk = try f.builder.beginBlock(f);
                        var join_blk = try f.builder.beginBlock(f);
                        const s_is_some = f.builder.intern("builtin.opt.is_some");
                        const cond_v = blk.builder.call(blk, self.info.store.tBool(), s_is_some, &.{l});
                        try f.builder.condBr(blk, cond_v, then_blk.id, &.{}, else_blk.id, &.{});
                        const res_ty = ty;
                        const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
                        // then: unwrap
                        const s_unwrap = f.builder.intern("builtin.opt.unwrap");
                        const unwrapped = blk.builder.call(&then_blk, res_ty, s_unwrap, &.{l});
                        try f.builder.br(&then_blk, join_blk.id, &.{unwrapped});
                        // else: rhs (already computed)
                        try f.builder.br(&else_blk, join_blk.id, &.{r});
                        try f.builder.endBlock(f, then_blk);
                        try f.builder.endBlock(f, else_blk);
                        blk.* = join_blk;
                        break :blk res_param;
                    },
                };
            },
            .Catch => {
                const row = a.exprs.get(.Catch, id);
                // if ok(expr) then unwrap_ok(expr) else { bind err?; handler }
                var then_blk = try f.builder.beginBlock(f);
                var else_blk = try f.builder.beginBlock(f);
                var join_blk = try f.builder.beginBlock(f);
                const lhs = try self.lowerExpr(a, env, f, blk, row.expr);
                const s_is_ok = f.builder.intern("builtin.err.is_ok");
                const is_ok = blk.builder.call(blk, self.info.store.tBool(), s_is_ok, &.{lhs});
                try f.builder.condBr(blk, is_ok, then_blk.id, &.{}, else_blk.id, &.{});
                const res_ty = self.getExprType(id) orelse self.info.store.tVoid();
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
                // then: unwrap ok
                const s_unwrap_ok = f.builder.intern("builtin.err.unwrap_ok");
                const okv = blk.builder.call(&then_blk, res_ty, s_unwrap_ok, &.{lhs});
                try f.builder.br(&then_blk, join_blk.id, &.{okv});
                // else: optionally bind error and evaluate handler
                // For now, skip binding; name is available in row.binding_name
                try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
                if (else_blk.term.value == 0) {
                    const hv = try self.lowerBlockExprValue(a, env, f, &else_blk, row.handler, res_ty);
                    try f.builder.br(&else_blk, join_blk.id, &.{hv});
                }
                try f.builder.endBlock(f, then_blk);
                try f.builder.endBlock(f, else_blk);
                blk.* = join_blk;
                return res_param;
            },
            .If => {
                const row = a.exprs.get(.If, id);
                var then_blk = try f.builder.beginBlock(f);
                var else_blk = try f.builder.beginBlock(f);
                var join_blk = try f.builder.beginBlock(f);
                const cond_v = try self.lowerExpr(a, env, f, blk, row.cond);
                try f.builder.condBr(blk, cond_v, then_blk.id, &.{}, else_blk.id, &.{});
                const res_ty = self.getExprType(id) orelse self.info.store.tVoid();
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
                // then arm value
                var then_val: tir.ValueId = undefined;
                try self.lowerExprAsStmtList(a, env, f, &then_blk, row.then_block);
                if (then_blk.term.value == 0) {
                    // If the then block did not end in a terminator, compute a value
                    then_val = try self.lowerBlockExprValue(a, env, f, &then_blk, row.then_block, res_ty);
                    try f.builder.br(&then_blk, join_blk.id, &.{then_val});
                }
                // else arm value (if present)
                var else_val: tir.ValueId = undefined;
                if (!row.else_block.isNone()) {
                    try self.lowerExprAsStmtList(a, env, f, &else_blk, row.else_block.unwrap());
                    if (else_blk.term.value == 0) {
                        else_val = try self.lowerBlockExprValue(a, env, f, &else_blk, row.else_block.unwrap(), res_ty);
                        try f.builder.br(&else_blk, join_blk.id, &.{else_val});
                    }
                } else {
                    if (else_blk.term.value == 0) {
                        // No else: pass undef of result type
                        else_val = f.builder.constUndef(&else_blk, res_ty);
                        try f.builder.br(&else_blk, join_blk.id, &.{else_val});
                    }
                }
                try f.builder.endBlock(f, then_blk);
                try f.builder.endBlock(f, else_blk);
                blk.* = join_blk;
                return res_param;
            },
            .Call => {
                const row = a.exprs.get(.Call, id);
                const callee_k = a.exprs.index.kinds.items[row.callee.toRaw()];
                if (callee_k != .Ident) return error.OutOfMemory;
                const name = a.exprs.strs.get(a.exprs.get(.Ident, row.callee).name);
                const sname = f.builder.intern(name);
                const args_ids = a.exprs.expr_pool.slice(row.args);
                var vals = try self.gpa.alloc(tir.ValueId, args_ids.len);
                defer self.gpa.free(vals);
                var j: usize = 0;
                while (j < args_ids.len) : (j += 1) vals[j] = try self.lowerExpr(a, env, f, blk, args_ids[j]);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                return blk.builder.call(blk, ty, sname, vals);
            },
            .Cast => {
                const row = a.exprs.get(.Cast, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const v = try self.lowerExpr(a, env, f, blk, row.expr);
                return switch (row.kind) {
                    .normal => blk.builder.cast(blk, .CastNormal, ty, v),
                    .bitcast => blk.builder.cast(blk, .CastBit, ty, v),
                    .saturate => blk.builder.cast(blk, .CastSaturate, ty, v),
                    .wrap => blk.builder.cast(blk, .CastWrap, ty, v),
                    .checked => blk.builder.cast(blk, .CastChecked, ty, v),
                };
            },
            .OptionalUnwrap => {
                const row = a.exprs.get(.OptionalUnwrap, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const v = try self.lowerExpr(a, env, f, blk, row.expr);
                const unwrap = blk.builder.intern("builtin.opt.unwrap");
                return blk.builder.call(blk, ty, unwrap, &.{v});
            },
            .ErrUnwrap => {
                const row = a.exprs.get(.ErrUnwrap, id);
                const ty = self.getExprType(id) orelse return error.OutOfMemory;
                const v = try self.lowerExpr(a, env, f, blk, row.expr);
                const unwrap_ok = blk.builder.intern("builtin.err.unwrap_ok");
                return blk.builder.call(blk, ty, unwrap_ok, &.{v});
            },
            .Match => {
                const row = a.exprs.get(.Match, id);
                const scrut = try self.lowerExpr(a, env, f, blk, row.expr);
                const res_ty = self.getExprType(id) orelse self.info.store.tVoid();
                var join_blk = try f.builder.beginBlock(f);
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
                const arms = a.exprs.arm_pool.slice(row.arms);
                if (arms.len == 0) return blk.builder.constUndef(blk, res_ty);
                // detect literal-int only match (no guards)
                var all_int = true;
                var values_buf = self.gpa.alloc(u64, arms.len) catch @panic("OOM");
                defer self.gpa.free(values_buf);
                var i: usize = 0;
                while (i < arms.len) : (i += 1) {
                    const arm = a.exprs.MatchArm.get(arms[i].toRaw());
                    if (!arm.guard.isNone()) {
                        all_int = false;
                        break;
                    }
                    const pk = a.pats.index.kinds.items[arm.pattern.toRaw()];
                    if (pk != .Literal) {
                        all_int = false;
                        break;
                    }
                    const pr = a.pats.get(.Literal, arm.pattern);
                    if (a.exprs.index.kinds.items[pr.expr.toRaw()] != .Literal) {
                        all_int = false;
                        break;
                    }
                    const lit = a.exprs.get(.Literal, pr.expr);
                    if (lit.kind != .int or lit.value.isNone()) {
                        all_int = false;
                        break;
                    }
                    values_buf[i] = std.fmt.parseInt(u64, a.exprs.strs.get(lit.value.unwrap()), 10) catch {
                        all_int = false;
                        break;
                    };
                }
                if (all_int) {
                    // build body blocks
                    var dests = self.gpa.alloc(Builder.SwitchDest, arms.len) catch @panic("OOM");
                    defer self.gpa.free(dests);
                    var bodies = try self.gpa.alloc(@TypeOf(try f.builder.beginBlock(f)), arms.len);
                    defer self.gpa.free(bodies);
                    i = 0;
                    while (i < arms.len) : (i += 1) bodies[i] = try f.builder.beginBlock(f);
                    // default next block
                    var def_blk = try f.builder.beginBlock(f);
                    // emit switch
                    try f.builder.switchInt(blk, scrut, values_buf, blk: {
                        i = 0;
                        while (i < arms.len) : (i += 1) {
                            dests[i] = .{ .dest = bodies[i].id, .args = &.{} };
                        }
                        break :blk dests;
                    }, def_blk.id, &.{});
                    // bodies -> join
                    i = 0;
                    while (i < arms.len) : (i += 1) {
                        try self.lowerExprAsStmtList(a, env, f, &bodies[i], a.exprs.MatchArm.get(arms[i].toRaw()).body);
                        if (bodies[i].term.value == 0) {
                            const v = try self.lowerBlockExprValue(a, env, f, &bodies[i], a.exprs.MatchArm.get(arms[i].toRaw()).body, res_ty);
                            try f.builder.br(&bodies[i], join_blk.id, &.{v});
                        }
                        try f.builder.endBlock(f, bodies[i]);
                    }
                    // default -> undef -> join
                    const uv = f.builder.constUndef(&def_blk, res_ty);
                    try f.builder.br(&def_blk, join_blk.id, &.{uv});
                    try f.builder.endBlock(f, def_blk);
                    blk.* = join_blk;
                    return res_param;
                } else {
                    // fallback chained tests with guards
                    var cur_blk = blk.*;
                    i = 0;
                    while (i < arms.len) : (i += 1) {
                        const arm_id = arms[i];
                        const arm = a.exprs.MatchArm.get(arm_id.toRaw());
                        var test_blk = try f.builder.beginBlock(f);
                        var body_blk = try f.builder.beginBlock(f);
                        const next_blk = if (i + 1 < arms.len) try f.builder.beginBlock(f) else join_blk;
                        try f.builder.br(&cur_blk, test_blk.id, &.{});
                        const pat_ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut);
                        var final_ok = pat_ok;
                        if (!arm.guard.isNone()) {
                            const g = try self.lowerExpr(a, env, f, &test_blk, arm.guard.unwrap());
                            final_ok = test_blk.builder.binBool(&test_blk, .LogicalAnd, final_ok, g);
                        }
                        try f.builder.condBr(&test_blk, final_ok, body_blk.id, &.{}, next_blk.id, &.{});
                        try self.lowerExprAsStmtList(a, env, f, &body_blk, arm.body);
                        if (body_blk.term.value == 0) {
                            const v = try self.lowerBlockExprValue(a, env, f, &body_blk, arm.body, res_ty);
                            try f.builder.br(&body_blk, join_blk.id, &.{v});
                        }
                        try f.builder.endBlock(f, test_blk);
                        try f.builder.endBlock(f, body_blk);
                        cur_blk = next_blk;
                    }
                    blk.* = join_blk;
                    return res_param;
                }
            },
            .While => {
                const row = a.exprs.get(.While, id);
                var header = try f.builder.beginBlock(f);
                var body = try f.builder.beginBlock(f);
                var exit_blk = try f.builder.beginBlock(f);
                var join_blk = try f.builder.beginBlock(f);
                const res_ty = self.getExprType(id) orelse self.info.store.tVoid();
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
                try f.builder.br(blk, header.id, &.{});
                const cond_v = if (!row.cond.isNone()) try self.lowerExpr(a, env, f, &header, row.cond.unwrap()) else f.builder.constBool(&header, self.info.store.tBool(), true);
                try f.builder.condBr(&header, cond_v, body.id, &.{}, exit_blk.id, &.{});
                // push loop context for break/continue with result join
                try self.loop_stack.append(self.gpa, .{
                    .label = if (!row.label.isNone()) a.exprs.strs.get(row.label.unwrap()) else null,
                    .continue_block = header.id,
                    .break_block = exit_blk.id,
                    .has_result = true,
                    .join_block = join_blk.id,
                    .res_param = res_param,
                    .res_ty = res_ty,
                    .defer_len_at_entry = @intCast(env.defers.items.len),
                });
                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.value == 0) try f.builder.br(&body, header.id, &.{});
                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
                // exit -> join undef
                const uv = f.builder.constUndef(&exit_blk, res_ty);
                try f.builder.br(&exit_blk, join_blk.id, &.{uv});
                try f.builder.endBlock(f, exit_blk);
                _ = self.loop_stack.pop();
                blk.* = join_blk;
                return res_param;
            },
            .For => {
                const row = a.exprs.get(.For, id);
                // Blocks
                var header = try f.builder.beginBlock(f);
                var body = try f.builder.beginBlock(f);
                var exit_blk = try f.builder.beginBlock(f);
                var join_blk = try f.builder.beginBlock(f);
                const res_ty = self.getExprType(id) orelse self.info.store.tVoid();
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

                // loop context
                try self.loop_stack.append(self.gpa, .{ .label = if (!row.label.isNone()) a.exprs.strs.get(row.label.unwrap()) else null, .continue_block = header.id, .break_block = exit_blk.id });

                // Range-based or collection-based
                if (a.exprs.index.kinds.items[row.iterable.toRaw()] == .Range) {
                    const rg = a.exprs.get(.Range, row.iterable);
                    if (rg.start.isNone() or rg.end.isNone()) return error.OutOfMemory;
                    const start_v = try self.lowerExpr(a, env, f, blk, rg.start.unwrap());
                    const end_v = try self.lowerExpr(a, env, f, blk, rg.end.unwrap());
                    const idx_ty = self.getExprType(rg.start.unwrap()) orelse return error.OutOfMemory;
                    const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);
                    try f.builder.br(blk, header.id, &.{start_v});
                    // header cond
                    const cond = if (rg.inclusive_right)
                        blk.builder.binBool(&header, .CmpLe, idx_param, end_v)
                    else
                        blk.builder.binBool(&header, .CmpLt, idx_param, end_v);
                    try f.builder.condBr(&header, cond, body.id, &.{}, exit_blk.id, &.{});
                    // body
                    try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                    if (body.term.value == 0) {
                        const one = blk.builder.constInt(&body, idx_ty, 1);
                        const next_i = blk.builder.bin(&body, .Add, idx_ty, idx_param, one);
                        try f.builder.br(&body, header.id, &.{next_i});
                    }
                } else {
                    // collection-based via index
                    const arr_v = try self.lowerExpr(a, env, f, blk, row.iterable);
                    const idx_ty = self.info.store.tUsize();
                    const s_len = f.builder.intern("builtin.len");
                    const len_v = blk.builder.call(blk, idx_ty, s_len, &.{arr_v});
                    const zero = blk.builder.constInt(blk, idx_ty, 0);
                    const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);
                    try f.builder.br(blk, header.id, &.{zero});
                    const cond = blk.builder.binBool(&header, .CmpLt, idx_param, len_v);
                    try f.builder.condBr(&header, cond, body.id, &.{}, exit_blk.id, &.{});
                    // body: element = arr[idx]
                    const elem_ty = self.info.store.tAny();
                    const elem = blk.builder.indexOp(&body, elem_ty, arr_v, idx_param);
                    // bind pattern to element
                    try self.bindPattern(a, env, f, &body, row.pattern, elem, elem_ty);
                    try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                    if (body.term.value == 0) {
                        const one = blk.builder.constInt(&body, idx_ty, 1);
                        const next_i = blk.builder.bin(&body, .Add, idx_ty, idx_param, one);
                        try f.builder.br(&body, header.id, &.{next_i});
                    }
                }
                // pop loop
                _ = self.loop_stack.pop();
                // exit -> join with undef if no value
                const uv = blk.builder.constUndef(&exit_blk, res_ty);
                try f.builder.br(&exit_blk, join_blk.id, &.{uv});
                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
                try f.builder.endBlock(f, exit_blk);
                blk.* = join_blk;
                return res_param;
            },
            else => return error.OutOfMemory,
        }
    }

    // Compute the value of a block expression: evaluate last expression or return undef of expected type
    fn lowerBlockExprValue(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, block_expr: ast.ExprId, expected_ty: types.TypeId) anyerror!tir.ValueId {
        if (a.exprs.index.kinds.items[block_expr.toRaw()] != .Block) {
            // Not a block; just lower as expression
            return self.lowerExpr(a, env, f, blk, block_expr);
        }
        const b = a.exprs.get(.Block, block_expr);
        const stmts = a.stmts.stmt_pool.slice(b.items);
        if (stmts.len == 0) return f.builder.constUndef(blk, expected_ty);
        // Run all but last as statements
        var i: usize = 0;
        while (i + 1 < stmts.len) : (i += 1) {
            try self.lowerStmt(a, env, f, blk, stmts[i]);
        }
        const last = stmts[stmts.len - 1];
        const lk = a.stmts.index.kinds.items[last.toRaw()];
        if (lk == .Expr) {
            const le = a.stmts.get(.Expr, last).expr;
            return self.lowerExpr(a, env, f, blk, le);
        } else {
            try self.lowerStmt(a, env, f, blk, last);
            return f.builder.constUndef(blk, expected_ty);
        }
    }

    fn lowerAddress(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId) anyerror!tir.ValueId {
        const k = a.exprs.index.kinds.items[id.toRaw()];
        switch (k) {
            .Ident => {
                const row = a.exprs.get(.Ident, id);
                const name = a.exprs.strs.get(row.name);
                const bnd = env.lookup(name) orelse return error.OutOfMemory;
                if (bnd.is_slot) return bnd.value;
                // take address of immutable -> alloca+store then return slot
                const ety = self.getExprType(id) orelse return error.OutOfMemory;
                const slot_ty = self.info.store.mkPtr(ety, false);
                const slot = f.builder.alloca(blk, slot_ty, tir.OptValueId.none(), 0);
                _ = f.builder.store(blk, ety, slot, bnd.value, 0);
                return slot;
            },
            .FieldAccess => {
                const row = a.exprs.get(.FieldAccess, id);
                const parent_ptr = try self.lowerAddress(a, env, f, blk, row.parent);
                var pty = self.getExprType(row.parent) orelse return error.OutOfMemory;
                // unwrap pointer type for element lookup
                if (self.info.store.index.kinds.items[pty.toRaw()] == .Ptr) {
                    const prow = self.info.store.Ptr.get(self.info.store.index.rows.items[pty.toRaw()]);
                    pty = prow.elem;
                }
                var idx_val: u32 = 0;
                if (row.is_tuple) {
                    idx_val = try std.fmt.parseInt(u32, a.exprs.strs.get(row.field), 10);
                } else {
                    if (self.info.store.index.kinds.items[pty.toRaw()] == .Struct) {
                        const srow = self.info.store.Struct.get(self.info.store.index.rows.items[pty.toRaw()]);
                        const fids = self.info.store.field_pool.slice(srow.fields);
                        const target = a.exprs.strs.get(row.field);
                        var i: u32 = 0;
                        while (i < fids.len) : (i += 1) {
                            const fr = self.info.store.Field.get(fids[i].toRaw());
                            if (std.mem.eql(u8, self.info.store.strs.get(fr.name), target)) {
                                idx_val = i;
                                break;
                            }
                        }
                    } else idx_val = 0;
                }
                const idx = blk.builder.gepConst(idx_val);
                const rty = self.info.store.mkPtr(self.getExprType(id) orelse return error.OutOfMemory, false);
                return blk.builder.gep(blk, rty, parent_ptr, &.{idx});
            },
            .IndexAccess => {
                const row = a.exprs.get(.IndexAccess, id);
                const base_ptr = try self.lowerAddress(a, env, f, blk, row.collection);
                const idx_v = try self.lowerExpr(a, env, f, blk, row.index);
                const idx = blk.builder.gepValue(idx_v);
                const rty = self.info.store.mkPtr(self.getExprType(id) orelse return error.OutOfMemory, false);
                return blk.builder.gep(blk, rty, base_ptr, &.{idx});
            },
            else => return error.OutOfMemory,
        }
    }

    fn getExprType(self: *const @This(), id: ast.ExprId) ?types.TypeId {
        return self.info.expr_types.items[id.toRaw()];
    }
    fn getDeclType(self: *const @This(), did: ast.DeclId) ?types.TypeId {
        return self.info.decl_types.items[did.toRaw()];
    }

    fn bindingNameOfPattern(_: *const @This(), a: *const ast.Ast, pid: ast.PatternId) ?StrId {
        const k = a.pats.index.kinds.items[pid.toRaw()];
        return switch (k) {
            .Binding => a.pats.get(.Binding, pid).name,
            else => null,
        };
    }

    fn bindPattern(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, value: tir.ValueId, vty: types.TypeId) !void {
        const k = a.pats.index.kinds.items[pid.toRaw()];
        switch (k) {
            .Binding => {
                const nm = a.pats.get(.Binding, pid).name;
                try env.bind(self.gpa, a, nm, .{ .value = value, .is_slot = false });
            },
            .Tuple => {
                const row = a.pats.get(.Tuple, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                var i: usize = 0;
                // Try to use tuple element types if available
                var etys: []const types.TypeId = &[_]types.TypeId{};
                const vk = self.info.store.index.kinds.items[vty.toRaw()];
                if (vk == .Tuple) {
                    const vrow = self.info.store.Tuple.get(self.info.store.index.rows.items[vty.toRaw()]);
                    etys = self.info.store.type_pool.slice(vrow.elems);
                }
                while (i < elems.len) : (i += 1) {
                    const ety = if (i < etys.len) etys[i] else self.info.store.tAny();
                    const ev = blk.builder.extractElem(blk, ety, value, @intCast(i));
                    try self.bindPattern(a, env, f, blk, elems[i], ev, ety);
                }
            },
            else => {
                // Fallback: bind nothing; full pattern space handled in later sweep
            },
        }
    }
    fn matchPattern(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, scrut: tir.ValueId) !tir.ValueId {
        // env used via lowerExpr in some branches
        const k = a.pats.index.kinds.items[pid.toRaw()];
        switch (k) {
            .Wildcard => return blk.builder.constBool(blk, self.info.store.tBool(), true),
            .Literal => {
                const pr = a.pats.get(.Literal, pid);
                const litv = try self.lowerExpr(a, env, f, blk, pr.expr);
                return blk.builder.binBool(blk, .CmpEq, scrut, litv);
            },
            .Binding, .Path, .Tuple, .Slice, .Struct, .VariantTuple, .VariantStruct, .Range, .Or, .At => {
                return blk.builder.constBool(blk, self.info.store.tBool(), true);
            },
        }
    }
};

const LoopCtx = struct {
    label: ?[]const u8,
    continue_block: tir.BlockId,
    break_block: tir.BlockId,
    // expression result join (optional)
    has_result: bool = false,
    join_block: tir.BlockId = tir.BlockId.fromRaw(0),
    res_param: tir.ValueId = tir.ValueId.fromRaw(0),
    res_ty: types.TypeId = undefined,
    // defers to run when exiting loop via break/continue
    defer_len_at_entry: u32 = 0,
};

const Env = struct {
    map: std.StringHashMapUnmanaged(ValueBinding) = .{},
    defers: std.ArrayListUnmanaged(DeferEntry) = .{},
    marks: std.ArrayListUnmanaged(u32) = .{},
    fn init(_: std.mem.Allocator) Env {
        return .{ .map = .{} };
    }
    fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
        self.map.deinit(gpa);
        self.defers.deinit(gpa);
        self.marks.deinit(gpa);
    }
    fn bind(self: *@This(), gpa: std.mem.Allocator, a: *const ast.Ast, name: StrId, vb: ValueBinding) !void {
        const s = a.exprs.strs.get(name);
        try self.map.put(gpa, s, vb);
    }
    fn lookup(self: *@This(), s: []const u8) ?ValueBinding {
        return self.map.get(s);
    }
    fn pushScope(self: *@This(), gpa: std.mem.Allocator) !void {
        try self.marks.append(gpa, @intCast(self.defers.items.len));
    }
    fn popScope(self: *@This()) u32 {
        if (self.marks.items.len == 0) return 0;
        const mark = self.marks.items[self.marks.items.len - 1];
        self.marks.items.len -= 1;
        self.defers.items.len = mark;
        return mark;
    }
};

const ValueBinding = struct { value: tir.ValueId, is_slot: bool };
const DeferEntry = struct { expr: ast.ExprId, is_err: bool };

const Builder = struct {
    gpa: std.mem.Allocator,
    t: *tir.TIR,
    next_value: u32 = 0,

    pub fn init(gpa: std.mem.Allocator, t: *tir.TIR) Builder {
        return .{ .gpa = gpa, .t = t };
    }

    fn freshValue(self: *@This()) tir.ValueId {
        const id = tir.ValueId.fromRaw(self.next_value);
        self.next_value += 1;
        return id;
    }
    // no-op duplicate; remove
    fn globalName(self: *@This(), s: []const u8) StrId {
        return self.intern(s);
    }

    pub const FunctionFrame = struct {
        builder: *Builder,
        id: tir.FuncId,
        param_vals: std.ArrayListUnmanaged(tir.ValueId) = .{},
        param_ids: std.ArrayListUnmanaged(tir.ParamId) = .{},
        blocks: std.ArrayListUnmanaged(tir.BlockId) = .{},
        pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
            self.param_vals.deinit(gpa);
            self.param_ids.deinit(gpa);
            self.blocks.deinit(gpa);
        }
    };

    pub const BlockFrame = struct {
        builder: *Builder,
        id: tir.BlockId,
        instrs: std.ArrayListUnmanaged(tir.InstrId) = .{},
        params: std.ArrayListUnmanaged(tir.ParamId) = .{},
        term: TermSlot = .{ .value = 0 },
        pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
            self.instrs.deinit(gpa);
            self.params.deinit(gpa);
        }
        fn termId(self: *const @This()) tir.TermId {
            return tir.TermId.fromRaw(@intCast(self.term.value));
        }
    };
    const TermSlot = struct { value: usize };
    const SwitchDest = struct { dest: tir.BlockId, args: []const tir.ValueId };

    pub fn beginFunction(self: *@This(), name: StrId, result: types.TypeId) !FunctionFrame {
        const idx = self.t.funcs.Function.add(self.gpa, .{ .name = name, .params = tir.RangeParam.empty(), .result = result, .blocks = tir.RangeBlock.empty() });
        return .{ .builder = self, .id = tir.FuncId.fromRaw(idx) };
    }
    pub fn addParam(self: *@This(), f: *FunctionFrame, name: ?StrId, ty: types.TypeId) !tir.ValueId {
        const vid = self.freshValue();
        const pid_u32 = self.t.funcs.Param.add(self.gpa, .{ .value = vid, .name = if (name) |n| OptStrId.some(n) else OptStrId.none(), .ty = ty });
        try f.param_ids.append(self.gpa, tir.ParamId.fromRaw(pid_u32));
        try f.param_vals.append(self.gpa, vid);
        return vid;
    }
    pub fn beginBlock(self: *@This(), f: *FunctionFrame) !BlockFrame {
        const idx = self.t.funcs.Block.add(self.gpa, .{ .params = tir.RangeParam.empty(), .instrs = tir.RangeInstr.empty(), .term = tir.TermId.fromRaw(0) });
        const bid = tir.BlockId.fromRaw(idx);
        try f.blocks.append(self.gpa, bid);
        return .{ .builder = self, .id = bid };
    }
    pub fn endBlock(self: *@This(), f: *FunctionFrame, blk: BlockFrame) !void {
        const instr_range = self.t.instrs.instr_pool.pushMany(self.gpa, blk.instrs.items);
        const param_range = self.t.funcs.param_pool.pushMany(self.gpa, blk.params.items);
        var row = self.t.funcs.Block.get(blk.id.toRaw());
        row.instrs = instr_range;
        row.params = param_range;
        row.term = blk.termId();
        self.t.funcs.Block.list.set(blk.id.toRaw(), row);
        var tmp = blk;
        tmp.deinit(self.gpa);
        _ = f;
    }
    pub fn endFunction(self: *@This(), f: FunctionFrame) !void {
        const prange = self.t.funcs.param_pool.pushMany(self.gpa, f.param_ids.items);
        const brange = self.t.funcs.block_pool.pushMany(self.gpa, f.blocks.items);
        var row = self.t.funcs.Function.get(f.id.toRaw());
        row.params = prange;
        row.blocks = brange;
        self.t.funcs.Function.list.set(f.id.toRaw(), row);
        var tmp = f;
        tmp.deinit(self.gpa);
    }

    // ---- instruction helpers ----
    fn constInt(self: *@This(), blk: *BlockFrame, ty: types.TypeId, v: i64) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ConstInt, tir.Rows.ConstInt{ .result = vid, .ty = ty, .value = v });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn constFloat(self: *@This(), blk: *BlockFrame, ty: types.TypeId, v: f64) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ConstFloat, tir.Rows.ConstFloat{ .result = vid, .ty = ty, .value = v });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn constBool(self: *@This(), blk: *BlockFrame, ty: types.TypeId, v: bool) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ConstBool, tir.Rows.ConstBool{ .result = vid, .ty = ty, .value = v });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn constString(self: *@This(), blk: *BlockFrame, ty: types.TypeId, s: []const u8) tir.ValueId {
        const sid = self.t.instrs.strs.intern(s);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ConstString, tir.Rows.ConstString{ .result = vid, .ty = ty, .text = sid });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn load(self: *@This(), blk: *BlockFrame, ty: types.TypeId, ptr: tir.ValueId, al: u32) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.Load, tir.Rows.Load{ .result = vid, .ty = ty, .ptr = ptr, .@"align" = al });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn store(self: *@This(), blk: *BlockFrame, ty: types.TypeId, ptr: tir.ValueId, value: tir.ValueId, al: u32) tir.InstrId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.Store, .{ .result = vid, .ty = ty, .ptr = ptr, .value = value, .@"align" = al });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return iid;
    }
    fn alloca(self: *@This(), blk: *BlockFrame, ty: types.TypeId, count: tir.OptValueId, al: u32) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.Alloca, tir.Rows.Alloca{ .result = vid, .ty = ty, .count = count, .@"align" = al });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn bin(self: *@This(), blk: *BlockFrame, comptime k: tir.OpKind, ty: types.TypeId, l: tir.ValueId, r: tir.ValueId) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(k, tir.Rows.Bin2{ .result = vid, .ty = ty, .lhs = l, .rhs = r });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn binBool(self: *@This(), blk: *BlockFrame, comptime k: tir.OpKind, l: tir.ValueId, r: tir.ValueId) tir.ValueId {
        const bty = self.t.type_store.tBool();
        const vid = self.freshValue();
        const iid = self.t.instrs.add(k, tir.Rows.Bin2{ .result = vid, .ty = bty, .lhs = l, .rhs = r });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn call(self: *@This(), blk: *BlockFrame, ty: types.TypeId, callee: StrId, args: []const tir.ValueId) tir.ValueId {
        const r = self.t.instrs.val_list_pool.pushMany(self.gpa, args);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.Call, tir.Rows.Call{ .result = vid, .ty = ty, .callee = callee, .args = r });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn indexOp(self: *@This(), blk: *BlockFrame, ty: types.TypeId, base: tir.ValueId, idx: tir.ValueId) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.Index, tir.Rows.Index{ .result = vid, .ty = ty, .base = base, .index = idx });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn intern(self: *@This(), s: []const u8) StrId {
        return self.t.instrs.strs.intern(s);
    }
    fn un1(self: *@This(), blk: *BlockFrame, comptime k: tir.OpKind, ty: types.TypeId, v: tir.ValueId) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(k, tir.Rows.Un1{ .result = vid, .ty = ty, .value = v });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn constNull(self: *@This(), blk: *BlockFrame, ty: types.TypeId) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ConstNull, tir.Rows.ConstNull{ .result = vid, .ty = ty });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn tupleMake(self: *@This(), blk: *BlockFrame, ty: types.TypeId, elems: []const tir.ValueId) tir.ValueId {
        const r = self.t.instrs.value_pool.pushMany(self.gpa, elems);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.TupleMake, tir.Rows.TupleMake{ .result = vid, .ty = ty, .elems = r });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn arrayMake(self: *@This(), blk: *BlockFrame, ty: types.TypeId, elems: []const tir.ValueId) tir.ValueId {
        const r = self.t.instrs.value_pool.pushMany(self.gpa, elems);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ArrayMake, tir.Rows.ArrayMake{ .result = vid, .ty = ty, .elems = r });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn structMake(self: *@This(), blk: *BlockFrame, ty: types.TypeId, fields: []const tir.Rows.StructFieldInit) tir.ValueId {
        var ids = self.gpa.alloc(tir.StructFieldInitId, fields.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const idx = self.t.instrs.StructFieldInit.add(self.gpa, fields[i]);
            ids[i] = tir.StructFieldInitId.fromRaw(idx);
        }
        const r = self.t.instrs.sfi_pool.pushMany(self.gpa, ids);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.StructMake, tir.Rows.StructMake{ .result = vid, .ty = ty, .fields = r });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn extractElem(self: *@This(), blk: *BlockFrame, ty: types.TypeId, agg: tir.ValueId, index: u32) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ExtractElem, tir.Rows.ExtractElem{ .result = vid, .ty = ty, .agg = agg, .index = index });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn insertElem(self: *@This(), blk: *BlockFrame, ty: types.TypeId, agg: tir.ValueId, index: u32, value: tir.ValueId) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.InsertElem, tir.Rows.InsertElem{ .result = vid, .ty = ty, .agg = agg, .index = index, .value = value });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn extractField(self: *@This(), blk: *BlockFrame, ty: types.TypeId, agg: tir.ValueId, index: u32) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ExtractField, tir.Rows.ExtractField{ .result = vid, .ty = ty, .agg = agg, .index = index, .name = OptStrId.none() });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn addressOf(self: *@This(), blk: *BlockFrame, ty: types.TypeId, v: tir.ValueId) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.AddressOf, tir.Rows.AddressOf{ .result = vid, .ty = ty, .value = v });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn cast(self: *@This(), blk: *BlockFrame, comptime k: tir.OpKind, ty: types.TypeId, v: tir.ValueId) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(k, tir.Rows.Un1{ .result = vid, .ty = ty, .value = v });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn addBlockParam(self: *@This(), blk: *BlockFrame, name: ?[]const u8, ty: types.TypeId) !tir.ValueId {
        const vid = self.freshValue();
        const sid = if (name) |n| OptStrId.some(self.intern(n)) else OptStrId.none();
        const pid = self.t.funcs.Param.add(self.gpa, .{ .value = vid, .name = sid, .ty = ty });
        try blk.params.append(self.gpa, tir.ParamId.fromRaw(pid));
        return vid;
    }
    pub fn addGlobal(self: *@This(), name: StrId, ty: types.TypeId) tir.GlobalId {
        const idx = self.t.funcs.Global.add(self.gpa, .{ .name = name, .ty = ty });
        return tir.GlobalId.fromRaw(idx);
    }
    fn edge(self: *@This(), dest: tir.BlockId, args: []const tir.ValueId) tir.EdgeId {
        const r = self.t.instrs.value_pool.pushMany(self.gpa, args);
        const eid = self.t.terms.Edge.add(self.gpa, .{ .dest = dest, .args = r });
        return tir.EdgeId.fromRaw(eid);
    }
    pub fn br(self: *@This(), blk: *BlockFrame, dest: tir.BlockId, args: []const tir.ValueId) !void {
        const e = self.edge(dest, args);
        const tid = self.t.terms.add(.Br, .{ .edge = e });
        blk.term = .{ .value = tid.toRaw() };
    }
    pub fn condBr(self: *@This(), blk: *BlockFrame, cond: tir.ValueId, then_dest: tir.BlockId, then_args: []const tir.ValueId, else_dest: tir.BlockId, else_args: []const tir.ValueId) !void {
        const te = self.edge(then_dest, then_args);
        const ee = self.edge(else_dest, else_args);
        const tid = self.t.terms.add(.CondBr, .{ .cond = cond, .then_edge = te, .else_edge = ee });
        blk.term = .{ .value = tid.toRaw() };
    }
    fn constUndef(self: *@This(), blk: *BlockFrame, ty: types.TypeId) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ConstUndef, tir.Rows.ConstUndef{ .result = vid, .ty = ty });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    fn setReturn(self: *@This(), blk: *BlockFrame, value: tir.OptValueId) !void {
        const tid = self.t.terms.add(.Return, .{ .value = value });
        blk.term = .{ .value = tid.toRaw() };
    }
    pub fn setReturnVal(self: *@This(), blk: *BlockFrame, v: tir.ValueId) !void {
        return self.setReturn(blk, tir.OptValueId.some(v));
    }
    pub fn setReturnVoid(self: *@This(), blk: *BlockFrame) !void {
        return self.setReturn(blk, tir.OptValueId.none());
    }
    pub fn setUnreachable(self: *@This(), blk: *BlockFrame) !void {
        const tid = self.t.terms.add(.Unreachable, .{});
        blk.term = .{ .value = tid.toRaw() };
    }

    // SwitchInt helper
    pub fn switchInt(self: *@This(), blk: *BlockFrame, scrut: tir.ValueId, case_vals: []const u64, case_dests: []const SwitchDest, default_dest: tir.BlockId, default_args: []const tir.ValueId) !void {
        std.debug.assert(case_vals.len == case_dests.len);
        // build cases
        var case_ids = self.gpa.alloc(tir.CaseId, case_vals.len) catch @panic("OOM");
        defer self.gpa.free(case_ids);
        var i: usize = 0;
        while (i < case_vals.len) : (i += 1) {
            const e = self.edge(case_dests[i].dest, case_dests[i].args);
            const cid = self.t.terms.Case.add(self.gpa, .{ .value = case_vals[i], .edge = e });
            case_ids[i] = tir.CaseId.fromRaw(cid);
        }
        const crange = self.t.terms.case_pool.pushMany(self.gpa, case_ids);
        const def_e = self.edge(default_dest, default_args);
        const tid = self.t.terms.add(.SwitchInt, .{ .scrut = scrut, .cases = crange, .default_edge = def_e });
        blk.term = .{ .value = tid.toRaw() };
    }

    // GEP helpers
    fn gepConst(self: *@This(), v: i64) tir.GepIndexId {
        const id = self.t.instrs.GepIndex.add(self.gpa, .{ .Const = v });
        return tir.GepIndexId.fromRaw(id);
    }
    fn gepValue(self: *@This(), val: tir.ValueId) tir.GepIndexId {
        const id = self.t.instrs.GepIndex.add(self.gpa, .{ .Value = val });
        return tir.GepIndexId.fromRaw(id);
    }
    fn gep(self: *@This(), blk: *BlockFrame, ty: types.TypeId, base: tir.ValueId, idxs: []const tir.GepIndexId) tir.ValueId {
        const r = self.t.instrs.gep_pool.pushMany(self.gpa, idxs);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.Gep, tir.Rows.Gep{ .result = vid, .ty = ty, .base = base, .indices = r });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
};
