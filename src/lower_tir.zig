const std = @import("std");
const ast = @import("ast.zig");
const cst = @import("cst.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");

const StrId = @import("cst.zig").StrId;
const OptStrId = @import("cst.zig").OptStrId;
const Context = @import("compile.zig").Context;
const ImportResolver = @import("import_resolver.zig").ImportResolver;
const Pipeline = @import("pipeline.zig").Pipeline;

pub const LowerTir = struct {
    gpa: std.mem.Allocator,
    context: *Context,
    pipeline: *Pipeline,

    // Simple loop stack to support break/continue in While/For (+ value loops)
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},

    // Mapping: module ident name -> prefix for mangling (module.func -> prefix_func)
    module_prefix: std.StringHashMapUnmanaged([]const u8) = .{},

    import_base_dir: []const u8 = ".",

    pub fn init(
        gpa: std.mem.Allocator,
        context: *Context,
        pipeline: *Pipeline,
    ) LowerTir {
        return .{ .gpa = gpa, .context = context, .pipeline = pipeline };
    }

    pub fn deinit(self: *LowerTir) void {
        self.loop_stack.deinit(self.gpa);
        var it = self.module_prefix.valueIterator();
        while (it.next()) |p| self.gpa.free(p.*);
        self.module_prefix.deinit(self.gpa);
    }

    pub fn setImportResolver(self: *@This(), r: *ImportResolver, base_dir: []const u8) void {
        self.import_resolver = r;
        self.import_base_dir = base_dir;
    }

    pub fn run(self: *@This(), a: *const ast.Ast) !tir.TIR {
        var t = tir.TIR.init(self.gpa, &self.context.type_info.store);
        var b = Builder.init(self.gpa, &t);

        // Lower top-level decls: functions and globals
        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        for (decls) |did| try self.lowerTopDecl(a, &b, did);

        return t;
    }

    pub fn setModulePrefix(self: *@This(), name: []const u8, prefix: []const u8) !void {
        const key = try self.gpa.dupe(u8, name);
        const val = try self.gpa.dupe(u8, prefix);
        const gop = try self.module_prefix.getOrPut(self.gpa, key);
        if (gop.found_existing) {
            self.gpa.free(key);
            self.gpa.free(gop.value_ptr.*);
        }
        gop.value_ptr.* = val;
    }

    // ============================
    // Utilities / common helpers
    // ============================

    const LowerMode = enum { rvalue, lvalue_addr };

    fn isVoid(self: *const @This(), ty: types.TypeId) bool {
        return self.context.type_info.store.index.kinds.items[ty.toRaw()] == .Void;
    }

    // Produce an undef that is never-void; if asked for void, give Any instead.
    fn safeUndef(self: *@This(), blk: *Builder.BlockFrame, ty: types.TypeId) tir.ValueId {
        if (self.isVoid(ty)) return blk.builder.constUndef(blk, self.context.type_info.store.tAny());
        return blk.builder.constUndef(blk, ty);
    }

    fn undef(_: *@This(), blk: *Builder.BlockFrame, ty: types.TypeId) tir.ValueId {
        return blk.builder.constUndef(blk, ty);
    }
    fn boolConst(self: *@This(), blk: *Builder.BlockFrame, v: bool) tir.ValueId {
        return blk.builder.constBool(blk, self.context.type_info.store.tBool(), v);
    }

    /// Insert an explicit coercion that realizes what the checker proved assignable/castable.
    fn emitCoerce(self: *@This(), blk: *Builder.BlockFrame, v: tir.ValueId, got: types.TypeId, want: types.TypeId) tir.ValueId {
        if (got.toRaw() == want.toRaw()) return v;

        const gk = self.context.type_info.store.index.kinds.items[got.toRaw()];
        const wk = self.context.type_info.store.index.kinds.items[want.toRaw()];

        const is_num = switch (gk) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64 => true,
            else => false,
        };
        const is_num_w = switch (wk) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64 => true,
            else => false,
        };
        if (is_num and is_num_w) return blk.builder.cast(blk, .CastNormal, want, v);
        if (gk == .Ptr and wk == .Ptr) return blk.builder.cast(blk, .CastBit, want, v);
        // Any/compatible assignable: use Normal cast as a materialization
        return blk.builder.cast(blk, .CastNormal, want, v);
    }

    // ============================
    // Top-level lowering
    // ============================

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
        // Global: record type
        if (!d.pattern.isNone()) {
            const nm = self.bindingNameOfPattern(a, d.pattern.unwrap()) orelse return;
            const ty = self.getDeclType(did) orelse return;
            _ = b.addGlobal(nm, ty);
        }
    }

    fn lowerFunction(self: *@This(), a: *const ast.Ast, b: *Builder, name: StrId, fun_eid: ast.ExprId) !void {
        const fid = self.getExprType(fun_eid) orelse return;
        if (self.context.type_info.store.index.kinds.items[fid.toRaw()] != .Function) return;
        const fnty = self.context.type_info.store.Function.get(self.context.type_info.store.index.rows.items[fid.toRaw()]);

        var f = try b.beginFunction(name, fnty.result, fnty.is_variadic);

        const fnr = a.exprs.get(.FunctionLit, fun_eid);
        // Params
        const params = a.exprs.param_pool.slice(fnr.params);
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = a.exprs.Param.get(params[i].toRaw());
            const pty = self.context.type_info.store.type_pool.slice(fnty.params)[i];
            const pname = if (!p.pat.isNone()) self.bindingNameOfPattern(a, p.pat.unwrap()) else null;
            _ = try b.addParam(&f, pname, pty);
        }

        // Entry block + env
        var blk = try b.beginBlock(&f);
        var env = Env.init(self.gpa);
        defer env.deinit(self.gpa);

        // Bind params
        i = 0;
        const param_vals = f.param_vals.items;
        while (i < params.len) : (i += 1) {
            const p = a.exprs.Param.get(params[i].toRaw());
            if (!p.pat.isNone()) {
                const pname = self.bindingNameOfPattern(a, p.pat.unwrap()) orelse continue;
                try env.bind(self.gpa, a, pname, .{ .value = param_vals[i], .is_slot = false });
            }
        }

        // Body
        if (!fnr.body.isNone()) {
            const body_id = fnr.body.unwrap();
            try env.pushScope(self.gpa);
            try self.lowerExprAsStmtList(a, &env, &f, &blk, body_id);
            _ = env.popScope();
        }

        if (blk.term.isNone()) {
            try b.setReturn(&blk, tir.OptValueId.none());
        }

        try b.endBlock(&f, blk);
        try b.endFunction(f);
    }

    // Lower a block or expression as a list of statements (ignores resulting value)
    fn lowerExprAsStmtList(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId) !void {
        if (a.exprs.index.kinds.items[id.toRaw()] == .Block) {
            const b = a.exprs.get(.Block, id);
            const stmts = a.stmts.stmt_pool.slice(b.items);
            try env.pushScope(self.gpa);
            for (stmts) |sid| {
                try self.lowerStmt(a, env, f, blk, sid);
            }
            _ = env.popScope();
        } else {
            _ = try self.lowerExpr(a, env, f, blk, id, null, .rvalue);
        }
    }

    fn lowerStmt(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, sid: ast.StmtId) !void {
        const k = a.stmts.index.kinds.items[sid.toRaw()];
        switch (k) {
            .Expr => {
                const e = a.stmts.get(.Expr, sid).expr;
                _ = try self.lowerExpr(a, env, f, blk, e, null, .rvalue);
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
                        if (!ent.is_err) _ = try self.lowerExpr(a, env, f, blk, ent.expr, null, .rvalue);
                    }
                    if (lc.has_result) {
                        const v = if (!br.value.isNone())
                            try self.lowerExpr(a, env, f, blk, br.value.unwrap(), lc.res_ty, .rvalue)
                        else
                            f.builder.constUndef(blk, lc.res_ty);
                        try f.builder.br(blk, lc.join_block, &.{v});
                    } else {
                        try f.builder.br(blk, lc.break_block, &.{});
                    }
                } else return error.LoweringBug;
            },
            .Continue => {
                const lc = if (self.loop_stack.items.len > 0) self.loop_stack.items[self.loop_stack.items.len - 1] else return error.LoweringBug;
                var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
                while (j >= 0 and @as(u32, @intCast(j)) >= lc.defer_len_at_entry) : (j -= 1) {
                    const ent = env.defers.items[@intCast(j)];
                    if (!ent.is_err) _ = try self.lowerExpr(a, env, f, blk, ent.expr, null, .rvalue);
                }
                try f.builder.br(blk, lc.continue_block, &.{});
            },
            .Decl => {
                const drow = a.stmts.get(.Decl, sid);
                const d = a.exprs.Decl.get(drow.decl.toRaw());
                const val = try self.lowerExpr(a, env, f, blk, d.value, self.getExprType(d.value), .rvalue);
                if (!d.pattern.isNone()) {
                    const nm = self.bindingNameOfPattern(a, d.pattern.unwrap()) orelse return;
                    if (d.flags.is_const) {
                        try env.bind(self.gpa, a, nm, .{ .value = val, .is_slot = false });
                    } else {
                        const vty = self.getExprType(d.value) orelse return;
                        const slot_ty = self.context.type_info.store.mkPtr(vty, false);
                        const slot = f.builder.alloca(blk, slot_ty, tir.OptValueId.none(), 0);
                        _ = f.builder.store(blk, vty, slot, val, 0);
                        try env.bind(self.gpa, a, nm, .{ .value = slot, .is_slot = true });
                    }
                }
            },
            .Assign => {
                const as = a.stmts.get(.Assign, sid);
                const lhs_ptr = try self.lowerExpr(a, env, f, blk, as.left, null, .lvalue_addr);
                const rhs = try self.lowerExpr(a, env, f, blk, as.right, self.getExprType(as.left), .rvalue);
                const rty = self.getExprType(as.left) orelse return error.LoweringBug;
                _ = f.builder.store(blk, rty, lhs_ptr, rhs, 0);
            },
            .Return => {
                const r = a.stmts.get(.Return, sid);
                // run normal defers (ignore err-only for now – handled below when needed)
                var j: isize = @intCast(env.defers.items.len);
                j -= 1;
                while (j >= 0) : (j -= 1) {
                    const ent = env.defers.items[@intCast(j)];
                    if (!ent.is_err) _ = try self.lowerExpr(a, env, f, blk, ent.expr, null, .rvalue);
                }

                if (!r.value.isNone()) {
                    const frow = f.builder.t.funcs.Function.get(f.id.toRaw());
                    const expect = frow.result;
                    const v_raw = try self.lowerExpr(a, env, f, blk, r.value.unwrap(), expect, .rvalue);
                    var v = v_raw;
                    if (self.getExprType(r.value.unwrap())) |got| {
                        v = self.emitCoerce(blk, v_raw, got, expect);
                    }
                    // Minimal errdefer: if function returns ErrorSet, run err-only defers when v carries an error
                    if (self.context.type_info.store.index.kinds.items[expect.toRaw()] == .ErrorSet) {
                        var then_blk = try f.builder.beginBlock(f);
                        var cont_blk = try f.builder.beginBlock(f);
                        const is_err_name = f.builder.intern("builtin.err.is_err");
                        const is_err = blk.builder.call(blk, self.context.type_info.store.tBool(), is_err_name, &.{v});
                        try f.builder.condBr(blk, is_err, then_blk.id, &.{}, cont_blk.id, &.{});
                        // run err-only defers in reverse
                        var ki: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
                        while (ki >= 0) : (ki -= 1) {
                            const ent = env.defers.items[@intCast(ki)];
                            if (ent.is_err) _ = try self.lowerExpr(a, env, f, &then_blk, ent.expr, null, .rvalue);
                        }
                        try f.builder.setReturnVal(&then_blk, v);
                        try f.builder.endBlock(f, then_blk);
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

    // ============================
    // Expressions
    // ============================

    const CalleeInfo = struct {
        name: StrId,
        fty: ?types.TypeId,
    };

    fn resolveCallee(self: *@This(), a: *const ast.Ast, f: *Builder.FunctionFrame, row: ast.Rows.Call) CalleeInfo {
        const ck = a.exprs.index.kinds.items[row.callee.toRaw()];
        if (ck == .Ident) {
            const nm = a.exprs.get(.Ident, row.callee).name;
            return .{ .name = nm, .fty = self.getExprType(row.callee) };
        }
        if (ck == .FieldAccess) {
            const fr = a.exprs.get(.FieldAccess, row.callee);
            if (a.exprs.index.kinds.items[fr.parent.toRaw()] == .Ident) {
                const mod_name = a.exprs.strs.get(a.exprs.get(.Ident, fr.parent).name);
                if (self.module_prefix.get(mod_name)) |pref| {
                    const fn_name = a.exprs.strs.get(fr.field);
                    const first = if (fn_name.len > 0) fn_name[0] else '_';
                    const is_extern_like = (first >= 'A' and first <= 'Z');
                    if (!is_extern_like) {
                        const m = std.fmt.allocPrint(self.gpa, "{s}_{s}", .{ pref, fn_name }) catch @panic("OOM");
                        defer self.gpa.free(m);
                        return .{ .name = f.builder.intern(m), .fty = self.getExprType(row.callee) };
                    }
                }
            }
            return .{ .name = a.exprs.get(.FieldAccess, row.callee).field, .fty = self.getExprType(row.callee) };
        }
        return .{ .name = f.builder.intern("<indirect>"), .fty = self.getExprType(row.callee) };
    }

    fn lowerCall(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId, expected: ?types.TypeId) !tir.ValueId {
        const row = a.exprs.get(.Call, id);
        const callee = self.resolveCallee(a, f, row);

        // Lower args
        const arg_ids = a.exprs.expr_pool.slice(row.args);
        var vals = try self.gpa.alloc(tir.ValueId, arg_ids.len);
        defer self.gpa.free(vals);
        var i: usize = 0;
        while (i < arg_ids.len) : (i += 1) {
            vals[i] = try self.lowerExpr(a, env, f, blk, arg_ids[i], null, .rvalue);
        }

        // Coerce fixed args to param types if we know them
        if (callee.fty) |fty| {
            if (self.context.type_info.store.index.kinds.items[fty.toRaw()] == .Function) {
                const fr2 = self.context.type_info.store.Function.get(self.context.type_info.store.index.rows.items[fty.toRaw()]);
                const param_tys = self.context.type_info.store.type_pool.slice(fr2.params);
                var fixed: usize = param_tys.len;
                if (fr2.is_variadic and fixed > 0) fixed -= 1;
                i = 0;
                while (i < vals.len and i < fixed) : (i += 1) {
                    const want = param_tys[i];
                    const got = self.getExprType(arg_ids[i]) orelse want;
                    if (want.toRaw() != got.toRaw()) {
                        vals[i] = self.emitCoerce(blk, vals[i], got, want);
                    }
                }
            }
        }

        const ret_ty = expected orelse (self.getExprType(id) orelse self.context.type_info.store.tVoid());
        return blk.builder.call(blk, ret_ty, callee.name, vals);
    }

    fn lowerExpr(
        self: *@This(),
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        mode: LowerMode,
    ) anyerror!tir.ValueId {
        const k = a.exprs.index.kinds.items[id.toRaw()];

        switch (k) {
            .Literal => {
                const lit = a.exprs.get(.Literal, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = switch (lit.kind) {
                    .int => blk.builder.constInt(blk, ty0, try std.fmt.parseInt(u64, a.exprs.strs.get(lit.value.unwrap()), 10)),
                    .imaginary => blk.builder.constInt(blk, ty0, 0), // TODO: complex number support
                    .float => blk.builder.constFloat(blk, ty0, try std.fmt.parseFloat(f64, a.exprs.strs.get(lit.value.unwrap()))),
                    .bool => blk.builder.constBool(blk, ty0, lit.bool_value),
                    .string => blk.builder.constString(blk, ty0, a.exprs.strs.get(lit.value.unwrap())),
                    .char => blk.builder.constInt(blk, ty0, @as(u64, lit.char_value)),
                };
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .NullLit => {
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = blk.builder.constNull(blk, ty0);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .UndefLit => {
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = blk.builder.constUndef(blk, ty0);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .Unary => {
                const row = a.exprs.get(.Unary, id);
                if (row.op == .address_of or mode == .lvalue_addr) {
                    // compute address of the operand
                    const ety = self.getExprType(row.expr) orelse return error.LoweringBug;
                    // When user asked address-of explicitly, produce pointer type
                    if (row.op == .address_of) {
                        const v = try self.lowerExpr(a, env, f, blk, row.expr, ety, .rvalue);
                        return blk.builder.addressOf(blk, self.context.type_info.store.mkPtr(ety, false), v);
                    }
                    // lvalue address request falls through to .Ident/.FieldAccess/.IndexAccess implementations
                }
                // rvalue unary
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v0 = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
                const v =
                    switch (row.op) {
                        .plus => v0,
                        .minus => blk.builder.bin(blk, .Sub, ty0, blk.builder.constInt(blk, ty0, 0), v0),
                        .logical_not => blk.builder.un1(blk, .LogicalNot, self.context.type_info.store.tBool(), v0),
                        .address_of => unreachable, // handled above
                    };
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .Range => {
                const row = a.exprs.get(.Range, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const start_v = if (!row.start.isNone()) try self.lowerExpr(a, env, f, blk, row.start.unwrap(), null, .rvalue) else blk.builder.constUndef(blk, ty0);
                const end_v = if (!row.end.isNone()) try self.lowerExpr(a, env, f, blk, row.end.unwrap(), null, .rvalue) else blk.builder.constUndef(blk, ty0);
                const incl = blk.builder.constBool(blk, self.context.type_info.store.tBool(), row.inclusive_right);
                const make = blk.builder.intern("builtin.range.make");
                const v = blk.builder.call(blk, ty0, make, &.{ start_v, end_v, incl });
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .Deref => {
                if (mode == .lvalue_addr) {
                    // address of deref target is the pointer value itself
                    const row = a.exprs.get(.Deref, id);
                    return try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
                }
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const row = a.exprs.get(.Deref, id);
                const ptr = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
                const v = blk.builder.load(blk, ty0, ptr, 0);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .TupleLit => {
                const row = a.exprs.get(.TupleLit, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const ids = a.exprs.expr_pool.slice(row.elems);
                var vals = try self.gpa.alloc(tir.ValueId, ids.len);
                defer self.gpa.free(vals);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    // coerce element to tuple element type if known
                    var expect_elem = self.context.type_info.store.tAny();
                    const vk = self.context.type_info.store.index.kinds.items[ty0.toRaw()];
                    if (vk == .Tuple) {
                        const trow = self.context.type_info.store.Tuple.get(self.context.type_info.store.index.rows.items[ty0.toRaw()]);
                        const elems = self.context.type_info.store.type_pool.slice(trow.elems);
                        if (i < elems.len) expect_elem = elems[i];
                    }
                    vals[i] = try self.lowerExpr(a, env, f, blk, ids[i], expect_elem, .rvalue);
                }
                const v = blk.builder.tupleMake(blk, ty0, vals);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .ArrayLit => {
                const row = a.exprs.get(.ArrayLit, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const ids = a.exprs.expr_pool.slice(row.elems);
                var vals = try self.gpa.alloc(tir.ValueId, ids.len);
                defer self.gpa.free(vals);
                var i: usize = 0;
                var expect_elem = self.context.type_info.store.tAny();
                const vk = self.context.type_info.store.index.kinds.items[ty0.toRaw()];
                if (vk == .Array) expect_elem = self.context.type_info.store.Array.get(self.context.type_info.store.index.rows.items[ty0.toRaw()]).elem;
                while (i < ids.len) : (i += 1) vals[i] = try self.lowerExpr(a, env, f, blk, ids[i], expect_elem, .rvalue);
                const v = blk.builder.arrayMake(blk, ty0, vals);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .StructLit => {
                const row = a.exprs.get(.StructLit, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const fids = a.exprs.sfv_pool.slice(row.fields);
                var fields = try self.gpa.alloc(tir.Rows.StructFieldInit, fids.len);
                defer self.gpa.free(fields);
                var i: usize = 0;
                // Determine expected field types if available
                var field_ids: []const cst.Index(types.FieldTag) = &[_]cst.Index(types.FieldTag){};
                if (self.context.type_info.store.index.kinds.items[ty0.toRaw()] == .Struct) {
                    const srow = self.context.type_info.store.Struct.get(self.context.type_info.store.index.rows.items[ty0.toRaw()]);
                    field_ids = self.context.type_info.store.field_pool.slice(srow.fields);
                }
                while (i < fids.len) : (i += 1) {
                    const sfv = a.exprs.StructFieldValue.get(fids[i].toRaw());
                    const want = if (i < field_ids.len) self.context.type_info.store.Field.get(field_ids[i].toRaw()).ty else self.context.type_info.store.tAny();
                    const v = try self.lowerExpr(a, env, f, blk, sfv.value, want, .rvalue);
                    fields[i] = .{ .index = @intCast(i), .name = sfv.name, .value = v };
                }
                const v = blk.builder.structMake(blk, ty0, fields);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .MapLit => {
                const row = a.exprs.get(.MapLit, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const kv_ids = a.exprs.kv_pool.slice(row.entries);
                var vals = try self.gpa.alloc(tir.ValueId, kv_ids.len * 2);
                defer self.gpa.free(vals);
                var j: usize = 0;
                for (kv_ids) |kid| {
                    const kv = a.exprs.KeyValue.get(kid.toRaw());
                    // best-effort: use expected key/value if map type is known
                    var key_want = self.context.type_info.store.tAny();
                    var val_want = self.context.type_info.store.tAny();
                    const mk = self.context.type_info.store.index.kinds.items[ty0.toRaw()];
                    if (mk == .Map) {
                        const mr = self.context.type_info.store.Map.get(self.context.type_info.store.index.rows.items[ty0.toRaw()]);
                        key_want = mr.key;
                        val_want = mr.value;
                    }
                    vals[j] = try self.lowerExpr(a, env, f, blk, kv.key, key_want, .rvalue);
                    j += 1;
                    vals[j] = try self.lowerExpr(a, env, f, blk, kv.value, val_want, .rvalue);
                    j += 1;
                }
                const make = blk.builder.intern("builtin.map.from_kv");
                const v = blk.builder.call(blk, ty0, make, vals);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .IndexAccess => {
                if (mode == .lvalue_addr) {
                    const row = a.exprs.get(.IndexAccess, id);
                    const base_ptr = try self.lowerExpr(a, env, f, blk, row.collection, null, .lvalue_addr);
                    const idx_v = try self.lowerExpr(a, env, f, blk, row.index, self.context.type_info.store.tUsize(), .rvalue);
                    const idx = blk.builder.gepValue(idx_v);
                    const rty = self.context.type_info.store.mkPtr(self.getExprType(id) orelse return error.LoweringBug, false);
                    return blk.builder.gep(blk, rty, base_ptr, &.{idx});
                } else {
                    const row = a.exprs.get(.IndexAccess, id);
                    const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                    const base = try self.lowerExpr(a, env, f, blk, row.collection, null, .rvalue);
                    const idx = try self.lowerExpr(a, env, f, blk, row.index, self.context.type_info.store.tUsize(), .rvalue);
                    const v = blk.builder.indexOp(blk, ty0, base, idx);
                    if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                    return v;
                }
            },
            .FieldAccess => {
                const row = a.exprs.get(.FieldAccess, id);
                // Imported module member constant materialization (rvalue only)
                if (mode == .rvalue and a.exprs.index.kinds.items[row.parent.toRaw()] == .Ident) {
                    const idr = a.exprs.get(.Ident, row.parent);
                    const name = a.exprs.strs.get(idr.name);
                    if (self.findTopLevelImportByName(a, name)) |imp_decl| {
                        const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                        if (self.materializeImportedConst(&self.context.resolver, a, imp_decl, row.field, ty0, blk, self.pipeline)) |vv| {
                            if (expected_ty) |want| return self.emitCoerce(blk, vv, ty0, want);
                            return vv;
                        }
                        // fallthrough to undef if unresolved
                        const v = blk.builder.constUndef(blk, ty0);
                        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                        return v;
                    }
                }

                // Use checker-resolved field index for both address and value paths.
                const resolved_idx = self.context.type_info.getFieldIndex(id) orelse return error.LoweringBug;
                if (mode == .lvalue_addr) {
                    const parent_ptr = try self.lowerExpr(a, env, f, blk, row.parent, null, .lvalue_addr);
                    const elem_ty = self.getExprType(id) orelse return error.LoweringBug;
                    // If parent is a pointer to an aggregate, we GEP through the pointer.
                    // We rely on the checker to have validated that GEP is legal here.
                    const idx = blk.builder.gepConst(@intCast(resolved_idx));
                    const rptr_ty = self.context.type_info.store.mkPtr(elem_ty, false);
                    return blk.builder.gep(blk, rptr_ty, parent_ptr, &.{idx});
                } else {
                    const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                    const parent_ty = self.getExprType(row.parent) orelse return error.LoweringBug;
                    const base = try self.lowerExpr(a, env, f, blk, row.parent, null, .rvalue);
                    // Choose the correct extractor based on the *value* kind of the parent.
                    const pk = self.context.type_info.store.index.kinds.items[parent_ty.toRaw()];
                    const v =
                        if (pk == .Tuple)
                            blk.builder.extractElem(blk, ty0, base, resolved_idx)
                        else
                            blk.builder.extractField(blk, ty0, base, resolved_idx);
                    if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                    return v;
                }
            },
            .Block => {
                const res_ty = expected_ty orelse (self.getExprType(id) orelse self.context.type_info.store.tVoid());
                return try self.lowerBlockExprValue(a, env, f, blk, id, res_ty);
            },
            .Ident => {
                const row = a.exprs.get(.Ident, id);
                const name = a.exprs.strs.get(row.name);
                if (mode == .lvalue_addr) {
                    var bnd = env.lookup(name);
                    if (bnd == null) {
                        if (self.findTopLevelDeclByName(a, name)) |did| {
                            const d = a.exprs.Decl.get(did.toRaw());
                            const ety = self.getExprType(d.value) orelse return error.LoweringBug;
                            const slot_ty = self.context.type_info.store.mkPtr(ety, false);
                            const slot = f.builder.alloca(blk, slot_ty, tir.OptValueId.none(), 0);
                            const val = try self.lowerExpr(a, env, f, blk, d.value, ety, .rvalue);
                            _ = f.builder.store(blk, ety, slot, val, 0);
                            try env.bind(self.gpa, a, row.name, .{ .value = slot, .is_slot = true });
                            bnd = env.lookup(name);
                        }
                    }
                    const binding = bnd orelse return error.LoweringBug;
                    if (binding.is_slot) return binding.value;
                    const ety2 = self.getExprType(id) orelse return error.LoweringBug;
                    const slot_ty2 = self.context.type_info.store.mkPtr(ety2, false);
                    const slot2 = f.builder.alloca(blk, slot_ty2, tir.OptValueId.none(), 0);
                    _ = f.builder.store(blk, ety2, slot2, binding.value, 0);
                    try env.bind(self.gpa, a, row.name, .{ .value = slot2, .is_slot = true });
                    return slot2;
                } else {
                    const bnd = blk: {
                        if (env.lookup(name)) |v| break :blk v;
                        if (self.findTopLevelDeclByName(a, name)) |did| {
                            const d = a.exprs.Decl.get(did.toRaw());
                            const val = try self.lowerExpr(a, env, f, blk, d.value, self.getExprType(d.value), .rvalue);
                            try env.bind(self.gpa, a, row.name, .{ .value = val, .is_slot = false });
                            break :blk env.lookup(name).?;
                        }
                        return error.LoweringBug;
                    };
                    if (bnd.is_slot) {
                        const ety = self.getExprType(id) orelse return error.LoweringBug;
                        var v = blk.builder.load(blk, ety, bnd.value, 0);
                        if (expected_ty) |want| v = self.emitCoerce(blk, v, ety, want);
                        return v;
                    } else {
                        var v = bnd.value;
                        if (expected_ty) |want| {
                            const got = self.getExprType(id) orelse want;
                            v = self.emitCoerce(blk, v, got, want);
                        }
                        return v;
                    }
                }
            },
            .Binary => {
                const row = a.exprs.get(.Binary, id);
                const ty0 = self.getExprType(id) orelse self.context.type_info.store.tVoid();
                const l = try self.lowerExpr(a, env, f, blk, row.left, null, .rvalue);
                const r = try self.lowerExpr(a, env, f, blk, row.right, null, .rvalue);
                const v = switch (row.op) {
                    .add => blk.builder.bin(blk, .Add, ty0, l, r),
                    .sub => blk.builder.bin(blk, .Sub, ty0, l, r),
                    .mul => blk.builder.bin(blk, .Mul, ty0, l, r),
                    .div => blk.builder.bin(blk, .Div, ty0, l, r),
                    .mod => blk.builder.bin(blk, .Mod, ty0, l, r),
                    .shl => blk.builder.bin(blk, .Shl, ty0, l, r),
                    .shr => blk.builder.bin(blk, .Shr, ty0, l, r),
                    .bit_and => blk.builder.bin(blk, .BitAnd, ty0, l, r),
                    .bit_or => blk.builder.bin(blk, .BitOr, ty0, l, r),
                    .bit_xor => blk.builder.bin(blk, .BitXor, ty0, l, r),
                    .eq => blk.builder.binBool(blk, .CmpEq, l, r),
                    .neq => blk.builder.binBool(blk, .CmpNe, l, r),
                    .lt => blk.builder.binBool(blk, .CmpLt, l, r),
                    .lte => blk.builder.binBool(blk, .CmpLe, l, r),
                    .gt => blk.builder.binBool(blk, .CmpGt, l, r),
                    .gte => blk.builder.binBool(blk, .CmpGe, l, r),
                    .logical_and => blk.builder.binBool(blk, .LogicalAnd, l, r),
                    .logical_or => blk.builder.binBool(blk, .LogicalOr, l, r),
                    .@"orelse" => blk: {
                        // optional-or-else
                        var then_blk = try f.builder.beginBlock(f);
                        var else_blk = try f.builder.beginBlock(f);
                        var join_blk = try f.builder.beginBlock(f);
                        const s_is_some = f.builder.intern("builtin.opt.is_some");
                        const cond_v = blk.builder.call(blk, self.context.type_info.store.tBool(), s_is_some, &.{l});
                        try f.builder.condBr(blk, cond_v, then_blk.id, &.{}, else_blk.id, &.{});
                        const res_ty = expected_ty orelse ty0;
                        const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
                        // then: unwrap
                        const s_unwrap = f.builder.intern("builtin.opt.unwrap");
                        var unwrapped = blk.builder.call(&then_blk, res_ty, s_unwrap, &.{l});
                        if (expected_ty) |want| {
                            const got = self.getExprType(row.left) orelse res_ty;
                            unwrapped = self.emitCoerce(&then_blk, unwrapped, got, want);
                        }
                        try f.builder.br(&then_blk, join_blk.id, &.{unwrapped});
                        // else: rhs
                        var rhs_v = r;
                        if (expected_ty) |want| {
                            const gotr = self.getExprType(row.right) orelse want;
                            rhs_v = self.emitCoerce(&else_blk, rhs_v, gotr, want);
                        }
                        try f.builder.br(&else_blk, join_blk.id, &.{rhs_v});
                        try f.builder.endBlock(f, then_blk);
                        try f.builder.endBlock(f, else_blk);
                        blk.* = join_blk;
                        break :blk res_param;
                    },
                };
                if (expected_ty) |want| {
                    // comparisons already bool; arithmetic already ty0
                    if (self.context.type_info.store.index.kinds.items[ty0.toRaw()] != .Void)
                        return self.emitCoerce(blk, v, ty0, want);
                }
                return v;
            },

            .Catch => {
                const row = a.exprs.get(.Catch, id);

                const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_info.store.tVoid());
                const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

                const lhs = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
                const s_is_ok = f.builder.intern("builtin.err.is_ok");

                var then_blk = try f.builder.beginBlock(f); // ok path
                var else_blk = try f.builder.beginBlock(f); // handler path

                if (produce_value) {
                    var join_blk = try f.builder.beginBlock(f);
                    const res_ty = out_ty_guess;
                    const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

                    const is_ok = blk.builder.call(blk, self.context.type_info.store.tBool(), s_is_ok, &.{lhs});
                    try f.builder.condBr(blk, is_ok, then_blk.id, &.{}, else_blk.id, &.{});

                    // then: unwrap ok(value)
                    const s_unwrap_ok = f.builder.intern("builtin.err.unwrap_ok");
                    var okv = blk.builder.call(&then_blk, res_ty, s_unwrap_ok, &.{lhs});
                    if (expected_ty) |want| {
                        const got = self.getExprType(row.expr) orelse res_ty;
                        okv = self.emitCoerce(&then_blk, okv, got, want);
                    }
                    try f.builder.br(&then_blk, join_blk.id, &.{okv});

                    // else: run handler (block/list); fallthrough value to join
                    try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
                    if (else_blk.term.isNone()) {
                        var hv = try self.lowerBlockExprValue(a, env, f, &else_blk, row.handler, res_ty);
                        if (expected_ty) |want| {
                            const got = self.getExprType(row.handler) orelse res_ty;
                            hv = self.emitCoerce(&else_blk, hv, got, want);
                        }
                        try f.builder.br(&else_blk, join_blk.id, &.{hv});
                    }

                    try f.builder.endBlock(f, then_blk);
                    try f.builder.endBlock(f, else_blk);
                    blk.* = join_blk;
                    return res_param;
                } else {
                    // No value: conditionally run handler, then continue
                    const exit_blk = try f.builder.beginBlock(f);
                    const is_ok = blk.builder.call(blk, self.context.type_info.store.tBool(), s_is_ok, &.{lhs});
                    try f.builder.condBr(blk, is_ok, then_blk.id, &.{}, else_blk.id, &.{});

                    // then: nothing to do, jump to exit
                    if (then_blk.term.isNone()) try f.builder.br(&then_blk, exit_blk.id, &.{});
                    try f.builder.endBlock(f, then_blk);

                    // else: execute handler as stmt
                    try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
                    if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{});
                    try f.builder.endBlock(f, else_blk);

                    blk.* = exit_blk;
                    return self.safeUndef(blk, self.context.type_info.store.tAny());
                }
            },
            .If => {
                const row = a.exprs.get(.If, id);
                var then_blk = try f.builder.beginBlock(f);
                var else_blk = try f.builder.beginBlock(f);

                const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_info.store.tVoid());
                const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

                const cond_v = try self.lowerExpr(a, env, f, blk, row.cond, self.context.type_info.store.tBool(), .rvalue);

                if (produce_value) {
                    var join_blk = try f.builder.beginBlock(f);
                    const res_ty = out_ty_guess;
                    const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

                    try f.builder.condBr(blk, cond_v, then_blk.id, &.{}, else_blk.id, &.{});
                    {
                        const old = blk.*;
                        try f.builder.endBlock(f, old);
                    }

                    // then
                    try self.lowerExprAsStmtList(a, env, f, &then_blk, row.then_block);
                    if (then_blk.term.isNone()) {
                        var v_then = try self.lowerBlockExprValue(a, env, f, &then_blk, row.then_block, res_ty);
                        if (expected_ty) |want| v_then = self.emitCoerce(&then_blk, v_then, self.getExprType(row.then_block) orelse res_ty, want);
                        try f.builder.br(&then_blk, join_blk.id, &.{v_then});
                    }

                    // else
                    if (!row.else_block.isNone()) {
                        try self.lowerExprAsStmtList(a, env, f, &else_blk, row.else_block.unwrap());
                        if (else_blk.term.isNone()) {
                            var v_else = try self.lowerBlockExprValue(a, env, f, &else_blk, row.else_block.unwrap(), res_ty);
                            if (expected_ty) |want| v_else = self.emitCoerce(&else_blk, v_else, self.getExprType(row.else_block.unwrap()) orelse res_ty, want);
                            try f.builder.br(&else_blk, join_blk.id, &.{v_else});
                        }
                    } else {
                        if (else_blk.term.isNone()) {
                            const uv = self.safeUndef(&else_blk, res_ty);
                            try f.builder.br(&else_blk, join_blk.id, &.{uv});
                        }
                    }

                    try f.builder.endBlock(f, then_blk);
                    try f.builder.endBlock(f, else_blk);
                    blk.* = join_blk;
                    return res_param;
                } else {
                    // statement-position if: no value, no phi
                    const exit_blk = try f.builder.beginBlock(f);
                    try f.builder.condBr(blk, cond_v, then_blk.id, &.{}, else_blk.id, &.{});
                    {
                        const old = blk.*;
                        try f.builder.endBlock(f, old);
                    }

                    try self.lowerExprAsStmtList(a, env, f, &then_blk, row.then_block);
                    if (then_blk.term.isNone()) try f.builder.br(&then_blk, exit_blk.id, &.{});
                    try f.builder.endBlock(f, then_blk);

                    if (!row.else_block.isNone()) {
                        try self.lowerExprAsStmtList(a, env, f, &else_blk, row.else_block.unwrap());
                    }
                    if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{});
                    try f.builder.endBlock(f, else_blk);

                    blk.* = exit_blk;
                    return self.safeUndef(blk, self.context.type_info.store.tAny());
                }
            },
            .Call => {
                return self.lowerCall(a, env, f, blk, id, expected_ty);
            },
            .Cast => {
                const row = a.exprs.get(.Cast, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
                const out = switch (row.kind) {
                    .normal => blk.builder.cast(blk, .CastNormal, ty0, v),
                    .bitcast => blk.builder.cast(blk, .CastBit, ty0, v),
                    .saturate => blk.builder.cast(blk, .CastSaturate, ty0, v),
                    .wrap => blk.builder.cast(blk, .CastWrap, ty0, v),
                    .checked => blk.builder.cast(blk, .CastChecked, ty0, v),
                };
                if (expected_ty) |want| return self.emitCoerce(blk, out, ty0, want);
                return out;
            },
            .OptionalUnwrap => {
                const row = a.exprs.get(.OptionalUnwrap, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
                const unwrap = blk.builder.intern("builtin.opt.unwrap");
                const out = blk.builder.call(blk, ty0, unwrap, &.{v});
                if (expected_ty) |want| return self.emitCoerce(blk, out, ty0, want);
                return out;
            },
            .ErrUnwrap => {
                const row = a.exprs.get(.ErrUnwrap, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
                const unwrap_ok = blk.builder.intern("builtin.err.unwrap_ok");
                const out = blk.builder.call(blk, ty0, unwrap_ok, &.{v});
                if (expected_ty) |want| return self.emitCoerce(blk, out, ty0, want);
                return out;
            },

            .Match => {
                const row = a.exprs.get(.Match, id);

                // Scrutinee value
                const scrut = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);

                // Result type of the whole match
                const res_ty = expected_ty orelse (self.getExprType(id) orelse self.context.type_info.store.tVoid());

                // Join block (phi-like param carries the match result)
                var join_blk = try f.builder.beginBlock(f);
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

                const arms = a.exprs.arm_pool.slice(row.arms);
                if (arms.len == 0) {
                    // No arms -> produce undef and just "return" the block param so callers can use it.
                    // We keep the contract that the caller’s current block becomes join_blk.
                    const uv = f.builder.constUndef(blk, res_ty);
                    try f.builder.br(blk, join_blk.id, &.{uv});
                    blk.* = join_blk;
                    return res_param;
                }

                // -------- Try the "all literal int patterns with no guards" fast path --------
                var all_int = true;
                var values = try self.gpa.alloc(u64, arms.len);
                defer self.gpa.free(values);

                var i: usize = 0;
                while (i < arms.len) : (i += 1) {
                    const arm = a.exprs.MatchArm.get(arms[i].toRaw());

                    // No guards
                    if (!arm.guard.isNone()) {
                        all_int = false;
                        break;
                    }

                    // Pattern must be a literal expr with int value
                    const pk = a.pats.index.kinds.items[arm.pattern.toRaw()];
                    if (pk != .Literal) {
                        all_int = false;
                        break;
                    }
                    const plit = a.pats.get(.Literal, arm.pattern);
                    if (a.exprs.index.kinds.items[plit.expr.toRaw()] != .Literal) {
                        all_int = false;
                        break;
                    }
                    const lit = a.exprs.get(.Literal, plit.expr);
                    if (lit.kind != .int or lit.value.isNone()) {
                        all_int = false;
                        break;
                    }

                    const s = a.exprs.strs.get(lit.value.unwrap());
                    const v = std.fmt.parseInt(u64, s, 10) catch {
                        all_int = false;
                        break;
                    };
                    values[i] = v;
                }

                if (all_int) {
                    // Build case dest blocks and default
                    var case_dests = try self.gpa.alloc(Builder.SwitchDest, arms.len);
                    defer self.gpa.free(case_dests);

                    var bodies = try self.gpa.alloc(@TypeOf(try f.builder.beginBlock(f)), arms.len);
                    defer self.gpa.free(bodies);

                    i = 0;
                    while (i < arms.len) : (i += 1) {
                        bodies[i] = try f.builder.beginBlock(f);
                    }
                    var default_blk = try f.builder.beginBlock(f);

                    try f.builder.switchInt(blk, scrut, values, blk: {
                        i = 0;
                        while (i < arms.len) : (i += 1) {
                            case_dests[i] = .{ .dest = bodies[i].id, .args = &.{} };
                        }
                        break :blk case_dests;
                    }, default_blk.id, &.{});

                    // Fill out each body; no pattern bindings to create in this fast path
                    i = 0;
                    while (i < arms.len) : (i += 1) {
                        const arm = a.exprs.MatchArm.get(arms[i].toRaw());
                        try self.lowerExprAsStmtList(a, env, f, &bodies[i], arm.body);
                        if (bodies[i].term.isNone()) {
                            var v = try self.lowerBlockExprValue(a, env, f, &bodies[i], arm.body, res_ty);
                            v = self.emitCoerce(&bodies[i], v, self.getExprType(arm.body) orelse res_ty, res_ty);
                            try f.builder.br(&bodies[i], join_blk.id, &.{v});
                        }
                        try f.builder.endBlock(f, bodies[i]);
                    }

                    const uv = f.builder.constUndef(&default_blk, res_ty);
                    try f.builder.br(&default_blk, join_blk.id, &.{uv});
                    try f.builder.endBlock(f, default_blk);

                    blk.* = join_blk;
                    return res_param;
                }

                // -------- General path: chained tests with optional guards --------
                // We create (test -> body -> next) for each arm, falling through to the
                // next arm if the test (pattern && guard) fails.
                var cur = blk.*;

                i = 0;
                while (i < arms.len) : (i += 1) {
                    const arm_id = arms[i];
                    const arm = a.exprs.MatchArm.get(arm_id.toRaw());

                    var test_blk = try f.builder.beginBlock(f);
                    var body_blk = try f.builder.beginBlock(f);
                    // The "next" block is either a fresh block (if more arms remain) or the join block.
                    const next_blk = if (i + 1 < arms.len) try f.builder.beginBlock(f) else join_blk;

                    // Jump from current to test
                    try f.builder.br(&cur, test_blk.id, &.{});

                    // Run pattern test
                    var ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut);

                    // Optional guard: ok = ok && guard
                    if (!arm.guard.isNone()) {
                        const g = try self.lowerExpr(a, env, f, &test_blk, arm.guard.unwrap(), self.context.type_info.store.tBool(), .rvalue);
                        ok = test_blk.builder.binBool(&test_blk, .LogicalAnd, ok, g);
                    }

                    // If this is the last arm and it fails, produce undef for the join
                    const else_args = if (next_blk.id.toRaw() == join_blk.id.toRaw()) blkargs: {
                        const uv = f.builder.constUndef(&test_blk, res_ty);
                        break :blkargs &.{uv};
                    } else &.{};

                    try f.builder.condBr(&test_blk, ok, body_blk.id, &.{}, next_blk.id, else_args);

                    // On success: bind pattern variables (using the original scrutinee)
                    // We attempt to pass the best type we know for scrutinee to bindPattern.
                    const scrut_ty = self.getExprType(row.expr) orelse self.context.type_info.store.tAny();
                    try self.bindPattern(a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);

                    // Body lowering
                    try self.lowerExprAsStmtList(a, env, f, &body_blk, arm.body);
                    if (body_blk.term.isNone()) {
                        var v2 = try self.lowerBlockExprValue(a, env, f, &body_blk, arm.body, res_ty);
                        v2 = self.emitCoerce(&body_blk, v2, self.getExprType(arm.body) orelse res_ty, res_ty);
                        try f.builder.br(&body_blk, join_blk.id, &.{v2});
                    }

                    // Close blocks and advance
                    try f.builder.endBlock(f, test_blk);
                    try f.builder.endBlock(f, body_blk);
                    cur = next_blk;
                }

                // Current becomes the join
                blk.* = join_blk;
                return res_param;
            },
            .While => {
                const row = a.exprs.get(.While, id);
                var header = try f.builder.beginBlock(f);
                var body = try f.builder.beginBlock(f);

                const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_info.store.tVoid());
                const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

                if (produce_value) {
                    var exit_blk = try f.builder.beginBlock(f);
                    var join_blk = try f.builder.beginBlock(f);
                    const res_ty = out_ty_guess;
                    const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

                    try f.builder.br(blk, header.id, &.{});
                    {
                        const old = blk.*;
                        try f.builder.endBlock(f, old);
                    }

                    const cond_v = if (!row.cond.isNone())
                        try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), self.context.type_info.store.tBool(), .rvalue)
                    else
                        f.builder.constBool(&header, self.context.type_info.store.tBool(), true);

                    try f.builder.condBr(&header, cond_v, body.id, &.{}, exit_blk.id, &.{});

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
                    if (body.term.isNone()) try f.builder.br(&body, header.id, &.{});
                    try f.builder.endBlock(f, header);
                    try f.builder.endBlock(f, body);

                    const uv = self.safeUndef(&exit_blk, res_ty);
                    try f.builder.br(&exit_blk, join_blk.id, &.{uv});
                    try f.builder.endBlock(f, exit_blk);

                    _ = self.loop_stack.pop();
                    blk.* = join_blk;
                    return res_param;
                } else {
                    // statement-position while: classic 3-block loop
                    const exit_blk = try f.builder.beginBlock(f);

                    try f.builder.br(blk, header.id, &.{});
                    {
                        const old = blk.*;
                        try f.builder.endBlock(f, old);
                    }

                    const cond_v = if (!row.cond.isNone())
                        try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), self.context.type_info.store.tBool(), .rvalue)
                    else
                        f.builder.constBool(&header, self.context.type_info.store.tBool(), true);

                    try f.builder.condBr(&header, cond_v, body.id, &.{}, exit_blk.id, &.{});

                    try self.loop_stack.append(self.gpa, .{
                        .label = if (!row.label.isNone()) a.exprs.strs.get(row.label.unwrap()) else null,
                        .continue_block = header.id,
                        .break_block = exit_blk.id,
                        .has_result = false, // << no value loop
                        .defer_len_at_entry = @intCast(env.defers.items.len),
                    });

                    try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                    if (body.term.isNone()) try f.builder.br(&body, header.id, &.{});
                    try f.builder.endBlock(f, header);
                    try f.builder.endBlock(f, body);

                    _ = self.loop_stack.pop();
                    blk.* = exit_blk;
                    return self.safeUndef(blk, self.context.type_info.store.tAny());
                }
            },
            .For => {
                const row = a.exprs.get(.For, id);

                // Decide if this for-expression needs to produce a value
                const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_info.store.tVoid());
                const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

                // Common blocks
                var header = try f.builder.beginBlock(f);
                var body = try f.builder.beginBlock(f);

                if (produce_value) {
                    // value-producing for
                    var exit_blk = try f.builder.beginBlock(f);
                    var join_blk = try f.builder.beginBlock(f);
                    const res_ty = out_ty_guess;
                    const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

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

                    if (a.exprs.index.kinds.items[row.iterable.toRaw()] == .Range) {
                        // for i in start..end
                        const rg = a.exprs.get(.Range, row.iterable);
                        if (rg.start.isNone() or rg.end.isNone()) return error.LoweringBug;

                        const start_v = try self.lowerExpr(a, env, f, blk, rg.start.unwrap(), null, .rvalue);
                        const end_v = try self.lowerExpr(a, env, f, blk, rg.end.unwrap(), null, .rvalue);
                        const idx_ty = self.getExprType(rg.start.unwrap()) orelse return error.LoweringBug;

                        const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);
                        try f.builder.br(blk, header.id, &.{start_v});
                        {
                            const old = blk.*;
                            try f.builder.endBlock(f, old);
                        }

                        const cond = if (rg.inclusive_right)
                            blk.builder.binBool(&header, .CmpLe, idx_param, end_v)
                        else
                            blk.builder.binBool(&header, .CmpLt, idx_param, end_v);
                        try f.builder.condBr(&header, cond, body.id, &.{}, exit_blk.id, &.{});

                        // bind loop pattern (just the index)
                        try self.bindPattern(a, env, f, &body, row.pattern, idx_param, idx_ty);
                        try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                        if (body.term.isNone()) {
                            const one = blk.builder.constInt(&body, idx_ty, 1);
                            const next_i = blk.builder.bin(&body, .Add, idx_ty, idx_param, one);
                            try f.builder.br(&body, header.id, &.{next_i});
                        }

                        try f.builder.endBlock(f, header);
                        try f.builder.endBlock(f, body);
                    } else {
                        // for x in iterable
                        const arr_v = try self.lowerExpr(a, env, f, blk, row.iterable, null, .rvalue);
                        const idx_ty = self.context.type_info.store.tUsize();
                        const s_len = f.builder.intern("builtin.len");
                        const len_v = blk.builder.call(blk, idx_ty, s_len, &.{arr_v});

                        const zero = blk.builder.constInt(blk, idx_ty, 0);
                        const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);

                        try f.builder.br(blk, header.id, &.{zero});
                        {
                            const old = blk.*;
                            try f.builder.endBlock(f, old);
                        }

                        const cond = blk.builder.binBool(&header, .CmpLt, idx_param, len_v);
                        try f.builder.condBr(&header, cond, body.id, &.{}, exit_blk.id, &.{});

                        // Determine element type
                        var elem_ty = self.context.type_info.store.tAny();
                        if (self.getExprType(row.iterable)) |it_ty| {
                            const ik = self.context.type_info.store.index.kinds.items[it_ty.toRaw()];
                            if (ik == .Array) elem_ty = self.context.type_info.store.Array.get(self.context.type_info.store.index.rows.items[it_ty.toRaw()]).elem else if (ik == .Slice) elem_ty = self.context.type_info.store.Slice.get(self.context.type_info.store.index.rows.items[it_ty.toRaw()]).elem else if (ik == .DynArray) elem_ty = self.context.type_info.store.DynArray.get(self.context.type_info.store.index.rows.items[it_ty.toRaw()]).elem;
                        }

                        const elem = blk.builder.indexOp(&body, elem_ty, arr_v, idx_param);
                        try self.bindPattern(a, env, f, &body, row.pattern, elem, elem_ty);

                        try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                        if (body.term.isNone()) {
                            const one = blk.builder.constInt(&body, idx_ty, 1);
                            const next_i = blk.builder.bin(&body, .Add, idx_ty, idx_param, one);
                            try f.builder.br(&body, header.id, &.{next_i});
                        }

                        try f.builder.endBlock(f, header);
                        try f.builder.endBlock(f, body);
                    }

                    // Exit -> join with a safe undef of the result type
                    const uv = self.safeUndef(&exit_blk, res_ty);
                    try f.builder.br(&exit_blk, join_blk.id, &.{uv});
                    try f.builder.endBlock(f, exit_blk);

                    _ = self.loop_stack.pop();
                    blk.* = join_blk;
                    return res_param;
                } else {
                    // statement-position for (no value)
                    const exit_blk = try f.builder.beginBlock(f);

                    // Loop stack entry (no value carried)
                    try self.loop_stack.append(self.gpa, .{
                        .label = if (!row.label.isNone()) a.exprs.strs.get(row.label.unwrap()) else null,
                        .continue_block = header.id,
                        .break_block = exit_blk.id,
                        .has_result = false,
                        .defer_len_at_entry = @intCast(env.defers.items.len),
                    });

                    if (a.exprs.index.kinds.items[row.iterable.toRaw()] == .Range) {
                        const rg = a.exprs.get(.Range, row.iterable);
                        if (rg.start.isNone() or rg.end.isNone()) return error.LoweringBug;

                        const start_v = try self.lowerExpr(a, env, f, blk, rg.start.unwrap(), null, .rvalue);
                        const end_v = try self.lowerExpr(a, env, f, blk, rg.end.unwrap(), null, .rvalue);
                        const idx_ty = self.getExprType(rg.start.unwrap()) orelse return error.LoweringBug;

                        const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);
                        try f.builder.br(blk, header.id, &.{start_v});
                        {
                            const old = blk.*;
                            try f.builder.endBlock(f, old);
                        }

                        const cond = if (rg.inclusive_right)
                            blk.builder.binBool(&header, .CmpLe, idx_param, end_v)
                        else
                            blk.builder.binBool(&header, .CmpLt, idx_param, end_v);
                        try f.builder.condBr(&header, cond, body.id, &.{}, exit_blk.id, &.{});

                        try self.bindPattern(a, env, f, &body, row.pattern, idx_param, idx_ty);
                        try self.lowerExprAsStmtList(a, env, f, &body, row.body);

                        if (body.term.isNone()) {
                            const one = blk.builder.constInt(&body, idx_ty, 1);
                            const next_i = blk.builder.bin(&body, .Add, idx_ty, idx_param, one);
                            try f.builder.br(&body, header.id, &.{next_i});
                        }

                        try f.builder.endBlock(f, header);
                        try f.builder.endBlock(f, body);
                    } else {
                        const arr_v = try self.lowerExpr(a, env, f, blk, row.iterable, null, .rvalue);
                        const idx_ty = self.context.type_info.store.tUsize();
                        const s_len = f.builder.intern("builtin.len");
                        const len_v = blk.builder.call(blk, idx_ty, s_len, &.{arr_v});

                        const zero = blk.builder.constInt(blk, idx_ty, 0);
                        const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);

                        try f.builder.br(blk, header.id, &.{zero});
                        {
                            const old = blk.*;
                            try f.builder.endBlock(f, old);
                        }

                        const cond = blk.builder.binBool(&header, .CmpLt, idx_param, len_v);
                        try f.builder.condBr(&header, cond, body.id, &.{}, exit_blk.id, &.{});

                        var elem_ty = self.context.type_info.store.tAny();
                        if (self.getExprType(row.iterable)) |it_ty| {
                            const ik = self.context.type_info.store.index.kinds.items[it_ty.toRaw()];
                            if (ik == .Array) elem_ty = self.context.type_info.store.Array.get(self.context.type_info.store.index.rows.items[it_ty.toRaw()]).elem else if (ik == .Slice) elem_ty = self.context.type_info.store.Slice.get(self.context.type_info.store.index.rows.items[it_ty.toRaw()]).elem else if (ik == .DynArray) elem_ty = self.context.type_info.store.DynArray.get(self.context.type_info.store.index.rows.items[it_ty.toRaw()]).elem;
                        }
                        const elem = blk.builder.indexOp(&body, elem_ty, arr_v, idx_param);
                        try self.bindPattern(a, env, f, &body, row.pattern, elem, elem_ty);

                        try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                        if (body.term.isNone()) {
                            const one = blk.builder.constInt(&body, idx_ty, 1);
                            const next_i = blk.builder.bin(&body, .Add, idx_ty, idx_param, one);
                            try f.builder.br(&body, header.id, &.{next_i});
                        }

                        try f.builder.endBlock(f, header);
                        try f.builder.endBlock(f, body);
                    }

                    _ = self.loop_stack.pop();
                    blk.* = exit_blk;
                    return self.safeUndef(blk, self.context.type_info.store.tAny());
                }
            },
            .Import => {
                // Lowered as 'any' module value (opaque); create undef of the checker type
                const ty0 = self.getExprType(id) orelse self.context.type_info.store.tAny();
                return blk.builder.constUndef(blk, ty0);
            },
            else => return error.LoweringBug,
        }
    }

    // Compute the value of a block expression (value position)
    fn lowerBlockExprValue(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, block_expr: ast.ExprId, expected_ty: types.TypeId) anyerror!tir.ValueId {
        if (a.exprs.index.kinds.items[block_expr.toRaw()] != .Block) {
            return self.lowerExpr(a, env, f, blk, block_expr, expected_ty, .rvalue);
        }
        const b = a.exprs.get(.Block, block_expr);
        const stmts = a.stmts.stmt_pool.slice(b.items);
        if (stmts.len == 0) return self.safeUndef(blk, expected_ty);
        var i: usize = 0;
        while (i + 1 < stmts.len) : (i += 1) {
            try self.lowerStmt(a, env, f, blk, stmts[i]);
        }
        const last = stmts[stmts.len - 1];
        const lk = a.stmts.index.kinds.items[last.toRaw()];
        if (lk == .Expr) {
            const le = a.stmts.get(.Expr, last).expr;
            return self.lowerExpr(a, env, f, blk, le, expected_ty, .rvalue);
        } else {
            try self.lowerStmt(a, env, f, blk, last);
            return self.safeUndef(blk, expected_ty);
        }
    }

    // ============================
    // Import materialization
    // ============================

    fn findTopLevelDeclByName(_: *const @This(), a: *const ast.Ast, name: []const u8) ?ast.DeclId {
        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        var i: usize = 0;
        while (i < decls.len) : (i += 1) {
            const d = a.exprs.Decl.get(decls[i].toRaw());
            if (d.pattern.isNone()) continue;
            const pid = d.pattern.unwrap();
            const pk = a.pats.index.kinds.items[pid.toRaw()];
            if (pk != .Binding) continue;
            const b = a.pats.get(.Binding, pid);
            if (std.mem.eql(u8, a.exprs.strs.get(b.name), name)) return decls[i];
        }
        return null;
    }
    fn findTopLevelImportByName(self: *const @This(), a: *const ast.Ast, name: []const u8) ?ast.DeclId {
        const did = self.findTopLevelDeclByName(a, name) orelse return null;
        const d = a.exprs.Decl.get(did.toRaw());
        return if (a.exprs.index.kinds.items[d.value.toRaw()] == .Import) did else null;
    }

    fn materializeImportedConst(self: *@This(), res: *@import("import_resolver.zig").ImportResolver, a: *const ast.Ast, imp_decl: ast.DeclId, member: StrId, expected_ty: types.TypeId, blk: *Builder.BlockFrame, pipeline: *Pipeline) ?tir.ValueId {
        const d = a.exprs.Decl.get(imp_decl.toRaw());
        const ir = a.exprs.get(.Import, d.value);
        if (a.exprs.index.kinds.items[ir.expr.toRaw()] != .Literal) return null;
        const lit = a.exprs.get(.Literal, ir.expr);
        if (lit.value.isNone()) return null;
        var s_full = a.exprs.strs.get(lit.value.unwrap());
        if (s_full.len >= 2 and s_full[0] == '"' and s_full[s_full.len - 1] == '"') s_full = s_full[1 .. s_full.len - 1];

        const me = res.resolve(self.import_base_dir, s_full, pipeline) catch return null;
        // Find member decl by name
        const want = a.exprs.strs.get(member);
        const decls = me.ast.exprs.decl_pool.slice(me.ast.unit.decls);
        var i: usize = 0;
        while (i < decls.len) : (i += 1) {
            const d2 = me.ast.exprs.Decl.get(decls[i].toRaw());
            if (d2.pattern.isNone()) continue;
            const pid = d2.pattern.unwrap();
            const pk = me.ast.pats.index.kinds.items[pid.toRaw()];
            if (pk != .Binding) continue;
            const b = me.ast.pats.get(.Binding, pid);
            const nm = me.ast.exprs.strs.get(b.name);
            if (std.mem.eql(u8, nm, want)) {
                return self.lowerImportedExprValue(me, d2.value, expected_ty, blk);
            }
        }
        return null;
    }

    fn lowerImportedExprValue(self: *@This(), me: *@import("import_resolver.zig").ModuleEntry, eid: ast.ExprId, expected_ty: types.TypeId, blk: *Builder.BlockFrame) ?tir.ValueId {
        const kinds = me.ast.exprs.index.kinds.items;
        switch (kinds[eid.toRaw()]) {
            .StructLit => {
                if (self.context.type_info.store.getKind(expected_ty) != .Struct) return null;
                const row = me.ast.exprs.get(.StructLit, eid);
                const sfields = me.ast.exprs.sfv_pool.slice(row.fields);
                const st = self.context.type_info.store.get(.Struct, expected_ty);
                const exp_fields = self.context.type_info.store.field_pool.slice(st.fields);
                var fields = self.gpa.alloc(tir.Rows.StructFieldInit, exp_fields.len) catch return null;
                var j: usize = 0;
                while (j < exp_fields.len) : (j += 1) {
                    const f = self.context.type_info.store.Field.get(exp_fields[j].toRaw());
                    const src_idx = if (j < sfields.len) j else sfields.len - 1;
                    const sfv = me.ast.exprs.StructFieldValue.get(sfields[src_idx].toRaw());
                    const vv = self.lowerImportedExprValue(me, sfv.value, f.ty, blk) orelse {
                        self.gpa.free(fields);
                        return null;
                    };
                    fields[j] = .{ .index = @intCast(j), .name = OptStrId.none(), .value = vv };
                }
                const v = blk.builder.structMake(blk, expected_ty, fields);
                self.gpa.free(fields);
                return v;
            },
            .Literal => {
                const lit = me.ast.exprs.get(.Literal, eid);
                const s = if (!lit.value.isNone()) me.ast.exprs.strs.get(lit.value.unwrap()) else "";
                const k = self.context.type_info.store.getKind(expected_ty);
                switch (k) {
                    .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64 => return blk.builder.constInt(blk, expected_ty, std.fmt.parseInt(u64, s, 10) catch 0),
                    .Bool => return blk.builder.constBool(blk, expected_ty, lit.bool_value),
                    .String => return blk.builder.constString(blk, expected_ty, s),
                    else => return null,
                }
            },
            else => return null,
        }
    }

    // ============================
    // Misc helpers
    // ============================

    fn getExprType(self: *const @This(), id: ast.ExprId) ?types.TypeId {
        const i = id.toRaw();
        if (i >= self.context.type_info.expr_types.items.len) return null;
        return self.context.type_info.expr_types.items[i];
    }
    fn getDeclType(self: *const @This(), did: ast.DeclId) ?types.TypeId {
        const i = did.toRaw();
        if (i >= self.context.type_info.decl_types.items.len) return null;
        return self.context.type_info.decl_types.items[i];
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
                var etys: []const types.TypeId = &[_]types.TypeId{};
                const vk = self.context.type_info.store.index.kinds.items[vty.toRaw()];
                if (vk == .Tuple) {
                    const vrow = self.context.type_info.store.Tuple.get(self.context.type_info.store.index.rows.items[vty.toRaw()]);
                    etys = self.context.type_info.store.type_pool.slice(vrow.elems);
                }
                while (i < elems.len) : (i += 1) {
                    const ety = if (i < etys.len) etys[i] else self.context.type_info.store.tAny();
                    const ev = blk.builder.extractElem(blk, ety, value, @intCast(i));
                    try self.bindPattern(a, env, f, blk, elems[i], ev, ety);
                }
            },
            else => {},
        }
    }

    fn matchPattern(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, scrut: tir.ValueId) !tir.ValueId {
        const k = a.pats.index.kinds.items[pid.toRaw()];
        switch (k) {
            .Wildcard => return blk.builder.constBool(blk, self.context.type_info.store.tBool(), true),
            .Literal => {
                const pr = a.pats.get(.Literal, pid);
                const litv = try self.lowerExpr(a, env, f, blk, pr.expr, null, .rvalue);
                return blk.builder.binBool(blk, .CmpEq, scrut, litv);
            },
            .Binding, .Path, .Tuple, .Slice, .Struct, .VariantTuple, .VariantStruct, .Range, .Or, .At => {
                return blk.builder.constBool(blk, self.context.type_info.store.tBool(), true);
            },
        }
    }
};

// ============================
// Context structs
// ============================

const LoopCtx = struct {
    label: ?[]const u8,
    continue_block: tir.BlockId,
    break_block: tir.BlockId,
    has_result: bool = false,
    join_block: tir.BlockId = tir.BlockId.fromRaw(0),
    res_param: tir.ValueId = tir.ValueId.fromRaw(0),
    res_ty: types.TypeId = undefined,
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

// ============================
// Builder facade over TIR
// ============================

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
        term: tir.OptTermId = .none(),
        pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
            self.instrs.deinit(gpa);
            self.params.deinit(gpa);
        }
    };
    const SwitchDest = struct { dest: tir.BlockId, args: []const tir.ValueId };

    pub fn beginFunction(self: *@This(), name: StrId, result: types.TypeId, is_variadic: bool) !FunctionFrame {
        const idx = self.t.funcs.Function.add(self.gpa, .{ .name = name, .params = tir.RangeParam.empty(), .result = result, .blocks = tir.RangeBlock.empty(), .is_variadic = is_variadic });
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
        row.term = blk.term.unwrap();
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
        _ = self.t.funcs.func_pool.push(self.gpa, f.id);
    }

    // ---- instruction helpers ----
    fn constInt(self: *@This(), blk: *BlockFrame, ty: types.TypeId, v: u64) tir.ValueId {
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
        const gid = tir.GlobalId.fromRaw(idx);
        _ = self.t.funcs.global_pool.push(self.gpa, gid);
        return gid;
    }
    fn edge(self: *@This(), dest: tir.BlockId, args: []const tir.ValueId) tir.EdgeId {
        const r = self.t.instrs.value_pool.pushMany(self.gpa, args);
        const eid = self.t.terms.Edge.add(self.gpa, .{ .dest = dest, .args = r });
        return tir.EdgeId.fromRaw(eid);
    }
    pub fn br(self: *@This(), blk: *BlockFrame, dest: tir.BlockId, args: []const tir.ValueId) !void {
        const e = self.edge(dest, args);
        const tid = self.t.terms.add(.Br, .{ .edge = e });
        blk.term = tir.OptTermId.some(tid);
    }
    pub fn condBr(self: *@This(), blk: *BlockFrame, cond: tir.ValueId, then_dest: tir.BlockId, then_args: []const tir.ValueId, else_dest: tir.BlockId, else_args: []const tir.ValueId) !void {
        const te = self.edge(then_dest, then_args);
        const ee = self.edge(else_dest, else_args);
        const tid = self.t.terms.add(.CondBr, .{ .cond = cond, .then_edge = te, .else_edge = ee });
        blk.term = tir.OptTermId.some(tid);
    }

    fn constUndef(self: *@This(), blk: *BlockFrame, ty: types.TypeId) tir.ValueId {
        // Disallow void undef
        std.debug.assert(self.t.type_store.getKind(ty) != .Void);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ConstUndef, tir.Rows.ConstUndef{ .result = vid, .ty = ty });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }

    fn setReturn(self: *@This(), blk: *BlockFrame, value: tir.OptValueId) !void {
        const tid = self.t.terms.add(.Return, .{ .value = value });
        blk.term = tir.OptTermId.some(tid);
    }
    pub fn setReturnVal(self: *@This(), blk: *BlockFrame, v: tir.ValueId) !void {
        return self.setReturn(blk, tir.OptValueId.some(v));
    }
    pub fn setReturnVoid(self: *@This(), blk: *BlockFrame) !void {
        return self.setReturn(blk, tir.OptValueId.none());
    }
    pub fn setUnreachable(self: *@This(), blk: *BlockFrame) !void {
        const tid = self.t.terms.add(.Unreachable, .{});
        blk.term = tir.OptTermId.some(tid);
    }

    pub fn switchInt(self: *@This(), blk: *BlockFrame, scrut: tir.ValueId, case_vals: []const u64, case_dests: []const SwitchDest, default_dest: tir.BlockId, default_args: []const tir.ValueId) !void {
        std.debug.assert(case_vals.len == case_dests.len);
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
        blk.term = tir.OptTermId.some(tid);
    }

    // GEP helpers
    fn gepConst(self: *@This(), v: u64) tir.GepIndexId {
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
