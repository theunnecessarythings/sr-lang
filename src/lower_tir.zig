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
const Builder = tir.Builder;

pub const LowerTir = struct {
    gpa: std.mem.Allocator,
    context: *Context,
    pipeline: *Pipeline,
    type_info: *types.TypeInfo,

    // Simple loop stack to support break/continue in While/For (+ value loops)
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},

    // Mapping: module ident name -> prefix for mangling (module.func -> prefix_func)
    module_prefix: std.StringHashMapUnmanaged([]const u8) = .{},

    import_base_dir: []const u8 = ".",

    const BindingSnapshot = struct {
        name: ast.StrId,
        prev: ?ValueBinding,
    };

    fn constInitFromLiteral(
        self: *LowerTir,
        a: *const ast.Ast,
        expr: ast.ExprId,
        ty: types.TypeId,
    ) ?tir.ConstInit {
        const kind = a.exprs.index.kinds.items[expr.toRaw()];
        if (kind != .Literal) return null;
        const lit = a.exprs.get(.Literal, expr);

        const ty_kind = self.context.type_store.getKind(ty);
        return switch (ty_kind) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => blk: {
                if (lit.kind != .int or lit.value.isNone()) break :blk null;
                const text = a.exprs.strs.get(lit.value.unwrap());
                const parsed = std.fmt.parseInt(i64, text, 10) catch return null;
                break :blk tir.ConstInit{ .int = parsed };
            },
            .Bool => blk: {
                if (lit.kind != .bool) break :blk null;
                break :blk tir.ConstInit{ .bool = lit.bool_value };
            },
            else => null,
        };
    }

    pub fn init(
        gpa: std.mem.Allocator,
        context: *Context,
        pipeline: *Pipeline,
        type_info: *types.TypeInfo,
    ) LowerTir {
        return .{ .gpa = gpa, .context = context, .pipeline = pipeline, .type_info = type_info };
    }

    pub fn deinit(self: *LowerTir) void {
        self.loop_stack.deinit(self.gpa);
        var it = self.module_prefix.valueIterator();
        while (it.next()) |p| self.gpa.free(p.*);
        self.module_prefix.deinit(self.gpa);
    }

    pub fn setImportResolver(self: *LowerTir, r: *ImportResolver, base_dir: []const u8) void {
        self.import_resolver = r;
        self.import_base_dir = base_dir;
    }

    fn lowerGlobalMlir(self: *LowerTir, a: *const ast.Ast, b: *Builder) !void {
        var global_mlir_decls: std.ArrayList(ast.DeclId) = .empty;
        defer global_mlir_decls.deinit(self.gpa);

        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        for (decls) |did| {
            const d = a.exprs.Decl.get(did);
            const kind = a.exprs.index.kinds.items[d.value.toRaw()];
            if (kind == .MlirBlock and d.pattern.isNone()) {
                try global_mlir_decls.append(self.gpa, did);
            }
        }

        if (global_mlir_decls.items.len == 0) return;

        const name = b.intern("__sr_global_mlir_init");
        var f = try b.beginFunction(name, self.context.type_store.tVoid(), false);
        var blk = try b.beginBlock(&f);
        var env = Env.init(self.gpa);
        defer env.deinit(self.gpa);

        for (global_mlir_decls.items) |did| {
            const d = a.exprs.Decl.get(did);
            _ = try self.lowerExpr(a, &env, &f, &blk, d.value, null, .rvalue);
        }

        if (blk.term.isNone()) {
            try b.setReturn(&blk, .none());
        }
        try b.endBlock(&f, blk);
        try b.endFunction(f);
    }

    pub fn run(self: *LowerTir, a: *const ast.Ast) !tir.TIR {
        var t = tir.TIR.init(self.gpa, &self.context.type_store);
        var b = Builder.init(self.gpa, &t);

        try self.lowerGlobalMlir(a, &b);

        // Lower top-level decls: functions and globals
        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        for (decls) |did| try self.lowerTopDecl(a, &b, did);

        return t;
    }

    pub fn setModulePrefix(self: *LowerTir, name: []const u8, prefix: []const u8) !void {
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

    fn isVoid(self: *const LowerTir, ty: types.TypeId) bool {
        return self.context.type_store.index.kinds.items[ty.toRaw()] == .Void;
    }

    // Produce an undef that is never-void; if asked for void, give Any instead.
    fn safeUndef(self: *LowerTir, blk: *Builder.BlockFrame, ty: types.TypeId) tir.ValueId {
        if (self.isVoid(ty)) return blk.builder.tirValue(.ConstUndef, blk, self.context.type_store.tAny(), .{});
        return blk.builder.tirValue(.ConstUndef, blk, ty, .{});
    }

    fn undef(_: *LowerTir, blk: *Builder.BlockFrame, ty: types.TypeId) tir.ValueId {
        return blk.builder.tirValue(.ConstUndef, blk, ty, .{});
    }

    /// Insert an explicit coercion that realizes what the checker proved assignable/castable.
    fn emitCoerce(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        v: tir.ValueId,
        got: types.TypeId,
        want: types.TypeId,
    ) tir.ValueId {
        if (got.eq(want)) return v;

        const ts = &self.context.type_store;
        const gk = ts.index.kinds.items[got.toRaw()];
        const wk = ts.index.kinds.items[want.toRaw()];

        // ---- Special-case: wrap into ErrorSet ----
        if (wk == .ErrorSet) {
            const es = ts.get(.ErrorSet, want);

            // payload union: { Ok: T, Err: E }
            var uf = [_]types.TypeStore.StructFieldArg{
                .{ .name = blk.builder.intern("Ok"), .ty = es.value_ty },
                .{ .name = blk.builder.intern("Err"), .ty = es.error_ty },
            };
            const payload_union_ty = ts.mkUnion(uf[0..]);

            // Value T -> Ok
            if (got.toRaw() == es.value_ty.toRaw()) {
                const tag_ok = blk.builder.tirValue(.ConstInt, blk, ts.tI32(), .{ .value = 0 });
                const payload = blk.builder.tirValue(.UnionMake, blk, payload_union_ty, .{
                    .field_index = 0, // Ok
                    .value = v,
                });
                return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = tag_ok },
                    .{ .index = 1, .name = .none(), .value = payload },
                });
            }

            // Error E -> Err
            if (got.toRaw() == es.error_ty.toRaw()) {
                const tag_err = blk.builder.tirValue(.ConstInt, blk, ts.tI32(), .{ .value = 1 });
                const payload = blk.builder.tirValue(.UnionMake, blk, payload_union_ty, .{
                    .field_index = 1, // Err
                    .value = v,
                });
                return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = tag_err },
                    .{ .index = 1, .name = .none(), .value = payload },
                });
            }
            // else fall through (e.g., Any → ErrorSet: let the generic path try)
        }

        // Numeric ⇄ numeric
        const is_num_got = switch (gk) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64 => true,
            else => false,
        };
        const is_num_want = switch (wk) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64 => true,
            else => false,
        };
        if (is_num_got and is_num_want)
            return blk.builder.tirValue(.CastNormal, blk, want, .{ .value = v });

        // Ptr ⇄ Ptr
        if (gk == .Ptr and wk == .Ptr)
            return blk.builder.tirValue(.CastBit, blk, want, .{ .value = v });

        // Fallback: materialize/assignable
        return blk.builder.tirValue(.CastNormal, blk, want, .{ .value = v });
    }

    // ============================
    // Top-level lowering
    // ============================

    fn lowerTopDecl(self: *LowerTir, a: *const ast.Ast, b: *Builder, did: ast.DeclId) !void {
        const d = a.exprs.Decl.get(did);
        const kind = a.exprs.index.kinds.items[d.value.toRaw()];

        if (kind == .MlirBlock and d.pattern.isNone()) {
            return; // handled by lowerGlobalMlir
        }

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
            if (self.constInitFromLiteral(a, d.value, ty)) |ci| {
                _ = b.addGlobalWithInit(nm, ty, ci);
            } else {
                _ = b.addGlobal(nm, ty);
            }
        }
    }

    fn lowerFunction(self: *LowerTir, a: *const ast.Ast, b: *Builder, name: StrId, fun_eid: ast.ExprId) !void {
        const fid = self.getExprType(fun_eid) orelse return;
        if (self.context.type_store.index.kinds.items[fid.toRaw()] != .Function) return;
        const fnty = self.context.type_store.get(.Function, fid);

        const fnr = a.exprs.get(.FunctionLit, fun_eid);

        if (!fnr.attrs.isNone()) {
            const attrs = a.exprs.attr_pool.slice(fnr.attrs.asRange());
            const mlir = a.exprs.strs.intern("mlir_fn");
            for (attrs) |aid| {
                const arow = a.exprs.Attribute.get(aid);
                if (arow.name.eq(mlir)) {
                    return; // skip lowering this function
                }
            }
        }

        var f = try b.beginFunction(name, fnty.result, fnty.is_variadic);

        // Params
        const params = a.exprs.param_pool.slice(fnr.params);
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = a.exprs.Param.get(params[i]);
            const pty = self.context.type_store.type_pool.slice(fnty.params)[i];
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
            const p = a.exprs.Param.get(params[i]);
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
    fn lowerExprAsStmtList(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId) !void {
        if (a.exprs.index.kinds.items[id.toRaw()] == .Block) {
            const b = a.exprs.get(.Block, id);
            const stmts = a.stmts.stmt_pool.slice(b.items);
            const start: u32 = @intCast(env.defers.items.len);
            try env.pushScope(self.gpa);
            for (stmts) |sid| {
                if (!blk.term.isNone()) break;
                try self.lowerStmt(a, env, f, blk, sid);
            }
            if (blk.term.isNone()) {
                const slice = env.defers.items[start .. env.defers.items.len];
                if (slice.len > 0) try self.emitDefers(a, env, f, blk, slice, false);
            }
            env.defers.items.len = start;
            _ = env.popScope();
        } else {
            _ = try self.lowerExpr(a, env, f, blk, id, null, .rvalue);
        }
    }

    /// Run "normal" (non-err) defers scheduled at or after `from`, in reverse order,
    /// and then truncate the defer stack back to `from`.
    fn runNormalDefersFrom(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        from: u32,
    ) !void {
        var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
        while (j >= 0 and @as(u32, @intCast(j)) >= from) : (j -= 1) {
            const ent = env.defers.items[@intCast(j)];
            if (!ent.is_err) {
                _ = try self.lowerExpr(a, env, f, blk, ent.expr, null, .rvalue);
            }
        }
        env.defers.items.len = from;
    }

    fn hasErrDefersFrom(_: *LowerTir, env: *Env, from: u32) bool {
        var i: usize = env.defers.items.len;
        while (i > from) : (i -= 1) {
            if (env.defers.items[i - 1].is_err) return true;
        }
        return false;
    }

    fn emitDefers(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        slice: []const DeferEntry,
        want_err: bool,
    ) !void {
        var j: isize = @as(isize, @intCast(slice.len)) - 1;
        while (j >= 0) : (j -= 1) {
            const ent = slice[@intCast(j)];
            if (ent.is_err == want_err) {
                _ = try self.lowerExpr(a, env, f, blk, ent.expr, null, .rvalue);
            }
        }
    }

    fn runDefersForLoopExit(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        lc: LoopCtx,
    ) !void {
        var j: isize = @as(isize, @intCast(env.defers.items.len)) - 1;
        while (j >= 0 and @as(u32, @intCast(j)) >= lc.defer_len_at_entry) : (j -= 1) {
            const ent = env.defers.items[@intCast(j)];
            if (!ent.is_err) _ = try self.lowerExpr(a, env, f, blk, ent.expr, null, .rvalue);
        }
    }

    fn lowerBreak(
        self: *LowerTir,
        a: *const ast.Ast,
        br: ast.Rows.Break,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
    ) !void {
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
            try self.runDefersForLoopExit(a, env, f, blk, lc);
            if (lc.has_result) {
                const v = if (!br.value.isNone())
                    try self.lowerExpr(a, env, f, blk, br.value.unwrap(), lc.res_ty, .rvalue)
                else
                    f.builder.tirValue(.ConstUndef, blk, lc.res_ty, .{});
                try f.builder.br(blk, lc.join_block, &.{v});
            } else {
                try f.builder.br(blk, lc.break_block, &.{});
            }
        } else return error.LoweringBug;
    }

    fn lowerContinue(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, cid: ast.Rows.Continue) !void {
        _ = cid;
        const lc = if (self.loop_stack.items.len > 0) self.loop_stack.items[self.loop_stack.items.len - 1] else return error.LoweringBug;
        try self.runDefersForLoopExit(a, env, f, blk, lc);
        switch (lc.continue_info) {
            .none => try f.builder.br(blk, lc.continue_block, &.{}),
            .range => |info| try f.builder.br(blk, info.update_block, &.{info.idx_value}),
        }
    }

    fn lowerDecl(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        sid: ast.StmtId,
    ) !void {
        const drow = a.stmts.get(.Decl, sid);
        const d = a.exprs.Decl.get(drow.decl);
        const vty = self.getExprType(d.value) orelse self.context.type_store.tAny();
        if (!d.pattern.isNone()) {
            // Destructure once for all names: bind as values for const, or slots for mut.
            try self.destructureDeclFromExpr(a, env, f, blk, d.pattern.unwrap(), d.value, vty, !d.flags.is_const);
        } else {
            // No pattern: just evaluate for side-effects.
            _ = try self.lowerExpr(a, env, f, blk, d.value, vty, .rvalue);
        }
    }

    fn lowerReturn(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        sid: ast.StmtId,
    ) !void {
        const r = a.stmts.get(.Return, sid);
        const defer_mark: u32 = 0;

        if (!r.value.isNone()) {
            const frow = f.builder.t.funcs.Function.get(f.id);
            const expect = frow.result;
            const v_raw = try self.lowerExpr(a, env, f, blk, r.value.unwrap(), null, .rvalue);
            var v = v_raw;
            if (self.getExprType(r.value.unwrap())) |got| {
                v = self.emitCoerce(blk, v_raw, got, expect);
            }

            const expect_kind = self.context.type_store.index.kinds.items[expect.toRaw()];
            const has_err_defers = expect_kind == .ErrorSet and self.hasErrDefersFrom(env, defer_mark);

            if (has_err_defers) {
                var err_blk = try f.builder.beginBlock(f);
                var ok_blk = try f.builder.beginBlock(f);
                const tag_ty = self.context.type_store.tI32();
                const tag = blk.builder.extractField(blk, tag_ty, v, 0);
                const zero = blk.builder.tirValue(.ConstInt, blk, tag_ty, .{ .value = 0 });
                const is_err = blk.builder.binBool(blk, .CmpNe, tag, zero);
                const br_cond = self.forceLocalCond(blk, is_err);
                try f.builder.condBr(blk, br_cond, err_blk.id, &.{}, ok_blk.id, &.{});

                const defer_slice = env.defers.items[defer_mark .. env.defers.items.len];

                try self.emitDefers(a, env, f, &err_blk, defer_slice, true);
                try self.emitDefers(a, env, f, &err_blk, defer_slice, false);
                try f.builder.setReturnVal(&err_blk, v);
                try f.builder.endBlock(f, err_blk);

                try self.emitDefers(a, env, f, &ok_blk, defer_slice, false);
                try f.builder.setReturnVal(&ok_blk, v);
                try f.builder.endBlock(f, ok_blk);

                env.defers.items.len = defer_mark;
                return;
            } else {
                try self.runNormalDefersFrom(a, env, f, blk, defer_mark);
                try f.builder.setReturnVal(blk, v);
                return;
            }
        } else {
            try self.runNormalDefersFrom(a, env, f, blk, defer_mark);
            try f.builder.setReturnVoid(blk);
            return;
        }
    }

    fn lowerAssign(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, sid: ast.StmtId) !void {
        const as = a.stmts.get(.Assign, sid);
        const lhs_ptr = try self.lowerExpr(a, env, f, blk, as.left, null, .lvalue_addr);
        const rhs = try self.lowerExpr(a, env, f, blk, as.right, self.getExprType(as.left), .rvalue);
        const rty = self.getExprType(as.left) orelse return error.LoweringBug;
        _ = f.builder.tirValue(.Store, blk, rty, .{ .ptr = lhs_ptr, .value = rhs, .@"align" = 0 });
    }

    fn lowerStmt(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, sid: ast.StmtId) !void {
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
            .Break => try self.lowerBreak(a, a.stmts.get(.Break, sid), env, f, blk),
            .Continue => try self.lowerContinue(a, env, f, blk, a.stmts.get(.Continue, sid)),
            .Decl => try self.lowerDecl(a, env, f, blk, sid),
            .Assign => try self.lowerAssign(a, env, f, blk, sid),
            .Return => try self.lowerReturn(a, env, f, blk, sid),
            .Unreachable => try f.builder.setUnreachable(blk),
            else => @panic("unhandled stmt kind"),
        }
    }

    // ============================
    // Expressions
    // ============================

    const CalleeInfo = struct {
        name: StrId,
        fty: ?types.TypeId,
    };

    fn resolveCallee(self: *LowerTir, a: *const ast.Ast, f: *Builder.FunctionFrame, row: ast.Rows.Call) CalleeInfo {
        const ck = a.exprs.index.kinds.items[row.callee.toRaw()];
        if (ck == .Ident) {
            const nm = a.exprs.get(.Ident, row.callee).name;
            return .{ .name = nm, .fty = self.getExprType(row.callee) };
        }
        if (ck == .FieldAccess)
            return .{
                .name = a.exprs.get(.FieldAccess, row.callee).field,
                .fty = self.getExprType(row.callee),
            };
        return .{ .name = f.builder.intern("<indirect>"), .fty = self.getExprType(row.callee) };
    }

    fn buildVariantItem(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        row: ast.Rows.Call,
        ety: types.TypeId,
        k: types.TypeKind,
    ) !tir.ValueId {
        var cur = row.callee;
        var last_name: ?StrId = null;
        while (a.exprs.index.kinds.items[cur.toRaw()] == .FieldAccess) {
            const fr = a.exprs.get(.FieldAccess, cur);
            last_name = fr.field;
            cur = fr.parent;
        }
        if (last_name == null) return error.LoweringBug;
        const lname = last_name.?;

        const fields = if (k == .Variant)
            self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, ety).variants)
        else
            self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, ety).variants);

        var tag_idx: u32 = 0;
        var payload_ty: types.TypeId = self.context.type_store.tVoid();
        var found = false;
        for (fields, 0..) |fld_id, i| {
            const fld = self.context.type_store.Field.get(fld_id);
            if (fld.name.eq(lname)) {
                tag_idx = @intCast(i);
                payload_ty = fld.ty;
                found = true;
                break;
            }
        }
        if (!found) return error.LoweringBug;

        const args = a.exprs.expr_pool.slice(row.args);
        const payload_kind = self.context.type_store.getKind(payload_ty);

        const payload_val: ?tir.ValueId = switch (payload_kind) {
            .Void => null,
            .Tuple => blk: {
                const tr = self.context.type_store.get(.Tuple, payload_ty);
                const subtys = self.context.type_store.type_pool.slice(tr.elems);
                var elems = try self.gpa.alloc(tir.ValueId, subtys.len);
                defer self.gpa.free(elems);
                for (subtys, 0..) |sty, i| {
                    const arg_id = if (i < args.len) args[i] else args[args.len - 1];
                    elems[i] = try self.lowerExpr(a, env, f, blk, arg_id, sty, .rvalue);
                }
                break :blk blk.builder.tupleMake(blk, payload_ty, elems);
            },
            else => try self.lowerExpr(a, env, f, blk, args[0], payload_ty, .rvalue),
        };

        // tag (i32)
        const tag_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), .{ .value = tag_idx });

        // union type for the payload field
        var union_fields_args = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
        defer self.gpa.free(union_fields_args);
        for (fields, 0..) |fld_id, i| {
            const fld = self.context.type_store.Field.get(fld_id);
            union_fields_args[i] = .{ .name = fld.name, .ty = fld.ty };
        }
        const union_ty = self.context.type_store.mkUnion(union_fields_args);

        // IMPORTANT: for void payload, do NOT call UnionMake (it would force an llvm.void store).
        const union_val: tir.ValueId = if (payload_val) |pv|
            blk.builder.tirValue(.UnionMake, blk, union_ty, .{ .field_index = tag_idx, .value = pv })
        else
            blk.builder.tirValue(.ConstUndef, blk, union_ty, .{});

        return blk.builder.structMake(blk, ety, &[_]tir.Rows.StructFieldInit{
            .{ .index = 0, .name = .none(), .value = tag_val },
            .{ .index = 1, .name = .none(), .value = union_val },
        });
    }

    fn lowerCall(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected: ?types.TypeId,
    ) !tir.ValueId {
        const row = a.exprs.get(.Call, id);
        const callee = self.resolveCallee(a, f, row);

        // Variant construction: if expected is a Variant/Error and callee is a path to a case, build VariantMake
        if (expected) |ety| {
            const k = self.context.type_store.getKind(ety);
            if (k == .Variant or k == .Error)
                return try self.buildVariantItem(a, env, f, blk, row, ety, k);
        }

        // Try to get callee param types
        var param_tys: []const types.TypeId = &.{};
        var fixed: usize = 0;
        var is_variadic = false;
        if (callee.fty) |fty| {
            if (self.context.type_store.index.kinds.items[fty.toRaw()] == .Function) {
                const fr2 = self.context.type_store.get(.Function, fty);
                param_tys = self.context.type_store.type_pool.slice(fr2.params);
                is_variadic = fr2.is_variadic;
                fixed = param_tys.len;
                if (is_variadic and fixed > 0) fixed -= 1; // last param is the vararg pack type
            }
        }

        // Lower args with expected param types when available
        const arg_ids = a.exprs.expr_pool.slice(row.args);
        var vals = try self.gpa.alloc(tir.ValueId, arg_ids.len);
        defer self.gpa.free(vals);
        var i: usize = 0;
        while (i < arg_ids.len) : (i += 1) {
            const want: ?types.TypeId = if (i < fixed) param_tys[i] else null;
            vals[i] = try self.lowerExpr(a, env, f, blk, arg_ids[i], want, .rvalue);
        }

        // Final safety: if we know param types, coerce the fixed ones
        if (param_tys.len > 0) {
            i = 0;
            while (i < vals.len and i < fixed) : (i += 1) {
                const want = param_tys[i];
                const got = self.getExprType(arg_ids[i]) orelse want;
                if (want.toRaw() != got.toRaw()) {
                    vals[i] = self.emitCoerce(blk, vals[i], got, want);
                }
            }
        }

        if (is_variadic and vals.len > fixed) {
            var j2: usize = fixed;
            while (j2 < vals.len) : (j2 += 1) {
                const got = self.getExprType(arg_ids[j2]) orelse self.context.type_store.tAny();
                if (self.isAny(got)) {
                    const k = a.exprs.index.kinds.items[arg_ids[j2].toRaw()];
                    const want: types.TypeId = switch (k) {
                        .Literal => blk: {
                            const lit = a.exprs.get(.Literal, arg_ids[j2]);
                            break :blk switch (lit.kind) {
                                .int, .char => self.context.type_store.tI64(),
                                .float, .imaginary => self.context.type_store.tF64(),
                                .bool => self.context.type_store.tBool(),
                                .string => self.context.type_store.tString(),
                            };
                        },
                        else => self.context.type_store.tUsize(),
                    };
                    vals[j2] = try self.lowerExpr(a, env, f, blk, arg_ids[j2], want, .rvalue);
                }
            }
        }

        // Choose a concrete return type: expected → stamped → callee.fty.ret → void
        const ret_ty = blk: {
            if (expected) |e| if (!self.isVoid(e)) break :blk e;
            if (self.getExprType(id)) |t| if (!self.isVoid(t) and !self.isAny(t)) break :blk t;
            if (callee.fty) |fty| {
                if (self.context.type_store.index.kinds.items[fty.toRaw()] == .Function) {
                    const fr2 = self.context.type_store.get(.Function, fty);
                    const rt = fr2.result; // adjust if your field is named differently
                    if (!self.isVoid(rt) and !self.isAny(rt)) break :blk rt;
                }
            }
            break :blk self.context.type_store.tVoid();
        };

        return blk.builder.call(blk, ret_ty, callee.name, vals);
    }

    fn lowerTypeExprOpaque(self: *LowerTir, blk: *Builder.BlockFrame, id: ast.ExprId, expected_ty: ?types.TypeId) tir.ValueId {
        const ty0 = self.getExprType(id) orelse self.context.type_store.tAny();
        const v = self.safeUndef(blk, ty0);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
    }

    fn lowerLiteral(
        self: *LowerTir,
        a: *const ast.Ast,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const lit = a.exprs.get(.Literal, id);
        // If the checker didn’t stamp a type, use the caller’s expected type.
        const ty0 = self.getExprType(id) orelse (expected_ty orelse return error.LoweringBug);
        const v = switch (lit.kind) {
            .int => blk.builder.tirValue(.ConstInt, blk, ty0, .{
                .value = try std.fmt.parseInt(u64, a.exprs.strs.get(lit.value.unwrap()), 10),
            }),
            .imaginary => blk: {
                // ty0 must be Complex(elem). Build from (re=0, im=value)
                const tk = self.context.type_store.getKind(ty0);
                if (tk != .Complex) break :blk blk.builder.tirValue(.ConstUndef, blk, ty0, .{});
                const crow = self.context.type_store.get(.Complex, ty0);
                const elem = crow.elem;
                const s = a.exprs.strs.get(lit.value.unwrap());
                // Parse as f64 and cast to elem as needed
                const parsed = try std.fmt.parseFloat(f64, s);
                const re0 = blk.builder.tirValue(.ConstFloat, blk, elem, .{ .value = 0.0 });
                const imv = blk.builder.tirValue(.ConstFloat, blk, elem, .{ .value = parsed });
                const cv = blk.builder.tirValue(.ComplexMake, blk, ty0, .{ .re = re0, .im = imv });
                break :blk cv;
            },
            .float => blk.builder.tirValue(.ConstFloat, blk, ty0, .{ .value = try std.fmt.parseFloat(f64, a.exprs.strs.get(lit.value.unwrap())) }),
            .bool => blk.builder.tirValue(.ConstBool, blk, ty0, .{ .value = lit.bool_value }),
            .string => blk.builder.tirValue(.ConstString, blk, ty0, .{ .text = lit.value.unwrap() }),
            .char => blk.builder.tirValue(.ConstInt, blk, ty0, .{ .value = @as(u64, lit.char_value) }),
        };
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
    }

    fn lowerUnary(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        mode: LowerMode,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.Unary, id);
        if (row.op == .address_of or mode == .lvalue_addr) {
            // compute address of the operand
            const ety = self.getExprType(row.expr) orelse return error.LoweringBug;
            // When user asked address-of explicitly, produce pointer type
            if (row.op == .address_of) {
                const v = try self.lowerExpr(a, env, f, blk, row.expr, ety, .rvalue);
                return blk.builder.tirValue(.AddressOf, blk, self.context.type_store.mkPtr(ety, false), .{ .value = v });
            }
            // lvalue address request falls through to .Ident/.FieldAccess/.IndexAccess implementations
        }
        // rvalue unary
        var ty0 = self.getExprType(id) orelse self.getExprType(row.expr) orelse self.context.type_store.tI64();

        // If the stamp is void/any or non-numeric for +/-, fall back to operand numeric (or i64)
        const is_num = self.isNumeric(ty0);
        if ((row.op == .pos or row.op == .neg) and (!is_num or self.isAny(ty0) or self.isVoid(ty0))) {
            if (self.getExprType(row.expr)) |et| {
                if (self.isNumeric(et)) {
                    ty0 = et;
                }
            }
            if (self.isAny(ty0) or self.isVoid(ty0)) ty0 = self.context.type_store.tI64();
        }

        var v0 = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);

        const v = switch (row.op) {
            .pos => v0,
            .neg => blk: {
                // Use a zero that matches ty0’s kind; if Complex, build complex(0,0)
                const zero = zblk: {
                    const k = self.context.type_store.index.kinds.items[ty0.toRaw()];
                    if (k == .Complex) {
                        const crow = self.context.type_store.get(.Complex, ty0);
                        const re0 = blk.builder.tirValue(.ConstFloat, blk, crow.elem, .{ .value = 0.0 });
                        const im0 = blk.builder.tirValue(.ConstFloat, blk, crow.elem, .{ .value = 0.0 });
                        break :zblk blk.builder.tirValue(.ComplexMake, blk, ty0, .{ .re = re0, .im = im0 });
                    }
                    if (self.isFloat(ty0)) break :zblk blk.builder.tirValue(.ConstFloat, blk, ty0, .{ .value = 0.0 });
                    // break :zblk blk.builder.tirValue(.ConstInt, blk, ty0, .{ .value = 0 });
                    break :zblk blk.builder.tirValue(.ConstInt, blk, ty0, .{ .value = 0 });
                };
                break :blk blk.builder.bin(blk, .Sub, ty0, zero, v0);
            },
            .logical_not => blk: {
                // Ensure operand is bool for logical ops
                const bty = self.context.type_store.tBool();
                const got = self.getExprType(row.expr) orelse bty;
                v0 = self.emitCoerce(blk, v0, got, bty);
                break :blk blk.builder.un1(blk, .LogicalNot, bty, v0);
            },
            .address_of => unreachable,
        };
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
    }

    fn lowerRange(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId, expected_ty: ?types.TypeId) anyerror!tir.ValueId {
        const row = a.exprs.get(.Range, id);
        const ty0 = self.getExprType(id) orelse return error.LoweringBug;
        const usize_ty = self.context.type_store.tUsize();
        const start_v = if (!row.start.isNone()) try self.lowerExpr(a, env, f, blk, row.start.unwrap(), usize_ty, .rvalue) else blk.builder.tirValue(.ConstUndef, blk, usize_ty, .{});
        const end_v = if (!row.end.isNone()) try self.lowerExpr(a, env, f, blk, row.end.unwrap(), usize_ty, .rvalue) else blk.builder.tirValue(.ConstUndef, blk, usize_ty, .{});
        const incl = blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), .{ .value = row.inclusive_right });
        // Materialize range as TIR RangeMake (typed as []usize)
        const v = blk.builder.rangeMake(blk, ty0, start_v, end_v, incl);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
    }

    fn lowerDeref(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        mode: LowerMode,
    ) !tir.ValueId {
        if (mode == .lvalue_addr) {
            // address of deref target is the pointer value itself
            const row = a.exprs.get(.Deref, id);
            return try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        }
        const ty0 = self.getExprType(id) orelse return error.LoweringBug;
        const row = a.exprs.get(.Deref, id);
        const ptr = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const v = blk.builder.tirValue(.Load, blk, ty0, .{ .ptr = ptr, .@"align" = 0 });
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
    }

    fn lowerArrayLit(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.ArrayLit, id);
        const ty0 = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tAny());
        const ids = a.exprs.expr_pool.slice(row.elems);
        var vals = try self.gpa.alloc(tir.ValueId, ids.len);
        defer self.gpa.free(vals);
        var i: usize = 0;
        var expect_elem = self.context.type_store.tAny();
        const vk = self.context.type_store.index.kinds.items[ty0.toRaw()];
        if (vk == .Array) expect_elem = self.context.type_store.get(.Array, ty0).elem;
        while (i < ids.len) : (i += 1)
            vals[i] = try self.lowerExpr(a, env, f, blk, ids[i], expect_elem, .rvalue);
        const v = blk.builder.arrayMake(blk, ty0, vals);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
    }

    fn lowerTupleLit(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.TupleLit, id);
        const ty0 = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tAny());
        const ids = a.exprs.expr_pool.slice(row.elems);
        var vals = try self.gpa.alloc(tir.ValueId, ids.len);
        defer self.gpa.free(vals);
        var i: usize = 0;
        while (i < ids.len) : (i += 1) {
            // coerce element to tuple element type if known
            var expect_elem = self.context.type_store.tAny();
            const vk = self.context.type_store.index.kinds.items[ty0.toRaw()];
            if (vk == .Tuple) {
                const trow = self.context.type_store.get(.Tuple, ty0);
                const elems = self.context.type_store.type_pool.slice(trow.elems);
                if (i < elems.len) expect_elem = elems[i];
            }
            vals[i] = try self.lowerExpr(a, env, f, blk, ids[i], expect_elem, .rvalue);
        }
        // Lower tuple literals using struct construction with ordinal fields
        var fields = try self.gpa.alloc(tir.Rows.StructFieldInit, vals.len);
        defer self.gpa.free(fields);
        var j: usize = 0;
        while (j < vals.len) : (j += 1) {
            fields[j] = .{ .index = @intCast(j), .name = .none(), .value = vals[j] };
        }
        const v = blk.builder.structMake(blk, ty0, fields);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
    }

    fn lowerStructLit(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.StructLit, id);
        const ty0 = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tAny());

        const fids = a.exprs.sfv_pool.slice(row.fields);
        var fields = try self.gpa.alloc(tir.Rows.StructFieldInit, fids.len);
        defer self.gpa.free(fields);

        const ty0_kind = self.context.type_store.getKind(ty0);
        var type_fields: []const types.FieldId = &.{};
        if (ty0_kind == .Struct) {
            type_fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, ty0).fields);
        } else if (ty0_kind == .Union) {
            type_fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Union, ty0).fields);
        }

        var i: usize = 0;
        while (i < fids.len) : (i += 1) {
            const sfv = a.exprs.StructFieldValue.get(fids[i]);

            var field_idx: ?usize = null;
            var want: types.TypeId = self.context.type_store.tAny();

            if (!sfv.name.isNone()) {
                const name_id = sfv.name.unwrap();
                for (type_fields, 0..) |fid, j| {
                    const fdef = self.context.type_store.Field.get(fid);
                    if (fdef.name.eq(name_id)) {
                        field_idx = j;
                        want = fdef.ty;
                        break;
                    }
                }
            } else if (i < type_fields.len) {
                // Positional field
                field_idx = i;
                want = self.context.type_store.Field.get(type_fields[i]).ty;
            }

            const v_val = try self.lowerExpr(a, env, f, blk, sfv.value, want, .rvalue);
            const final_idx = field_idx orelse i;
            fields[i] = .{ .index = @intCast(final_idx), .name = sfv.name, .value = v_val };
        }

        const v = if (ty0_kind == .Union) blk: {
            std.debug.assert(fields.len == 1);
            const field = fields[0];
            break :blk blk.builder.tirValue(.UnionMake, blk, ty0, .{
                .field_index = field.index,
                .value = field.value,
            });
        } else blk.builder.structMake(blk, ty0, fields);

        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
    }

    fn lowerMapLit(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.MapLit, id);
        const ty0 = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tAny());
        const kv_ids = a.exprs.kv_pool.slice(row.entries);
        var vals = try self.gpa.alloc(tir.ValueId, kv_ids.len * 2);
        defer self.gpa.free(vals);
        var j: usize = 0;
        for (kv_ids) |kid| {
            const kv = a.exprs.KeyValue.get(kid);
            // best-effort: use expected key/value if map type is known
            var key_want = self.context.type_store.tAny();
            var val_want = self.context.type_store.tAny();
            const mk = self.context.type_store.index.kinds.items[ty0.toRaw()];
            if (mk == .Map) {
                const mr = self.context.type_store.get(.Map, ty0);
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
    }

    fn lowerIndexAccess(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        mode: LowerMode,
    ) anyerror!tir.ValueId {
        if (mode == .lvalue_addr) {
            const row = a.exprs.get(.IndexAccess, id);
            const base_ptr = try self.lowerExpr(a, env, f, blk, row.collection, null, .lvalue_addr);
            // Prefer a usize constant for literal indices to avoid casts in TIR
            const idx_v = blk: {
                const ik = a.exprs.index.kinds.items[row.index.toRaw()];
                if (ik == .Literal) {
                    const lit = a.exprs.get(.Literal, row.index);
                    if (lit.kind == .int) {
                        const s = a.exprs.strs.get(lit.value.unwrap());
                        const uv = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), .{
                            .value = try std.fmt.parseInt(u64, s, 10),
                        });
                        break :blk uv;
                    }
                }
                break :blk try self.lowerExpr(a, env, f, blk, row.index, self.context.type_store.tUsize(), .rvalue);
            };
            const idx = blk.builder.gepValue(idx_v);
            const rty = self.context.type_store.mkPtr(self.getExprType(id) orelse return error.LoweringBug, false);
            return blk.builder.gep(blk, rty, base_ptr, &.{idx});
        } else {
            const row = a.exprs.get(.IndexAccess, id);
            const ty0 = self.getExprType(id) orelse return error.LoweringBug;
            const base = try self.lowerExpr(a, env, f, blk, row.collection, null, .rvalue);
            // If result is a slice, the index expression should be a range ([]usize);
            // otherwise, index is a single usize.
            const idx = blk: {
                const rk = self.context.type_store.index.kinds.items[ty0.toRaw()];
                if (rk == .Slice) {
                    const want = self.context.type_store.mkSlice(self.context.type_store.tUsize());
                    break :blk try self.lowerExpr(a, env, f, blk, row.index, want, .rvalue);
                } else {
                    // Prefer a usize constant for literal indices to avoid casts in TIR
                    const ik = a.exprs.index.kinds.items[row.index.toRaw()];
                    if (ik == .Literal) {
                        const lit = a.exprs.get(.Literal, row.index);
                        if (lit.kind == .int) {
                            const s = a.exprs.strs.get(lit.value.unwrap());
                            const uv = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), .{
                                .value = try std.fmt.parseInt(u64, s, 10),
                            });
                            break :blk uv;
                        }
                    }
                    break :blk try self.lowerExpr(a, env, f, blk, row.index, self.context.type_store.tUsize(), .rvalue);
                }
            };
            const v = blk.builder.indexOp(blk, ty0, base, idx);
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
            return v;
        }
    }

    fn lowerImportedModuleMember(self: *LowerTir, a: *const ast.Ast, blk: *Builder.BlockFrame, parent_id: ast.ExprId, field_name: StrId, expected_ty: ?types.TypeId) !?tir.ValueId {
        const idr = a.exprs.get(.Ident, parent_id);
        if (self.findTopLevelImportByName(a, idr.name)) |imp_decl| {
            const ty0 = self.getExprType(parent_id) orelse (expected_ty orelse self.context.type_store.tAny());
            if (self.materializeImportedConst(&self.context.resolver, a, imp_decl, field_name, ty0, blk, self.pipeline)) |vv| {
                if (expected_ty) |want| return self.emitCoerce(blk, vv, ty0, want);
                return vv;
            }
            const v = blk.builder.tirValue(.ConstUndef, blk, ty0, .{});
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
            return v;
        }
        return null;
    }

    fn lowerEnumMember(
        self: *LowerTir,
        _: *const ast.Ast,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        parent_expr: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) !?tir.ValueId {
        const parent_ty = self.getExprType(parent_expr) orelse return null;
        const parent_kind = self.context.type_store.getKind(parent_ty);
        if (parent_kind != .Enum and parent_kind != .TypeType) return null;
        if (parent_kind == .TypeType) {
            const tr = self.context.type_store.get(.TypeType, parent_ty);
            const of_kind = self.context.type_store.getKind(tr.of);
            if (of_kind != .Enum) return null;
        }
        const ty0 = self.getExprType(id) orelse (expected_ty orelse self.context.type_store.tAny());
        const idx = self.type_info.getFieldIndex(id) orelse return error.LoweringBug; // enum members should be indexed by the checker
        var ev = blk.builder.tirValue(.ConstInt, blk, ty0, .{ .value = idx });
        if (expected_ty) |want| ev = self.emitCoerce(blk, ev, ty0, want);
        return ev;
    }

    fn lowerVariantTagLiteral(
        self: *LowerTir,
        _: *const ast.Ast,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        parent_expr: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) !?tir.ValueId {
        const ty = self.getExprType(parent_expr) orelse return null;
        const parent_kind = self.context.type_store.getKind(ty);
        if (parent_kind != .TypeType) return null;

        const tr = self.context.type_store.get(.TypeType, ty);
        const of_kind = self.context.type_store.getKind(tr.of);
        if (of_kind != .Variant and of_kind != .Error) return null;

        const is_variant = of_kind == .Variant;
        const fields = if (is_variant)
            self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, tr.of).variants)
        else
            self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, tr.of).variants);
        const tag_idx = self.type_info.getFieldIndex(id);
        const payload_ty = if (tag_idx) |ti|
            self.context.type_store.Field.get(fields[ti]).ty
        else
            return null;
        const payload_kind = self.context.type_store.getKind(payload_ty);
        if (payload_kind != .Void) return null; // only literal tags for no-payload cases
        const ty0 = self.getExprType(id) orelse (expected_ty orelse self.context.type_store.tAny());
        if (self.context.type_store.getKind(payload_ty) != .Void) return null;
        const tag_val = blk.builder.extractField(blk, self.context.type_store.tI32(), self.safeUndef(blk, ty), 0);
        if (expected_ty) |want| return self.emitCoerce(blk, tag_val, ty0, want);
        return tag_val;
    }

    fn lowerFieldAccess(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        mode: LowerMode,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.FieldAccess, id);

        // 1) imported module member (rvalue only)
        if (mode == .rvalue and a.exprs.index.kinds.items[row.parent.toRaw()] == .Ident) {
            if (try self.lowerImportedModuleMember(a, blk, row.parent, row.field, expected_ty)) |v| {
                return v;
            }
        }

        const idx_maybe = self.type_info.getFieldIndex(id);

        // 2) EnumName.Member => constant (rvalue)
        if (mode == .rvalue) {
            if (try self.lowerEnumMember(a, blk, id, row.parent, expected_ty)) |v| {
                return v;
            }
        }

        // 3) address path (needs concrete field index)
        if (mode == .lvalue_addr) {
            const parent_ptr = try self.lowerExpr(a, env, f, blk, row.parent, null, .lvalue_addr);
            const elem_ty = self.getExprType(id) orelse return error.LoweringBug;
            const idx = idx_maybe orelse return error.LoweringBug;
            const rptr_ty = self.context.type_store.mkPtr(elem_ty, false);
            return blk.builder.gep(blk, rptr_ty, parent_ptr, &.{blk.builder.gepConst(@intCast(idx))});
        }

        // 4) rvalue extraction
        const ty0 = self.getExprType(id) orelse (expected_ty orelse self.context.type_store.tAny());
        var base = try self.lowerExpr(a, env, f, blk, row.parent, null, .rvalue);

        const parent_ty_opt = self.getExprType(row.parent);
        const is_tuple = if (parent_ty_opt) |pt|
            self.context.type_store.index.kinds.items[pt.toRaw()] == .Tuple
        else
            false;

        var v: tir.ValueId = undefined;
        if (idx_maybe) |resolved_idx| {
            const parent_kind = self.context.type_store.getKind(parent_ty_opt orelse self.context.type_store.tAny());
            v = if (parent_kind == .Variant) blk: {
                // accessing the payload field out of a runtime variant value
                const variants = self.context.type_store.get(.Variant, parent_ty_opt.?).variants;
                const fields = self.context.type_store.field_pool.slice(variants);
                var union_fields_args = try self.gpa.alloc(types.TypeStore.StructFieldArg, variants.len);
                defer self.gpa.free(union_fields_args);
                for (fields, 0..) |fld_id, i| {
                    const fld = self.context.type_store.Field.get(fld_id);
                    union_fields_args[i] = .{ .name = fld.name, .ty = fld.ty };
                }
                const union_ty = self.context.type_store.mkUnion(union_fields_args);
                base = blk.builder.extractField(blk, union_ty, base, 1);
                break :blk blk.builder.tirValue(.UnionField, blk, ty0, .{ .base = base, .field_index = resolved_idx });
            } else if (parent_kind == .TypeType) blk: {
                // VariantType.C  => construct the value (void payload must NOT use UnionMake)
                const of_ty = self.context.type_store.get(.TypeType, parent_ty_opt.?).of;
                const of_kind = self.context.type_store.getKind(of_ty);
                std.debug.assert(of_kind == .Variant or of_kind == .Error);

                const fields = if (of_kind == .Variant)
                    self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, of_ty).variants)
                else
                    self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, of_ty).variants);

                const field_id = fields[resolved_idx];
                const field = self.context.type_store.Field.get(field_id);
                const payload_ty = field.ty;

                const tag_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), .{ .value = resolved_idx });

                var union_fields_args = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                defer self.gpa.free(union_fields_args);
                for (fields, 0..) |fld_id2, j2| {
                    const fld2 = self.context.type_store.Field.get(fld_id2);
                    union_fields_args[j2] = .{ .name = fld2.name, .ty = fld2.ty };
                }
                const union_ty = self.context.type_store.mkUnion(union_fields_args);

                const union_val =
                    if (self.context.type_store.getKind(payload_ty) == .Void)
                        // ← fix: void payload => just undef union, no UnionMake
                        blk.builder.tirValue(.ConstUndef, blk, union_ty, .{})
                    else
                        blk.builder.tirValue(.UnionMake, blk, union_ty, .{
                            .field_index = resolved_idx,
                            .value = self.undef(blk, payload_ty),
                        });

                const v_res = blk.builder.structMake(blk, of_ty, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = tag_val },
                    .{ .index = 1, .name = .none(), .value = union_val },
                });

                if (expected_ty) |want| break :blk self.emitCoerce(blk, v_res, of_ty, want);
                break :blk v_res;
            } else if (is_tuple)
                blk.builder.extractElem(blk, ty0, base, resolved_idx)
            else if (parent_kind == .Union)
                blk.builder.tirValue(.UnionField, blk, ty0, .{ .base = base, .field_index = resolved_idx })
            else
                blk.builder.extractField(blk, ty0, base, resolved_idx);
        } else {
            if (is_tuple) return error.LoweringBug;
            v = blk.builder.extractFieldNamed(blk, ty0, base, row.field);
        }

        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
    }

    fn lowerIdent(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        mode: LowerMode,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.Ident, id);
        const name = row.name;

        // Pre-lift a couple things we end up consulting a few times.
        const expr_ty_opt = self.getExprType(id);
        const did_opt = self.findTopLevelDeclByName(a, name);

        // Helper: when an expected type is a pointer, use its element;
        // otherwise fall back to the expression type (or Any).
        const want_elem = blk: {
            if (expected_ty) |want| {
                if (self.context.type_store.getKind(want) == .Ptr)
                    break :blk self.context.type_store.get(.Ptr, want).elem;
            }
            break :blk (expr_ty_opt orelse self.context.type_store.tAny());
        };

        if (mode == .lvalue_addr) {
            // 1) If it's already a slot, we're done.
            if (env.lookup(name)) |bnd| if (bnd.is_slot) return bnd.value;

            // 2) If it's a top-level decl, bind its address as a slot and return.
            if (did_opt) |did| {
                const d = a.exprs.Decl.get(did);
                const gty = self.getDeclType(did) orelse return error.LoweringBug;
                const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
                const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, .{ .name = name });
                try env.bind(self.gpa, a, name, .{ .value = addr, .is_slot = true });
                return addr;
            }

            // 3) Otherwise it must be a local value binding that needs a slot.
            if (env.lookup(name)) |bnd| {
                const slot_ty = self.context.type_store.mkPtr(want_elem, false);
                const slot = f.builder.tirValue(.Alloca, blk, slot_ty, .{ .count = tir.OptValueId.none(), .@"align" = 0 });

                const src_ty = (expr_ty_opt orelse want_elem);
                const to_store = self.emitCoerce(blk, bnd.value, src_ty, want_elem);
                _ = f.builder.tirValue(.Store, blk, want_elem, .{ .ptr = slot, .value = to_store, .@"align" = 0 });

                try env.bind(self.gpa, a, name, .{ .value = slot, .is_slot = true });
                return slot;
            }

            // 4) Nowhere to get it from.
            return error.LoweringBug;
        }

        // ---- rvalue path -----------------------------------------------------

        // Acquire or synthesize a binding once, then decide how to produce a value.
        const bnd = env.lookup(name) orelse blk: {
            if (did_opt) |did| {
                const d = a.exprs.Decl.get(did);
                const gty = self.getDeclType(did) orelse return error.LoweringBug;
                const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
                const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, .{ .name = name });
                try env.bind(self.gpa, a, name, .{ .value = addr, .is_slot = true });
                break :blk env.lookup(name).?;
            }

            // Not a value binding or top-level decl (likely a type name etc.).
            // Bind a safe placeholder so downstream code can keep going.
            const ty0 = expr_ty_opt orelse self.context.type_store.tAny();
            const placeholder = self.safeUndef(blk, ty0);
            try env.bind(self.gpa, a, name, .{ .value = placeholder, .is_slot = false });
            break :blk env.lookup(name).?;
        };

        if (bnd.is_slot) {
            const load_ty = expr_ty_opt orelse (expected_ty orelse self.context.type_store.tAny());
            var loaded = blk.builder.tirValue(.Load, blk, load_ty, .{ .ptr = bnd.value, .@"align" = 0 });
            if (expected_ty) |want| loaded = self.emitCoerce(blk, loaded, load_ty, want);
            return loaded;
        }

        // Non-slot: coerce if a target type was requested.
        const got_ty = expr_ty_opt orelse (expected_ty orelse self.context.type_store.tAny());
        return if (expected_ty) |want| self.emitCoerce(blk, bnd.value, got_ty, want) else bnd.value;
    }

    fn lowerBinary(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.Binary, id);

        // --- fast-path: variant/error equality against a tag literal (e.g. err == MyErr.NotFound) ---
        if (row.op == .eq or row.op == .neq) {
            const l_ty = self.getExprType(row.left);
            const r_ty = self.getExprType(row.right);

            // left is value, right is tag literal
            if (l_ty != null and self.isVariantLike(l_ty.?)) {
                if (self.tagConstFromTypePath(a, row.right)) |info| {
                    if (info.of_ty.toRaw() == l_ty.?.toRaw()) {
                        const lhs_val = try self.lowerExpr(a, env, f, blk, row.left, l_ty, .rvalue);
                        const lhs_tag = blk.builder.extractField(blk, self.context.type_store.tI32(), lhs_val, 0);
                        const want_tag = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), .{ .value = info.tag_idx });
                        const cmp = if (row.op == .eq)
                            blk.builder.binBool(blk, .CmpEq, lhs_tag, want_tag)
                        else
                            blk.builder.binBool(blk, .CmpNe, lhs_tag, want_tag);
                        return cmp;
                    }
                }
            }
            // right is value, left is tag literal
            if (r_ty != null and self.isVariantLike(r_ty.?)) {
                if (self.tagConstFromTypePath(a, row.left)) |info| {
                    if (info.of_ty.toRaw() == r_ty.?.toRaw()) {
                        const rhs_val = try self.lowerExpr(a, env, f, blk, row.right, r_ty, .rvalue);
                        const rhs_tag = blk.builder.extractField(blk, self.context.type_store.tI32(), rhs_val, 0);
                        const want_tag = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), .{ .value = info.tag_idx });
                        const cmp = if (row.op == .eq)
                            blk.builder.binBool(blk, .CmpEq, rhs_tag, want_tag)
                        else
                            blk.builder.binBool(blk, .CmpNe, rhs_tag, want_tag);
                        return cmp;
                    }
                }
            }
        }
        // --- end fast-path ---

        const stamped_result = self.getExprType(id);
        var lhs_expect: ?types.TypeId = null;
        var rhs_expect: ?types.TypeId = null;
        var op_ty: ?types.TypeId = stamped_result;

        switch (row.op) {
            .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor => {
                if (op_ty) |t| {
                    if (self.context.type_store.index.kinds.items[t.toRaw()] == .Complex) {
                        lhs_expect = t;
                        rhs_expect = t;
                    } else {
                        const want = self.commonNumeric(self.getExprType(row.left), self.getExprType(row.right)) orelse (expected_ty orelse self.context.type_store.tI64());
                        lhs_expect = want;
                        rhs_expect = want;
                        if (op_ty == null or self.isVoid(op_ty.?) or self.isAny(op_ty.?)) op_ty = want;
                    }
                } else {
                    const want = self.commonNumeric(self.getExprType(row.left), self.getExprType(row.right)) orelse (expected_ty orelse self.context.type_store.tI64());
                    lhs_expect = want;
                    rhs_expect = want;
                    if (op_ty == null or self.isVoid(op_ty.?) or self.isAny(op_ty.?)) op_ty = want;
                }
            },
            .eq, .neq, .lt, .lte, .gt, .gte => {
                const want = self.commonNumeric(self.getExprType(row.left), self.getExprType(row.right)) orelse (self.getExprType(row.left) orelse self.getExprType(row.right));
                lhs_expect = want;
                rhs_expect = want;
                op_ty = self.context.type_store.tBool();
            },
            .logical_and, .logical_or => {
                const bty = self.context.type_store.tBool();
                lhs_expect = bty;
                rhs_expect = bty;
                op_ty = self.context.type_store.tBool();
            },
            .@"orelse" => {
                lhs_expect = self.getExprType(row.left);
                rhs_expect = expected_ty;
                if (op_ty == null or self.isVoid(op_ty.?)) op_ty = (expected_ty orelse self.context.type_store.tAny());
            },
        }

        const l = try self.lowerExpr(a, env, f, blk, row.left, lhs_expect, .rvalue);
        const r = try self.lowerExpr(a, env, f, blk, row.right, rhs_expect, .rvalue);

        const ty0 = blk: {
            if (op_ty) |t| break :blk t;
            const want = self.commonNumeric(self.getExprType(row.left), self.getExprType(row.right)) orelse self.context.type_store.tI64();
            break :blk want;
        };

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
                var then_blk = try f.builder.beginBlock(f);
                var else_blk = try f.builder.beginBlock(f);
                var join_blk = try f.builder.beginBlock(f);
                const s_is_some = f.builder.intern("builtin.opt.is_some");
                const cond_v = blk.builder.call(blk, self.context.type_store.tBool(), s_is_some, &.{l});
                const br_cond = self.forceLocalCond(blk, cond_v);
                try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{});
                const res_ty = expected_ty orelse ty0;
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
                const s_unwrap = f.builder.intern("builtin.opt.unwrap");
                var unwrapped = blk.builder.call(&then_blk, res_ty, s_unwrap, &.{l});
                if (expected_ty) |want| {
                    const got = self.getExprType(row.left) orelse res_ty;
                    unwrapped = self.emitCoerce(&then_blk, unwrapped, got, want);
                }
                try f.builder.br(&then_blk, join_blk.id, &.{unwrapped});
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
            if (!self.isVoid(ty0))
                return self.emitCoerce(blk, v, ty0, want);
        }
        return v;
    }

    fn lowerCatch(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.Catch, id);
        const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
        const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

        const lhs = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const es_ty = self.getExprType(row.expr).?;
        const es = self.context.type_store.get(.ErrorSet, es_ty);

        // An ErrorSet is a tagged union { tag, payload }, where tag=0 is OK, non-zero is Err.
        const tag = blk.builder.extractField(blk, self.context.type_store.tI32(), lhs, 0);
        const zero = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), .{ .value = 0 });
        const is_ok = blk.builder.binBool(blk, .CmpEq, tag, zero);

        var then_blk = try f.builder.beginBlock(f); // ok path
        var else_blk = try f.builder.beginBlock(f); // err path

        const payload_union_ty = self.context.type_store.mkUnion(&.{
            .{ .name = f.builder.intern("Ok"), .ty = es.value_ty },
            .{ .name = f.builder.intern("Err"), .ty = es.error_ty },
        });

        if (produce_value) {
            var join_blk = try f.builder.beginBlock(f);
            const res_ty = out_ty_guess;
            const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

            const br_cond = self.forceLocalCond(blk, is_ok);
            try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{});
            {
                // Close the current block after emitting the branch (mirrors lowerIf).
                const old = blk.*;
                try f.builder.endBlock(f, old);
            }

            // then (ok) branch: unwrap value
            const payload_union_ok = then_blk.builder.extractField(&then_blk, payload_union_ty, lhs, 1);
            const ok_val = then_blk.builder.tirValue(.UnionField, &then_blk, es.value_ty, .{
                .base = payload_union_ok,
                .field_index = 0,
            });
            try f.builder.br(&then_blk, join_blk.id, &.{ok_val});

            // else (err) branch: unwrap error and run handler
            try env.pushScope(self.gpa); // Push scope for handler
            const payload_union_err = else_blk.builder.extractField(&else_blk, payload_union_ty, lhs, 1);
            const err_val = else_blk.builder.tirValue(.UnionField, &else_blk, es.error_ty, .{
                .base = payload_union_err,
                .field_index = 1,
            });
            if (!row.binding_name.isNone()) {
                const name = row.binding_name.unwrap();
                try env.bind(self.gpa, a, name, .{ .value = err_val, .is_slot = false });
            }
            try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
            _ = env.popScope(); // Pop scope after handler
            if (else_blk.term.isNone()) {
                const hv = try self.lowerBlockExprValue(a, env, f, &else_blk, row.handler, res_ty);
                try f.builder.br(&else_blk, join_blk.id, &.{hv});
            }

            try f.builder.endBlock(f, then_blk);
            try f.builder.endBlock(f, else_blk);
            blk.* = join_blk;
            return res_param;
        } else {
            // No value: conditionally run handler, then continue
            const exit_blk = try f.builder.beginBlock(f);

            const br_cond = self.forceLocalCond(blk, is_ok);
            try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{});
            {
                // Close the current block after emitting the branch.
                const old = blk.*;
                try f.builder.endBlock(f, old);
            }

            // then: nothing to do, jump to exit
            if (then_blk.term.isNone()) try f.builder.br(&then_blk, exit_blk.id, &.{});
            try f.builder.endBlock(f, then_blk);

            // else: execute handler as stmt
            try env.pushScope(self.gpa); // Push scope for handler
            const payload_union_err = else_blk.builder.extractField(&else_blk, payload_union_ty, lhs, 1);
            const err_val = else_blk.builder.tirValue(.UnionField, &else_blk, es.error_ty, .{
                .base = payload_union_err,
                .field_index = 1,
            });
            if (!row.binding_name.isNone()) {
                const name = row.binding_name.unwrap();
                try env.bind(self.gpa, a, name, .{ .value = err_val, .is_slot = false });
            }
            try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
            _ = env.popScope(); // Pop scope after handler
            if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{});
            try f.builder.endBlock(f, else_blk);

            blk.* = exit_blk;
            return self.safeUndef(blk, self.context.type_store.tAny());
        }
    }

    fn lowerIf(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.If, id);
        var then_blk = try f.builder.beginBlock(f);
        var else_blk = try f.builder.beginBlock(f);

        const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
        const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

        const cond_v = try self.lowerExpr(a, env, f, blk, row.cond, self.context.type_store.tBool(), .rvalue);

        if (produce_value) {
            var join_blk = try f.builder.beginBlock(f);
            const res_ty = out_ty_guess;
            const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

            const br_cond = self.forceLocalCond(blk, cond_v);
            try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{});
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

            const br_cond = self.forceLocalCond(blk, cond_v);
            try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{});
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
            return self.safeUndef(blk, self.context.type_store.tAny());
        }
    }

    fn lowerCast(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.Cast, id);
        const ty0 = self.getExprType(id) orelse return error.LoweringBug;
        const v = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const out = switch (row.kind) {
            .normal => blk.builder.tirValue(.CastNormal, blk, ty0, .{ .value = v }),
            .bitcast => blk.builder.tirValue(.CastBit, blk, ty0, .{ .value = v }),
            .saturate => blk.builder.tirValue(.CastSaturate, blk, ty0, .{ .value = v }),
            .wrap => blk.builder.tirValue(.CastWrap, blk, ty0, .{ .value = v }),
            .checked => blk.builder.tirValue(.CastChecked, blk, ty0, .{ .value = v }),
        };
        if (expected_ty) |want| return self.emitCoerce(blk, out, ty0, want);
        return out;
    }

    fn lowerOptionalUnwrap(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.OptionalUnwrap, id);
        const ty0 = self.getExprType(id) orelse return error.LoweringBug;
        const v = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const unwrap = blk.builder.intern("builtin.opt.unwrap");
        const out = blk.builder.call(blk, ty0, unwrap, &.{v});
        if (expected_ty) |want| return self.emitCoerce(blk, out, ty0, want);
        return out;
    }

    fn lowerErrUnwrap(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.ErrUnwrap, id);
        const ty0 = self.getExprType(id) orelse return error.LoweringBug;
        const v = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const unwrap_ok = blk.builder.intern("builtin.err.unwrap_ok");
        const out = blk.builder.call(blk, ty0, unwrap_ok, &.{v});
        if (expected_ty) |want| return self.emitCoerce(blk, out, ty0, want);
        return out;
    }

    fn isAllIntMatch(_: *LowerTir, a: *const ast.Ast, arms_slice: []const ast.MatchArmId, values_buf: []u64) bool {
        if (arms_slice.len != values_buf.len) return false;
        for (arms_slice, 0..) |arm_id, i| {
            const arm = a.exprs.MatchArm.get(arm_id);
            if (!arm.guard.isNone()) return false;
            const pk = a.pats.index.kinds.items[arm.pattern.toRaw()];
            if (pk != .Literal) return false;
            const plit = a.pats.get(.Literal, arm.pattern);
            if (a.exprs.index.kinds.items[plit.expr.toRaw()] != .Literal) return false;
            const lit = a.exprs.get(.Literal, plit.expr);
            if (lit.kind != .int or lit.value.isNone()) return false;
            const s = a.exprs.strs.get(lit.value.unwrap());
            values_buf[i] = std.fmt.parseInt(u64, s, 10) catch return false;
        }
        return true;
    }

    fn lowerMatch(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.Match, id);

        // Scrutinee value
        const scrut = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);

        // Decide if this match-expression needs to produce a value
        const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
        const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

        if (produce_value) {
            // ------- value-producing path -------
            const res_ty = out_ty_guess;

            // Join block (phi-like param carries the match result)
            var join_blk = try f.builder.beginBlock(f);
            const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

            const arms = a.exprs.arm_pool.slice(row.arms);
            if (arms.len == 0) {
                const uv = self.safeUndef(blk, res_ty);
                try f.builder.br(blk, join_blk.id, &.{uv});
                blk.* = join_blk;
                return res_param;
            }

            const values = try self.gpa.alloc(u64, arms.len);
            defer self.gpa.free(values);

            if (self.isAllIntMatch(a, arms, values)) {
                var case_dests = try self.gpa.alloc(Builder.SwitchDest, arms.len);
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
                }, default_blk.id, &.{});

                // Fill bodies
                i = 0;
                while (i < arms.len) : (i += 1) {
                    const arm = a.exprs.MatchArm.get(arms[i]);
                    try self.lowerExprAsStmtList(a, env, f, &bodies[i], arm.body);
                    if (bodies[i].term.isNone()) {
                        var v = try self.lowerBlockExprValue(a, env, f, &bodies[i], arm.body, res_ty);
                        v = self.emitCoerce(&bodies[i], v, self.getExprType(arm.body) orelse res_ty, res_ty);
                        try f.builder.br(&bodies[i], join_blk.id, &.{v});
                    }
                    try f.builder.endBlock(f, bodies[i]);
                }

                const uv = self.safeUndef(&default_blk, res_ty);
                try f.builder.br(&default_blk, join_blk.id, &.{uv});
                try f.builder.endBlock(f, default_blk);

                blk.* = join_blk;
                return res_param;
            }

            // -------- General path: chained tests with optional guards --------
            var cur = blk.*;

            var j: usize = 0;
            while (j < arms.len) : (j += 1) {
                const arm_id = arms[j];
                const arm = a.exprs.MatchArm.get(arm_id);

                var test_blk = try f.builder.beginBlock(f);
                var body_blk = try f.builder.beginBlock(f);
                const next_blk = if (j + 1 < arms.len) try f.builder.beginBlock(f) else join_blk;

                try f.builder.br(&cur, test_blk.id, &.{});
                try f.builder.endBlock(f, cur);

                // pattern test
                const arm_scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                const ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut, arm_scrut_ty);

                // if last arm fails, feed an undef to the join
                const else_args = if (next_blk.id.toRaw() == join_blk.id.toRaw()) blkargs: {
                    const uv = self.safeUndef(&test_blk, res_ty);
                    break :blkargs &.{uv};
                } else &.{};

                if (!arm.guard.isNone()) {
                    var guard_blk = try f.builder.beginBlock(f);
                    const br_cond = self.forceLocalCond(&test_blk, ok);
                    try f.builder.condBr(&test_blk, br_cond, guard_blk.id, &.{}, next_blk.id, else_args);
                    try f.builder.endBlock(f, test_blk);

                    var binding_names = std.ArrayListUnmanaged(ast.StrId){};
                    defer binding_names.deinit(self.gpa);
                    try self.collectPatternBindings(a, arm.pattern, &binding_names);

                    var saved = std.ArrayListUnmanaged(BindingSnapshot){};
                    defer saved.deinit(self.gpa);
                    for (binding_names.items) |name| {
                        try saved.append(self.gpa, .{ .name = name, .prev = env.lookup(name) });
                    }

                    try self.bindPattern(a, env, f, &guard_blk, arm.pattern, scrut, arm_scrut_ty);
                    const guard_val = try self.lowerExpr(a, env, f, &guard_blk, arm.guard.unwrap(), self.context.type_store.tBool(), .rvalue);
                    const guard_cond = self.forceLocalCond(&guard_blk, guard_val);
                    try self.restoreBindings(env, saved.items);
                    try f.builder.condBr(&guard_blk, guard_cond, body_blk.id, &.{}, next_blk.id, else_args);
                    try f.builder.endBlock(f, guard_blk);
                } else {
                    const br_cond = self.forceLocalCond(&test_blk, ok);
                    try f.builder.condBr(&test_blk, br_cond, body_blk.id, &.{}, next_blk.id, else_args);
                    try f.builder.endBlock(f, test_blk);
                }

                // bind + body
                const scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                try self.bindPattern(a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);

                try self.lowerExprAsStmtList(a, env, f, &body_blk, arm.body);
                if (body_blk.term.isNone()) {
                    var v2 = try self.lowerBlockExprValue(a, env, f, &body_blk, arm.body, res_ty);
                    v2 = self.emitCoerce(&body_blk, v2, self.getExprType(arm.body) orelse res_ty, res_ty);
                    try f.builder.br(&body_blk, join_blk.id, &.{v2});
                }

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
                try f.builder.br(blk, exit_blk.id, &.{});
                blk.* = exit_blk;
                return self.safeUndef(blk, self.context.type_store.tAny());
            }

            const values = try self.gpa.alloc(u64, arms.len);
            defer self.gpa.free(values);

            if (self.isAllIntMatch(a, arms, values)) {
                var case_dests = try self.gpa.alloc(Builder.SwitchDest, arms.len);
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
                }, default_blk.id, &.{});

                i = 0;
                while (i < arms.len) : (i += 1) {
                    const arm = a.exprs.MatchArm.get(arms[i]);
                    try self.lowerExprAsStmtList(a, env, f, &bodies[i], arm.body);
                    if (bodies[i].term.isNone()) try f.builder.br(&bodies[i], exit_blk.id, &.{});
                    try f.builder.endBlock(f, bodies[i]);
                }

                try f.builder.br(&default_blk, exit_blk.id, &.{});
                try f.builder.endBlock(f, default_blk);

                blk.* = exit_blk;
                return self.safeUndef(blk, self.context.type_store.tAny());
            }

            // General path (no value): chained tests, fallthrough to exit
            var cur = blk.*;
            var l: usize = 0;
            while (l < arms.len) : (l += 1) {
                const arm_id = arms[l];
                const arm = a.exprs.MatchArm.get(arm_id);

                var test_blk = try f.builder.beginBlock(f);
                var body_blk = try f.builder.beginBlock(f);
                const next_blk = if (l + 1 < arms.len) try f.builder.beginBlock(f) else exit_blk;

                try f.builder.br(&cur, test_blk.id, &.{});
                try f.builder.endBlock(f, cur);

                const arm_scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                const ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut, arm_scrut_ty);

                if (!arm.guard.isNone()) {
                    var guard_blk = try f.builder.beginBlock(f);
                    const br_cond = self.forceLocalCond(&test_blk, ok);
                    try f.builder.condBr(&test_blk, br_cond, guard_blk.id, &.{}, next_blk.id, &.{});
                    try f.builder.endBlock(f, test_blk);

                    var binding_names = std.ArrayListUnmanaged(ast.StrId){};
                    defer binding_names.deinit(self.gpa);
                    try self.collectPatternBindings(a, arm.pattern, &binding_names);

                    var saved = std.ArrayListUnmanaged(BindingSnapshot){};
                    defer saved.deinit(self.gpa);
                    for (binding_names.items) |name| {
                        try saved.append(self.gpa, .{ .name = name, .prev = env.lookup(name) });
                    }

                    try self.bindPattern(a, env, f, &guard_blk, arm.pattern, scrut, arm_scrut_ty);
                    const guard_val = try self.lowerExpr(a, env, f, &guard_blk, arm.guard.unwrap(), self.context.type_store.tBool(), .rvalue);
                    const guard_cond = self.forceLocalCond(&guard_blk, guard_val);
                    try self.restoreBindings(env, saved.items);
                    try f.builder.condBr(&guard_blk, guard_cond, body_blk.id, &.{}, next_blk.id, &.{});
                    try f.builder.endBlock(f, guard_blk);
                } else {
                    const br_cond = self.forceLocalCond(&test_blk, ok);
                    try f.builder.condBr(&test_blk, br_cond, body_blk.id, &.{}, next_blk.id, &.{});
                    try f.builder.endBlock(f, test_blk);
                }

                const scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                try self.bindPattern(a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);

                try self.lowerExprAsStmtList(a, env, f, &body_blk, arm.body);
                if (body_blk.term.isNone()) try f.builder.br(&body_blk, exit_blk.id, &.{});

                try f.builder.endBlock(f, body_blk);
                cur = next_blk;
            }

            blk.* = exit_blk;
            return self.safeUndef(blk, self.context.type_store.tAny());
        }
    }

    fn lowerWhile(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.While, id);
        var header = try f.builder.beginBlock(f);
        var body = try f.builder.beginBlock(f);

        const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
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

            if (row.is_pattern and !row.pattern.isNone() and !row.cond.isNone()) {
                const subj = try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), null, .rvalue);
                const subj_ty = self.getExprType(row.cond.unwrap()) orelse self.context.type_store.tAny();

                const ok = try self.matchPattern(a, env, f, &header, row.pattern.unwrap(), subj, subj_ty);

                const br_cond = self.forceLocalCond(blk, ok);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{});

                // bind `x` etc. for the body
                try self.bindPattern(a, env, f, &body, row.pattern.unwrap(), subj, subj_ty);
            } else {
                const cond_v = if (!row.cond.isNone())
                    try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), self.context.type_store.tBool(), .rvalue)
                else
                    f.builder.tirValue(.ConstBool, &header, self.context.type_store.tBool(), .{ .value = true });

                const br_cond = self.forceLocalCond(&header, cond_v);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{});
            }

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
            // statement-position while
            const exit_blk = try f.builder.beginBlock(f);

            try f.builder.br(blk, header.id, &.{});
            {
                const old = blk.*;
                try f.builder.endBlock(f, old);
            }

            if (row.is_pattern and !row.pattern.isNone() and !row.cond.isNone()) {
                const subj = try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), null, .rvalue);
                const subj_ty = self.getExprType(row.cond.unwrap()) orelse self.context.type_store.tAny();

                const ok = try self.matchPattern(a, env, f, &header, row.pattern.unwrap(), subj, subj_ty);

                const br_cond = self.forceLocalCond(&header, ok);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{});

                // bind `x` etc. for the body
                try self.bindPattern(a, env, f, &body, row.pattern.unwrap(), subj, subj_ty);
            } else {
                const cond_v = if (!row.cond.isNone())
                    try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), self.context.type_store.tBool(), .rvalue)
                else
                    f.builder.tirValue(.ConstBool, &header, self.context.type_store.tBool(), .{ .value = true });
                const br_cond = self.forceLocalCond(&header, cond_v);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{});
            }

            try self.loop_stack.append(self.gpa, .{
                .label = if (!row.label.isNone()) a.exprs.strs.get(row.label.unwrap()) else null,
                .continue_block = header.id,
                .break_block = exit_blk.id,
                .has_result = false,
                .defer_len_at_entry = @intCast(env.defers.items.len),
            });

            try self.lowerExprAsStmtList(a, env, f, &body, row.body);
            if (body.term.isNone()) try f.builder.br(&body, header.id, &.{});
            try f.builder.endBlock(f, header);
            try f.builder.endBlock(f, body);

            _ = self.loop_stack.pop();
            blk.* = exit_blk;
            return self.safeUndef(blk, self.context.type_store.tAny());
        }
    }

    fn getIterableLen(self: *LowerTir, blk: *Builder.BlockFrame, iter_ty: types.TypeId, idx_ty: types.TypeId) !tir.ValueId {
        const iter_ty_kind = self.context.type_store.index.kinds.items[iter_ty.toRaw()];
        return switch (iter_ty_kind) {
            .Array => blk: {
                const at = self.context.type_store.get(.Array, iter_ty);
                break :blk blk.builder.tirValue(.ConstInt, blk, idx_ty, .{ .value = @as(u64, @intCast(at.len)) });
            },
            .Slice, .DynArray => @panic("Not implemented"),
            else => return error.LoweringBug,
        };
    }

    fn lowerFor(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.For, id);

        // Decide if this for-expression needs to produce a value
        const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
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

                var update_blk = try f.builder.beginBlock(f);
                const update_param = try f.builder.addBlockParam(&update_blk, null, idx_ty);
                const one_update = update_blk.builder.tirValue(.ConstInt, &update_blk, idx_ty, .{ .value = 1 });
                const next_update = update_blk.builder.bin(&update_blk, .Add, idx_ty, update_param, one_update);
                const update_block_id = update_blk.id;
                try f.builder.br(&update_blk, header.id, &.{next_update});
                try f.builder.endBlock(f, update_blk);

                try f.builder.br(blk, header.id, &.{start_v});
                {
                    const old = blk.*;
                    try f.builder.endBlock(f, old);
                }

                const cond = if (rg.inclusive_right)
                    blk.builder.binBool(&header, .CmpLe, idx_param, end_v)
                else
                    blk.builder.binBool(&header, .CmpLt, idx_param, end_v);

                const br_cond = self.forceLocalCond(&header, cond);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{});

                try self.bindPattern(a, env, f, &body, row.pattern, idx_param, idx_ty);

                var lc = &self.loop_stack.items[self.loop_stack.items.len - 1];
                lc.continue_block = update_block_id;
                lc.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param});

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            } else {
                // for x in iterable
                const arr_v = try self.lowerExpr(a, env, f, blk, row.iterable, null, .rvalue);
                const idx_ty = self.context.type_store.tUsize();
                const iter_ty = self.getExprType(row.iterable) orelse return error.LoweringBug;
                const len_v = try self.getIterableLen(blk, iter_ty, idx_ty);

                const zero = blk.builder.tirValue(.ConstInt, blk, idx_ty, .{ .value = 0 });
                const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);

                var update_blk = try f.builder.beginBlock(f);
                const update_param = try f.builder.addBlockParam(&update_blk, null, idx_ty);
                const one_update = update_blk.builder.tirValue(.ConstInt, &update_blk, idx_ty, .{ .value = 1 });
                const next_update = update_blk.builder.bin(&update_blk, .Add, idx_ty, update_param, one_update);
                const update_block_id = update_blk.id;
                try f.builder.br(&update_blk, header.id, &.{next_update});
                try f.builder.endBlock(f, update_blk);

                try f.builder.br(blk, header.id, &.{zero});
                {
                    const old = blk.*;
                    try f.builder.endBlock(f, old);
                }

                const cond = blk.builder.binBool(&header, .CmpLt, idx_param, len_v);
                const br_cond = self.forceLocalCond(&header, cond);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{});

                // Determine element type
                var elem_ty = self.context.type_store.tAny();
                if (self.getExprType(row.iterable)) |it_ty| {
                    const ik = self.context.type_store.index.kinds.items[it_ty.toRaw()];
                    if (ik == .Array)
                        elem_ty = self.context.type_store.get(.Array, it_ty).elem
                    else if (ik == .Slice)
                        elem_ty = self.context.type_store.get(.Slice, it_ty).elem
                    else if (ik == .DynArray)
                        elem_ty = self.context.type_store.get(.DynArray, it_ty).elem;
                }

                const elem = blk.builder.indexOp(&body, elem_ty, arr_v, idx_param);
                try self.bindPattern(a, env, f, &body, row.pattern, elem, elem_ty);

                var lc2 = &self.loop_stack.items[self.loop_stack.items.len - 1];
                lc2.continue_block = update_block_id;
                lc2.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param});

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
                var update_blk = try f.builder.beginBlock(f);
                const update_param = try f.builder.addBlockParam(&update_blk, null, idx_ty);
                const one_update = update_blk.builder.tirValue(.ConstInt, &update_blk, idx_ty, .{ .value = 1 });
                const next_update = update_blk.builder.bin(&update_blk, .Add, idx_ty, update_param, one_update);
                const update_block_id = update_blk.id;
                try f.builder.br(&update_blk, header.id, &.{next_update});
                try f.builder.endBlock(f, update_blk);
                try f.builder.br(blk, header.id, &.{start_v});
                {
                    const old = blk.*;
                    try f.builder.endBlock(f, old);
                }

                const cond = if (rg.inclusive_right)
                    blk.builder.binBool(&header, .CmpLe, idx_param, end_v)
                else
                    blk.builder.binBool(&header, .CmpLt, idx_param, end_v);

                const br_cond = self.forceLocalCond(&header, cond);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{});

                try self.bindPattern(a, env, f, &body, row.pattern, idx_param, idx_ty);

                var lc = &self.loop_stack.items[self.loop_stack.items.len - 1];
                lc.continue_block = update_block_id;
                lc.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);

                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param});

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            } else {
                const arr_v = try self.lowerExpr(a, env, f, blk, row.iterable, null, .rvalue);
                const idx_ty = self.context.type_store.tUsize();
                const iter_ty = self.getExprType(row.iterable) orelse return error.LoweringBug;
                const len_v = try self.getIterableLen(blk, iter_ty, idx_ty);

                const zero = blk.builder.tirValue(.ConstInt, blk, idx_ty, .{ .value = 0 });
                const idx_param = try f.builder.addBlockParam(&header, null, idx_ty);

                var update_blk = try f.builder.beginBlock(f);
                const update_param = try f.builder.addBlockParam(&update_blk, null, idx_ty);
                const one_update = update_blk.builder.tirValue(.ConstInt, &update_blk, idx_ty, .{ .value = 1 });
                const next_update = update_blk.builder.bin(&update_blk, .Add, idx_ty, update_param, one_update);
                const update_block_id = update_blk.id;
                try f.builder.br(&update_blk, header.id, &.{next_update});
                try f.builder.endBlock(f, update_blk);

                try f.builder.br(blk, header.id, &.{zero});
                {
                    const old = blk.*;
                    try f.builder.endBlock(f, old);
                }

                const cond = blk.builder.binBool(&header, .CmpLt, idx_param, len_v);
                const br_cond = self.forceLocalCond(&header, cond);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{});

                var elem_ty = self.context.type_store.tAny();
                if (self.getExprType(row.iterable)) |it_ty| {
                    const ik = self.context.type_store.index.kinds.items[it_ty.toRaw()];
                    if (ik == .Array)
                        elem_ty = self.context.type_store.get(.Array, it_ty).elem
                    else if (ik == .Slice)
                        elem_ty = self.context.type_store.get(.Slice, it_ty).elem
                    else if (ik == .DynArray)
                        elem_ty = self.context.type_store.get(.DynArray, it_ty).elem;
                }
                const elem = blk.builder.indexOp(&body, elem_ty, arr_v, idx_param);
                try self.bindPattern(a, env, f, &body, row.pattern, elem, elem_ty);

                var lc2 = &self.loop_stack.items[self.loop_stack.items.len - 1];
                lc2.continue_block = update_block_id;
                lc2.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param});

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            }

            _ = self.loop_stack.pop();
            blk.* = exit_blk;
            return self.safeUndef(blk, self.context.type_store.tAny());
        }
    }

    fn lowerExpr(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        mode: LowerMode,
    ) anyerror!tir.ValueId {
        const expr_kind = a.exprs.index.kinds.items[id.toRaw()];

        return switch (expr_kind) {
            .Literal => self.lowerLiteral(a, blk, id, expected_ty),
            .NullLit => {
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = blk.builder.constNull(blk, ty0);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .UndefLit => {
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = blk.builder.tirValue(.ConstUndef, blk, ty0, .{});
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .Unary => self.lowerUnary(a, env, f, blk, id, expected_ty, mode),
            .Range => self.lowerRange(a, env, f, blk, id, expected_ty),
            .Deref => self.lowerDeref(a, env, f, blk, id, expected_ty, mode),
            .TupleLit => self.lowerTupleLit(a, env, f, blk, id, expected_ty),
            .ArrayLit => self.lowerArrayLit(a, env, f, blk, id, expected_ty),
            .StructLit => self.lowerStructLit(a, env, f, blk, id, expected_ty),
            .MapLit => self.lowerMapLit(a, env, f, blk, id, expected_ty),
            .IndexAccess => self.lowerIndexAccess(a, env, f, blk, id, expected_ty, mode),
            .FieldAccess => self.lowerFieldAccess(a, env, f, blk, id, expected_ty, mode),
            .Block => {
                const res_ty = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
                return try self.lowerBlockExprValue(a, env, f, blk, id, res_ty);
            },
            .Ident => self.lowerIdent(a, env, f, blk, id, expected_ty, mode),
            .Binary => self.lowerBinary(a, env, f, blk, id, expected_ty),
            .Catch => self.lowerCatch(a, env, f, blk, id, expected_ty),
            .If => self.lowerIf(a, env, f, blk, id, expected_ty),
            .Call => self.lowerCall(a, env, f, blk, id, expected_ty),
            .Cast => self.lowerCast(a, env, f, blk, id, expected_ty),
            .OptionalUnwrap => self.lowerOptionalUnwrap(a, env, f, blk, id, expected_ty),
            .ErrUnwrap => self.lowerErrUnwrap(a, env, f, blk, id, expected_ty),
            .UnionType => self.lowerTypeExprOpaque(blk, id, expected_ty),
            .Match => self.lowerMatch(a, env, f, blk, id, expected_ty),
            .While => self.lowerWhile(a, env, f, blk, id, expected_ty),
            .For => self.lowerFor(a, env, f, blk, id, expected_ty),
            .Import => blk.builder.tirValue(.ConstUndef, blk, self.getExprType(id) orelse self.context.type_store.tAny(), .{}),
            .VariantType, .EnumType, .StructType => self.lowerTypeExprOpaque(blk, id, expected_ty),
            .MlirBlock => {
                const row = a.exprs.get(.MlirBlock, id);
                const ty0 = self.getExprType(id) orelse self.context.type_store.tAny(); // MlirBlock is opaque, so it's Any
                const result_id = f.builder.freshValue();
                _ = f.builder.addMlirBlock(blk, result_id, ty0, row.kind, row.text);
                return result_id;
            },
            else => {
                std.debug.print("lowerExpr: unhandled expr kind {}\n", .{expr_kind});
                return error.LoweringBug;
            },
        };
    }

    // Compute the value of a block expression (value position)
    fn lowerBlockExprValue(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, block_expr: ast.ExprId, expected_ty: types.TypeId) anyerror!tir.ValueId {
        if (a.exprs.index.kinds.items[block_expr.toRaw()] != .Block) {
            return self.lowerExpr(a, env, f, blk, block_expr, expected_ty, .rvalue);
        }
        const b = a.exprs.get(.Block, block_expr);
        const stmts = a.stmts.stmt_pool.slice(b.items);
        if (stmts.len == 0) return self.safeUndef(blk, expected_ty);

        // Remember where this block's scope begins on the defer stack.
        const mark: u32 = @intCast(env.defers.items.len);
        var i: usize = 0;
        while (i + 1 < stmts.len) : (i += 1) {
            try self.lowerStmt(a, env, f, blk, stmts[i]);
        }
        const last = stmts[stmts.len - 1];
        const lk = a.stmts.index.kinds.items[last.toRaw()];
        if (lk == .Expr) {
            const le = a.stmts.get(.Expr, last).expr;
            // Evaluate the last expression value-first, then run defers belonging to this block,
            // then return the computed value. This preserves the "defer runs at scope exit" rule.
            const v = try self.lowerExpr(a, env, f, blk, le, expected_ty, .rvalue);
            // If the checker stamped a different type than expected, keep your existing
            // higher-level coercion behavior by not touching `v` here beyond scope-finalization.
            try self.runNormalDefersFrom(a, env, f, blk, mark);
            return v;
        } else {
            try self.lowerStmt(a, env, f, blk, last);
            // Natural fallthrough out of the block scope: run normal defers for this block.
            // Early exits (return/break/continue) won’t reach here and already run defers.
            try self.runNormalDefersFrom(a, env, f, blk, mark);
            return self.safeUndef(blk, expected_ty);
        }
    }

    // ============================
    // Import materialization
    // ============================

    fn findTopLevelDeclByName(self: *const LowerTir, a: *const ast.Ast, name: ast.StrId) ?ast.DeclId {
        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        var i: usize = 0;
        while (i < decls.len) : (i += 1) {
            const d = a.exprs.Decl.get(decls[i]);
            if (d.pattern.isNone()) continue;
            const pid = d.pattern.unwrap();
            if (self.patternContainsName(a, pid, name)) return decls[i];
        }
        return null;
    }

    fn patternContainsName(
        self: *const LowerTir,
        a: *const ast.Ast,
        pid: ast.PatternId,
        name: ast.StrId,
    ) bool {
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        return switch (pk) {
            .Binding => a.pats.get(.Binding, pid).name.eq(name),
            .Tuple => {
                const row = a.pats.get(.Tuple, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                for (elems) |eid| if (self.patternContainsName(a, eid, name)) return true;
                return false;
            },
            .Struct => {
                const row = a.pats.get(.Struct, pid);
                const fields = a.pats.field_pool.slice(row.fields);
                for (fields) |fid| {
                    const frow = a.pats.StructField.get(fid);
                    if (self.patternContainsName(a, frow.pattern, name)) return true;
                }
                return false;
            },
            .VariantTuple => {
                const row = a.pats.get(.VariantTuple, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                for (elems) |eid| if (self.patternContainsName(a, eid, name)) return true;
                return false;
            },
            .VariantStruct => {
                const row = a.pats.get(.VariantStruct, pid);
                const fields = a.pats.field_pool.slice(row.fields);
                for (fields) |fid| {
                    const frow = a.pats.StructField.get(fid);
                    if (self.patternContainsName(a, frow.pattern, name)) return true;
                }
                return false;
            },
            .Slice => {
                const row = a.pats.get(.Slice, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                for (elems) |eid| if (self.patternContainsName(a, eid, name)) return true;
                if (!row.rest_binding.isNone()) {
                    if (self.patternContainsName(a, row.rest_binding.unwrap(), name)) return true;
                }
                return false;
            },
            .Or => {
                const row = a.pats.get(.Or, pid);
                const alts = a.pats.pat_pool.slice(row.alts);
                for (alts) |aid| if (self.patternContainsName(a, aid, name)) return true;
                return false;
            },
            .At => {
                const row = a.pats.get(.At, pid);
                // if (std.mem.eql(u8, a.exprs.strs.get(row.binder), name)) return true;
                if (row.binder.eq(name)) return true;
                return self.patternContainsName(a, row.pattern, name);
            },
            else => return false,
        };
    }
    fn findTopLevelImportByName(self: *const LowerTir, a: *const ast.Ast, name: ast.StrId) ?ast.DeclId {
        const did = self.findTopLevelDeclByName(a, name) orelse return null;
        const d = a.exprs.Decl.get(did);
        return if (a.exprs.index.kinds.items[d.value.toRaw()] == .Import) did else null;
    }

    fn materializeImportedConst(
        self: *LowerTir,
        res: *ImportResolver,
        a: *const ast.Ast,
        imp_decl: ast.DeclId,
        member: StrId,
        expected_ty: types.TypeId,
        blk: *Builder.BlockFrame,
        pipeline: *Pipeline,
    ) ?tir.ValueId {
        const d = a.exprs.Decl.get(imp_decl);
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
            const d2 = me.ast.exprs.Decl.get(decls[i]);
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

    /// True if `ty` is a numeric scalar type.
    fn isNumeric(self: *const LowerTir, ty: types.TypeId) bool {
        if (self.isVoid(ty)) return false;
        const k = self.context.type_store.index.kinds.items[ty.toRaw()];
        return switch (k) {
            .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64, .Usize, .F32, .F64 => true,
            else => false,
        };
    }

    fn isFloat(self: *const LowerTir, ty: types.TypeId) bool {
        const k = self.context.type_store.index.kinds.items[ty.toRaw()];
        return (k == .F32) or (k == .F64);
    }

    fn isAny(self: *const LowerTir, ty: types.TypeId) bool {
        return self.context.type_store.index.kinds.items[ty.toRaw()] == .Any;
    }

    /// Choose a common numeric type for binary ops when the checker didn't provide one.
    fn commonNumeric(
        self: *const LowerTir,
        l: ?types.TypeId,
        r: ?types.TypeId,
    ) ?types.TypeId {
        if (l) |lt| if (self.isNumeric(lt)) {
            if (r) |rt| {
                if (self.isNumeric(rt)) {
                    // naive widening preference: floats > signed > unsigned; 64 > 32 > 16 > 8
                    const kL = self.context.type_store.index.kinds.items[lt.toRaw()];
                    const kR = self.context.type_store.index.kinds.items[rt.toRaw()];
                    // if either side is float, pick the wider float
                    if ((kL == .F64) or (kR == .F64)) return self.context.type_store.tF64();
                    if ((kL == .F32) or (kR == .F32)) return self.context.type_store.tF32();
                    // prefer signed width of the wider side
                    const signedPref = [_]types.TypeId{
                        self.context.type_store.tI64(), self.context.type_store.tI32(),
                        self.context.type_store.tI16(), self.context.type_store.tI8(),
                    };
                    for (signedPref) |cand| {
                        if (lt.eq(cand) or rt.eq(cand)) return cand;
                    }
                    // otherwise fall back to the wider unsigned
                    if (lt.toRaw() == self.context.type_store.tU64().toRaw() or rt.toRaw() == self.context.type_store.tU64().toRaw()) return self.context.type_store.tU64();
                    if (lt.toRaw() == self.context.type_store.tU32().toRaw() or rt.toRaw() == self.context.type_store.tU32().toRaw()) return self.context.type_store.tU32();
                    if (lt.toRaw() == self.context.type_store.tU16().toRaw() or rt.toRaw() == self.context.type_store.tU16().toRaw()) return self.context.type_store.tU16();
                    return self.context.type_store.tU8();
                }
                return lt; // one numeric, one non-numeric → pick numeric side
            }
            return lt;
        } else if (r) |rt| if (self.isNumeric(rt)) return rt;
        return null;
    }

    fn lowerImportedExprValue(self: *LowerTir, me: *@import("import_resolver.zig").ModuleEntry, eid: ast.ExprId, expected_ty: types.TypeId, blk: *Builder.BlockFrame) ?tir.ValueId {
        const kinds = me.ast.exprs.index.kinds.items;
        switch (kinds[eid.toRaw()]) {
            .StructLit => {
                if (self.context.type_store.getKind(expected_ty) != .Struct) return null;
                const row = me.ast.exprs.get(.StructLit, eid);
                const sfields = me.ast.exprs.sfv_pool.slice(row.fields);
                const st = self.context.type_store.get(.Struct, expected_ty);
                const exp_fields = self.context.type_store.field_pool.slice(st.fields);
                var fields = self.gpa.alloc(tir.Rows.StructFieldInit, exp_fields.len) catch return null;
                var j: usize = 0;
                while (j < exp_fields.len) : (j += 1) {
                    const f = self.context.type_store.Field.get(exp_fields[j]);
                    const src_idx = if (j < sfields.len) j else sfields.len - 1;
                    const sfv = me.ast.exprs.StructFieldValue.get(sfields[src_idx]);
                    const vv = self.lowerImportedExprValue(me, sfv.value, f.ty, blk) orelse {
                        self.gpa.free(fields);
                        return null;
                    };
                    fields[j] = .{ .index = @intCast(j), .name = .none(), .value = vv };
                }
                const v = blk.builder.structMake(blk, expected_ty, fields);
                self.gpa.free(fields);
                return v;
            },
            .Literal => {
                const lit = me.ast.exprs.get(.Literal, eid);
                const s = if (!lit.value.isNone()) me.ast.exprs.strs.get(lit.value.unwrap()) else "";
                const k = self.context.type_store.getKind(expected_ty);
                switch (k) {
                    .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64 => {
                        const parsed = std.fmt.parseInt(i64, s, 10) catch return null;
                        return blk.builder.tirValue(.ConstInt, blk, expected_ty, .{ .value = @as(u64, @intCast(parsed)) });
                    },
                    .Bool => return blk.builder.tirValue(.ConstBool, blk, expected_ty, .{ .value = lit.bool_value }),
                    .String => return blk.builder.tirValue(.ConstString, blk, expected_ty, .{ .text = lit.value.unwrap() }),
                    else => return null,
                }
            },
            else => return null,
        }
    }

    // ============================
    // Misc helpers
    // ============================

    fn getExprType(self: *const LowerTir, id: ast.ExprId) ?types.TypeId {
        const i = id.toRaw();
        std.debug.assert(i < self.type_info.expr_types.items.len);
        return self.type_info.expr_types.items[i];
    }
    fn getDeclType(self: *const LowerTir, did: ast.DeclId) ?types.TypeId {
        const i = did.toRaw();
        std.debug.assert(i < self.type_info.decl_types.items.len);
        return self.type_info.decl_types.items[i];
    }

    fn getUnionTypeFromVariant(self: *const LowerTir, vty: types.TypeId) ?types.TypeId {
        const ts = &self.context.type_store;
        const k = ts.getKind(vty);

        if (k == .Variant or k == .Error) {
            const fields = if (k == .Variant)
                ts.field_pool.slice(ts.get(.Variant, vty).variants)
            else
                ts.field_pool.slice(ts.get(.Error, vty).variants);

            var args = self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len) catch return null;
            defer self.gpa.free(args);

            for (fields, 0..) |fid, i| {
                const f = ts.Field.get(fid);
                args[i] = .{ .name = f.name, .ty = f.ty };
            }
            return ts.mkUnion(args);
        }

        // Fallback if a legacy representation is ever seen.
        if (k == .Struct) {
            const sfields = ts.field_pool.slice(ts.get(.Struct, vty).fields);
            if (sfields.len != 2) return null;
            return ts.Field.get(sfields[1]).ty;
        }

        return null;
    }

    fn bindingNameOfPattern(_: *const LowerTir, a: *const ast.Ast, pid: ast.PatternId) ?StrId {
        const k = a.pats.index.kinds.items[pid.toRaw()];
        return switch (k) {
            .Binding => a.pats.get(.Binding, pid).name,
            else => null,
        };
    }

    fn bindPattern(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        pid: ast.PatternId,
        value: tir.ValueId,
        vty: types.TypeId,
    ) !void {
        const k = a.pats.index.kinds.items[pid.toRaw()];
        switch (k) {
            .Binding => {
                const nm = a.pats.get(.Binding, pid).name;
                try env.bind(self.gpa, a, nm, .{ .value = value, .is_slot = false });
            },
            .At => {
                const at = a.pats.get(.At, pid);
                try env.bind(self.gpa, a, at.binder, .{ .value = value, .is_slot = false });
                try self.bindPattern(a, env, f, blk, at.pattern, value, vty);
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
                    const ev = blk.builder.extractElem(blk, ety, value, @intCast(i));
                    try self.bindPattern(a, env, f, blk, pe, ev, ety);
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
                const union_agg = blk.builder.extractField(blk, union_ty, value, 1);

                // Determine the concrete payload type for this case
                const payload_fields = self.context.type_store.field_pool.slice(
                    self.context.type_store.get(.Union, union_ty).fields,
                );
                const fld = self.context.type_store.Field.get(payload_fields[tag_idx]);
                const payload_ty = fld.ty;

                const pelems = a.pats.pat_pool.slice(pr.elems);

                if (self.context.type_store.getKind(payload_ty) == .Tuple) {
                    // Read the whole tuple payload value, then destructure
                    const tuple_val = blk.builder.tirValue(.UnionField, blk, payload_ty, .{
                        .base = union_agg,
                        .field_index = tag_idx,
                    });

                    const tr = self.context.type_store.get(.Tuple, payload_ty);
                    const subtys = self.context.type_store.type_pool.slice(tr.elems);

                    for (pelems, 0..) |pe, i| {
                        const ety = if (i < subtys.len) subtys[i] else self.context.type_store.tAny();
                        const ev = blk.builder.extractElem(blk, ety, tuple_val, @intCast(i));
                        try self.bindPattern(a, env, f, blk, pe, ev, ety);
                    }
                } else {
                    // Single non-tuple payload
                    const pv = blk.builder.tirValue(.UnionField, blk, payload_ty, .{
                        .base = union_agg,
                        .field_index = tag_idx,
                    });
                    if (pelems.len > 0) {
                        try self.bindPattern(a, env, f, blk, pelems[0], pv, payload_ty);
                    }
                }
            },
            // Other pattern forms can be added as needed.
            else => {},
        }
    }

    // Destructure a declaration pattern and bind its sub-bindings either as values (const) or slots (mutable).
    fn destructureDeclPattern(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, value: tir.ValueId, vty: types.TypeId, to_slots: bool) !void {
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        switch (pk) {
            .Binding => {
                const nm = a.pats.get(.Binding, pid).name;
                if (to_slots) {
                    const slot_ty = self.context.type_store.mkPtr(vty, false);
                    const slot = f.builder.tirValue(.Alloca, blk, slot_ty, .{ .count = tir.OptValueId.none(), .@"align" = 0 });
                    _ = f.builder.tirValue(.Store, blk, vty, .{ .ptr = slot, .value = value, .@"align" = 0 });
                    try env.bind(self.gpa, a, nm, .{ .value = slot, .is_slot = true });
                } else {
                    try env.bind(self.gpa, a, nm, .{ .value = value, .is_slot = false });
                }
            },
            .Tuple => {
                const row = a.pats.get(.Tuple, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                var etys: []const types.TypeId = &[_]types.TypeId{};
                const vk = self.context.type_store.index.kinds.items[vty.toRaw()];
                if (vk == .Tuple) {
                    const vrow = self.context.type_store.get(.Tuple, vty);
                    etys = self.context.type_store.type_pool.slice(vrow.elems);
                }
                var i: usize = 0;
                while (i < elems.len) : (i += 1) {
                    const ety = if (i < etys.len) etys[i] else self.context.type_store.tAny();
                    const ev = blk.builder.extractElem(blk, ety, value, @intCast(i));
                    try self.destructureDeclPattern(a, env, f, blk, elems[i], ev, ety, to_slots);
                }
            },
            .Struct => {
                const row = a.pats.get(.Struct, pid);
                const fields = a.pats.field_pool.slice(row.fields);
                // If we know the struct type, build a name->(index, ty) map.
                var idx_by_name: ?[]const types.FieldId = null;
                if (self.context.type_store.getKind(vty) == .Struct) {
                    const srow = self.context.type_store.get(.Struct, vty);
                    idx_by_name = self.context.type_store.field_pool.slice(srow.fields);
                }
                for (fields) |fid| {
                    const pf = a.pats.StructField.get(fid);
                    // Determine field type and extraction method
                    var fty = self.context.type_store.tAny();
                    var extracted: tir.ValueId = undefined;
                    if (idx_by_name) |field_ids| {
                        // scan for matching name
                        var found = false;
                        var j: usize = 0;
                        while (j < field_ids.len) : (j += 1) {
                            const stf = self.context.type_store.Field.get(field_ids[j]);
                            if (stf.name.toRaw() == pf.name.toRaw()) {
                                fty = stf.ty;
                                extracted = blk.builder.extractField(blk, fty, value, @intCast(j));
                                found = true;
                                break;
                            }
                        }
                        if (!found) {
                            // name not present on this struct type; bind undef of Any
                            extracted = self.undef(blk, fty);
                        }
                    } else {
                        // Unknown layout; fall back to by-name extraction in IR
                        extracted = blk.builder.extractFieldNamed(blk, fty, value, pf.name);
                    }
                    try self.destructureDeclPattern(a, env, f, blk, pf.pattern, extracted, fty, to_slots);
                }
            },
            else => {
                // Patterns not yet supported for declarations are ignored for now.
            },
        }
    }

    // Prefer destructuring directly from the source expression when available (avoids building temp tuples).
    fn destructureDeclFromTupleLit(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, src_expr: ast.ExprId, vty: types.TypeId, to_slots: bool) anyerror!void {
        const row = a.pats.get(.Tuple, pid);
        const elems_pat = a.pats.pat_pool.slice(row.elems);
        const elr = a.exprs.get(.TupleLit, src_expr);
        const elems_expr = a.exprs.expr_pool.slice(elr.elems);
        var etys: []const types.TypeId = &[_]types.TypeId{};
        const vk = self.context.type_store.index.kinds.items[vty.toRaw()];
        if (vk == .Tuple) {
            const vrow = self.context.type_store.get(.Tuple, vty);
            etys = self.context.type_store.type_pool.slice(vrow.elems);
        }
        const n = @min(elems_pat.len, elems_expr.len);
        var i: usize = 0;
        while (i < n) : (i += 1) {
            const ety = if (i < etys.len) etys[i] else self.context.type_store.tAny();
            try self.destructureDeclFromExpr(a, env, f, blk, elems_pat[i], elems_expr[i], ety, to_slots);
        }
        // If pattern has more elements than expr, fill remaining with undef of element type.
        while (i < elems_pat.len) : (i += 1) {
            const ety = if (i < etys.len) etys[i] else self.context.type_store.tAny();
            const uv = self.undef(blk, ety);
            try self.destructureDeclPattern(a, env, f, blk, elems_pat[i], uv, ety, to_slots);
        }
    }

    fn destructureDeclFromStructLit(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, src_expr: ast.ExprId, vty: types.TypeId, to_slots: bool) !void {
        const pr = a.pats.get(.Struct, pid);
        const pfields = a.pats.field_pool.slice(pr.fields);
        const sr = a.exprs.get(.StructLit, src_expr);
        const sfields = a.exprs.sfv_pool.slice(sr.fields);
        // compute field types if known
        var type_fields: []const types.FieldId = &[_]types.FieldId{};
        if (self.context.type_store.getKind(vty) == .Struct) {
            const srow = self.context.type_store.get(.Struct, vty);
            type_fields = self.context.type_store.field_pool.slice(srow.fields);
        }
        // For each pattern field, find matching expr field by name and destructure from its value expr.
        for (pfields) |pfid| {
            const pf = a.pats.StructField.get(pfid);
            // find expr field by name
            var val_expr: ?ast.ExprId = null;
            for (sfields) |sfid| {
                const sf = a.exprs.StructFieldValue.get(sfid);
                if (sf.name.toRaw() == pf.name.toRaw()) {
                    val_expr = sf.value;
                    break;
                }
            }
            var fty = self.context.type_store.tAny();
            // find field type by name if known
            for (type_fields) |tfid| {
                const tf = self.context.type_store.Field.get(tfid);
                if (tf.name.toRaw() == pf.name.toRaw()) {
                    fty = tf.ty;
                    break;
                }
            }
            if (val_expr) |ve| {
                try self.destructureDeclFromExpr(a, env, f, blk, pf.pattern, ve, fty, to_slots);
            } else {
                // missing -> bind undef
                const uv = self.undef(blk, fty);
                try self.destructureDeclPattern(a, env, f, blk, pf.pattern, uv, fty, to_slots);
            }
        }
    }

    fn destructureDeclFromExpr(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, src_expr: ast.ExprId, vty: types.TypeId, to_slots: bool) anyerror!void {
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        switch (pk) {
            .Binding => {
                const val = try self.lowerExpr(a, env, f, blk, src_expr, vty, .rvalue);
                return try self.destructureDeclPattern(a, env, f, blk, pid, val, vty, to_slots);
            },
            .Tuple => {
                // If RHS is a tuple-literal, lower elements individually to avoid creating a temporary aggregate.
                if (a.exprs.index.kinds.items[src_expr.toRaw()] == .TupleLit) {
                    try self.destructureDeclFromTupleLit(a, env, f, blk, pid, src_expr, vty, to_slots);
                    return;
                }
                // Fallback: lower full expr once, then destructure via extracts.
                const val = try self.lowerExpr(a, env, f, blk, src_expr, vty, .rvalue);
                return try self.destructureDeclPattern(a, env, f, blk, pid, val, vty, to_slots);
            },
            .Struct => {
                if (a.exprs.index.kinds.items[src_expr.toRaw()] == .StructLit) {
                    try self.destructureDeclFromStructLit(a, env, f, blk, pid, src_expr, vty, to_slots);
                    return;
                }
                // fallback: lower whole expr and destructure by field extraction
                const val = try self.lowerExpr(a, env, f, blk, src_expr, vty, .rvalue);
                return try self.destructureDeclPattern(a, env, f, blk, pid, val, vty, to_slots);
            },
            .VariantTuple => {
                // Handle call-form variant literal: V.C(arg1, arg2, ...)
                const pr = a.pats.get(.VariantTuple, pid);
                const p_segs = a.pats.seg_pool.slice(pr.path);
                const case_name = a.pats.PathSeg.get(p_segs[p_segs.len - 1]).name;
                if (a.exprs.index.kinds.items[src_expr.toRaw()] == .Call) {
                    const call = a.exprs.get(.Call, src_expr);
                    // Extract last path segment from callee
                    var callee_last: ?ast.StrId = null;
                    var cur = call.callee;
                    while (a.exprs.index.kinds.items[cur.toRaw()] == .FieldAccess) {
                        const fr = a.exprs.get(.FieldAccess, cur);
                        callee_last = fr.field;
                        cur = fr.parent;
                    }
                    if (callee_last != null and callee_last.?.toRaw() == case_name.toRaw()) {
                        // Use args directly
                        const args = a.exprs.expr_pool.slice(call.args);
                        var elem_tys: []const types.TypeId = &[_]types.TypeId{};
                        if (self.context.type_store.getKind(vty) == .Variant) {
                            const V = self.context.type_store.get(.Variant, vty);
                            const fields = self.context.type_store.field_pool.slice(V.variants);
                            var j: usize = 0;
                            while (j < fields.len) : (j += 1) {
                                const fld = self.context.type_store.Field.get(fields[j]);
                                if (fld.name.eq(case_name) and self.context.type_store.getKind(fld.ty) == .Tuple) {
                                    const tr = self.context.type_store.get(.Tuple, fld.ty);
                                    elem_tys = self.context.type_store.type_pool.slice(tr.elems);
                                    break;
                                }
                            }
                        }
                        const pelems = a.pats.pat_pool.slice(pr.elems);
                        var i: usize = 0;
                        const n = @min(pelems.len, args.len);
                        while (i < n) : (i += 1) {
                            const ety = if (i < elem_tys.len) elem_tys[i] else self.context.type_store.tAny();
                            try self.destructureDeclFromExpr(a, env, f, blk, pelems[i], args[i], ety, to_slots);
                        }
                        while (i < pelems.len) : (i += 1) {
                            const ety = if (i < elem_tys.len) elem_tys[i] else self.context.type_store.tAny();
                            const uv = self.undef(blk, ety);
                            try self.destructureDeclPattern(a, env, f, blk, pelems[i], uv, ety, to_slots);
                        }
                        return;
                    }
                }
                // Fallback: cannot extract from a non-literal variant without dedicated ops; bind undefs to subpatterns.
                const pelems = a.pats.pat_pool.slice(pr.elems);
                var elem_tys: []const types.TypeId = &[_]types.TypeId{};
                // Try fetch payload tuple element types by case name.
                if (self.context.type_store.getKind(vty) == .Variant) {
                    const V = self.context.type_store.get(.Variant, vty);
                    const fields = self.context.type_store.field_pool.slice(V.variants);
                    var j: usize = 0;
                    while (j < fields.len) : (j += 1) {
                        const fld = self.context.type_store.Field.get(fields[j]);
                        if (fld.name.eq(case_name) and self.context.type_store.getKind(fld.ty) == .Tuple) {
                            const tr = self.context.type_store.get(.Tuple, fld.ty);
                            elem_tys = self.context.type_store.type_pool.slice(tr.elems);
                            break;
                        }
                    }
                }
                var i: usize = 0;
                while (i < pelems.len) : (i += 1) {
                    const ety = if (i < elem_tys.len) elem_tys[i] else self.context.type_store.tAny();
                    const uv = self.undef(blk, ety);
                    try self.destructureDeclPattern(a, env, f, blk, pelems[i], uv, ety, to_slots);
                }
            },
            .VariantStruct => {
                const pr = a.pats.get(.VariantStruct, pid);
                const segs = a.pats.seg_pool.slice(pr.path);
                const case_name = a.pats.PathSeg.get(segs[segs.len - 1]).name;
                // Handle struct-literal with typed path: V.C{ ... }
                if (a.exprs.index.kinds.items[src_expr.toRaw()] == .StructLit) {
                    const sl = a.exprs.get(.StructLit, src_expr);
                    if (!sl.ty.isNone()) {
                        // Extract last segment from type path
                        var cur = sl.ty.unwrap();
                        var last_seg: ?ast.StrId = null;
                        while (a.exprs.index.kinds.items[cur.toRaw()] == .FieldAccess) {
                            const fr = a.exprs.get(.FieldAccess, cur);
                            last_seg = fr.field;
                            cur = fr.parent;
                        }
                        if (last_seg != null and last_seg.?.toRaw() == case_name.toRaw()) {
                            // Compute field tys for this case if known
                            var field_tys: []const types.FieldId = &[_]types.FieldId{};
                            if (self.context.type_store.getKind(vty) == .Variant) {
                                const V = self.context.type_store.get(.Variant, vty);
                                const variants = self.context.type_store.field_pool.slice(V.variants);
                                var j: usize = 0;
                                while (j < variants.len) : (j += 1) {
                                    const vf = self.context.type_store.Field.get(variants[j]);
                                    if (vf.name.eq(case_name) and self.context.type_store.getKind(vf.ty) == .Struct) {
                                        const sr = self.context.type_store.get(.Struct, vf.ty);
                                        field_tys = self.context.type_store.field_pool.slice(sr.fields);
                                        break;
                                    }
                                }
                            }
                            const pfields = a.pats.field_pool.slice(pr.fields);
                            const sfields = a.exprs.sfv_pool.slice(sl.fields);
                            for (pfields) |pfid| {
                                const pf = a.pats.StructField.get(pfid);
                                // find matching expr field by name
                                var val_expr: ?ast.ExprId = null;
                                for (sfields) |sfid| {
                                    const sf = a.exprs.StructFieldValue.get(sfid);
                                    if (sf.name.toRaw() == pf.name.toRaw()) {
                                        val_expr = sf.value;
                                        break;
                                    }
                                }
                                var fty = self.context.type_store.tAny();
                                // lookup field type by name
                                for (field_tys) |tfid| {
                                    const tf = self.context.type_store.Field.get(tfid);
                                    if (tf.name.toRaw() == pf.name.toRaw()) {
                                        fty = tf.ty;
                                        break;
                                    }
                                }
                                if (val_expr) |ve2| {
                                    try self.destructureDeclFromExpr(a, env, f, blk, pf.pattern, ve2, fty, to_slots);
                                } else {
                                    const uv = self.undef(blk, fty);
                                    try self.destructureDeclPattern(a, env, f, blk, pf.pattern, uv, fty, to_slots);
                                }
                            }
                            return;
                        }
                    }
                }
                // Fallback: cannot extract; bind undefs to subpatterns.
                const pfields = a.pats.field_pool.slice(pr.fields);
                for (pfields) |pfid| {
                    const pf = a.pats.StructField.get(pfid);
                    const uv = self.undef(blk, self.context.type_store.tAny());
                    try self.destructureDeclPattern(a, env, f, blk, pf.pattern, uv, self.context.type_store.tAny(), to_slots);
                }
            },
            else => {
                // Default: lower entire expr and bind.
                const val = try self.lowerExpr(a, env, f, blk, src_expr, vty, .rvalue);
                return try self.destructureDeclPattern(a, env, f, blk, pid, val, vty, to_slots);
            },
        }
    }

    fn tagIndexForCase(self: *const LowerTir, case_ty: types.TypeId, name: StrId) ?u32 {
        const k = self.context.type_store.getKind(case_ty);
        if (k != .Variant and k != .Error) return null;
        const fields = if (k == .Variant)
            self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, case_ty).variants)
        else
            self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, case_ty).variants);
        for (fields, 0..) |fid, i| {
            const frow = self.context.type_store.Field.get(fid);
            if (frow.name.eq(name)) return @intCast(i);
        }
        return null;
    }

    /// Ensure `cond` is defined in `blk` and is i1.
    /// This always emits a local SSA (CastNormal) in `blk`, even if the source is already a bool.
    fn forceLocalCond(self: *LowerTir, blk: *Builder.BlockFrame, cond: tir.ValueId) tir.ValueId {
        const tBool = self.context.type_store.tBool();
        // Emit a no-op CastNormal to anchor `cond` in this block.
        return blk.builder.tirValue(.CastNormal, blk, tBool, .{ .value = cond });
    }

    fn isVariantLike(self: *const LowerTir, ty: types.TypeId) bool {
        const k = self.context.type_store.getKind(ty);
        return k == .Variant or k == .Error;
    }

    /// If `expr` is a tag literal like `MyErr.NotFound` (i.e. a field access on a
    /// TypeType whose `.of` is Variant or Error) return the variant/error type and
    /// the resolved tag index. Only returns for void-payload cases (constructorless).
    fn tagConstFromTypePath(
        self: *const LowerTir,
        a: *const ast.Ast,
        expr: ast.ExprId,
    ) ?struct { of_ty: types.TypeId, tag_idx: u32 } {
        if (a.exprs.index.kinds.items[expr.toRaw()] != .FieldAccess) return null;
        const fr = a.exprs.get(.FieldAccess, expr);
        const pty = self.getExprType(fr.parent) orelse return null;
        if (self.context.type_store.getKind(pty) != .TypeType) return null;

        const of_ty = self.context.type_store.get(.TypeType, pty).of;
        const of_kind = self.context.type_store.getKind(of_ty);
        if (of_kind != .Variant and of_kind != .Error) return null;

        // We rely on the checker to have resolved the field index.
        const idx = self.type_info.getFieldIndex(expr) orelse return null;

        // Only treat it as a pure tag literal if that case has void payload.
        const fields = if (of_kind == .Variant)
            self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, of_ty).variants)
        else
            self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, of_ty).variants);
        if (idx >= fields.len) return null;
        const payload_ty = self.context.type_store.Field.get(fields[idx]).ty;
        if (self.context.type_store.getKind(payload_ty) != .Void) return null;

        return .{ .of_ty = of_ty, .tag_idx = @intCast(idx) };
    }

    fn matchPattern(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, scrut: tir.ValueId, scrut_ty: types.TypeId) !tir.ValueId {
        const k = a.pats.index.kinds.items[pid.toRaw()];
        switch (k) {
            .Wildcard => return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), .{ .value = true }),
            .Literal => {
                const pr = a.pats.get(.Literal, pid);
                const litv = try self.lowerExpr(a, env, f, blk, pr.expr, null, .rvalue);
                return blk.builder.binBool(blk, .CmpEq, scrut, litv);
            },
            .VariantTuple => {
                const vt = a.pats.get(.VariantTuple, pid);
                const segs = a.pats.seg_pool.slice(vt.path);
                if (segs.len == 0) return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), .{ .value = false });
                const last = a.pats.PathSeg.get(segs[segs.len - 1]);
                if (self.tagIndexForCase(scrut_ty, last.name)) |idx| {
                    const tag = blk.builder.extractField(blk, self.context.type_store.tI32(), scrut, 0);
                    const want = f.builder.tirValue(
                        .ConstInt,
                        blk,
                        self.context.type_store.tI32(),
                        .{ .value = @as(u64, @intCast(idx)) },
                    );
                    return blk.builder.binBool(blk, .CmpEq, tag, want);
                }
                return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), .{ .value = false });
            },
            .At => {
                const node = a.pats.get(.At, pid);
                return try self.matchPattern(a, env, f, blk, node.pattern, scrut, scrut_ty);
            },
            .VariantStruct => {
                const vs = a.pats.get(.VariantStruct, pid);
                const segs = a.pats.seg_pool.slice(vs.path);
                if (segs.len == 0) return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), .{ .value = false });
                const last = a.pats.PathSeg.get(segs[segs.len - 1]);
                if (self.tagIndexForCase(scrut_ty, last.name)) |idx| {
                    const tag = blk.builder.extractField(blk, self.context.type_store.tI32(), scrut, 0);
                    const want = f.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), .{ .value = @as(u64, @intCast(idx)) });
                    return blk.builder.binBool(blk, .CmpEq, tag, want);
                }
                return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), .{ .value = false });
            },
            .Path => {
                // Tag-only variant pattern
                const pp = a.pats.get(.Path, pid);
                const segs = a.pats.seg_pool.slice(pp.segments);
                if (segs.len == 0) return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), .{ .value = false });
                const last = a.pats.PathSeg.get(segs[segs.len - 1]);
                if (self.tagIndexForCase(scrut_ty, last.name)) |idx| {
                    const tag = blk.builder.extractField(blk, self.context.type_store.tI32(), scrut, 0);
                    const want = f.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), .{ .value = @as(u64, @intCast(idx)) });
                    return blk.builder.binBool(blk, .CmpEq, tag, want);
                }
                return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), .{ .value = false });
            },
            .Binding, .Tuple, .Slice, .Struct, .Range, .Or => {
                return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), .{ .value = true });
            },
        }
    }

    fn collectPatternBindings(
        self: *LowerTir,
        a: *const ast.Ast,
        pid: ast.PatternId,
        list: *std.ArrayListUnmanaged(ast.StrId),
    ) !void {
        const kind = a.pats.index.kinds.items[pid.toRaw()];
        switch (kind) {
            .Binding => {
                const nm = a.pats.get(.Binding, pid).name;
                try list.append(self.gpa, nm);
            },
            .At => {
                const node = a.pats.get(.At, pid);
                try list.append(self.gpa, node.binder);
                try self.collectPatternBindings(a, node.pattern, list);
            },
            .Tuple => {
                const row = a.pats.get(.Tuple, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                for (elems) |child| try self.collectPatternBindings(a, child, list);
            },
            .Slice => {
                const row = a.pats.get(.Slice, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                for (elems) |child| try self.collectPatternBindings(a, child, list);
                if (!row.rest_binding.isNone())
                    try self.collectPatternBindings(a, row.rest_binding.unwrap(), list);
            },
            .Struct => {
                const row = a.pats.get(.Struct, pid);
                const fields = a.pats.field_pool.slice(row.fields);
                for (fields) |fid| {
                    const pf = a.pats.StructField.get(fid);
                    try self.collectPatternBindings(a, pf.pattern, list);
                }
            },
            .VariantTuple => {
                const row = a.pats.get(.VariantTuple, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                for (elems) |child| try self.collectPatternBindings(a, child, list);
            },
            .VariantStruct => {
                const row = a.pats.get(.VariantStruct, pid);
                const fields = a.pats.field_pool.slice(row.fields);
                for (fields) |fid| {
                    const pf = a.pats.StructField.get(fid);
                    try self.collectPatternBindings(a, pf.pattern, list);
                }
            },
            .Or => {
                const row = a.pats.get(.Or, pid);
                const alts = a.pats.pat_pool.slice(row.alts);
                for (alts) |alt| try self.collectPatternBindings(a, alt, list);
            },
            else => {},
        }
    }

    fn restoreBindings(self: *LowerTir, env: *Env, saved: []const BindingSnapshot) !void {
        var i: usize = saved.len;
        while (i > 0) : (i -= 1) {
            const entry = saved[i - 1];
            try env.restoreBinding(self.gpa, entry.name, entry.prev);
        }
    }
};

// ============================
// Context structs
// ============================

const ContinueInfo = union(enum) {
    none,
    range: struct { update_block: tir.BlockId, idx_value: tir.ValueId },
};

const LoopCtx = struct {
    label: ?[]const u8,
    continue_block: tir.BlockId,
    break_block: tir.BlockId,
    has_result: bool = false,
    join_block: tir.BlockId = tir.BlockId.fromRaw(0),
    res_param: tir.ValueId = tir.ValueId.fromRaw(0),
    res_ty: types.TypeId = undefined,
    defer_len_at_entry: u32 = 0,
    continue_info: ContinueInfo = .none,
};

const Env = struct {
    map: std.AutoArrayHashMapUnmanaged(ast.StrId, ValueBinding) = .{},
    defers: std.ArrayListUnmanaged(DeferEntry) = .{},
    marks: std.ArrayListUnmanaged(u32) = .{},

    fn init(_: std.mem.Allocator) Env {
        return .{ .map = .{} };
    }
    fn deinit(self: *Env, gpa: std.mem.Allocator) void {
        self.map.deinit(gpa);
        self.defers.deinit(gpa);
        self.marks.deinit(gpa);
    }
    fn bind(self: *Env, gpa: std.mem.Allocator, _: *const ast.Ast, name: StrId, vb: ValueBinding) !void {
        try self.map.put(gpa, name, vb);
    }
    fn lookup(self: *Env, s: ast.StrId) ?ValueBinding {
        return self.map.get(s);
    }
    fn restoreBinding(self: *Env, gpa: std.mem.Allocator, name: StrId, prev: ?ValueBinding) !void {
        if (prev) |val| {
            try self.map.put(gpa, name, val);
        } else {
            _ = self.map.swapRemove(name);
        }
    }
    fn pushScope(self: *Env, gpa: std.mem.Allocator) !void {
        try self.marks.append(gpa, @intCast(self.defers.items.len));
    }
    fn popScope(self: *Env) u32 {
        if (self.marks.items.len == 0) return 0;
        const mark = self.marks.items[self.marks.items.len - 1];
        self.marks.items.len -= 1;
        self.defers.items.len = mark;
        return mark;
    }
};

const ValueBinding = struct { value: tir.ValueId, is_slot: bool };
const DeferEntry = struct { expr: ast.ExprId, is_err: bool };
