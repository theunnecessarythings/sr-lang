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
    type_info: *types.TypeInfo,

    // Simple loop stack to support break/continue in While/For (+ value loops)
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},

    // Mapping: module ident name -> prefix for mangling (module.func -> prefix_func)
    module_prefix: std.StringHashMapUnmanaged([]const u8) = .{},

    import_base_dir: []const u8 = ".",

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

    pub fn setImportResolver(self: *@This(), r: *ImportResolver, base_dir: []const u8) void {
        self.import_resolver = r;
        self.import_base_dir = base_dir;
    }

    fn lowerGlobalMlir(self: *@This(), a: *const ast.Ast, b: *Builder) !void {
        var global_mlir_decls: std.ArrayList(ast.DeclId) = .empty;
        defer global_mlir_decls.deinit(self.gpa);

        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        for (decls) |did| {
            const d = a.exprs.Decl.get(did.toRaw());
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
            const d = a.exprs.Decl.get(did.toRaw());
            _ = try self.lowerExpr(a, &env, &f, &blk, d.value, null, .rvalue);
        }

        if (blk.term.isNone()) {
            try b.setReturn(&blk, tir.OptValueId.none());
        }
        try b.endBlock(&f, blk);
        try b.endFunction(f);
    }

    pub fn run(self: *@This(), a: *const ast.Ast) !tir.TIR {
        var t = tir.TIR.init(self.gpa, &self.context.type_store);
        var b = Builder.init(self.gpa, &t);

        try self.lowerGlobalMlir(a, &b);

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
        return self.context.type_store.index.kinds.items[ty.toRaw()] == .Void;
    }

    // Produce an undef that is never-void; if asked for void, give Any instead.
    fn safeUndef(self: *@This(), blk: *Builder.BlockFrame, ty: types.TypeId) tir.ValueId {
        if (self.isVoid(ty)) return blk.builder.constUndef(blk, self.context.type_store.tAny());
        return blk.builder.constUndef(blk, ty);
    }

    fn undef(_: *@This(), blk: *Builder.BlockFrame, ty: types.TypeId) tir.ValueId {
        return blk.builder.constUndef(blk, ty);
    }
    fn boolConst(self: *@This(), blk: *Builder.BlockFrame, v: bool) tir.ValueId {
        return blk.builder.constBool(blk, self.context.type_store.tBool(), v);
    }

    /// Insert an explicit coercion that realizes what the checker proved assignable/castable.
    fn emitCoerce(self: *@This(), blk: *Builder.BlockFrame, v: tir.ValueId, got: types.TypeId, want: types.TypeId) tir.ValueId {
        if (got.toRaw() == want.toRaw()) return v;

        const gk = self.context.type_store.index.kinds.items[got.toRaw()];
        const wk = self.context.type_store.index.kinds.items[want.toRaw()];

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
            _ = b.addGlobal(nm, ty);
        }
    }

    fn lowerFunction(self: *@This(), a: *const ast.Ast, b: *Builder, name: StrId, fun_eid: ast.ExprId) !void {
        const fid = self.getExprType(fun_eid) orelse return;
        if (self.context.type_store.index.kinds.items[fid.toRaw()] != .Function) return;
        const fnty = self.context.type_store.Function.get(self.context.type_store.index.rows.items[fid.toRaw()]);

        const fnr = a.exprs.get(.FunctionLit, fun_eid);

        if (!fnr.attrs.isNone()) {
            const attrs = a.exprs.attr_pool.slice(fnr.attrs.asRange());
            const mlir = a.exprs.strs.intern("mlir_fn");
            for (attrs) |aid| {
                const arow = a.exprs.Attribute.get(aid.toRaw());
                if (arow.name.toRaw() == mlir.toRaw()) {
                    return; // skip lowering this function
                }
            }
        }

        var f = try b.beginFunction(name, fnty.result, fnty.is_variadic);

        // Params
        const params = a.exprs.param_pool.slice(fnr.params);
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            const p = a.exprs.Param.get(params[i].toRaw());
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

    /// Run "normal" (non-err) defers scheduled at or after `from`, in reverse order,
    /// and then truncate the defer stack back to `from`.
    fn runNormalDefersFrom(
        self: *@This(),
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
                const vty = self.getExprType(d.value) orelse self.context.type_store.tAny();
                if (!d.pattern.isNone()) {
                    // Destructure once for all names: bind as values for const, or slots for mut.
                    try self.destructureDeclFromExpr(a, env, f, blk, d.pattern.unwrap(), d.value, vty, !d.flags.is_const);
                } else {
                    // No pattern: just evaluate for side-effects.
                    _ = try self.lowerExpr(a, env, f, blk, d.value, vty, .rvalue);
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
                    if (self.context.type_store.index.kinds.items[expect.toRaw()] == .ErrorSet) {
                        var then_blk = try f.builder.beginBlock(f);
                        var cont_blk = try f.builder.beginBlock(f);
                        const is_err_name = f.builder.intern("builtin.err.is_err");
                        const is_err = blk.builder.call(blk, self.context.type_store.tBool(), is_err_name, &.{v});
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

        // Variant construction: if expected is a Variant/Error and callee is a path to a case, build VariantMake
        if (expected) |ety| {
            const k = self.context.type_store.getKind(ety);
            if (k == .Variant or k == .Error) {
                // Extract last segment from callee path (FieldAccess chain)
                var cur = row.callee;
                var last_name: ?StrId = null;
                while (a.exprs.index.kinds.items[cur.toRaw()] == .FieldAccess) {
                    const fr = a.exprs.get(.FieldAccess, cur);
                    last_name = fr.field;
                    cur = fr.parent;
                }
                if (last_name) |lname| {
                    // Find case index and payload type
                    const fields = if (k == .Variant)
                        self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, ety).variants)
                    else
                        self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, ety).variants);
                    var tag_idx: u32 = 0;
                    var payload_ty: types.TypeId = self.context.type_store.tVoid();
                    var found = false;
                    var i_f: usize = 0;
                    while (i_f < fields.len) : (i_f += 1) {
                        const fld = self.context.type_store.Field.get(fields[i_f].toRaw());
                        if (fld.name.toRaw() == lname.toRaw()) { tag_idx = @intCast(i_f); payload_ty = fld.ty; found = true; break; }
                    }
                    if (found) {
                        // Lower payload according to payload_ty
                        const args = a.exprs.expr_pool.slice(row.args);
                        var pay_v: tir.OptValueId = tir.OptValueId.none();
                        if (self.context.type_store.getKind(payload_ty) == .Void) {
                            // no payload
                        } else if (self.context.type_store.getKind(payload_ty) == .Tuple) {
                            const tr = self.context.type_store.get(.Tuple, payload_ty);
                            const subtys = self.context.type_store.type_pool.slice(tr.elems);
                            var elems = try self.gpa.alloc(tir.ValueId, subtys.len);
                            defer self.gpa.free(elems);
                            var j2: usize = 0;
                            while (j2 < subtys.len) : (j2 += 1) {
                                const arg_id = if (j2 < args.len) args[j2] else args[args.len - 1];
                                elems[j2] = try self.lowerExpr(a, env, f, blk, arg_id, subtys[j2], .rvalue);
                            }
                            const tuple_v = blk.builder.tupleMake(blk, payload_ty, elems);
                            pay_v = tir.OptValueId.some(tuple_v);
                        } else {
                            // single payload: take first arg
                            if (args.len > 0) {
                                const pv = try self.lowerExpr(a, env, f, blk, args[0], payload_ty, .rvalue);
                                pay_v = tir.OptValueId.some(pv);
                            }
                        }
                        return blk.builder.variantMake(blk, ety, tag_idx, pay_v, payload_ty);
                    }
                }
            }
        }

        // Try to get callee param types
        var param_tys: []const types.TypeId = &.{};
        var fixed: usize = 0;
        var is_variadic = false;
        if (callee.fty) |fty| {
            if (self.context.type_store.index.kinds.items[fty.toRaw()] == .Function) {
                const fr2 = self.context.type_store.Function.get(self.context.type_store.index.rows.items[fty.toRaw()]);
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

        // For varargs or unknown-typed parameters, avoid passing `any` into FFI:
        // if the arg's stamped type is `any`, re-lower with a literal-informed default.
        // ints -> i64, floats -> f64, bool -> bool, string -> string, else -> usize.
        var j: usize = fixed;
        while (j < vals.len) : (j += 1) {
            const got_opt = self.getExprType(arg_ids[j]);
            const got = got_opt orelse self.context.type_store.tAny();
            if (self.isAny(got)) {
                const k = a.exprs.index.kinds.items[arg_ids[j].toRaw()];
                const want: types.TypeId = switch (k) {
                    .Literal => blk: {
                        const lit = a.exprs.get(.Literal, arg_ids[j]);
                        break :blk switch (lit.kind) {
                            .int, .char => self.context.type_store.tI64(),
                            .float => self.context.type_store.tF64(),
                            .bool => self.context.type_store.tBool(),
                            .string => self.context.type_store.tString(),
                            .imaginary => self.context.type_store.tF64(), // placeholder
                        };
                    },
                    else => self.context.type_store.tUsize(),
                };
                // Re-lower the argument with a concrete expected type.
                vals[j] = try self.lowerExpr(a, env, f, blk, arg_ids[j], want, .rvalue);
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
                    const fr2 = self.context.type_store.Function.get(self.context.type_store.index.rows.items[fty.toRaw()]);
                    const rt = fr2.result; // adjust if your field is named differently
                    if (!self.isVoid(rt) and !self.isAny(rt)) break :blk rt;
                }
            }
            break :blk self.context.type_store.tVoid();
        };

        return blk.builder.call(blk, ret_ty, callee.name, vals);
    }

    fn lowerTypeExprOpaque(self: *@This(), blk: *Builder.BlockFrame, id: ast.ExprId, expected_ty: ?types.TypeId) tir.ValueId {
        const ty0 = self.getExprType(id) orelse self.context.type_store.tAny();
        const v = self.safeUndef(blk, ty0);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
        return v;
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
        const expr_kind = a.exprs.index.kinds.items[id.toRaw()];

        switch (expr_kind) {
            .Literal => {
                const lit = a.exprs.get(.Literal, id);
                // If the checker didn’t stamp a type, use the caller’s expected type.
                const ty0 = self.getExprType(id) orelse (expected_ty orelse return error.LoweringBug);
                const v = switch (lit.kind) {
                    .int => blk.builder.constInt(blk, ty0, try std.fmt.parseInt(u64, a.exprs.strs.get(lit.value.unwrap()), 10)),
                    .imaginary => blk: {
                        // ty0 must be Complex(elem). Build from (re=0, im=value)
                        const tk = self.context.type_store.getKind(ty0);
                        if (tk != .Complex) break :blk blk.builder.constUndef(blk, ty0);
                        const crow = self.context.type_store.get(.Complex, ty0);
                        const elem = crow.elem;
                        const s = a.exprs.strs.get(lit.value.unwrap());
                        // Parse as f64 and cast to elem as needed
                        const parsed = try std.fmt.parseFloat(f64, s);
                        const re0 = blk.builder.constFloat(blk, elem, 0.0);
                        const imv = blk.builder.constFloat(blk, elem, parsed);
                        const cv = blk.builder.complexMake(blk, ty0, re0, imv);
                        break :blk cv;
                    },
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
                        return blk.builder.addressOf(blk, self.context.type_store.mkPtr(ety, false), v);
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
                                const re0 = blk.builder.constFloat(blk, crow.elem, 0.0);
                                const im0 = blk.builder.constFloat(blk, crow.elem, 0.0);
                                break :zblk blk.builder.complexMake(blk, ty0, re0, im0);
                            }
                            if (self.isFloat(ty0)) break :zblk blk.builder.constFloat(blk, ty0, 0.0);
                            break :zblk blk.builder.constInt(blk, ty0, 0);
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
            },
            .Range => {
                const row = a.exprs.get(.Range, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const usize_ty = self.context.type_store.tUsize();
                const start_v = if (!row.start.isNone()) try self.lowerExpr(a, env, f, blk, row.start.unwrap(), usize_ty, .rvalue) else blk.builder.constUndef(blk, usize_ty);
                const end_v = if (!row.end.isNone()) try self.lowerExpr(a, env, f, blk, row.end.unwrap(), usize_ty, .rvalue) else blk.builder.constUndef(blk, usize_ty);
                const incl = blk.builder.constBool(blk, self.context.type_store.tBool(), row.inclusive_right);
                // Materialize range as TIR RangeMake (typed as []usize)
                const v = blk.builder.rangeMake(blk, ty0, start_v, end_v, incl);
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
                        const trow = self.context.type_store.Tuple.get(self.context.type_store.index.rows.items[ty0.toRaw()]);
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
                    fields[j] = .{ .index = @intCast(j), .name = OptStrId.none(), .value = vals[j] };
                }
                const v = blk.builder.structMake(blk, ty0, fields);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .ArrayLit => {
                const row = a.exprs.get(.ArrayLit, id);
                const ty0 = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tAny());
                const ids = a.exprs.expr_pool.slice(row.elems);
                var vals = try self.gpa.alloc(tir.ValueId, ids.len);
                defer self.gpa.free(vals);
                var i: usize = 0;
                var expect_elem = self.context.type_store.tAny();
                const vk = self.context.type_store.index.kinds.items[ty0.toRaw()];
                if (vk == .Array) expect_elem = self.context.type_store.Array.get(self.context.type_store.index.rows.items[ty0.toRaw()]).elem;
                while (i < ids.len) : (i += 1) vals[i] = try self.lowerExpr(a, env, f, blk, ids[i], expect_elem, .rvalue);
                const v = blk.builder.arrayMake(blk, ty0, vals);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .StructLit => {
                const row = a.exprs.get(.StructLit, id);
                // const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const ty0 = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tAny());

                const fids = a.exprs.sfv_pool.slice(row.fields);
                var fields = try self.gpa.alloc(tir.Rows.StructFieldInit, fids.len);
                defer self.gpa.free(fields);
                var i: usize = 0;
                // Determine expected field types if available
                var field_ids: []const cst.Index(types.FieldTag) = &[_]cst.Index(types.FieldTag){};
                if (self.context.type_store.index.kinds.items[ty0.toRaw()] == .Struct) {
                    const srow = self.context.type_store.Struct.get(self.context.type_store.index.rows.items[ty0.toRaw()]);
                    field_ids = self.context.type_store.field_pool.slice(srow.fields);
                }
                while (i < fids.len) : (i += 1) {
                    const sfv = a.exprs.StructFieldValue.get(fids[i].toRaw());
                    const want = if (i < field_ids.len) self.context.type_store.Field.get(field_ids[i].toRaw()).ty else self.context.type_store.tAny();
                    const v = try self.lowerExpr(a, env, f, blk, sfv.value, want, .rvalue);
                    fields[i] = .{ .index = @intCast(i), .name = sfv.name, .value = v };
                }
                const v = blk.builder.structMake(blk, ty0, fields);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .MapLit => {
                const row = a.exprs.get(.MapLit, id);
                const ty0 = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tAny());
                const kv_ids = a.exprs.kv_pool.slice(row.entries);
                var vals = try self.gpa.alloc(tir.ValueId, kv_ids.len * 2);
                defer self.gpa.free(vals);
                var j: usize = 0;
                for (kv_ids) |kid| {
                    const kv = a.exprs.KeyValue.get(kid.toRaw());
                    // best-effort: use expected key/value if map type is known
                    var key_want = self.context.type_store.tAny();
                    var val_want = self.context.type_store.tAny();
                    const mk = self.context.type_store.index.kinds.items[ty0.toRaw()];
                    if (mk == .Map) {
                        const mr = self.context.type_store.Map.get(self.context.type_store.index.rows.items[ty0.toRaw()]);
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
                    // Prefer a usize constant for literal indices to avoid casts in TIR
                    const idx_v = blk: {
                        const ik = a.exprs.index.kinds.items[row.index.toRaw()];
                        if (ik == .Literal) {
                            const lit = a.exprs.get(.Literal, row.index);
                            if (lit.kind == .int) {
                                const s = a.exprs.strs.get(lit.value.unwrap());
                                const uv = blk.builder.constInt(blk, self.context.type_store.tUsize(), try std.fmt.parseInt(u64, s, 10));
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
                                    const uv = blk.builder.constInt(blk, self.context.type_store.tUsize(), try std.fmt.parseInt(u64, s, 10));
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
            },

            .FieldAccess => {
                const row = a.exprs.get(.FieldAccess, id);

                // ---------- 1) Imported module member (rvalue only) ----------
                if (mode == .rvalue and a.exprs.index.kinds.items[row.parent.toRaw()] == .Ident) {
                    const idr = a.exprs.get(.Ident, row.parent);
                    const name = a.exprs.strs.get(idr.name);
                    if (self.findTopLevelImportByName(a, name)) |imp_decl| {
                        const ty0 = self.getExprType(id) orelse (expected_ty orelse self.context.type_store.tAny());
                        if (self.materializeImportedConst(&self.context.resolver, a, imp_decl, row.field, ty0, blk, self.pipeline)) |vv| {
                            if (expected_ty) |want| return self.emitCoerce(blk, vv, ty0, want);
                            return vv;
                        }
                        const v = blk.builder.constUndef(blk, ty0);
                        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                        return v;
                    }
                }

                // Checker-resolved field index (if any)
                const idx_maybe = self.type_info.getFieldIndex(id);

                // ---------- 2) EnumName.Member => constant ----------
                if (mode == .rvalue) {
                    const parent_kind = a.exprs.index.kinds.items[row.parent.toRaw()];
                    var is_enum_parent = (parent_kind == .EnumType);

                    if (!is_enum_parent) {
                        if (self.getExprType(row.parent)) |pty| {
                            is_enum_parent = (self.context.type_store.index.kinds.items[pty.toRaw()] == .Enum);
                        }
                    }
                    if (is_enum_parent) {
                        const ty0 = self.getExprType(id) orelse (expected_ty orelse self.context.type_store.tAny());
                        const idx = idx_maybe orelse return error.LoweringBug; // enum members should be indexed by the checker
                        var ev = blk.builder.constInt(blk, ty0, @intCast(idx));
                        if (expected_ty) |want| ev = self.emitCoerce(blk, ev, ty0, want);
                        return ev;
                    }
                }

                // ---------- 3) Address path: must have an index (for GEP) ----------
                if (mode == .lvalue_addr) {
                    const parent_ptr = try self.lowerExpr(a, env, f, blk, row.parent, null, .lvalue_addr);
                    const elem_ty = self.getExprType(id) orelse return error.LoweringBug;
                    const idx = idx_maybe orelse return error.LoweringBug; // need concrete field index for lvalue
                    const rptr_ty = self.context.type_store.mkPtr(elem_ty, false);
                    return blk.builder.gep(blk, rptr_ty, parent_ptr, &.{blk.builder.gepConst(@intCast(idx))});
                }

                // ---------- 4) Rvalue struct/tuple access ----------
                const ty0 = self.getExprType(id) orelse (expected_ty orelse self.context.type_store.tAny());
                const base = try self.lowerExpr(a, env, f, blk, row.parent, null, .rvalue);

                // We only need the parent type to distinguish tuple vs struct; if unknown, assume non-tuple.
                const parent_ty_opt = self.getExprType(row.parent);
                const is_tuple = if (parent_ty_opt) |pt|
                    self.context.type_store.index.kinds.items[pt.toRaw()] == .Tuple
                else
                    false;

                var v: tir.ValueId = undefined;
                if (idx_maybe) |resolved_idx| {
                    v = if (is_tuple)
                        blk.builder.extractElem(blk, ty0, base, resolved_idx)
                    else
                        blk.builder.extractField(blk, ty0, base, resolved_idx);
                } else {
                    // No index from the checker. Tuples have no names -> we must error.
                    if (is_tuple) return error.LoweringBug;
                    // Struct: fall back to extraction by name (no need for parent_ty).
                    v = blk.builder.extractFieldNamed(blk, ty0, base, row.field);
                }

                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want);
                return v;
            },
            .Block => {
                const res_ty = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
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
                            const dty = self.getExprType(d.value) orelse return error.LoweringBug;
                            // Materialize the entire decl's pattern into the env (as slots for mut, values for const)
                            try self.destructureDeclFromExpr(a, env, f, blk, d.pattern.unwrap(), d.value, dty, !d.flags.is_const);
                            bnd = env.lookup(name);
                        }
                    }
                    const binding = bnd orelse return error.LoweringBug;
                    if (binding.is_slot) return binding.value;

                    // We need a slot for a value-only binding; pick a best-effort element type.
                    const ety2 = self.getExprType(id) orelse blk: {
                        if (expected_ty) |want| {
                            // If caller expects a pointer here, use its pointee as the slot element type.
                            if (self.context.type_store.getKind(want) == .Ptr) {
                                const ptr = self.context.type_store.get(.Ptr, want);
                                break :blk ptr.elem;
                            }
                        }
                        break :blk self.context.type_store.tAny();
                    };

                    const slot_ty2 = self.context.type_store.mkPtr(ety2, false);
                    const slot2 = f.builder.alloca(blk, slot_ty2, tir.OptValueId.none(), 0);

                    // Store the value into the slot; coerce if caller told us a target type.
                    var to_store = binding.value;
                    if (expected_ty) |want| {
                        // If expected is a pointer, store as its element type; else try best-effort.
                        if (self.context.type_store.getKind(want) == .Ptr) {
                            const ptr = self.context.type_store.get(.Ptr, want);
                            to_store = self.emitCoerce(blk, binding.value, ety2, ptr.elem);
                            _ = f.builder.store(blk, ptr.elem, slot2, to_store, 0);
                        } else {
                            to_store = self.emitCoerce(blk, binding.value, ety2, ety2);
                            _ = f.builder.store(blk, ety2, slot2, to_store, 0);
                        }
                    } else {
                        _ = f.builder.store(blk, ety2, slot2, to_store, 0);
                    }

                    try env.bind(self.gpa, a, row.name, .{ .value = slot2, .is_slot = true });
                    return slot2;
                } else {
                    const bnd = blk: {
                        if (env.lookup(name)) |v| break :blk v;

                        // Top-level decl?
                        if (self.findTopLevelDeclByName(a, name)) |did| {
                            const d = a.exprs.Decl.get(did.toRaw());
                            const dty = self.getExprType(d.value) orelse self.context.type_store.tAny();
                            // Destructure and bind all names for this top-level decl; mutable -> slots.
                            try self.destructureDeclFromExpr(a, env, f, blk, d.pattern.unwrap(), d.value, dty, !d.flags.is_const);
                            break :blk env.lookup(name).?;
                        }

                        // Not a value binding or top-level decl (likely a type name or similar).
                        // Produce a safe placeholder instead of failing. This keeps lowering going,
                        // and callers will typically just use it as a type-operand or ignore it.
                        const ty0 = self.getExprType(id) orelse self.context.type_store.tAny();
                        const placeholder = self.safeUndef(blk, ty0);
                        try env.bind(self.gpa, a, row.name, .{ .value = placeholder, .is_slot = false });
                        break :blk env.lookup(name).?;
                    };

                    if (bnd.is_slot) {
                        // ⬅️ this was the crash site: fall back to expected_ty or Any
                        const ety = self.getExprType(id) orelse (expected_ty orelse self.context.type_store.tAny());
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

                const stamped_result = self.getExprType(id);
                var lhs_expect: ?types.TypeId = null;
                var rhs_expect: ?types.TypeId = null;
                var op_ty: ?types.TypeId = stamped_result;
                switch (row.op) {
                    // Arithmetic / bitwise -> both sides usually share the resulting numeric type.
                    .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor => {
                        // If checker stamped Complex result, drive both operands to Complex
                        if (op_ty) |t| if (self.context.type_store.index.kinds.items[t.toRaw()] == .Complex) {
                            lhs_expect = t;
                            rhs_expect = t;
                        } else {
                            const want = self.commonNumeric(self.getExprType(row.left), self.getExprType(row.right)) orelse (expected_ty orelse self.context.type_store.tI64());
                            lhs_expect = want;
                            rhs_expect = want;
                            // If the checker didn't stamp a concrete result type (void/any), use `want`.
                            if (op_ty == null or self.isVoid(op_ty.?) or self.isAny(op_ty.?)) op_ty = want;
                        } else {
                            const want = self.commonNumeric(self.getExprType(row.left), self.getExprType(row.right)) orelse (expected_ty orelse self.context.type_store.tI64());
                            lhs_expect = want;
                            rhs_expect = want;
                            if (op_ty == null or self.isVoid(op_ty.?) or self.isAny(op_ty.?)) op_ty = want;
                        }
                    },

                    // Comparisons: result is bool; operands should be comparable (prefer outer hint if any).
                    .eq, .neq, .lt, .lte, .gt, .gte => {
                        const want = self.commonNumeric(self.getExprType(row.left), self.getExprType(row.right)) orelse (self.getExprType(row.left) orelse self.getExprType(row.right));
                        lhs_expect = want;
                        rhs_expect = want;
                        op_ty = self.context.type_store.tBool();
                    },

                    // Short-circuit bools
                    .logical_and, .logical_or => {
                        const bty = self.context.type_store.tBool();
                        lhs_expect = bty;
                        rhs_expect = bty;
                        op_ty = self.context.type_store.tBool();
                    },

                    // Optional “orelse”: left is optional; right yields overall result type.
                    .@"orelse" => {
                        lhs_expect = self.getExprType(row.left); // keep checker-stamped opt
                        rhs_expect = expected_ty; // prefer outer expectation for value
                        // When result type wasn't stamped, prefer caller expectation if any.
                        if (op_ty == null or self.isVoid(op_ty.?)) op_ty = (expected_ty orelse self.context.type_store.tAny());
                    },
                }

                // Lower with those expectations
                const l = try self.lowerExpr(a, env, f, blk, row.left, lhs_expect, .rvalue);
                const r = try self.lowerExpr(a, env, f, blk, row.right, rhs_expect, .rvalue);

                const ty0 = blk: {
                    if (op_ty) |t| break :blk t;
                    // absolute fallback to avoid void arithmetic
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
                        // optional-or-else
                        var then_blk = try f.builder.beginBlock(f);
                        var else_blk = try f.builder.beginBlock(f);
                        var join_blk = try f.builder.beginBlock(f);
                        const s_is_some = f.builder.intern("builtin.opt.is_some");
                        const cond_v = blk.builder.call(blk, self.context.type_store.tBool(), s_is_some, &.{l});
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
                    if (!self.isVoid(ty0))
                        return self.emitCoerce(blk, v, ty0, want);
                }
                return v;
            },

            .Catch => {
                const row = a.exprs.get(.Catch, id);

                const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
                const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

                const lhs = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
                const s_is_ok = f.builder.intern("builtin.err.is_ok");

                var then_blk = try f.builder.beginBlock(f); // ok path
                var else_blk = try f.builder.beginBlock(f); // handler path

                if (produce_value) {
                    var join_blk = try f.builder.beginBlock(f);
                    const res_ty = out_ty_guess;
                    const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

                    const is_ok = blk.builder.call(blk, self.context.type_store.tBool(), s_is_ok, &.{lhs});
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
                    const is_ok = blk.builder.call(blk, self.context.type_store.tBool(), s_is_ok, &.{lhs});
                    try f.builder.condBr(blk, is_ok, then_blk.id, &.{}, else_blk.id, &.{});

                    // then: nothing to do, jump to exit
                    if (then_blk.term.isNone()) try f.builder.br(&then_blk, exit_blk.id, &.{});
                    try f.builder.endBlock(f, then_blk);

                    // else: execute handler as stmt
                    try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
                    if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{});
                    try f.builder.endBlock(f, else_blk);

                    blk.* = exit_blk;
                    return self.safeUndef(blk, self.context.type_store.tAny());
                }
            },
            .If => {
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
                    return self.safeUndef(blk, self.context.type_store.tAny());
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

                    // -------- Try the "all literal int patterns with no guards" fast path --------
                    var all_int = true;
                    var values = try self.gpa.alloc(u64, arms.len);
                    defer self.gpa.free(values);

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
                        values[i] = std.fmt.parseInt(u64, s, 10) catch {
                            all_int = false;
                            break;
                        };
                    }

                    if (all_int) {
                        var case_dests = try self.gpa.alloc(Builder.SwitchDest, arms.len);
                        defer self.gpa.free(case_dests);

                        var bodies = try self.gpa.alloc(@TypeOf(try f.builder.beginBlock(f)), arms.len);
                        defer self.gpa.free(bodies);

                        i = 0;
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
                            const arm = a.exprs.MatchArm.get(arms[i].toRaw());
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
                        const arm = a.exprs.MatchArm.get(arm_id.toRaw());

                        var test_blk = try f.builder.beginBlock(f);
                        var body_blk = try f.builder.beginBlock(f);
                        const next_blk = if (j + 1 < arms.len) try f.builder.beginBlock(f) else join_blk;

                        try f.builder.br(&cur, test_blk.id, &.{});

                        // pattern test
                        var ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut);
                        if (!arm.guard.isNone()) {
                            const g = try self.lowerExpr(a, env, f, &test_blk, arm.guard.unwrap(), self.context.type_store.tBool(), .rvalue);
                            ok = test_blk.builder.binBool(&test_blk, .LogicalAnd, ok, g);
                        }

                        // if last arm fails, feed an undef to the join
                        const else_args = if (next_blk.id.toRaw() == join_blk.id.toRaw()) blkargs: {
                            const uv = self.safeUndef(&test_blk, res_ty);
                            break :blkargs &.{uv};
                        } else &.{};

                        try f.builder.condBr(&test_blk, ok, body_blk.id, &.{}, next_blk.id, else_args);

                        // bind + body
                        const scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                        try self.bindPattern(a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);

                        try self.lowerExprAsStmtList(a, env, f, &body_blk, arm.body);
                        if (body_blk.term.isNone()) {
                            var v2 = try self.lowerBlockExprValue(a, env, f, &body_blk, arm.body, res_ty);
                            v2 = self.emitCoerce(&body_blk, v2, self.getExprType(arm.body) orelse res_ty, res_ty);
                            try f.builder.br(&body_blk, join_blk.id, &.{v2});
                        }

                        try f.builder.endBlock(f, test_blk);
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

                    // Fast-path ints?
                    var all_int = true;
                    var values = try self.gpa.alloc(u64, arms.len);
                    defer self.gpa.free(values);

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
                        values[i] = std.fmt.parseInt(u64, s, 10) catch {
                            all_int = false;
                            break;
                        };
                    }

                    if (all_int) {
                        var case_dests = try self.gpa.alloc(Builder.SwitchDest, arms.len);
                        defer self.gpa.free(case_dests);
                        var bodies = try self.gpa.alloc(@TypeOf(try f.builder.beginBlock(f)), arms.len);
                        defer self.gpa.free(bodies);

                        i = 0;
                        while (i < arms.len) : (i += 1) bodies[i] = try f.builder.beginBlock(f);
                        var default_blk = try f.builder.beginBlock(f);

                        try f.builder.switchInt(blk, scrut, values, blk: {
                            i = 0;
                            while (i < arms.len) : (i += 1) case_dests[i] = .{ .dest = bodies[i].id, .args = &.{} };
                            break :blk case_dests;
                        }, default_blk.id, &.{});

                        i = 0;
                        while (i < arms.len) : (i += 1) {
                            const arm = a.exprs.MatchArm.get(arms[i].toRaw());
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
                        const arm = a.exprs.MatchArm.get(arm_id.toRaw());

                        var test_blk = try f.builder.beginBlock(f);
                        var body_blk = try f.builder.beginBlock(f);
                        const next_blk = if (l + 1 < arms.len) try f.builder.beginBlock(f) else exit_blk;

                        try f.builder.br(&cur, test_blk.id, &.{});

                        var ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut);
                        if (!arm.guard.isNone()) {
                            const g = try self.lowerExpr(a, env, f, &test_blk, arm.guard.unwrap(), self.context.type_store.tBool(), .rvalue);
                            ok = test_blk.builder.binBool(&test_blk, .LogicalAnd, ok, g);
                        }

                        try f.builder.condBr(&test_blk, ok, body_blk.id, &.{}, next_blk.id, &.{});

                        const scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                        try self.bindPattern(a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);

                        try self.lowerExprAsStmtList(a, env, f, &body_blk, arm.body);
                        if (body_blk.term.isNone()) try f.builder.br(&body_blk, exit_blk.id, &.{});

                        try f.builder.endBlock(f, test_blk);
                        try f.builder.endBlock(f, body_blk);
                        cur = next_blk;
                    }

                    blk.* = exit_blk;
                    return self.safeUndef(blk, self.context.type_store.tAny());
                }
            },
            .While => {
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

                    const cond_v = if (!row.cond.isNone())
                        try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), self.context.type_store.tBool(), .rvalue)
                    else
                        f.builder.constBool(&header, self.context.type_store.tBool(), true);

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
                        try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), self.context.type_store.tBool(), .rvalue)
                    else
                        f.builder.constBool(&header, self.context.type_store.tBool(), true);

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
                    return self.safeUndef(blk, self.context.type_store.tAny());
                }
            },
            .For => {
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
                        const idx_ty = self.context.type_store.tUsize();
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
                        var elem_ty = self.context.type_store.tAny();
                        if (self.getExprType(row.iterable)) |it_ty| {
                            const ik = self.context.type_store.index.kinds.items[it_ty.toRaw()];
                            if (ik == .Array) elem_ty = self.context.type_store.Array.get(self.context.type_store.index.rows.items[it_ty.toRaw()]).elem else if (ik == .Slice) elem_ty = self.context.type_store.Slice.get(self.context.type_store.index.rows.items[it_ty.toRaw()]).elem else if (ik == .DynArray) elem_ty = self.context.type_store.DynArray.get(self.context.type_store.index.rows.items[it_ty.toRaw()]).elem;
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
                        const idx_ty = self.context.type_store.tUsize();
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

                        var elem_ty = self.context.type_store.tAny();
                        if (self.getExprType(row.iterable)) |it_ty| {
                            const ik = self.context.type_store.index.kinds.items[it_ty.toRaw()];
                            if (ik == .Array) elem_ty = self.context.type_store.Array.get(self.context.type_store.index.rows.items[it_ty.toRaw()]).elem else if (ik == .Slice) elem_ty = self.context.type_store.Slice.get(self.context.type_store.index.rows.items[it_ty.toRaw()]).elem else if (ik == .DynArray) elem_ty = self.context.type_store.DynArray.get(self.context.type_store.index.rows.items[it_ty.toRaw()]).elem;
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
                    return self.safeUndef(blk, self.context.type_store.tAny());
                }
            },
            .Import => {
                // Lowered as 'any' module value (opaque); create undef of the checker type
                const ty0 = self.getExprType(id) orelse self.context.type_store.tAny();
                return blk.builder.constUndef(blk, ty0);
            },
            // No special VariantLit nodes expected in expressions after CST->AST; handled via struct/call forms.
            .VariantType, .EnumType, .StructType => {
                return self.lowerTypeExprOpaque(blk, id, expected_ty);
            },
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

    fn findTopLevelDeclByName(self: *const @This(), a: *const ast.Ast, name: []const u8) ?ast.DeclId {
        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        var i: usize = 0;
        while (i < decls.len) : (i += 1) {
            const d = a.exprs.Decl.get(decls[i].toRaw());
            if (d.pattern.isNone()) continue;
            const pid = d.pattern.unwrap();
            if (self.patternContainsName(a, pid, name)) return decls[i];
        }
        return null;
    }

    fn patternContainsName(self: *const @This(), a: *const ast.Ast, pid: ast.PatternId, name: []const u8) bool {
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        switch (pk) {
            .Binding => {
                const b = a.pats.get(.Binding, pid);
                return std.mem.eql(u8, a.exprs.strs.get(b.name), name);
            },
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
                    const frow = a.pats.StructField.get(fid.toRaw());
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
                    const frow = a.pats.StructField.get(fid.toRaw());
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
                if (std.mem.eql(u8, a.exprs.strs.get(row.binder), name)) return true;
                return self.patternContainsName(a, row.pattern, name);
            },
            else => return false,
        }
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

    /// True if `ty` is a numeric scalar type.
    fn isNumeric(self: *const @This(), ty: types.TypeId) bool {
        if (self.isVoid(ty)) return false;
        const k = self.context.type_store.index.kinds.items[ty.toRaw()];
        return switch (k) {
            .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64, .Usize, .F32, .F64 => true,
            else => false,
        };
    }

    fn isFloat(self: *const @This(), ty: types.TypeId) bool {
        const k = self.context.type_store.index.kinds.items[ty.toRaw()];
        return (k == .F32) or (k == .F64);
    }

    fn isAny(self: *const @This(), ty: types.TypeId) bool {
        return self.context.type_store.index.kinds.items[ty.toRaw()] == .Any;
    }

    /// Choose a common numeric type for binary ops when the checker didn't provide one.
    fn commonNumeric(
        self: *const @This(),
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
                        if (lt.toRaw() == cand.toRaw() or rt.toRaw() == cand.toRaw()) return cand;
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

    fn lowerImportedExprValue(self: *@This(), me: *@import("import_resolver.zig").ModuleEntry, eid: ast.ExprId, expected_ty: types.TypeId, blk: *Builder.BlockFrame) ?tir.ValueId {
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
                    const f = self.context.type_store.Field.get(exp_fields[j].toRaw());
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
                const k = self.context.type_store.getKind(expected_ty);
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
        if (i >= self.type_info.expr_types.items.len) return null;
        return self.type_info.expr_types.items[i];
    }
    fn getDeclType(self: *const @This(), did: ast.DeclId) ?types.TypeId {
        const i = did.toRaw();
        if (i >= self.type_info.decl_types.items.len) return null;
        return self.type_info.decl_types.items[i];
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
                const vk = self.context.type_store.index.kinds.items[vty.toRaw()];
                if (vk == .Tuple) {
                    const vrow = self.context.type_store.Tuple.get(self.context.type_store.index.rows.items[vty.toRaw()]);
                    etys = self.context.type_store.type_pool.slice(vrow.elems);
                }
                while (i < elems.len) : (i += 1) {
                    const ety = if (i < etys.len) etys[i] else self.context.type_store.tAny();
                    const ev = blk.builder.extractElem(blk, ety, value, @intCast(i));
                    try self.bindPattern(a, env, f, blk, elems[i], ev, ety);
                }
            },
            else => {},
        }
    }

    // Destructure a declaration pattern and bind its sub-bindings either as values (const) or slots (mutable).
    fn destructureDeclPattern(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, value: tir.ValueId, vty: types.TypeId, to_slots: bool) !void {
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        switch (pk) {
            .Binding => {
                const nm = a.pats.get(.Binding, pid).name;
                if (to_slots) {
                    const slot_ty = self.context.type_store.mkPtr(vty, false);
                    const slot = f.builder.alloca(blk, slot_ty, tir.OptValueId.none(), 0);
                    _ = f.builder.store(blk, vty, slot, value, 0);
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
                    const vrow = self.context.type_store.Tuple.get(self.context.type_store.index.rows.items[vty.toRaw()]);
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
                    const pf = a.pats.StructField.get(fid.toRaw());
                    // Determine field type and extraction method
                    var fty = self.context.type_store.tAny();
                    var extracted: tir.ValueId = undefined;
                    if (idx_by_name) |field_ids| {
                        // scan for matching name
                        var found = false;
                        var j: usize = 0;
                        while (j < field_ids.len) : (j += 1) {
                            const stf = self.context.type_store.Field.get(field_ids[j].toRaw());
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
    fn destructureDeclFromExpr(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, src_expr: ast.ExprId, vty: types.TypeId, to_slots: bool) !void {
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        switch (pk) {
            .Binding => {
                const val = try self.lowerExpr(a, env, f, blk, src_expr, vty, .rvalue);
                return try self.destructureDeclPattern(a, env, f, blk, pid, val, vty, to_slots);
            },
            .Tuple => {
                // If RHS is a tuple-literal, lower elements individually to avoid creating a temporary aggregate.
                if (a.exprs.index.kinds.items[src_expr.toRaw()] == .TupleLit) {
                    const row = a.pats.get(.Tuple, pid);
                    const elems_pat = a.pats.pat_pool.slice(row.elems);
                    const elr = a.exprs.get(.TupleLit, src_expr);
                    const elems_expr = a.exprs.expr_pool.slice(elr.elems);
                    var etys: []const types.TypeId = &[_]types.TypeId{};
                    const vk = self.context.type_store.index.kinds.items[vty.toRaw()];
                    if (vk == .Tuple) {
                        const vrow = self.context.type_store.Tuple.get(self.context.type_store.index.rows.items[vty.toRaw()]);
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
                    return;
                }
                // Fallback: lower full expr once, then destructure via extracts.
                const val = try self.lowerExpr(a, env, f, blk, src_expr, vty, .rvalue);
                return try self.destructureDeclPattern(a, env, f, blk, pid, val, vty, to_slots);
            },
            .Struct => {
                if (a.exprs.index.kinds.items[src_expr.toRaw()] == .StructLit) {
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
                        const pf = a.pats.StructField.get(pfid.toRaw());
                        // find expr field by name
                        var val_expr: ?ast.ExprId = null;
                        for (sfields) |sfid| {
                            const sf = a.exprs.StructFieldValue.get(sfid.toRaw());
                            if (sf.name.toRaw() == pf.name.toRaw()) {
                                val_expr = sf.value;
                                break;
                            }
                        }
                        var fty = self.context.type_store.tAny();
                        // find field type by name if known
                        for (type_fields) |tfid| {
                            const tf = self.context.type_store.Field.get(tfid.toRaw());
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
                const case_name = a.pats.PathSeg.get(p_segs[p_segs.len - 1].toRaw()).name;
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
                                const fld = self.context.type_store.Field.get(fields[j].toRaw());
                                if (fld.name.toRaw() == case_name.toRaw() and self.context.type_store.getKind(fld.ty) == .Tuple) {
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
                        const fld = self.context.type_store.Field.get(fields[j].toRaw());
                        if (fld.name.toRaw() == case_name.toRaw() and self.context.type_store.getKind(fld.ty) == .Tuple) {
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
                const case_name = a.pats.PathSeg.get(segs[segs.len - 1].toRaw()).name;
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
                                    const vf = self.context.type_store.Field.get(variants[j].toRaw());
                                    if (vf.name.toRaw() == case_name.toRaw() and self.context.type_store.getKind(vf.ty) == .Struct) {
                                        const sr = self.context.type_store.get(.Struct, vf.ty);
                                        field_tys = self.context.type_store.field_pool.slice(sr.fields);
                                        break;
                                    }
                                }
                            }
                            const pfields = a.pats.field_pool.slice(pr.fields);
                            const sfields = a.exprs.sfv_pool.slice(sl.fields);
                            for (pfields) |pfid| {
                                const pf = a.pats.StructField.get(pfid.toRaw());
                                // find matching expr field by name
                                var val_expr: ?ast.ExprId = null;
                                for (sfields) |sfid| {
                                    const sf = a.exprs.StructFieldValue.get(sfid.toRaw());
                                    if (sf.name.toRaw() == pf.name.toRaw()) { val_expr = sf.value; break; }
                                }
                                var fty = self.context.type_store.tAny();
                                // lookup field type by name
                                for (field_tys) |tfid| {
                                    const tf = self.context.type_store.Field.get(tfid.toRaw());
                                    if (tf.name.toRaw() == pf.name.toRaw()) { fty = tf.ty; break; }
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
                    const pf = a.pats.StructField.get(pfid.toRaw());
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

    fn matchPattern(self: *@This(), a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, scrut: tir.ValueId) !tir.ValueId {
        const k = a.pats.index.kinds.items[pid.toRaw()];
        switch (k) {
            .Wildcard => return blk.builder.constBool(blk, self.context.type_store.tBool(), true),
            .Literal => {
                const pr = a.pats.get(.Literal, pid);
                const litv = try self.lowerExpr(a, env, f, blk, pr.expr, null, .rvalue);
                return blk.builder.binBool(blk, .CmpEq, scrut, litv);
            },
            .Binding, .Path, .Tuple, .Slice, .Struct, .VariantTuple, .VariantStruct, .Range, .Or, .At => {
                return blk.builder.constBool(blk, self.context.type_store.tBool(), true);
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
    fn rangeMake(self: *@This(), blk: *BlockFrame, ty: types.TypeId, start: tir.ValueId, end: tir.ValueId, inclusive: tir.ValueId) tir.ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.RangeMake, tir.Rows.RangeMake{ .result = vid, .ty = ty, .start = start, .end = end, .inclusive = inclusive });
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
        fn extractFieldNamed(self: *@This(), blk: *BlockFrame, ty: types.TypeId, agg: tir.ValueId, name: StrId) tir.ValueId {
            const vid = self.freshValue();
            const iid = self.t.instrs.add(
                .ExtractField,
                tir.Rows.ExtractField{
                    .result = vid,
                    .ty = ty,
                    .agg = agg,
                    .index = 0, // ignored when name is provided
                    .name = OptStrId.some(name),
                },
            );
            blk.instrs.append(self.gpa, iid) catch @panic("OOM");
            return vid;
        }
        fn complexMake(self: *@This(), blk: *BlockFrame, ty: types.TypeId, re: tir.ValueId, im: tir.ValueId) tir.ValueId {
            const vid = self.freshValue();
            const iid = self.t.instrs.add(.ComplexMake, tir.Rows.ComplexMake{ .result = vid, .ty = ty, .re = re, .im = im });
            blk.instrs.append(self.gpa, iid) catch @panic("OOM");
            return vid;
        }
        fn variantMake(self: *@This(), blk: *BlockFrame, ty: types.TypeId, tag: u32, payload: tir.OptValueId, payload_ty: types.TypeId) tir.ValueId {
            const vid = self.freshValue();
            const iid = self.t.instrs.add(.VariantMake, tir.Rows.VariantMake{ .result = vid, .ty = ty, .tag = tag, .payload = payload, .payload_ty = payload_ty });
            blk.instrs.append(self.gpa, iid) catch @panic("OOM");
            return vid;
        }
        fn variantTag(self: *@This(), blk: *BlockFrame, value: tir.ValueId) tir.ValueId {
            const vid = self.freshValue();
            const ty = self.t.t.funcs.tstore.*.tI32();
            const iid = self.t.instrs.add(.VariantTag, tir.Rows.VariantTag{ .result = vid, .ty = ty, .value = value });
            blk.instrs.append(self.gpa, iid) catch @panic("OOM");
            return vid;
        }
        fn variantPayloadPtr(self: *@This(), blk: *BlockFrame, result_ptr_ty: types.TypeId, value: tir.ValueId) tir.ValueId {
            const vid = self.freshValue();
            const iid = self.t.instrs.add(.VariantPayloadPtr, tir.Rows.VariantPayloadPtr{ .result = vid, .ty = result_ptr_ty, .value = value });
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

    pub fn addCall(self: *Builder, blk: *BlockFrame, result: tir.ValueId, ty: types.TypeId, callee: tir.StrId, args: []const tir.ValueId) tir.InstrId {
        const r = self.t.instrs.val_list_pool.pushMany(self.gpa, args);
        const row: tir.Rows.Call = .{ .result = result, .ty = ty, .callee = callee, .args = r };
        const id = self.t.instrs.add(.Call, row);
        blk.instrs.append(self.gpa, id) catch @panic("OOM");
        return id;
    }

    pub fn addMlirBlock(self: *Builder, blk: *BlockFrame, result: tir.ValueId, ty: types.TypeId, kind: ast.MlirKind, text: tir.StrId) tir.InstrId {
        const row: tir.Rows.MlirBlock = .{ .result = .some(result), .ty = ty, .kind = kind, .text = text };
        const id = self.t.instrs.add(.MlirBlock, row);
        blk.instrs.append(self.gpa, id) catch @panic("OOM");
        return id;
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
