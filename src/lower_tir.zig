const std = @import("std");
const ast = @import("ast.zig");
const cst = @import("cst.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const check_pattern_matching = @import("check_pattern_matching.zig");
const checker = @import("checker.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const mlir_codegen = @import("mlir_codegen.zig");
const comp = @import("comptime.zig");
const monomorphize = @import("monomorphize.zig");

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
    module_id: usize,
    chk: *checker.Checker,

    // Simple loop stack to support break/continue in While/For (+ value loops)
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},

    // Mapping: module ident name -> prefix for mangling (module.func -> prefix_func)
    module_prefix: std.StringHashMapUnmanaged([]const u8) = .{},
    module_call_cache: std.AutoHashMap(u64, StrId),
    method_lowered: std.AutoHashMap(usize, void),
    monomorphizer: monomorphize.Monomorphizer,
    monomorph_context_stack: std.ArrayListUnmanaged(monomorphize.MonomorphizationContext) = .{},
    expr_type_override_stack: std.ArrayListUnmanaged(ExprTypeOverrideFrame) = .{},

    import_base_dir: []const u8 = ".",

    var g_mlir_inited: bool = false;
    var g_mlir_ctx: mlir.Context = undefined;

    const BindingSnapshot = struct {
        name: ast.StrId,
        prev: ?ValueBinding,
    };

    const ExprTypeOverrideFrame = struct {
        map: std.AutoArrayHashMapUnmanaged(u32, types.TypeId) = .{},

        fn deinit(self: *ExprTypeOverrideFrame, gpa: std.mem.Allocator) void {
            self.map.deinit(gpa);
        }
    };

    fn pushExprTypeOverrideFrame(self: *LowerTir) !void {
        try self.expr_type_override_stack.append(self.gpa, .{});
    }

    fn popExprTypeOverrideFrame(self: *LowerTir) void {
        if (self.expr_type_override_stack.items.len == 0) return;
        const idx = self.expr_type_override_stack.items.len - 1;
        self.expr_type_override_stack.items[idx].deinit(self.gpa);
        self.expr_type_override_stack.items.len -= 1;
    }

    fn pushComptimeBindings(self: *LowerTir, bindings: []const Pipeline.ComptimeBinding) !bool {
        if (bindings.len == 0) return false;

        var infos = try self.gpa.alloc(monomorphize.BindingInfo, bindings.len);
        var init_count: usize = 0;
        const info_cleanup = true;
        defer {
            if (info_cleanup) {
                var j: usize = 0;
                while (j < init_count) : (j += 1) infos[j].deinit(self.gpa);
                self.gpa.free(infos);
            }
        }

        for (bindings, 0..) |binding, i| {
            switch (binding) {
                .type_param => |tp| {
                    infos[i] = monomorphize.BindingInfo.typeParam(tp.name, tp.ty);
                },
                .value_param => |vp| {
                    infos[i] = try monomorphize.BindingInfo.valueParam(self.gpa, vp.name, vp.ty, vp.value);
                },
            }
            init_count = i + 1;
        }

        var ctx = try monomorphize.MonomorphizationContext.init(
            self.gpa,
            infos[0..init_count],
            0,
            self.context.type_store.tVoid(),
        );
        errdefer ctx.deinit(self.gpa);

        self.monomorph_context_stack.append(self.gpa, ctx) catch |err| {
            ctx.deinit(self.gpa);
            return err;
        };

        return true;
    }

    fn noteExprType(self: *LowerTir, expr: ast.ExprId, ty: types.TypeId) !void {
        if (self.expr_type_override_stack.items.len == 0) return;
        if (self.isAny(ty)) return;
        var frame = &self.expr_type_override_stack.items[self.expr_type_override_stack.items.len - 1];
        try frame.map.put(self.gpa, expr.toRaw(), ty);
    }

    fn lookupExprTypeOverride(self: *const LowerTir, expr: ast.ExprId) ?types.TypeId {
        var i: usize = self.expr_type_override_stack.items.len;
        while (i > 0) {
            i -= 1;
            const frame = &self.expr_type_override_stack.items[i];
            if (frame.map.get(expr.toRaw())) |entry| {
                return entry;
            }
        }
        return null;
    }

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
                if (lit.kind != .int) break :blk null;
                const info = switch (lit.data) {
                    .int => |int_info| int_info,
                    else => return null,
                };
                if (!info.valid) break :blk null;
                const max_i64: u128 = @intCast(std.math.maxInt(i64));
                if (info.value > max_i64) break :blk null;
                break :blk tir.ConstInit{ .int = @intCast(info.value) };
            },
            .Bool => blk: {
                if (lit.kind != .bool) break :blk null;
                const value = switch (lit.data) {
                    .bool => |b| b,
                    else => return null,
                };
                break :blk tir.ConstInit{ .bool = value };
            },
            else => null,
        };
    }

    pub fn init(
        gpa: std.mem.Allocator,
        context: *Context,
        pipeline: *Pipeline,
        type_info: *types.TypeInfo,
        module_id: usize,
        chk: *checker.Checker,
    ) LowerTir {
        std.debug.assert(type_info.module_id == module_id);
        return .{
            .gpa = gpa,
            .context = context,
            .pipeline = pipeline,
            .type_info = type_info,
            .module_id = module_id,
            .chk = chk,
            .module_call_cache = std.AutoHashMap(u64, StrId).init(gpa),
            .method_lowered = std.AutoHashMap(usize, void).init(gpa),
            .monomorphizer = monomorphize.Monomorphizer.init(gpa),
            .expr_type_override_stack = .{},
        };
    }

    pub fn deinit(self: *LowerTir) void {
        self.loop_stack.deinit(self.gpa);
        var it = self.module_prefix.valueIterator();
        while (it.next()) |p| self.gpa.free(p.*);
        self.module_prefix.deinit(self.gpa);
        self.module_call_cache.deinit();
        self.method_lowered.deinit();
        while (self.monomorph_context_stack.items.len > 0) {
            var ctx = self.monomorph_context_stack.pop().?;
            ctx.deinit(self.gpa);
        }
        self.monomorph_context_stack.deinit(self.gpa);
        while (self.expr_type_override_stack.items.len > 0) {
            self.expr_type_override_stack.items[self.expr_type_override_stack.items.len - 1].deinit(self.gpa);
            self.expr_type_override_stack.items.len -= 1;
        }
        self.expr_type_override_stack.deinit(self.gpa);
        self.monomorphizer.deinit();
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
        var f = try b.beginFunction(name, self.context.type_store.tVoid(), false, .empty());
        var blk = try b.beginBlock(&f);
        var env = Env.init(self.gpa);
        defer env.deinit(self.gpa);

        for (global_mlir_decls.items) |did| {
            const d = a.exprs.Decl.get(did);
            _ = try self.lowerExpr(a, &env, &f, &blk, d.value, null, .rvalue);
        }

        if (blk.term.isNone()) {
            // This synthesized initializer has no source span; emit a location-less return.
            try b.setReturn(&blk, .none(), tir.OptLocId.none());
        }
        try b.endBlock(&f, blk);
        try b.endFunction(f);
    }

    fn lowerMlirBlock(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        loc: tir.OptLocId,
    ) !tir.ValueId {
        const row = a.exprs.get(.MlirBlock, id);
        const expr_ty_opt = self.getExprType(id);
        var ty0 = expr_ty_opt orelse (expected_ty orelse self.context.type_store.tAny());
        if (expected_ty) |want| {
            if (expr_ty_opt) |expr_ty| {
                if (self.isAny(expr_ty) and !self.isAny(want)) {
                    ty0 = want;
                }
            } else {
                ty0 = want;
            }
        }

        // Lower args
        const arg_ids = a.exprs.expr_pool.slice(row.args);
        var arg_vals = try self.gpa.alloc(tir.ValueId, arg_ids.len);
        defer self.gpa.free(arg_vals);
        for (arg_ids, 0..) |arg_id, i| {
            arg_vals[i] = try self.lowerExpr(a, env, f, blk, arg_id, null, .rvalue);
        }
        const args_range = blk.builder.t.instrs.value_pool.pushMany(self.gpa, arg_vals);

        const result_id = blk.builder.freshValue();
        const iid = blk.builder.t.instrs.add(.MlirBlock, .{
            .result = .some(result_id),
            .ty = ty0,
            .kind = row.kind,
            .text = row.text,
            .args = args_range,
            .loc = loc,
        });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        if (expected_ty) |want| {
            if (!ty0.eq(want)) {
                return self.emitCoerce(blk, result_id, ty0, want, loc);
            }
        }
        return result_id;
    }

    pub fn run(self: *LowerTir, a: *const ast.Ast) !tir.TIR {
        var t = tir.TIR.init(self.gpa, &self.context.type_store);
        var b = Builder.init(self.gpa, &t);

        self.module_call_cache.clearRetainingCapacity();
        self.method_lowered.clearRetainingCapacity();

        try self.lowerGlobalMlir(a, &b);

        // Lower top-level decls: functions and globals
        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        for (decls) |did| try self.lowerTopDecl(a, &b, did);

        var method_it = self.type_info.method_table.iterator();
        while (method_it.next()) |entry| {
            const method = entry.value_ptr.*;
            const decl_id = method.decl_id;
            if (self.method_lowered.contains(decl_id.toRaw())) continue;
            const name = try self.methodSymbolName(a, decl_id);
            try self.tryLowerNamedFunction(a, &b, decl_id, name, true);
        }

        try self.monomorphizer.run(self, a, &b, monomorphLowerCallback);

        return t;
    }

    pub fn setModulePrefix(self: *LowerTir, name: []const u8, prefix: []const u8) !void {
        const key = try self.gpa.dupe(u8, name);
        const val = try self.gpa.dupe(u8, prefix);
        const gop = try self.module_prefix.getOrPut(self.gpa, key);
        if (gop.found_existing) {
            self.gpa.free(key);
            self.gpa.free(gop.value_ptr.*);
            gop.value_ptr.* = val;
            self.module_call_cache.clearRetainingCapacity();
            return;
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

    inline fn locToOpt(_: *const LowerTir, loc: ast.LocId) tir.OptLocId {
        return tir.OptLocId.some(loc);
    }

    inline fn optLocToOpt(_: *const LowerTir, opt_loc: ast.OptLocId) tir.OptLocId {
        return if (opt_loc.isNone()) tir.OptLocId.none() else tir.OptLocId.some(opt_loc.unwrap());
    }

    inline fn rowOptLoc(self: *const LowerTir, row: anytype) tir.OptLocId {
        if (comptime @hasField(@TypeOf(row), "loc")) {
            return self.locToOpt(row.loc);
        }
        return tir.OptLocId.none();
    }

    fn exprOptLoc(self: *const LowerTir, a: *const ast.Ast, id: ast.ExprId) tir.OptLocId {
        const kind = a.exprs.index.kinds.items[id.toRaw()];
        inline for (@typeInfo(ast.ExprKind).@"enum".fields) |field| {
            const tag: ast.ExprKind = @enumFromInt(field.value);
            if (tag == kind) {
                const row = a.exprs.get(tag, id);
                return self.rowOptLoc(row);
            }
        }
        return tir.OptLocId.none();
    }

    fn optExprOptLoc(self: *const LowerTir, a: *const ast.Ast, id: ast.OptExprId) tir.OptLocId {
        return if (id.isNone()) tir.OptLocId.none() else self.exprOptLoc(a, id.unwrap());
    }

    fn patternOptLoc(self: *const LowerTir, a: *const ast.Ast, id: ast.PatternId) tir.OptLocId {
        const kind = a.pats.index.kinds.items[id.toRaw()];
        inline for (@typeInfo(ast.PatternKind).@"enum".fields) |field| {
            const tag: ast.PatternKind = @enumFromInt(field.value);
            if (tag == kind) {
                const row = a.pats.get(tag, id);
                return self.rowOptLoc(row);
            }
        }
        return tir.OptLocId.none();
    }

    fn optPatternOptLoc(self: *const LowerTir, a: *const ast.Ast, id: ast.OptPatternId) tir.OptLocId {
        return if (id.isNone()) tir.OptLocId.none() else self.patternOptLoc(a, id.unwrap());
    }

    fn stmtOptLoc(self: *const LowerTir, a: *const ast.Ast, id: ast.StmtId) tir.OptLocId {
        const kind = a.stmts.index.kinds.items[id.toRaw()];
        inline for (@typeInfo(ast.StmtKind).@"enum".fields) |field| {
            const tag: ast.StmtKind = @enumFromInt(field.value);
            if (tag == kind) {
                const row = a.stmts.get(tag, id);
                return self.stmtRowOptLoc(a, tag, row);
            }
        }
        return tir.OptLocId.none();
    }

    fn stmtRowOptLoc(
        self: *const LowerTir,
        a: *const ast.Ast,
        comptime tag: ast.StmtKind,
        row: ast.StmtRowT(tag),
    ) tir.OptLocId {
        return switch (tag) {
            .Expr => self.exprOptLoc(a, row.expr),
            .Decl => self.rowOptLoc(a.exprs.Decl.get(row.decl)),
            else => self.rowOptLoc(row),
        };
    }

    // Produce an undef that is never-void; if asked for void, give Any instead.
    fn safeUndef(self: *LowerTir, blk: *Builder.BlockFrame, ty: types.TypeId, loc: tir.OptLocId) tir.ValueId {
        if (self.isVoid(ty)) {
            return blk.builder.tirValue(.ConstUndef, blk, self.context.type_store.tAny(), loc, .{});
        }
        return blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{});
    }

    fn undef(_: *LowerTir, blk: *Builder.BlockFrame, ty: types.TypeId, loc: tir.OptLocId) tir.ValueId {
        return blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{});
    }

    /// Insert an explicit coercion that realizes what the checker proved assignable/castable.
    fn emitCoerce(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        v: tir.ValueId,
        got: types.TypeId,
        want: types.TypeId,
        loc: tir.OptLocId,
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
                const tag_ok = blk.builder.tirValue(.ConstInt, blk, ts.tI32(), loc, .{ .value = 0 });
                const payload = blk.builder.tirValue(.UnionMake, blk, payload_union_ty, loc, .{
                    .field_index = 0, // Ok
                    .value = v,
                });
                return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = tag_ok },
                    .{ .index = 1, .name = .none(), .value = payload },
                }, loc);
            }

            // Error E -> Err
            if (got.toRaw() == es.error_ty.toRaw()) {
                const tag_err = blk.builder.tirValue(.ConstInt, blk, ts.tI32(), loc, .{ .value = 1 });
                const payload = blk.builder.tirValue(.UnionMake, blk, payload_union_ty, loc, .{
                    .field_index = 1, // Err
                    .value = v,
                });
                return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = tag_err },
                    .{ .index = 1, .name = .none(), .value = payload },
                }, loc);
            }
            // else fall through (e.g., Any → ErrorSet: let the generic path try)
        }

        if (wk == .Optional) {
            const opt = ts.get(.Optional, want);
            const bool_ty = ts.tBool();

            if (gk == .Optional) {
                const got_opt = ts.get(.Optional, got);
                if (got_opt.elem.eq(opt.elem)) return v;

                const flag = blk.builder.extractField(blk, bool_ty, v, 0, loc);
                var payload = blk.builder.extractField(blk, got_opt.elem, v, 1, loc);
                payload = self.emitCoerce(blk, payload, got_opt.elem, opt.elem, loc);
                return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = flag },
                    .{ .index = 1, .name = .none(), .value = payload },
                }, loc);
            }

            const payload = self.emitCoerce(blk, v, got, opt.elem, loc);
            const some_flag = blk.builder.tirValue(.ConstBool, blk, bool_ty, loc, .{ .value = true });
            return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = some_flag },
                .{ .index = 1, .name = .none(), .value = payload },
            }, loc);
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
            return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = v });

        // Ptr ⇄ Ptr
        if (gk == .Ptr and wk == .Ptr)
            return blk.builder.tirValue(.CastBit, blk, want, loc, .{ .value = v });

        // Fallback: materialize/assignable
        return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = v });
    }

    // ============================
    // Top-level lowering
    // ============================

    fn tryLowerNamedFunction(
        self: *LowerTir,
        a: *const ast.Ast,
        b: *Builder,
        did: ast.DeclId,
        name: StrId,
        is_method: bool,
    ) !void {
        if (is_method and self.method_lowered.contains(did.toRaw())) return;

        const decl = a.exprs.Decl.get(did);
        const kind = a.exprs.index.kinds.items[decl.value.toRaw()];
        if (kind != .FunctionLit) return;

        const fn_ty_opt = self.getExprType(decl.value);
        if (fn_ty_opt == null) return;
        const fn_ty = fn_ty_opt.?;
        if (self.context.type_store.getKind(fn_ty) != .Function) return;

        const fn_ty_info = self.context.type_store.get(.Function, fn_ty);
        const param_tys = self.context.type_store.type_pool.slice(fn_ty_info.params);
        for (param_tys) |param_ty| {
            if (self.isAny(param_ty)) return;
        }

        const fn_lit = a.exprs.get(.FunctionLit, decl.value);
        const params = a.exprs.param_pool.slice(fn_lit.params);
        var skip_params: usize = 0;
        while (skip_params < params.len and a.exprs.Param.get(params[skip_params]).is_comptime) : (skip_params += 1) {}
        if (skip_params != 0) return;

        try self.lowerFunction(a, b, name, decl.value, null);

        if (is_method) {
            try self.method_lowered.put(did.toRaw(), {});
        }
    }

    fn lowerTopDecl(self: *LowerTir, a: *const ast.Ast, b: *Builder, did: ast.DeclId) !void {
        const d = a.exprs.Decl.get(did);
        const kind = a.exprs.index.kinds.items[d.value.toRaw()];

        if (kind == .MlirBlock and d.pattern.isNone()) {
            return; // handled by lowerGlobalMlir
        }

        if (kind == .FunctionLit and !a.exprs.get(.FunctionLit, d.value).flags.is_extern) {
            var name_opt: ?StrId = null;
            if (!d.pattern.isNone()) {
                name_opt = self.bindingNameOfPattern(a, d.pattern.unwrap());
            } else if (!d.method_path.isNone()) {
                name_opt = try self.methodSymbolName(a, did);
            }

            if (name_opt) |nm| {
                const is_method = !d.method_path.isNone();
                try self.tryLowerNamedFunction(a, b, did, nm, is_method);
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

    fn lowerAttrs(
        self: *LowerTir,
        a: *const ast.Ast,
        b: *Builder,
        range: ast.OptRangeAttr,
    ) !tir.RangeAttribute {
        if (range.isNone()) return .empty();
        const attrs = a.exprs.attr_pool.slice(range.asRange());
        var attr_list: std.ArrayList(tir.AttributeId) = .empty;
        defer attr_list.deinit(self.gpa);

        for (attrs) |aid| {
            const arow = a.exprs.Attribute.get(aid);
            // const value = try self.lowerExpr(a, env, f, blk, arow.value, null, .rvalue);
            try attr_list.append(self.gpa, b.t.instrs.Attribute.add(self.gpa, .{ .name = arow.name, .value = .none() }));
        }
        return b.t.instrs.attribute_pool.pushMany(self.gpa, attr_list.items);
    }

    fn lowerFunction(
        self: *LowerTir,
        a: *const ast.Ast,
        b: *Builder,
        name: StrId,
        fun_eid: ast.ExprId,
        ctx: ?*const monomorphize.MonomorphizationContext,
    ) !void {
        const fid = if (ctx) |c|
            c.specialized_ty
        else
            (self.getExprType(fun_eid) orelse return);
        if (self.context.type_store.index.kinds.items[fid.toRaw()] != .Function) return;
        const fnty = self.context.type_store.get(.Function, fid);

        const fnr = a.exprs.get(.FunctionLit, fun_eid);
        const fn_loc = self.locToOpt(fnr.loc);

        try self.pushExprTypeOverrideFrame();
        defer self.popExprTypeOverrideFrame();

        if (!fnr.attrs.isNone()) {
            const attrs = a.exprs.attr_pool.slice(fnr.attrs.asRange());
            const mlir_fn_str = a.exprs.strs.intern("mlir_fn");
            for (attrs) |aid| {
                const arow = a.exprs.Attribute.get(aid);
                if (arow.name.eq(mlir_fn_str)) {
                    return; // skip lowering this function
                }
            }
        }

        const attrs = try self.lowerAttrs(a, b, fnr.attrs);
        var f = try b.beginFunction(name, fnty.result, fnty.is_variadic, attrs);

        // Params
        const params = a.exprs.param_pool.slice(fnr.params);
        var i: usize = 0;
        const skip_params: usize = if (ctx) |c| c.skip_params else 0;
        const runtime_param_tys = self.context.type_store.type_pool.slice(fnty.params);
        var runtime_index: usize = 0;
        while (i < params.len) : (i += 1) {
            if (i < skip_params) continue;
            const p = a.exprs.Param.get(params[i]);
            const pty = runtime_param_tys[runtime_index];
            const pname = if (!p.pat.isNone()) self.bindingNameOfPattern(a, p.pat.unwrap()) else null;
            _ = try b.addParam(&f, pname, pty);
            runtime_index += 1;
        }

        // Entry block + env
        var blk = try b.beginBlock(&f);
        var env = Env.init(self.gpa);
        defer env.deinit(self.gpa);

        if (ctx) |c| {
            for (c.bindings) |binding| {
                switch (binding.kind) {
                    .type_param => {},
                    .value_param => |vp| {
                        const const_val = try self.constValueFromComptime(&blk, vp.ty, vp.value);
                        try env.bind(self.gpa, a, binding.name, .{ .value = const_val, .ty = vp.ty, .is_slot = false });
                    },
                    .runtime_param => {},
                }
            }
        }

        // Bind params
        i = 0;
        const param_vals = f.param_vals.items;
        runtime_index = 0;
        while (i < params.len) : (i += 1) {
            if (i < skip_params) continue;
            const p = a.exprs.Param.get(params[i]);
            if (!p.pat.isNone()) {
                const pname = self.bindingNameOfPattern(a, p.pat.unwrap()) orelse continue;
                const pty = runtime_param_tys[runtime_index];
                try env.bind(self.gpa, a, pname, .{ .value = param_vals[runtime_index], .ty = pty, .is_slot = false });
            }
            runtime_index += 1;
        }

        // Body
        if (!fnr.body.isNone()) {
            const body_id = fnr.body.unwrap();
            try env.pushScope(self.gpa);
            try self.lowerExprAsStmtList(a, &env, &f, &blk, body_id);
            _ = env.popScope();
        }

        if (blk.term.isNone()) {
            try b.setReturn(&blk, tir.OptValueId.none(), fn_loc);
        }

        try b.endBlock(&f, blk);
        try b.endFunction(f);
    }

    fn lowerSpecializedFunction(
        self: *LowerTir,
        a: *const ast.Ast,
        b: *Builder,
        req: *const monomorphize.MonomorphizationRequest,
    ) !void {
        var ctx = try monomorphize.MonomorphizationContext.init(
            self.gpa,
            req.bindings,
            req.skip_params,
            req.specialized_ty,
        );
        errdefer ctx.deinit(self.gpa);

        self.monomorph_context_stack.append(self.gpa, ctx) catch |err| {
            ctx.deinit(self.gpa);
            return err;
        };
        defer {
            var popped = self.monomorph_context_stack.pop();
            if (popped) |*p|
                p.deinit(self.gpa);
        }

        const active_ctx = &self.monomorph_context_stack.items[self.monomorph_context_stack.items.len - 1];
        const decl = a.exprs.Decl.get(req.decl_id);
        try self.lowerFunction(a, b, req.mangled_name, decl.value, active_ctx);
    }

    fn monomorphLowerCallback(
        ctx: ?*anyopaque,
        a: *const ast.Ast,
        b: *Builder,
        req: *const monomorphize.MonomorphizationRequest,
    ) anyerror!void {
        std.debug.assert(ctx != null);
        const self: *LowerTir = @ptrCast(@alignCast(ctx.?));
        try self.lowerSpecializedFunction(a, b, req);
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
                const slice = env.defers.items[start..env.defers.items.len];
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

    fn loopCtxForLabel(self: *LowerTir, opt_label: ast.OptStrId) ?*LoopCtx {
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

    fn lowerBreak(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        sid: ast.StmtId,
    ) !void {
        const br = a.stmts.get(.Break, sid);
        const loc = self.stmtOptLoc(a, sid);
        var target: ?LoopCtx = null;
        var i: isize = @as(isize, @intCast(self.loop_stack.items.len)) - 1;
        while (i >= 0) : (i -= 1) {
            const lc = self.loop_stack.items[@intCast(i)];
            if (br.label.isNone() or (!lc.label.isNone() and std.mem.eql(u8, a.exprs.strs.get(lc.label.unwrap()), a.exprs.strs.get(br.label.unwrap())))) {
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
                    f.builder.tirValue(.ConstUndef, blk, lc.res_ty.?, loc, .{});
                try f.builder.br(blk, lc.join_block, &.{v}, loc);
            } else {
                try f.builder.br(blk, lc.break_block, &.{}, loc);
            }
        } else return error.LoweringBug;
    }

    fn lowerContinue(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        sid: ast.StmtId,
    ) !void {
        const cid = a.stmts.get(.Continue, sid);
        const loc = self.stmtOptLoc(a, sid);
        const lc = self.loopCtxForLabel(cid.label) orelse return error.LoweringBug;
        try self.runDefersForLoopExit(a, env, f, blk, lc.*);
        switch (lc.continue_info) {
            .none => try f.builder.br(blk, lc.continue_block, &.{}, loc),
            .range => |info| try f.builder.br(blk, info.update_block, &.{info.idx_value}, loc),
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
        const value_ty = self.getExprType(d.value) orelse self.context.type_store.tAny();
        const decl_ty = self.getDeclType(drow.decl) orelse value_ty;
        if (!d.pattern.isNone()) {
            // Destructure once for all names: bind as values for const, or slots for mut.
            try self.destructureDeclFromExpr(a, env, f, blk, d.pattern.unwrap(), d.value, decl_ty, !d.flags.is_const);
        } else {
            if (!d.method_path.isNone()) {
                const vk = a.exprs.index.kinds.items[d.value.toRaw()];
                if (vk == .FunctionLit) return;
            }
            // No pattern: just evaluate for side-effects.
            _ = try self.lowerExpr(a, env, f, blk, d.value, decl_ty, .rvalue);
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
        const stmt_loc = self.stmtOptLoc(a, sid);
        const defer_mark: u32 = 0;

        if (!r.value.isNone()) {
            const frow = f.builder.t.funcs.Function.get(f.id);
            const expect = frow.result;
            const want: ?types.TypeId = if (self.isVoid(expect)) null else expect;
            const value_expr = r.value.unwrap();
            const value_loc = self.exprOptLoc(a, value_expr);
            const v_raw = try self.lowerExpr(a, env, f, blk, value_expr, want, .rvalue);
            var v = v_raw;
            if (want == null) {
                if (self.getExprType(r.value.unwrap())) |got| {
                    v = self.emitCoerce(blk, v_raw, got, expect, value_loc);
                }
            }

            const expect_kind = self.context.type_store.index.kinds.items[expect.toRaw()];
            const has_err_defers = expect_kind == .ErrorSet and self.hasErrDefersFrom(env, defer_mark);

            if (has_err_defers) {
                var err_blk = try f.builder.beginBlock(f);
                var ok_blk = try f.builder.beginBlock(f);
                const tag_ty = self.context.type_store.tI32();
                const tag = blk.builder.extractField(blk, tag_ty, v, 0, value_loc);
                const zero = blk.builder.tirValue(.ConstInt, blk, tag_ty, value_loc, .{ .value = 0 });
                const is_err = blk.builder.binBool(blk, .CmpNe, tag, zero, value_loc);
                const br_cond = self.forceLocalCond(blk, is_err, value_loc);
                try f.builder.condBr(blk, br_cond, err_blk.id, &.{}, ok_blk.id, &.{}, stmt_loc);

                const defer_slice = env.defers.items[defer_mark..env.defers.items.len];

                try self.emitDefers(a, env, f, &err_blk, defer_slice, true);
                try self.emitDefers(a, env, f, &err_blk, defer_slice, false);
                try f.builder.setReturnVal(&err_blk, v, stmt_loc);
                try f.builder.endBlock(f, err_blk);

                try self.emitDefers(a, env, f, &ok_blk, defer_slice, false);
                try f.builder.setReturnVal(&ok_blk, v, stmt_loc);
                try f.builder.endBlock(f, ok_blk);

                env.defers.items.len = defer_mark;
                return;
            } else {
                try self.runNormalDefersFrom(a, env, f, blk, defer_mark);
                try f.builder.setReturnVal(blk, v, stmt_loc);
                return;
            }
        } else {
            try self.runNormalDefersFrom(a, env, f, blk, defer_mark);
            try f.builder.setReturnVoid(blk, stmt_loc);
            return;
        }
    }

    fn lowerAssign(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, sid: ast.StmtId) !void {
        const as = a.stmts.get(.Assign, sid);
        const lhs_ptr = try self.lowerExpr(a, env, f, blk, as.left, null, .lvalue_addr);
        const rhs = try self.lowerExpr(a, env, f, blk, as.right, self.getExprType(as.left), .rvalue);
        const rty = self.getExprType(as.left) orelse return error.LoweringBug;
        const stmt_loc = self.stmtOptLoc(a, sid);
        _ = f.builder.tirValue(.Store, blk, rty, stmt_loc, .{ .ptr = lhs_ptr, .value = rhs, .@"align" = 0 });
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
            .Break => try self.lowerBreak(a, env, f, blk, sid),
            .Continue => try self.lowerContinue(a, env, f, blk, sid),
            .Decl => try self.lowerDecl(a, env, f, blk, sid),
            .Assign => try self.lowerAssign(a, env, f, blk, sid),
            .Return => try self.lowerReturn(a, env, f, blk, sid),
            .Unreachable => try f.builder.setUnreachable(blk, self.stmtOptLoc(a, sid)),
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

    fn resolveTypeArg(self: *LowerTir, expr: ast.ExprId) ?types.TypeId {
        const ty = self.getExprType(expr) orelse return null;
        if (self.context.type_store.getKind(ty) != .TypeType) return null;
        return self.context.type_store.get(.TypeType, ty).of;
    }

    fn appendMangleValue(
        self: *LowerTir,
        buf: *std.ArrayList(u8),
        value: comp.ComptimeValue,
    ) !void {
        var w = buf.writer(self.gpa);
        switch (value) {
            .Int => |val| try w.print("i{}", .{val}),
            .Float => |val| try w.print("f{d}", .{val}),
            .Bool => |val| try w.print("{s}", .{if (val) "true" else "false"}),
            .Void => try w.print("void", .{}),
            .String => |s| {
                try w.print("s{}_", .{s.len});
                for (s) |ch| {
                    const keep = std.ascii.isAlphanumeric(ch) or ch == '_';
                    try buf.append(self.gpa, if (keep) ch else '_');
                }
            },
            .Type => |ty| try self.context.type_store.fmt(ty, w),
        }
    }

    fn mangleMonomorphName(
        self: *LowerTir,
        base: StrId,
        bindings: []const monomorphize.BindingInfo,
    ) !StrId {
        var buf: std.ArrayList(u8) = .empty;
        defer buf.deinit(self.gpa);

        try buf.appendSlice(self.gpa, self.context.type_store.strs.get(base));
        for (bindings) |info| {
            try buf.append(self.gpa, '_');
            switch (info.kind) {
                .type_param => |ty| {
                    const w = buf.writer(self.gpa);
                    try self.context.type_store.fmt(ty, w);
                },
                .value_param => |vp| try self.appendMangleValue(&buf, vp.value),
                .runtime_param => |ty| {
                    const w = buf.writer(self.gpa);
                    try self.context.type_store.fmt(ty, w);
                },
            }
        }

        return self.context.type_store.strs.intern(buf.items);
    }

    fn moduleCallKey(alias: ast.StrId, field: StrId) u64 {
        return (@as(u64, alias.toRaw()) << 32) | @as(u64, field.toRaw());
    }

    fn methodSymbolName(
        self: *LowerTir,
        a: *const ast.Ast,
        did: ast.DeclId,
    ) !StrId {
        const decl = a.exprs.Decl.get(did);
        std.debug.assert(!decl.method_path.isNone());
        const seg_ids = a.exprs.method_path_pool.slice(decl.method_path.asRange());
        if (seg_ids.len < 2) return error.LoweringBug;

        const owner_seg = a.exprs.MethodPathSeg.get(seg_ids[0]);
        const method_seg = a.exprs.MethodPathSeg.get(seg_ids[seg_ids.len - 1]);
        const owner_name = a.exprs.strs.get(owner_seg.name);
        const method_name = a.exprs.strs.get(method_seg.name);

        const symbol = try std.fmt.allocPrint(self.gpa, "{s}__{s}", .{ owner_name, method_name });
        defer self.gpa.free(symbol);
        return self.context.type_store.strs.intern(symbol);
    }

    fn resolveModuleFieldCallee(
        self: *LowerTir,
        a: *const ast.Ast,
        f: *Builder.FunctionFrame,
        field_access: ast.ExprId,
    ) !?StrId {
        const fr = a.exprs.get(.FieldAccess, field_access);
        const parent_kind = a.exprs.index.kinds.items[fr.parent.toRaw()];
        if (parent_kind != .Ident) return null;

        const ident = a.exprs.get(.Ident, fr.parent);
        const alias_name = a.exprs.strs.get(ident.name);
        const prefix = self.module_prefix.get(alias_name) orelse return null;

        const key = moduleCallKey(ident.name, fr.field);
        if (self.module_call_cache.get(key)) |existing| return existing;

        const field_name = a.exprs.strs.get(fr.field);
        const mangled = try std.fmt.allocPrint(self.gpa, "{s}_{s}", .{ prefix, field_name });
        defer self.gpa.free(mangled);

        const interned = f.builder.intern(mangled);
        try self.module_call_cache.put(key, interned);
        return interned;
    }

    fn resolveCallee(self: *LowerTir, a: *const ast.Ast, f: *Builder.FunctionFrame, row: ast.Rows.Call) !CalleeInfo {
        const ck = a.exprs.index.kinds.items[row.callee.toRaw()];
        if (ck == .Ident) {
            const nm = a.exprs.get(.Ident, row.callee).name;
            return .{ .name = nm, .fty = self.getExprType(row.callee) };
        }
        if (ck == .FieldAccess) {
            if (try self.resolveModuleFieldCallee(a, f, row.callee)) |mangled|
                return .{ .name = mangled, .fty = self.getExprType(row.callee) };

            return .{
                .name = a.exprs.get(.FieldAccess, row.callee).field,
                .fty = self.getExprType(row.callee),
            };
        }
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
        loc: tir.OptLocId,
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
                break :blk blk.builder.tupleMake(blk, payload_ty, elems, loc);
            },
            else => try self.lowerExpr(a, env, f, blk, args[0], payload_ty, .rvalue),
        };

        // tag (i32)
        const tag_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), loc, .{ .value = tag_idx });

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
            blk.builder.tirValue(.UnionMake, blk, union_ty, loc, .{ .field_index = tag_idx, .value = pv })
        else
            blk.builder.tirValue(.ConstUndef, blk, union_ty, loc, .{});

        return blk.builder.structMake(blk, ety, &[_]tir.Rows.StructFieldInit{
            .{ .index = 0, .name = .none(), .value = tag_val },
            .{ .index = 1, .name = .none(), .value = union_val },
        }, loc);
    }

    fn runComptimeExpr(
        self: *LowerTir,
        a: *const ast.Ast,
        expr: ast.ExprId,
        result_ty: types.TypeId,
        bindings: []const Pipeline.ComptimeBinding,
    ) !comp.ComptimeValue {
        const pushed = try self.pushComptimeBindings(bindings);
        defer if (pushed) {
            var popped = self.monomorph_context_stack.pop();
            if (popped) |*ctx| ctx.deinit(self.gpa);
        };

        const result_kind = self.context.type_store.getKind(result_ty);
        if (result_kind == .TypeType) {
            const tt = self.context.type_store.get(.TypeType, result_ty);
            if (!self.isAny(tt.of)) return .{ .Type = tt.of };
            // Otherwise, fall through and evaluate the expression to compute the concrete type.
        }

        var tmp_tir = tir.TIR.init(self.gpa, &self.context.type_store);
        defer tmp_tir.deinit();
        var tmp_builder = tir.Builder.init(self.gpa, &tmp_tir);

        const ptr_ty = self.context.type_store.mkPtr(self.context.type_store.tU8(), false);
        const thunk_name = tmp_builder.intern("__comptime_thunk");
        const expr_loc = self.exprOptLoc(a, expr);

        const attr_id = tmp_tir.instrs.Attribute.add(self.gpa, .{
            .name = a.exprs.strs.intern("llvm.emit_c_interface"),
            .value = .none(),
        });
        const attrs = tmp_tir.instrs.attribute_pool.pushMany(self.gpa, &.{attr_id});
        const thunk_ret_ty = switch (result_kind) {
            .Void => self.context.type_store.tVoid(),
            else => result_ty,
        };

        var thunk_fn = try tmp_builder.beginFunction(thunk_name, thunk_ret_ty, false, attrs);
        const api_ptr_val = try tmp_builder.addParam(&thunk_fn, tmp_builder.intern("api_ptr"), ptr_ty);
        var thunk_blk = try tmp_builder.beginBlock(&thunk_fn);

        var tmp_env = Env.init(self.gpa);
        defer tmp_env.deinit(self.gpa);
        try tmp_env.bind(self.gpa, a, tmp_builder.intern("comptime_api_ptr"), .{ .value = api_ptr_val, .ty = ptr_ty, .is_slot = false });

        const result_val_id = try self.lowerExpr(a, &tmp_env, &thunk_fn, &thunk_blk, expr, result_ty, .rvalue);
        if (result_kind != .Void) {
            if (thunk_blk.term.isNone()) {
                try tmp_builder.setReturnVal(&thunk_blk, result_val_id, expr_loc);
            }
        } else if (thunk_blk.term.isNone()) {
            try tmp_builder.setReturnVoid(&thunk_blk, expr_loc);
        }
        try tmp_builder.endBlock(&thunk_fn, thunk_blk);
        try tmp_builder.endFunction(thunk_fn);

        if (!g_mlir_inited) {
            g_mlir_ctx = compile.initMLIR(self.gpa);
            g_mlir_inited = true;
        }
        var gen = mlir_codegen.MlirCodegen.init(self.gpa, self.context, g_mlir_ctx);
        defer gen.deinit();
        var mlir_module = try gen.emitModule(&tmp_tir, self.context, a.exprs.locs);

        try compile.run_passes(&gen.mlir_ctx, &mlir_module);
        _ = mlir.c.LLVMInitializeNativeTarget();
        _ = mlir.c.LLVMInitializeNativeAsmPrinter();
        const engine = mlir.c.mlirExecutionEngineCreate(mlir_module.handle, 2, 0, null, false);
        defer mlir.c.mlirExecutionEngineDestroy(engine);

        var comptime_api = comp.ComptimeApi{
            .context = self.context,
            .print = comp.comptime_print_impl,
            .get_type_by_name = comp.get_type_by_name_impl,
            .type_of = comp.type_of_impl,
        };

        const thunk_fn_name_ref = mlir.StringRef.from("__comptime_thunk");
        const func_ptr = mlir.c.mlirExecutionEngineLookup(engine, thunk_fn_name_ref.inner);
        if (func_ptr == null) return error.ComptimeExecutionFailed;
        const non_null_ptr = func_ptr.?;

        if (result_kind == .Void) {
            callComptimeThunk(void, non_null_ptr, &comptime_api);
            return .Void;
        }

        if (result_kind == .Bool) {
            const raw = callComptimeThunk(bool, non_null_ptr, &comptime_api);
            return comp.ComptimeValue{ .Bool = raw };
        }

        if (result_kind == .F64) {
            const raw = callComptimeThunk(f64, non_null_ptr, &comptime_api);
            return comp.ComptimeValue{ .Float = raw };
        }

        if (result_kind == .F32) {
            const raw = callComptimeThunk(f32, non_null_ptr, &comptime_api);
            return comp.ComptimeValue{ .Float = @floatCast(f64, raw) };
        }

        inline for (.{
            .{ .kind = types.TypeKind.I8, .T = i8 },
            .{ .kind = types.TypeKind.I16, .T = i16 },
            .{ .kind = types.TypeKind.I32, .T = i32 },
            .{ .kind = types.TypeKind.I64, .T = i64 },
            .{ .kind = types.TypeKind.U8, .T = u8 },
            .{ .kind = types.TypeKind.U16, .T = u16 },
            .{ .kind = types.TypeKind.U32, .T = u32 },
            .{ .kind = types.TypeKind.U64, .T = u64 },
            .{ .kind = types.TypeKind.Usize, .T = usize },
        }) |entry| {
            if (result_kind == entry.kind) {
                const raw = callComptimeThunk(entry.T, non_null_ptr, &comptime_api);
                if (castIntThunkResultToU128(raw)) |casted| {
                    return comp.ComptimeValue{ .Int = casted };
                } else {
                    return error.UnsupportedComptimeType;
                }
            }
        }

        return error.UnsupportedComptimeType;
    }

    fn callComptimeThunk(comptime Ret: type, func_ptr: *anyopaque, api: *comp.ComptimeApi) Ret {
        const FnPtr = *const fn (*comp.ComptimeApi) callconv(.c) Ret;
        const typed: FnPtr = @ptrCast(@alignCast(func_ptr));
        return typed(api);
    }

    fn castIntThunkResultToU128(value: anytype) ?u128 {
        const info = @typeInfo(@TypeOf(value)).Int;
        if (info.signedness == .signed) {
            return std.math.cast(u128, value);
        } else {
            return @as(u128, value);
        }
    }

    fn jitEvalComptimeBlock(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
    ) !tir.ValueId {
        _ = env;
        _ = f;

        const cb = a.exprs.get(.ComptimeBlock, id);
        const result_ty = self.getExprType(cb.block) orelse return error.LoweringBug;
        const comptime_value = try self.runComptimeExpr(a, cb.block, result_ty, &[_]Pipeline.ComptimeBinding{});
        const loc = self.exprOptLoc(a, id);

        return switch (comptime_value) {
            .Int => |val| blk.builder.tirValue(.ConstInt, blk, result_ty, loc, .{ .value = @as(u64, @intCast(val)) }),
            .Float => |val| blk.builder.tirValue(.ConstFloat, blk, result_ty, loc, .{ .value = val }),
            .Bool => |val| blk.builder.tirValue(.ConstBool, blk, result_ty, loc, .{ .value = val }),
            .Void => blk.builder.tirValue(.ConstUndef, blk, self.context.type_store.tVoid(), loc, .{}),
            .String => |s| blk.builder.tirValue(.ConstString, blk, result_ty, loc, .{ .text = blk.builder.intern(s) }),
            .Type => return error.UnsupportedComptimeType,
        };
    }

    fn evalComptimeExprValue(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        expr: ast.ExprId,
        result_ty: types.TypeId,
    ) !comp.ComptimeValue {
        _ = env;
        _ = f;
        _ = blk;
        return self.runComptimeExpr(a, expr, result_ty, &[_]Pipeline.ComptimeBinding{});
    }

    fn constValueFromComptime(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        ty: types.TypeId,
        value: comp.ComptimeValue,
    ) !tir.ValueId {
        _ = self;
        // These values are synthesized from specialization metadata; no source location is available.
        return switch (value) {
            .Int => |val| blk: {
                const casted = std.math.cast(u64, val) orelse return error.LoweringBug;
                break :blk blk.builder.tirValue(.ConstInt, blk, ty, tir.OptLocId.none(), .{ .value = casted });
            },
            .Float => |val| blk.builder.tirValue(.ConstFloat, blk, ty, tir.OptLocId.none(), .{ .value = val }),
            .Bool => |val| blk.builder.tirValue(.ConstBool, blk, ty, tir.OptLocId.none(), .{ .value = val }),
            .Void => blk.builder.tirValue(.ConstUndef, blk, ty, tir.OptLocId.none(), .{}),
            .String => |s| blk.builder.tirValue(.ConstString, blk, ty, tir.OptLocId.none(), .{ .text = blk.builder.intern(s) }),
            .Type => return error.UnsupportedComptimeType,
        };
    }

    fn constValueFromLiteral(self: *LowerTir, a: *const ast.Ast, expr: ast.ExprId) !?comp.ComptimeValue {
        const kind = a.exprs.index.kinds.items[expr.toRaw()];
        if (kind != .Literal) return null;
        const lit = a.exprs.get(.Literal, expr);

        return switch (lit.kind) {
            .int => blk: {
                const info = switch (lit.data) {
                    .int => |int_info| int_info,
                    else => return null,
                };
                if (!info.valid) return null;
                break :blk comp.ComptimeValue{ .Int = info.value };
            },
            .float => blk: {
                const info = switch (lit.data) {
                    .float => |float_info| float_info,
                    else => return null,
                };
                if (!info.valid) return null;
                break :blk comp.ComptimeValue{ .Float = info.value };
            },
            .bool => blk: {
                const value = switch (lit.data) {
                    .bool => |b| b,
                    else => return null,
                };
                break :blk comp.ComptimeValue{ .Bool = value };
            },
            .string => blk: {
                const s = switch (lit.data) {
                    .string => |s_id| a.exprs.strs.get(s_id),
                    else => return null,
                };
                const owned_s = try self.gpa.dupe(u8, s);
                break :blk comp.ComptimeValue{ .String = owned_s };
            },
            else => null,
        };
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
        var callee = try self.resolveCallee(a, f, row);
        const loc = self.exprOptLoc(a, id);
        var arg_ids = a.exprs.expr_pool.slice(row.args);
        var method_arg_buf: []ast.ExprId = &.{};
        var method_decl_id: ?ast.DeclId = null;
        var method_binding: ?types.TypeInfo.MethodBinding = null;
        defer {
            if (method_arg_buf.len != 0) self.gpa.free(method_arg_buf);
        }

        var callee_name = a.exprs.strs.get(callee.name);
        if (std.mem.eql(u8, callee_name, "get_type_by_name") or
            std.mem.eql(u8, callee_name, "comptime_print") or
            std.mem.eql(u8, callee_name, "type_of"))
        {
            const api_ptr_bnd = env.lookup(f.builder.intern("comptime_api_ptr")) orelse return error.LoweringBug;
            const api_ptr = api_ptr_bnd.value;

            const ptr_ty = self.context.type_store.mkPtr(self.context.type_store.tU8(), false);
            const fn_ptr_ty = self.context.type_store.mkPtr(self.context.type_store.tVoid(), false);

            const comptime_api_struct_ty = self.context.type_store.mkStruct(&.{
                .{ .name = f.builder.intern("context"), .ty = ptr_ty },
                .{ .name = f.builder.intern("print"), .ty = fn_ptr_ty },
                .{ .name = f.builder.intern("get_type_by_name"), .ty = fn_ptr_ty },
                .{ .name = f.builder.intern("type_of"), .ty = fn_ptr_ty },
            });

            const comptime_api_ptr_ty = self.context.type_store.mkPtr(comptime_api_struct_ty, false);
            const typed_api_ptr = blk.builder.tirValue(.CastBit, blk, comptime_api_ptr_ty, loc, .{ .value = api_ptr });

            const ctx_ptr_ptr = blk.builder.gep(blk, self.context.type_store.mkPtr(ptr_ty, false), typed_api_ptr, &.{blk.builder.gepConst(0)}, loc);

            const ctx_ptr = blk.builder.tirValue(.Load, blk, ptr_ty, loc, .{ .ptr = ctx_ptr_ptr, .@"align" = 0 });

            const fn_ptr_idx: u64 = if (std.mem.eql(u8, callee_name, "comptime_print")) 1 else if (std.mem.eql(u8, callee_name, "get_type_by_name")) 2 else 3;

            const fn_ptr_ptr = blk.builder.gep(blk, self.context.type_store.mkPtr(fn_ptr_ty, false), typed_api_ptr, &.{blk.builder.gepConst(fn_ptr_idx)}, loc);
            const fn_ptr = blk.builder.tirValue(.Load, blk, fn_ptr_ty, loc, .{ .ptr = fn_ptr_ptr, .@"align" = 0 });

            var all_args: std.ArrayList(tir.ValueId) = .empty;
            defer all_args.deinit(self.gpa);
            try all_args.append(self.gpa, ctx_ptr);
            // For type_of, we need to pass the raw ExprId, not the lowered value.
            if (std.mem.eql(u8, callee_name, "type_of")) {
                // Ensure there's exactly one argument for type_of
                std.debug.assert(arg_ids.len == 1);
                const arg_type_id = self.getExprType(arg_ids[0]) orelse return error.LoweringBug;
                try all_args.append(self.gpa, blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tU32(), loc, .{ .value = arg_type_id.toRaw() }));
            } else {
                for (arg_ids) |arg_id| {
                    try all_args.append(self.gpa, try self.lowerExpr(a, env, f, blk, arg_id, null, .rvalue));
                }
            }

            const ret_ty = self.getExprType(id) orelse self.context.type_store.tAny();
            return blk.builder.indirectCall(blk, ret_ty, fn_ptr, all_args.items, loc);
        }

        // Variant construction: if expected is a Variant/Error and callee is a path to a case, build VariantMake
        if (expected) |ety| {
            const k = self.context.type_store.getKind(ety);
            if (k == .Variant or k == .Error)
                return try self.buildVariantItem(a, env, f, blk, row, ety, k, loc);
        }

        if (self.type_info.getMethodBinding(row.callee)) |binding| {
            if (a.exprs.index.kinds.items[row.callee.toRaw()] == .FieldAccess) {
                const symbol = try self.methodSymbolName(a, binding.decl_id);
                callee.name = symbol;
                callee.fty = binding.func_type;
                callee_name = self.context.type_store.strs.get(callee.name);
                method_decl_id = binding.decl_id;
                method_binding = binding;

                if (binding.requires_implicit_receiver) {
                    const field_expr = a.exprs.get(.FieldAccess, row.callee);
                    method_arg_buf = try self.gpa.alloc(ast.ExprId, arg_ids.len + 1);
                    method_arg_buf[0] = field_expr.parent;
                    std.mem.copyForwards(ast.ExprId, method_arg_buf[1..], arg_ids);
                    arg_ids = method_arg_buf;
                }
            }
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
        if (callee.fty) |fty| {
            if (self.context.type_store.index.kinds.items[fty.toRaw()] == .Function) {
                const decl_id_opt = if (method_decl_id) |mid|
                    mid
                else
                    self.findTopLevelDeclByName(a, callee.name);
                if (decl_id_opt) |decl_id| {
                    const decl = a.exprs.Decl.get(decl_id);
                    const base_kind = a.exprs.index.kinds.items[decl.value.toRaw()];
                    if (base_kind == .FunctionLit) {
                        const params = a.exprs.param_pool.slice(a.exprs.get(.FunctionLit, decl.value).params);

                        var skip_params: usize = 0;
                        while (skip_params < params.len and a.exprs.Param.get(params[skip_params]).is_comptime) : (skip_params += 1) {}

                        var binding_infos: std.ArrayList(monomorphize.BindingInfo) = .empty;
                        defer {
                            for (binding_infos.items) |*info| info.deinit(self.gpa);
                            binding_infos.deinit(self.gpa);
                        }

                        var ok = true;
                        if (arg_ids.len >= skip_params) {
                            var idx: usize = 0;
                            while (idx < skip_params) : (idx += 1) {
                                const param = a.exprs.Param.get(params[idx]);
                                if (param.pat.isNone()) {
                                    ok = false;
                                    break;
                                }

                                const pname = self.bindingNameOfPattern(a, param.pat.unwrap()) orelse {
                                    ok = false;
                                    break;
                                };

                                var param_ty = if (idx < param_tys.len)
                                    param_tys[idx]
                                else
                                    self.context.type_store.tAny();

                                if (!param.ty.isNone()) {
                                    const ty_expr_id = param.ty.unwrap();
                                    if (a.exprs.index.kinds.items[ty_expr_id.toRaw()] == .Ident) {
                                        const ident_name = a.exprs.get(.Ident, ty_expr_id).name;
                                        for (binding_infos.items) |info| {
                                            if (info.name.eq(ident_name) and info.kind == .type_param) {
                                                param_ty = info.kind.type_param;
                                                break;
                                            }
                                        }
                                    }
                                }
                                const arg_expr = arg_ids[idx];
                                const param_kind = self.context.type_store.getKind(param_ty);

                                if (param_kind == .TypeType) {
                                    const targ = self.resolveTypeArg(arg_expr) orelse {
                                        ok = false;
                                        break;
                                    };
                                    try binding_infos.append(self.gpa, monomorphize.BindingInfo.typeParam(pname, targ));
                                } else {
                                    const comptime_val_opt = if (a.exprs.index.kinds.items[arg_expr.toRaw()] == .Literal)
                                        try self.constValueFromLiteral(a, arg_expr)
                                    else
                                        null;

                                    const comptime_val = if (comptime_val_opt) |cv| cv else self.evalComptimeExprValue(a, env, f, blk, arg_expr, param_ty) catch {
                                        ok = false;
                                        break;
                                    };

                                    var info = monomorphize.BindingInfo.valueParam(self.gpa, pname, param_ty, comptime_val) catch {
                                        ok = false;
                                        break;
                                    };
                                    binding_infos.append(self.gpa, info) catch |err| {
                                        info.deinit(self.gpa);
                                        return err;
                                    };
                                }
                            }
                        }

                        if (ok) {
                            const original_args = arg_ids;
                            var runtime_idx: usize = skip_params;
                            while (runtime_idx < params.len and runtime_idx < original_args.len) : (runtime_idx += 1) {
                                const param = a.exprs.Param.get(params[runtime_idx]);
                                if (param.pat.isNone()) continue;
                                const pname = self.bindingNameOfPattern(a, param.pat.unwrap()) orelse continue;

                                const param_ty = if (runtime_idx < param_tys.len)
                                    param_tys[runtime_idx]
                                else
                                    self.context.type_store.tAny();
                                if (!self.isAny(param_ty)) continue;

                                const arg_ty = self.getExprType(original_args[runtime_idx]) orelse continue;
                                if (self.isAny(arg_ty)) continue;

                                try binding_infos.append(self.gpa, monomorphize.BindingInfo.runtimeParam(pname, arg_ty));
                            }
                        }

                        if (ok and binding_infos.items.len > 0) {
                            const mangled = try self.mangleMonomorphName(callee.name, binding_infos.items);
                            const result = try self.monomorphizer.request(
                                a,
                                &self.context.type_store,
                                callee.name,
                                decl_id,
                                fty,
                                binding_infos.items,
                                skip_params,
                                mangled,
                            );
                            callee.name = result.mangled_name;
                            callee.fty = result.specialized_ty;
                            callee_name = self.context.type_store.strs.get(callee.name);
                            arg_ids = arg_ids[skip_params..];

                            const spec_info = self.context.type_store.get(.Function, result.specialized_ty);
                            param_tys = self.context.type_store.type_pool.slice(spec_info.params);
                            is_variadic = spec_info.is_variadic;
                            fixed = param_tys.len;
                            if (is_variadic and fixed > 0) fixed -= 1;
                        }
                    }
                }
            }
        }

        var vals = try self.gpa.alloc(tir.ValueId, arg_ids.len);
        defer self.gpa.free(vals);
        var i: usize = 0;
        while (i < arg_ids.len) : (i += 1) {
            const want: ?types.TypeId = if (i < fixed) param_tys[i] else null;
            const mode: LowerMode = blk: {
                if (method_binding) |mb| {
                    if (mb.requires_implicit_receiver and mb.needs_addr_of and i == 0) {
                        break :blk .lvalue_addr;
                    }
                }
                break :blk .rvalue;
            };
            vals[i] = try self.lowerExpr(a, env, f, blk, arg_ids[i], want, mode);
        }

        // Final safety: if we know param types, coerce the fixed ones
        if (param_tys.len > 0) {
            i = 0;
            while (i < vals.len and i < fixed) : (i += 1) {
                const want = param_tys[i];
                const got = blk: {
                    if (method_binding) |mb| {
                        if (mb.requires_implicit_receiver and mb.needs_addr_of and i == 0) {
                            break :blk mb.self_param_type orelse want;
                        }
                    }
                    break :blk self.getExprType(arg_ids[i]) orelse want;
                };
                if (want.toRaw() != got.toRaw()) {
                    const arg_loc = self.exprOptLoc(a, arg_ids[i]);
                    vals[i] = self.emitCoerce(blk, vals[i], got, want, arg_loc);
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
            if (expected) |e| if (!self.isVoid(e) and !self.isAny(e)) break :blk e;
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

        if (!self.isAny(ret_ty)) {
            self.type_info.setExprType(id, ret_ty);
            try self.noteExprType(id, ret_ty);
        }

        return blk.builder.call(blk, ret_ty, callee.name, vals, loc);
    }

    fn lowerTypeExprOpaque(
        self: *LowerTir,
        a: *const ast.Ast,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) tir.ValueId {
        const ty0 = self.getExprType(id) orelse self.context.type_store.tAny();
        const loc = self.exprOptLoc(a, id);
        const v = self.safeUndef(blk, ty0, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);
        const base_ty = blk: {
            const kind = self.context.type_store.index.kinds.items[ty0.toRaw()];
            if (kind == .Optional) {
                const opt = self.context.type_store.get(.Optional, ty0);
                break :blk opt.elem;
            }
            break :blk ty0;
        };

        const v = switch (lit.kind) {
            .int => blk: {
                const info = switch (lit.data) {
                    .int => |int_info| int_info,
                    else => return error.LoweringBug,
                };
                if (!info.valid) return error.LoweringBug;
                const value64 = std.math.cast(u64, info.value) orelse return error.LoweringBug;
                break :blk blk.builder.tirValue(.ConstInt, blk, base_ty, loc, .{ .value = value64 });
            },
            .imaginary => blk: {
                // ty0 must be Complex(elem). Build from (re=0, im=value)
                const tk = self.context.type_store.getKind(base_ty);
                if (tk != .Complex) break :blk blk.builder.tirValue(.ConstUndef, blk, ty0, loc, .{});
                const crow = self.context.type_store.get(.Complex, base_ty);
                const elem = crow.elem;
                const info = switch (lit.data) {
                    .imaginary => |imag| imag,
                    else => return error.LoweringBug,
                };
                if (!info.valid) return error.LoweringBug;
                const parsed = info.value;
                const re0 = blk.builder.tirValue(.ConstFloat, blk, elem, loc, .{ .value = 0.0 });
                const imv = blk.builder.tirValue(.ConstFloat, blk, elem, loc, .{ .value = parsed });
                const cv = blk.builder.tirValue(.ComplexMake, blk, base_ty, loc, .{ .re = re0, .im = imv });
                break :blk cv;
            },
            .float => blk: {
                const info = switch (lit.data) {
                    .float => |float_info| float_info,
                    else => return error.LoweringBug,
                };
                if (!info.valid) return error.LoweringBug;
                break :blk blk.builder.tirValue(.ConstFloat, blk, base_ty, loc, .{ .value = info.value });
            },
            .bool => blk.builder.tirValue(.ConstBool, blk, base_ty, loc, .{ .value = switch (lit.data) {
                .bool => |b| b,
                else => return error.LoweringBug,
            } }),
            .string => blk.builder.tirValue(.ConstString, blk, base_ty, loc, .{ .text = switch (lit.data) {
                .string => |sid| sid,
                else => return error.LoweringBug,
            } }),
            .char => blk.builder.tirValue(.ConstInt, blk, base_ty, loc, .{ .value = std.math.cast(u64, switch (lit.data) {
                .char => |codepoint| codepoint,
                else => return error.LoweringBug,
            }) orelse return error.LoweringBug }),
        };
        const want_ty = expected_ty orelse ty0;
        if (!want_ty.eq(base_ty)) return self.emitCoerce(blk, v, base_ty, want_ty, loc);
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
        const loc = self.exprOptLoc(a, id);
        const operand_loc = self.exprOptLoc(a, row.expr);
        if (row.op == .address_of or mode == .lvalue_addr) {
            // compute address of the operand
            const ety = self.getExprType(row.expr) orelse return error.LoweringBug;
            // When user asked address-of explicitly, produce pointer type
            if (row.op == .address_of) {
                const v = try self.lowerExpr(a, env, f, blk, row.expr, ety, .rvalue);
                return blk.builder.tirValue(.AddressOf, blk, self.context.type_store.mkPtr(ety, false), loc, .{ .value = v });
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

        const operand_expect: ?types.TypeId = switch (row.op) {
            .pos, .neg => ty0,
            .logical_not => self.context.type_store.tBool(),
            .address_of => null,
        };

        var v0 = try self.lowerExpr(a, env, f, blk, row.expr, operand_expect, .rvalue);

        const v = switch (row.op) {
            .pos => v0,
            .neg => blk: {
                // Use a zero that matches ty0’s kind; if Complex, build complex(0,0)
                const zero = zblk: {
                    const k = self.context.type_store.index.kinds.items[ty0.toRaw()];
                    if (k == .Complex) {
                        const crow = self.context.type_store.get(.Complex, ty0);
                        const re0 = blk.builder.tirValue(.ConstFloat, blk, crow.elem, loc, .{ .value = 0.0 });
                        const im0 = blk.builder.tirValue(.ConstFloat, blk, crow.elem, loc, .{ .value = 0.0 });
                        break :zblk blk.builder.tirValue(.ComplexMake, blk, ty0, loc, .{ .re = re0, .im = im0 });
                    }
                    if (self.isFloat(ty0)) break :zblk blk.builder.tirValue(.ConstFloat, blk, ty0, loc, .{ .value = 0.0 });
                    // break :zblk blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = 0 });
                    break :zblk blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = 0 });
                };
                break :blk blk.builder.bin(blk, .Sub, ty0, zero, v0, loc);
            },
            .logical_not => blk: {
                // Ensure operand is bool for logical ops
                const bty = self.context.type_store.tBool();
                const got = self.getExprType(row.expr) orelse bty;
                v0 = self.emitCoerce(blk, v0, got, bty, operand_loc);
                break :blk blk.builder.un1(blk, .LogicalNot, bty, v0, loc);
            },
            .address_of => unreachable,
        };
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
        return v;
    }

    fn lowerRange(self: *LowerTir, a: *const ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId, expected_ty: ?types.TypeId) anyerror!tir.ValueId {
        const row = a.exprs.get(.Range, id);
        const ty0 = self.getExprType(id) orelse return error.LoweringBug;
        const loc = self.exprOptLoc(a, id);
        const usize_ty = self.context.type_store.tUsize();
        const start_v = if (!row.start.isNone()) try self.lowerExpr(a, env, f, blk, row.start.unwrap(), usize_ty, .rvalue) else blk.builder.tirValue(.ConstUndef, blk, usize_ty, loc, .{});
        const end_v = if (!row.end.isNone()) try self.lowerExpr(a, env, f, blk, row.end.unwrap(), usize_ty, .rvalue) else blk.builder.tirValue(.ConstUndef, blk, usize_ty, loc, .{});
        const incl = blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = row.inclusive_right });
        // Materialize range as TIR RangeMake (typed as []usize)
        const v = blk.builder.rangeMake(blk, ty0, start_v, end_v, incl, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);
        const v = blk.builder.tirValue(.Load, blk, ty0, loc, .{ .ptr = ptr, .@"align" = 0 });
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);
        const ids = a.exprs.expr_pool.slice(row.elems);
        var vals = try self.gpa.alloc(tir.ValueId, ids.len);
        defer self.gpa.free(vals);
        var i: usize = 0;
        var expect_elem = self.context.type_store.tAny();
        const vk = self.context.type_store.index.kinds.items[ty0.toRaw()];
        if (vk == .Array) expect_elem = self.context.type_store.get(.Array, ty0).elem;
        while (i < ids.len) : (i += 1)
            vals[i] = try self.lowerExpr(a, env, f, blk, ids[i], expect_elem, .rvalue);
        const v = blk.builder.arrayMake(blk, ty0, vals, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);
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
        const v = blk.builder.structMake(blk, ty0, fields, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
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
        var ty0 = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tAny());
        const loc = self.exprOptLoc(a, id);

        if (self.context.type_store.getKind(ty0) == .Optional) {
            const opt = self.context.type_store.get(.Optional, ty0);
            if (self.context.type_store.getKind(opt.elem) == .Struct) {
                ty0 = opt.elem;
            }
        }

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
            break :blk blk.builder.tirValue(.UnionMake, blk, ty0, loc, .{
                .field_index = field.index,
                .value = field.value,
            });
        } else blk.builder.structMake(blk, ty0, fields, loc);

        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);
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
        const v = blk.builder.call(blk, ty0, make, vals, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);
        if (mode == .lvalue_addr) {
            const row = a.exprs.get(.IndexAccess, id);
            const base_ptr = try self.lowerExpr(a, env, f, blk, row.collection, null, .lvalue_addr);
            // Prefer a usize constant for literal indices to avoid casts in TIR
            const idx_v = blk: {
                const ik = a.exprs.index.kinds.items[row.index.toRaw()];
                if (ik == .Literal) {
                    const lit = a.exprs.get(.Literal, row.index);
                    if (lit.kind == .int) {
                        const info = switch (lit.data) {
                            .int => |int_info| int_info,
                            else => return error.LoweringBug,
                        };
                        if (!info.valid) return error.LoweringBug;
                        const value = std.math.cast(u64, info.value) orelse return error.LoweringBug;
                        const uv = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{
                            .value = value,
                        });
                        break :blk uv;
                    }
                }
                break :blk try self.lowerExpr(a, env, f, blk, row.index, self.context.type_store.tUsize(), .rvalue);
            };
            const idx = blk.builder.gepValue(idx_v);
            const rty = self.context.type_store.mkPtr(self.getExprType(id) orelse return error.LoweringBug, false);
            return blk.builder.gep(blk, rty, base_ptr, &.{idx}, loc);
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
                            const info = switch (lit.data) {
                                .int => |int_info| int_info,
                                else => return error.LoweringBug,
                            };
                            if (!info.valid) return error.LoweringBug;
                            const value = std.math.cast(u64, info.value) orelse return error.LoweringBug;
                            const uv = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{
                                .value = value,
                            });
                            break :blk uv;
                        }
                    }
                    break :blk try self.lowerExpr(a, env, f, blk, row.index, self.context.type_store.tUsize(), .rvalue);
                }
            };
            const v = blk.builder.indexOp(blk, ty0, base, idx, loc);
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
            return v;
        }
    }

    fn lowerImportedModuleMember(
        self: *LowerTir,
        a: *const ast.Ast,
        blk: *Builder.BlockFrame,
        parent_id: ast.ExprId,
        field_name: StrId,
        expected_ty: ?types.TypeId,
        loc: tir.OptLocId,
    ) !?tir.ValueId {
        const idr = a.exprs.get(.Ident, parent_id);
        if (self.findTopLevelImportByName(a, idr.name)) |imp_decl| {
            const ty0 = self.getExprType(parent_id) orelse (expected_ty orelse self.context.type_store.tAny());
            if (self.materializeImportedConst(&self.context.resolver, a, imp_decl, field_name, ty0, blk, self.pipeline)) |vv| {
                if (expected_ty) |want| return self.emitCoerce(blk, vv, ty0, want, loc);
                return vv;
            }
            const v = blk.builder.tirValue(.ConstUndef, blk, ty0, loc, .{});
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
            return v;
        }
        return null;
    }

    fn lowerEnumMember(
        self: *LowerTir,
        a: *const ast.Ast,
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
        const loc = self.exprOptLoc(a, id);
        const idx = self.type_info.getFieldIndex(id) orelse return error.LoweringBug; // enum members should be indexed by the checker
        var ev = blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = idx });
        if (expected_ty) |want| ev = self.emitCoerce(blk, ev, ty0, want, loc);
        return ev;
    }

    fn lowerVariantTagLiteral(
        self: *LowerTir,
        a: *const ast.Ast,
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
        const loc = self.exprOptLoc(a, id);
        if (self.context.type_store.getKind(payload_ty) != .Void) return null;
        const tag_val = blk.builder.extractField(blk, self.context.type_store.tI32(), self.safeUndef(blk, ty, loc), 0, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, tag_val, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);

        const parent_ty_opt = self.getExprType(row.parent);
        if (parent_ty_opt) |parent_ty| {
            const parent_kind = self.context.type_store.getKind(parent_ty);
            const field_name = a.exprs.strs.get(row.field);
            if (std.mem.eql(u8, field_name, "len")) {
                switch (parent_kind) {
                    .Array, .Slice, .DynArray, .String => {
                        const base = try self.lowerExpr(a, env, f, blk, row.parent, null, .rvalue);
                        const ty0 = self.context.type_store.tUsize();
                        const v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
                        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
                        return v;
                    },
                    else => {},
                }
            }
        }

        // 1) imported module member (rvalue only)
        if (mode == .rvalue and a.exprs.index.kinds.items[row.parent.toRaw()] == .Ident) {
            if (try self.lowerImportedModuleMember(a, blk, row.parent, row.field, expected_ty, loc)) |v| {
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
            return blk.builder.gep(blk, rptr_ty, parent_ptr, &.{blk.builder.gepConst(@intCast(idx))}, loc);
        }

        // 4) rvalue extraction
        const ty0 = self.getExprType(id) orelse (expected_ty orelse self.context.type_store.tAny());
        var base = try self.lowerExpr(a, env, f, blk, row.parent, null, .rvalue);

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
                base = blk.builder.extractField(blk, union_ty, base, 1, loc);
                break :blk blk.builder.tirValue(.UnionField, blk, ty0, loc, .{ .base = base, .field_index = resolved_idx });
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

                const tag_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), loc, .{ .value = resolved_idx });

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
                        blk.builder.tirValue(.ConstUndef, blk, union_ty, loc, .{})
                    else
                        blk.builder.tirValue(.UnionMake, blk, union_ty, loc, .{
                            .field_index = resolved_idx,
                            .value = self.undef(blk, payload_ty, loc),
                        });

                const v_res = blk.builder.structMake(blk, of_ty, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = tag_val },
                    .{ .index = 1, .name = .none(), .value = union_val },
                }, loc);

                if (expected_ty) |want| break :blk self.emitCoerce(blk, v_res, of_ty, want, loc);
                break :blk v_res;
            } else if (is_tuple)
                blk.builder.extractElem(blk, ty0, base, resolved_idx, loc)
            else if (parent_kind == .Union)
                blk.builder.tirValue(.UnionField, blk, ty0, loc, .{ .base = base, .field_index = resolved_idx })
            else
                blk.builder.extractField(blk, ty0, base, resolved_idx, loc);
        } else {
            if (is_tuple) return error.LoweringBug;
            v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
        }

        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);

        // Pre-lift a couple things we end up consulting a few times.
        var expr_ty_opt = self.getExprType(id);
        const did_opt = self.findTopLevelDeclByName(a, name);

        if (self.monomorph_context_stack.items.len > 0) {
            const ctx = &self.monomorph_context_stack.items[self.monomorph_context_stack.items.len - 1];
            if (ctx.lookupType(name)) |bound_ty| {
                expr_ty_opt = self.context.type_store.mkTypeType(bound_ty);
            }
        }

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
                const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = name });
                try env.bind(self.gpa, a, name, .{ .value = addr, .ty = gty, .is_slot = true });
                return addr;
            }

            // 3) Otherwise it must be a local value binding that needs a slot.
            if (env.lookup(name)) |bnd| {
                const slot_ty = self.context.type_store.mkPtr(want_elem, false);
                const slot = f.builder.tirValue(.Alloca, blk, slot_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });

                const src_ty = if (expr_ty_opt) |ty| if (!self.isAny(ty)) ty else bnd.ty else bnd.ty;
                const to_store = self.emitCoerce(blk, bnd.value, src_ty, want_elem, loc);
                _ = f.builder.tirValue(.Store, blk, want_elem, loc, .{ .ptr = slot, .value = to_store, .@"align" = 0 });

                try env.bind(self.gpa, a, name, .{ .value = slot, .ty = want_elem, .is_slot = true });
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
                const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = name });
                try env.bind(self.gpa, a, name, .{ .value = addr, .ty = gty, .is_slot = true });
                break :blk env.lookup(name).?;
            }

            // Not a value binding or top-level decl (likely a type name etc.).
            // Bind a safe placeholder so downstream code can keep going.
            const ty0 = expr_ty_opt orelse self.context.type_store.tAny();
            const placeholder = self.safeUndef(blk, ty0, loc);
            try env.bind(self.gpa, a, name, .{ .value = placeholder, .ty = ty0, .is_slot = false });
            break :blk env.lookup(name).?;
        };

        if (bnd.is_slot) {
            const load_ty = if (expr_ty_opt) |ty|
                if (!self.isAny(ty)) ty else bnd.ty
            else if (expected_ty) |want|
                want
            else
                bnd.ty;
            var loaded = blk.builder.tirValue(.Load, blk, load_ty, loc, .{ .ptr = bnd.value, .@"align" = 0 });
            if (expected_ty) |want| loaded = self.emitCoerce(blk, loaded, load_ty, want, loc);
            return loaded;
        }

        // Non-slot: coerce if a target type was requested.
        const got_ty = if (expr_ty_opt) |ty|
            if (!self.isAny(ty)) ty else bnd.ty
        else if (expected_ty) |want|
            want
        else
            bnd.ty;
        return if (expected_ty) |want| self.emitCoerce(blk, bnd.value, got_ty, want, loc) else bnd.value;
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
        const loc = self.exprOptLoc(a, id);

        // --- fast-path: variant/error equality against a tag literal (e.g. err == MyErr.NotFound) ---
        if (row.op == .eq or row.op == .neq) {
            const l_ty = self.getExprType(row.left);
            const r_ty = self.getExprType(row.right);

            // left is value, right is tag literal
            if (l_ty != null and self.isVariantLike(l_ty.?)) {
                if (self.tagConstFromTypePath(a, row.right)) |info| {
                    if (info.of_ty.toRaw() == l_ty.?.toRaw()) {
                        const lhs_val = try self.lowerExpr(a, env, f, blk, row.left, l_ty, .rvalue);
                        const lhs_tag = blk.builder.extractField(blk, self.context.type_store.tI32(), lhs_val, 0, loc);
                        const want_tag = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), loc, .{ .value = info.tag_idx });
                        const cmp = if (row.op == .eq)
                            blk.builder.binBool(blk, .CmpEq, lhs_tag, want_tag, loc)
                        else
                            blk.builder.binBool(blk, .CmpNe, lhs_tag, want_tag, loc);
                        return cmp;
                    }
                }
            }
            // right is value, left is tag literal
            if (r_ty != null and self.isVariantLike(r_ty.?)) {
                if (self.tagConstFromTypePath(a, row.left)) |info| {
                    if (info.of_ty.toRaw() == r_ty.?.toRaw()) {
                        const rhs_val = try self.lowerExpr(a, env, f, blk, row.right, r_ty, .rvalue);
                        const rhs_tag = blk.builder.extractField(blk, self.context.type_store.tI32(), rhs_val, 0, loc);
                        const want_tag = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), loc, .{ .value = info.tag_idx });
                        const cmp = if (row.op == .eq)
                            blk.builder.binBool(blk, .CmpEq, rhs_tag, want_tag, loc)
                        else
                            blk.builder.binBool(blk, .CmpNe, rhs_tag, want_tag, loc);
                        return cmp;
                    }
                }
            }
        }
        // --- end fast-path ---

        const lhs_stamped = self.getExprType(row.left);
        const rhs_stamped = self.getExprType(row.right);
        const lhs_hint = try self.refineExprType(a, env, row.left, lhs_stamped);
        const rhs_hint = try self.refineExprType(a, env, row.right, rhs_stamped);

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
                        const want = self.commonNumeric(lhs_hint, rhs_hint) orelse (expected_ty orelse self.context.type_store.tI64());
                        lhs_expect = want;
                        rhs_expect = want;
                        if (op_ty == null or self.isVoid(op_ty.?) or self.isAny(op_ty.?)) op_ty = want;
                    }
                } else {
                    const want = self.commonNumeric(lhs_hint, rhs_hint) orelse (expected_ty orelse self.context.type_store.tI64());
                    lhs_expect = want;
                    rhs_expect = want;
                    if (op_ty == null or self.isVoid(op_ty.?) or self.isAny(op_ty.?)) op_ty = want;
                }
            },
            .eq, .neq, .lt, .lte, .gt, .gte => {
                const want = self.commonNumeric(lhs_hint, rhs_hint) orelse lhs_hint orelse rhs_hint;
                lhs_expect = want;
                rhs_expect = want;
                op_ty = self.context.type_store.tBool();
                if (row.op == .eq or row.op == .neq) {
                    const ts = &self.context.type_store;
                    const lhs_ty_hint = lhs_hint orelse lhs_stamped;
                    const rhs_ty_hint = rhs_hint orelse rhs_stamped;
                    if (lhs_ty_hint) |lh| {
                        const lhs_kind = ts.index.kinds.items[lh.toRaw()];
                        if (lhs_kind == .Optional and rhs_ty_hint != null) {
                            const rhs_kind = ts.index.kinds.items[rhs_ty_hint.?.toRaw()];
                            if (rhs_kind != .Optional) {
                                lhs_expect = lh;
                                rhs_expect = ts.get(.Optional, lh).elem;
                            }
                        }
                    }
                    if (rhs_ty_hint) |rh| {
                        const rhs_kind = ts.index.kinds.items[rh.toRaw()];
                        if (rhs_kind == .Optional and lhs_ty_hint != null) {
                            const lhs_kind = ts.index.kinds.items[lhs_ty_hint.?.toRaw()];
                            if (lhs_kind != .Optional) {
                                rhs_expect = rh;
                                lhs_expect = ts.get(.Optional, rh).elem;
                            }
                        }
                    }
                }
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

        // --- Handle Optional(T) equality/inequality cases ---
        const l_ty = self.getExprType(row.left) orelse return error.LoweringBug;
        const r_ty = self.getExprType(row.right) orelse return error.LoweringBug;

        const l_is_optional = self.context.type_store.getKind(l_ty) == .Optional;
        const r_is_optional = self.context.type_store.getKind(r_ty) == .Optional;

        const bool_ty = self.context.type_store.tBool();
        const null_ty = self.context.type_store.mkOptional(self.context.type_store.tAny());

        if (row.op == .eq or row.op == .neq) {
            if (l_is_optional and r_is_optional) {
                if (l_ty.eq(null_ty) or r_ty.eq(null_ty)) { // One of them is explicitly the null type
                    const optional_val = if (l_ty.eq(null_ty)) r else l; // The non-null optional
                    const flag = blk.builder.extractField(blk, bool_ty, optional_val, 0, loc); // Extract is_some flag

                    const result = if (row.op == .eq)
                        blk.builder.binBool(blk, .CmpEq, flag, blk.builder.tirValue(.ConstBool, blk, bool_ty, loc, .{ .value = false }), .none())
                    else
                        blk.builder.binBool(blk, .CmpNe, flag, blk.builder.tirValue(.ConstBool, blk, bool_ty, loc, .{ .value = false }), .none());

                    return result;
                }
            } else if (l_is_optional != r_is_optional) {
                const opt_val = if (l_is_optional) l else r;
                const opt_ty = if (l_is_optional) l_ty else r_ty;
                const opt_info = self.context.type_store.get(.Optional, opt_ty);
                const other_val = if (l_is_optional) r else l;
                const other_ty_raw = if (l_is_optional)
                    (self.getExprType(row.right) orelse (rhs_expect orelse opt_info.elem))
                else
                    (self.getExprType(row.left) orelse (lhs_expect orelse opt_info.elem));

                var coerced_other = other_val;
                if (!other_ty_raw.eq(opt_info.elem)) {
                    coerced_other = self.emitCoerce(blk, other_val, other_ty_raw, opt_info.elem, loc);
                }

                const flag = blk.builder.extractField(blk, bool_ty, opt_val, 0, loc);
                const payload = blk.builder.extractField(blk, opt_info.elem, opt_val, 1, loc);

                var then_blk = try f.builder.beginBlock(f);
                var else_blk = try f.builder.beginBlock(f);
                var join_blk = try f.builder.beginBlock(f);

                const payload_param = try f.builder.addBlockParam(&then_blk, null, opt_info.elem);
                const other_param = try f.builder.addBlockParam(&then_blk, null, opt_info.elem);
                const res_param = try f.builder.addBlockParam(&join_blk, null, bool_ty);

                try f.builder.condBr(blk, flag, then_blk.id, &.{ payload, coerced_other }, else_blk.id, &.{}, loc);
                const orig_blk = blk.*;
                try f.builder.endBlock(f, orig_blk);

                const cmp = if (row.op == .eq)
                    then_blk.builder.binBool(&then_blk, .CmpEq, payload_param, other_param, loc)
                else
                    then_blk.builder.binBool(&then_blk, .CmpNe, payload_param, other_param, loc);

                try f.builder.br(&then_blk, join_blk.id, &.{cmp}, loc);
                try f.builder.endBlock(f, then_blk);

                const else_val = else_blk.builder.tirValue(.ConstBool, &else_blk, bool_ty, loc, .{ .value = (row.op == .neq) });
                try f.builder.br(&else_blk, join_blk.id, &.{else_val}, loc);
                try f.builder.endBlock(f, else_blk);

                blk.* = join_blk;
                return res_param;
            }
        }
        // --- End Optional(T) equality/inequality handling ---

        const ty0 = blk: {
            if (op_ty) |t| break :blk t;
            const want = self.commonNumeric(self.getExprType(row.left), self.getExprType(row.right)) orelse self.context.type_store.tI64();
            break :blk want;
        };
        try self.noteExprType(id, ty0);

        const v = switch (row.op) {
            .add => if (row.saturate)
                blk.builder.bin(blk, .BinSatAdd, ty0, l, r, loc)
            else if (row.wrap)
                blk.builder.bin(blk, .BinWrapAdd, ty0, l, r, loc)
            else
                blk.builder.bin(blk, .Add, ty0, l, r, loc),
            .sub => if (row.saturate)
                blk.builder.bin(blk, .BinSatSub, ty0, l, r, loc)
            else if (row.wrap)
                blk.builder.bin(blk, .BinWrapSub, ty0, l, r, loc)
            else
                blk.builder.bin(blk, .Sub, ty0, l, r, loc),
            .mul => if (row.saturate)
                blk.builder.bin(blk, .BinSatMul, ty0, l, r, loc)
            else if (row.wrap)
                blk.builder.bin(blk, .BinWrapMul, ty0, l, r, loc)
            else
                blk.builder.bin(blk, .Mul, ty0, l, r, loc),
            .div => blk.builder.bin(blk, .Div, ty0, l, r, loc),
            .mod => blk.builder.bin(blk, .Mod, ty0, l, r, loc),
            .shl => if (row.saturate)
                blk.builder.bin(blk, .BinSatShl, ty0, l, r, loc)
            else
                blk.builder.bin(blk, .Shl, ty0, l, r, loc),
            .shr => blk.builder.bin(blk, .Shr, ty0, l, r, loc),
            .bit_and => blk.builder.bin(blk, .BitAnd, ty0, l, r, loc),
            .bit_or => blk.builder.bin(blk, .BitOr, ty0, l, r, loc),
            .bit_xor => blk.builder.bin(blk, .BitXor, ty0, l, r, loc),
            .eq => blk.builder.binBool(blk, .CmpEq, l, r, loc),
            .neq => blk.builder.binBool(blk, .CmpNe, l, r, loc),
            .lt => blk.builder.binBool(blk, .CmpLt, l, r, loc),
            .lte => blk.builder.binBool(blk, .CmpLe, l, r, loc),
            .gt => blk.builder.binBool(blk, .CmpGt, l, r, loc),
            .gte => blk.builder.binBool(blk, .CmpGe, l, r, loc),
            .logical_and => blk.builder.binBool(blk, .LogicalAnd, l, r, loc),
            .logical_or => blk.builder.binBool(blk, .LogicalOr, l, r, loc),
            .@"orelse" => blk: {
                var then_blk = try f.builder.beginBlock(f);
                var else_blk = try f.builder.beginBlock(f);
                var join_blk = try f.builder.beginBlock(f);
                const opt_src_ty = self.getExprType(row.left) orelse return error.LoweringBug;
                if (self.context.type_store.index.kinds.items[opt_src_ty.toRaw()] != .Optional)
                    return error.LoweringBug;
                const opt_info = self.context.type_store.get(.Optional, opt_src_ty);
                const flag = blk.builder.extractField(blk, bool_ty, l, 0, loc);
                const payload = blk.builder.extractField(blk, opt_info.elem, l, 1, loc);
                const then_param = try f.builder.addBlockParam(&then_blk, null, opt_info.elem);
                const res_ty = expected_ty orelse ty0;
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
                try f.builder.condBr(blk, flag, then_blk.id, &.{payload}, else_blk.id, &.{}, loc);
                const orig_blk = blk.*;
                try f.builder.endBlock(f, orig_blk);

                var unwrapped = then_param;
                if (expected_ty) |want| {
                    unwrapped = self.emitCoerce(&then_blk, unwrapped, opt_info.elem, want, loc);
                }
                try f.builder.br(&then_blk, join_blk.id, &.{unwrapped}, loc);
                var rhs_v = r;
                if (expected_ty) |want| {
                    const gotr = self.getExprType(row.right) orelse want;
                    rhs_v = self.emitCoerce(&else_blk, rhs_v, gotr, want, loc);
                }
                try f.builder.br(&else_blk, join_blk.id, &.{rhs_v}, loc);
                try f.builder.endBlock(f, then_blk);
                try f.builder.endBlock(f, else_blk);
                blk.* = join_blk;
                break :blk res_param;
            },
        };
        if (expected_ty) |want| {
            if (!self.isVoid(ty0))
                return self.emitCoerce(blk, v, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);
        const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
        const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

        const lhs = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const es_ty = self.getExprType(row.expr).?;
        const es = self.context.type_store.get(.ErrorSet, es_ty);
        const expr_loc = self.exprOptLoc(a, row.expr);

        // An ErrorSet is a tagged union { tag, payload }, where tag=0 is OK, non-zero is Err.
        const tag = blk.builder.extractField(blk, self.context.type_store.tI32(), lhs, 0, expr_loc);
        const zero = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), expr_loc, .{ .value = 0 });
        const is_ok = blk.builder.binBool(blk, .CmpEq, tag, zero, expr_loc);

        var then_blk = try f.builder.beginBlock(f); // ok path
        var else_blk = try f.builder.beginBlock(f); // err path

        const payload_union_ty = self.context.type_store.mkUnion(&.{
            .{ .name = f.builder.intern("Ok"), .ty = es.value_ty },
            .{ .name = f.builder.intern("Err"), .ty = es.error_ty },
        });

        if (produce_value) {
            var join_blk = try f.builder.beginBlock(f);
            const res_ty = out_ty_guess;
            try self.noteExprType(id, res_ty);
            const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

            const br_cond = self.forceLocalCond(blk, is_ok, expr_loc);
            try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{}, loc);
            {
                // Close the current block after emitting the branch (mirrors lowerIf).
                const old = blk.*;
                try f.builder.endBlock(f, old);
            }

            // then (ok) branch: unwrap value
            const payload_union_ok = then_blk.builder.extractField(&then_blk, payload_union_ty, lhs, 1, expr_loc);
            const ok_val = then_blk.builder.tirValue(.UnionField, &then_blk, es.value_ty, loc, .{
                .base = payload_union_ok,
                .field_index = 0,
            });
            try f.builder.br(&then_blk, join_blk.id, &.{ok_val}, loc);

            // else (err) branch: unwrap error and run handler
            try env.pushScope(self.gpa); // Push scope for handler
            const payload_union_err = else_blk.builder.extractField(&else_blk, payload_union_ty, lhs, 1, expr_loc);
            const err_val = else_blk.builder.tirValue(.UnionField, &else_blk, es.error_ty, loc, .{
                .base = payload_union_err,
                .field_index = 1,
            });
            if (!row.binding_name.isNone()) {
                const name = row.binding_name.unwrap();
                try env.bind(self.gpa, a, name, .{ .value = err_val, .ty = es.error_ty, .is_slot = false });
            }
            try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
            _ = env.popScope(); // Pop scope after handler
            if (else_blk.term.isNone()) {
                const hv = try self.lowerBlockExprValue(a, env, f, &else_blk, row.handler, res_ty);
                try f.builder.br(&else_blk, join_blk.id, &.{hv}, loc);
            }

            try f.builder.endBlock(f, then_blk);
            try f.builder.endBlock(f, else_blk);
            blk.* = join_blk;
            return res_param;
        } else {
            // No value: conditionally run handler, then continue
            const exit_blk = try f.builder.beginBlock(f);

            const br_cond = self.forceLocalCond(blk, is_ok, expr_loc);
            try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{}, loc);
            {
                // Close the current block after emitting the branch.
                const old = blk.*;
                try f.builder.endBlock(f, old);
            }

            // then: nothing to do, jump to exit
            if (then_blk.term.isNone()) try f.builder.br(&then_blk, exit_blk.id, &.{}, loc);
            try f.builder.endBlock(f, then_blk);

            // else: execute handler as stmt
            try env.pushScope(self.gpa); // Push scope for handler
            const payload_union_err = else_blk.builder.extractField(&else_blk, payload_union_ty, lhs, 1, expr_loc);
            const err_val = else_blk.builder.tirValue(.UnionField, &else_blk, es.error_ty, loc, .{
                .base = payload_union_err,
                .field_index = 1,
            });
            if (!row.binding_name.isNone()) {
                const name = row.binding_name.unwrap();
                try env.bind(self.gpa, a, name, .{ .value = err_val, .ty = es.error_ty, .is_slot = false });
            }
            try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
            _ = env.popScope(); // Pop scope after handler
            if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{}, loc);
            try f.builder.endBlock(f, else_blk);

            blk.* = exit_blk;
            return self.safeUndef(blk, self.context.type_store.tAny(), loc);
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
        const loc = self.exprOptLoc(a, id);

        const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
        const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

        const cond_v = try self.lowerExpr(a, env, f, blk, row.cond, self.context.type_store.tBool(), .rvalue);

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

            // then
            try self.lowerExprAsStmtList(a, env, f, &then_blk, row.then_block);
            if (then_blk.term.isNone()) {
                var v_then = try self.lowerBlockExprValue(a, env, f, &then_blk, row.then_block, res_ty);
                if (expected_ty) |want| v_then = self.emitCoerce(&then_blk, v_then, self.getExprType(row.then_block) orelse res_ty, want, loc);
                try f.builder.br(&then_blk, join_blk.id, &.{v_then}, loc);
            }

            // else
            if (!row.else_block.isNone()) {
                try self.lowerExprAsStmtList(a, env, f, &else_blk, row.else_block.unwrap());
                if (else_blk.term.isNone()) {
                    var v_else = try self.lowerBlockExprValue(a, env, f, &else_blk, row.else_block.unwrap(), res_ty);
                    if (expected_ty) |want| v_else = self.emitCoerce(&else_blk, v_else, self.getExprType(row.else_block.unwrap()) orelse res_ty, want, loc);
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

            const br_cond = self.forceLocalCond(blk, cond_v, loc);
            try f.builder.condBr(blk, br_cond, then_blk.id, &.{}, else_blk.id, &.{}, loc);
            {
                const old = blk.*;
                try f.builder.endBlock(f, old);
            }

            try self.lowerExprAsStmtList(a, env, f, &then_blk, row.then_block);
            if (then_blk.term.isNone()) try f.builder.br(&then_blk, exit_blk.id, &.{}, loc);
            try f.builder.endBlock(f, then_blk);

            if (!row.else_block.isNone()) {
                try self.lowerExprAsStmtList(a, env, f, &else_blk, row.else_block.unwrap());
            }
            if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{}, loc);
            try f.builder.endBlock(f, else_blk);

            blk.* = exit_blk;
            return self.safeUndef(blk, self.context.type_store.tAny(), loc);
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
        const loc = self.exprOptLoc(a, id);
        const out = switch (row.kind) {
            .normal => blk.builder.tirValue(.CastNormal, blk, ty0, loc, .{ .value = v }),
            .bitcast => blk.builder.tirValue(.CastBit, blk, ty0, loc, .{ .value = v }),
            .saturate => blk.builder.tirValue(.CastSaturate, blk, ty0, loc, .{ .value = v }),
            .wrap => blk.builder.tirValue(.CastWrap, blk, ty0, loc, .{ .value = v }),
            .checked => blk.builder.tirValue(.CastChecked, blk, ty0, loc, .{ .value = v }),
        };
        if (expected_ty) |want| return self.emitCoerce(blk, out, ty0, want, loc);
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
        const elem_ty = self.getExprType(id) orelse return error.LoweringBug;
        const opt_ty = self.getExprType(row.expr) orelse return error.LoweringBug;
        if (self.context.type_store.index.kinds.items[opt_ty.toRaw()] != .Optional)
            return error.LoweringBug;
        const opt_info = self.context.type_store.get(.Optional, opt_ty);
        const loc = self.exprOptLoc(a, id);
        const expr_loc = self.exprOptLoc(a, row.expr);

        const opt_val = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const bool_ty = self.context.type_store.tBool();
        const flag = blk.builder.extractField(blk, bool_ty, opt_val, 0, expr_loc);
        const payload = blk.builder.extractField(blk, opt_info.elem, opt_val, 1, expr_loc);

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
        const loc = self.exprOptLoc(a, id);
        const out = blk.builder.call(blk, ty0, unwrap_ok, &.{v}, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, out, ty0, want, loc);
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
        const loc = self.exprOptLoc(a, id);

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
                const uv = self.safeUndef(blk, res_ty, loc);
                try f.builder.br(blk, join_blk.id, &.{uv}, loc);
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
                }, default_blk.id, &.{}, loc);

                // Fill bodies
                i = 0;
                while (i < arms.len) : (i += 1) {
                    const arm = a.exprs.MatchArm.get(arms[i]);
                    try self.lowerExprAsStmtList(a, env, f, &bodies[i], arm.body);
                    if (bodies[i].term.isNone()) {
                        var v = try self.lowerBlockExprValue(a, env, f, &bodies[i], arm.body, res_ty);
                        v = self.emitCoerce(&bodies[i], v, self.getExprType(arm.body) orelse res_ty, res_ty, loc);
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
            var cur = blk.*;

            var j: usize = 0;
            while (j < arms.len) : (j += 1) {
                const arm_id = arms[j];
                const arm = a.exprs.MatchArm.get(arm_id);

                var test_blk = try f.builder.beginBlock(f);
                var body_blk = try f.builder.beginBlock(f);
                const next_blk = if (j + 1 < arms.len) try f.builder.beginBlock(f) else join_blk;

                try f.builder.br(&cur, test_blk.id, &.{}, loc);
                try f.builder.endBlock(f, cur);

                // pattern test
                const arm_scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                const ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut, arm_scrut_ty, loc);

                // if last arm fails, feed an undef to the join
                const else_args = if (next_blk.id.toRaw() == join_blk.id.toRaw()) blkargs: {
                    const uv = self.safeUndef(&test_blk, res_ty, loc);
                    break :blkargs &.{uv};
                } else &.{};

                var binding_names = std.ArrayListUnmanaged(ast.StrId){};

                // Collect bindings for lowering

                try check_pattern_matching.collectPatternBindings(self.chk, arm.pattern, &binding_names);
                defer binding_names.deinit(self.gpa);

                var saved = std.ArrayListUnmanaged(BindingSnapshot){};
                try saved.ensureTotalCapacity(self.gpa, binding_names.items.len);
                defer saved.deinit(self.gpa);

                for (binding_names.items) |name| {
                    try saved.append(self.gpa, .{ .name = name, .prev = env.lookup(name) });
                }

                if (!arm.guard.isNone()) {
                    var guard_blk = try f.builder.beginBlock(f);
                    const br_cond = self.forceLocalCond(&test_blk, ok, loc);
                    try f.builder.condBr(&test_blk, br_cond, guard_blk.id, &.{}, next_blk.id, else_args, loc);
                    try f.builder.endBlock(f, test_blk);

                    try self.bindPattern(a, env, f, &guard_blk, arm.pattern, scrut, arm_scrut_ty);
                    const guard_id = arm.guard.unwrap();
                    const guard_loc = self.exprOptLoc(a, guard_id);
                    const guard_val = try self.lowerExpr(a, env, f, &guard_blk, guard_id, self.context.type_store.tBool(), .rvalue);
                    const guard_cond = self.forceLocalCond(&guard_blk, guard_val, guard_loc);
                    try self.restoreBindings(env, saved.items);
                    try f.builder.condBr(&guard_blk, guard_cond, body_blk.id, &.{}, next_blk.id, else_args, guard_loc);
                    try f.builder.endBlock(f, guard_blk);
                } else {
                    const br_cond = self.forceLocalCond(&test_blk, ok, loc);
                    try f.builder.condBr(&test_blk, br_cond, body_blk.id, &.{}, next_blk.id, else_args, loc);
                    try f.builder.endBlock(f, test_blk);
                }

                // bind + body
                const scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                try self.bindPattern(a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);

                if (body_blk.term.isNone()) {
                    var v2 = try self.lowerBlockExprValue(a, env, f, &body_blk, arm.body, res_ty);
                    v2 = self.emitCoerce(&body_blk, v2, self.getExprType(arm.body) orelse res_ty, res_ty, loc);
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
                return self.safeUndef(blk, self.context.type_store.tAny(), loc);
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
                }, default_blk.id, &.{}, loc);

                i = 0;
                while (i < arms.len) : (i += 1) {
                    const arm = a.exprs.MatchArm.get(arms[i]);
                    try self.lowerExprAsStmtList(a, env, f, &bodies[i], arm.body);
                    if (bodies[i].term.isNone()) try f.builder.br(&bodies[i], exit_blk.id, &.{}, loc);
                    try f.builder.endBlock(f, bodies[i]);
                }

                try f.builder.br(&default_blk, exit_blk.id, &.{}, loc);
                try f.builder.endBlock(f, default_blk);

                blk.* = exit_blk;
                return self.safeUndef(blk, self.context.type_store.tAny(), loc);
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

                try f.builder.br(&cur, test_blk.id, &.{}, loc);
                try f.builder.endBlock(f, cur);

                const arm_scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                const ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut, arm_scrut_ty, loc);

                if (!arm.guard.isNone()) {
                    var guard_blk = try f.builder.beginBlock(f);
                    const br_cond = self.forceLocalCond(&test_blk, ok, loc);
                    try f.builder.condBr(&test_blk, br_cond, guard_blk.id, &.{}, next_blk.id, &.{}, loc);
                    try f.builder.endBlock(f, test_blk);

                    var binding_names = std.ArrayListUnmanaged(ast.StrId){};
                    defer binding_names.deinit(self.gpa);
                    try check_pattern_matching.collectPatternBindings(self.chk, arm.pattern, &binding_names);

                    var saved = std.ArrayListUnmanaged(BindingSnapshot){};
                    defer saved.deinit(self.gpa);
                    for (binding_names.items) |name| {
                        try saved.append(self.gpa, .{ .name = name, .prev = env.lookup(name) });
                    }

                    try self.bindPattern(a, env, f, &guard_blk, arm.pattern, scrut, arm_scrut_ty);
                    const guard_id = arm.guard.unwrap();
                    const guard_loc = self.exprOptLoc(a, guard_id);
                    const guard_val = try self.lowerExpr(a, env, f, &guard_blk, guard_id, self.context.type_store.tBool(), .rvalue);
                    const guard_cond = self.forceLocalCond(&guard_blk, guard_val, guard_loc);
                    try self.restoreBindings(env, saved.items);
                    try f.builder.condBr(&guard_blk, guard_cond, body_blk.id, &.{}, next_blk.id, &.{}, guard_loc);
                    try f.builder.endBlock(f, guard_blk);
                } else {
                    const br_cond = self.forceLocalCond(&test_blk, ok, loc);
                    try f.builder.condBr(&test_blk, br_cond, body_blk.id, &.{}, next_blk.id, &.{}, loc);
                    try f.builder.endBlock(f, test_blk);
                }

                const scrut_ty = self.getExprType(row.expr) orelse self.context.type_store.tAny();
                try self.bindPattern(a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);

                try self.lowerExprAsStmtList(a, env, f, &body_blk, arm.body);
                if (body_blk.term.isNone()) try f.builder.br(&body_blk, exit_blk.id, &.{}, loc);

                try f.builder.endBlock(f, body_blk);
                cur = next_blk;
            }

            blk.* = exit_blk;
            return self.safeUndef(blk, self.context.type_store.tAny(), loc);
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
        const loc = self.exprOptLoc(a, id);

        const out_ty_guess = expected_ty orelse (self.getExprType(id) orelse self.context.type_store.tVoid());
        const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

        if (produce_value) {
            var exit_blk = try f.builder.beginBlock(f);
            var join_blk = try f.builder.beginBlock(f);
            const res_ty = out_ty_guess;
            const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

            try f.builder.br(blk, header.id, &.{}, loc);
            {
                const old = blk.*;
                try f.builder.endBlock(f, old);
            }

            if (row.is_pattern and !row.pattern.isNone() and !row.cond.isNone()) {
                const subj = try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), null, .rvalue);
                const subj_ty = self.getExprType(row.cond.unwrap()) orelse self.context.type_store.tAny();

                const ok = try self.matchPattern(a, env, f, &header, row.pattern.unwrap(), subj, subj_ty, loc);

                const br_cond = self.forceLocalCond(blk, ok, loc);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{}, loc);

                // bind `x` etc. for the body
                try self.bindPattern(a, env, f, &body, row.pattern.unwrap(), subj, subj_ty);
            } else {
                const cond_loc = if (!row.cond.isNone()) self.exprOptLoc(a, row.cond.unwrap()) else loc;
                const cond_v = if (!row.cond.isNone())
                    try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), self.context.type_store.tBool(), .rvalue)
                else
                    f.builder.tirValue(.ConstBool, &header, self.context.type_store.tBool(), cond_loc, .{ .value = true });

                const br_cond = self.forceLocalCond(&header, cond_v, cond_loc);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{}, loc);
            }

            try self.loop_stack.append(self.gpa, .{
                .label = row.label,
                .continue_block = header.id,
                .break_block = exit_blk.id,
                .has_result = true,
                .join_block = join_blk.id,
                .res_param = .some(res_param),
                .res_ty = res_ty,
                .continue_info = .none,
                .defer_len_at_entry = @intCast(env.defers.items.len),
            });

            try self.lowerExprAsStmtList(a, env, f, &body, row.body);
            if (body.term.isNone()) try f.builder.br(&body, header.id, &.{}, loc);
            try f.builder.endBlock(f, header);
            try f.builder.endBlock(f, body);

            const uv = self.safeUndef(&exit_blk, res_ty, loc);
            try f.builder.br(&exit_blk, join_blk.id, &.{uv}, loc);
            try f.builder.endBlock(f, exit_blk);

            _ = self.loop_stack.pop();
            blk.* = join_blk;
            return res_param;
        } else {
            // statement-position while
            const exit_blk = try f.builder.beginBlock(f);

            try f.builder.br(blk, header.id, &.{}, loc);
            {
                const old = blk.*;
                try f.builder.endBlock(f, old);
            }

            if (row.is_pattern and !row.pattern.isNone() and !row.cond.isNone()) {
                const subj = try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), null, .rvalue);
                const subj_ty = self.getExprType(row.cond.unwrap()) orelse self.context.type_store.tAny();

                const ok = try self.matchPattern(a, env, f, &header, row.pattern.unwrap(), subj, subj_ty, loc);

                const br_cond = self.forceLocalCond(&header, ok, loc);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{}, loc);

                // bind `x` etc. for the body
                try self.bindPattern(a, env, f, &body, row.pattern.unwrap(), subj, subj_ty);
            } else {
                const cond_loc = if (!row.cond.isNone()) self.exprOptLoc(a, row.cond.unwrap()) else loc;
                const cond_v = if (!row.cond.isNone())
                    try self.lowerExpr(a, env, f, &header, row.cond.unwrap(), self.context.type_store.tBool(), .rvalue)
                else
                    f.builder.tirValue(.ConstBool, &header, self.context.type_store.tBool(), cond_loc, .{ .value = true });
                const br_cond = self.forceLocalCond(&header, cond_v, cond_loc);
                try f.builder.condBr(&header, br_cond, body.id, &.{}, exit_blk.id, &.{}, loc);
            }

            try self.loop_stack.append(self.gpa, .{
                .label = row.label,
                .continue_block = header.id,
                .break_block = exit_blk.id,
                .has_result = false,
                .join_block = exit_blk.id,
                .res_ty = null,
                .res_param = .none(),
                .continue_info = .none,
                .defer_len_at_entry = @intCast(env.defers.items.len),
            });

            try self.lowerExprAsStmtList(a, env, f, &body, row.body);
            if (body.term.isNone()) try f.builder.br(&body, header.id, &.{}, loc);
            try f.builder.endBlock(f, header);
            try f.builder.endBlock(f, body);

            _ = self.loop_stack.pop();
            blk.* = exit_blk;
            return self.safeUndef(blk, self.context.type_store.tAny(), loc);
        }
    }

    fn getIterableLen(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        iter_ty: types.TypeId,
        idx_ty: types.TypeId,
        loc: tir.OptLocId,
    ) !tir.ValueId {
        const iter_ty_kind = self.context.type_store.index.kinds.items[iter_ty.toRaw()];
        return switch (iter_ty_kind) {
            .Array => blk: {
                const at = self.context.type_store.get(.Array, iter_ty);
                break :blk blk.builder.tirValue(.ConstInt, blk, idx_ty, loc, .{ .value = @as(u64, @intCast(at.len)) });
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
        const loc = self.exprOptLoc(a, id);
        const iterable_loc = self.exprOptLoc(a, row.iterable);

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
                .label = row.label,
                .continue_block = header.id,
                .break_block = exit_blk.id,
                .has_result = true,
                .join_block = join_blk.id,
                .res_param = .some(res_param),
                .res_ty = res_ty,
                .continue_info = .none,
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

                try self.bindPattern(a, env, f, &body, row.pattern, idx_param, idx_ty);

                var lc = &self.loop_stack.items[self.loop_stack.items.len - 1];
                lc.continue_block = update_block_id;
                lc.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param}, loc);

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            } else {
                // for x in iterable
                const arr_v = try self.lowerExpr(a, env, f, blk, row.iterable, null, .rvalue);
                const idx_ty = self.context.type_store.tUsize();
                const iter_ty = self.getExprType(row.iterable) orelse return error.LoweringBug;
                const len_v = try self.getIterableLen(blk, iter_ty, idx_ty, iterable_loc);

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

                const elem = blk.builder.indexOp(&body, elem_ty, arr_v, idx_param, iterable_loc);
                try self.bindPattern(a, env, f, &body, row.pattern, elem, elem_ty);

                var lc2 = &self.loop_stack.items[self.loop_stack.items.len - 1];
                lc2.continue_block = update_block_id;
                lc2.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param}, loc);

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            }

            // Exit -> join with a safe undef of the result type
            const uv = self.safeUndef(&exit_blk, res_ty, loc);
            try f.builder.br(&exit_blk, join_blk.id, &.{uv}, loc);
            try f.builder.endBlock(f, exit_blk);

            _ = self.loop_stack.pop();
            blk.* = join_blk;
            return res_param;
        } else {
            // statement-position for (no value)
            const exit_blk = try f.builder.beginBlock(f);

            // Loop stack entry (no value carried)
            try self.loop_stack.append(self.gpa, .{
                .label = row.label,
                .continue_block = header.id,
                .break_block = exit_blk.id,
                .has_result = false,
                .join_block = exit_blk.id,
                .res_ty = null,
                .res_param = .none(),
                .continue_info = .none,
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

                try self.bindPattern(a, env, f, &body, row.pattern, idx_param, idx_ty);

                var lc = &self.loop_stack.items[self.loop_stack.items.len - 1];
                lc.continue_block = update_block_id;
                lc.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);

                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param}, loc);

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            } else {
                const arr_v = try self.lowerExpr(a, env, f, blk, row.iterable, null, .rvalue);
                const idx_ty = self.context.type_store.tUsize();
                const iter_ty = self.getExprType(row.iterable) orelse return error.LoweringBug;
                const len_v = try self.getIterableLen(blk, iter_ty, idx_ty, iterable_loc);

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
                if (self.getExprType(row.iterable)) |it_ty| {
                    const ik = self.context.type_store.index.kinds.items[it_ty.toRaw()];
                    if (ik == .Array)
                        elem_ty = self.context.type_store.get(.Array, it_ty).elem
                    else if (ik == .Slice)
                        elem_ty = self.context.type_store.get(.Slice, it_ty).elem
                    else if (ik == .DynArray)
                        elem_ty = self.context.type_store.get(.DynArray, it_ty).elem;
                }
                const elem = blk.builder.indexOp(&body, elem_ty, arr_v, idx_param, iterable_loc);
                try self.bindPattern(a, env, f, &body, row.pattern, elem, elem_ty);

                var lc2 = &self.loop_stack.items[self.loop_stack.items.len - 1];
                lc2.continue_block = update_block_id;
                lc2.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param}, loc);

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            }

            _ = self.loop_stack.pop();
            blk.* = exit_blk;
            return self.safeUndef(blk, self.context.type_store.tAny(), loc);
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

        _ = try self.refineExprType(a, env, id, self.getExprType(id));

        return switch (expr_kind) {
            .Literal => self.lowerLiteral(a, blk, id, expected_ty),
            .NullLit => {
                const loc = self.exprOptLoc(a, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = blk.builder.constNull(blk, ty0, loc);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
                return v;
            },
            .UndefLit => {
                const loc = self.exprOptLoc(a, id);
                const ty0 = self.getExprType(id) orelse return error.LoweringBug;
                const v = blk.builder.tirValue(.ConstUndef, blk, ty0, loc, .{});
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
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
            .UnionType => self.lowerTypeExprOpaque(a, blk, id, expected_ty),
            .Match => self.lowerMatch(a, env, f, blk, id, expected_ty),
            .While => self.lowerWhile(a, env, f, blk, id, expected_ty),
            .For => self.lowerFor(a, env, f, blk, id, expected_ty),
            .MlirBlock => blk: {
                if (mode == .lvalue_addr) return error.LoweringBug;
                const loc = self.exprOptLoc(a, id);
                break :blk try self.lowerMlirBlock(a, env, f, blk, id, expected_ty, loc);
            },
            .Import => blk: {
                const loc = self.exprOptLoc(a, id);
                break :blk blk.builder.tirValue(
                    .ConstUndef,
                    blk,
                    self.getExprType(id) orelse self.context.type_store.tAny(),
                    loc,
                    .{},
                );
            },
            .VariantType, .EnumType, .StructType => self.lowerTypeExprOpaque(a, blk, id, expected_ty),
            .CodeBlock => blk: {
                const r = a.exprs.get(.CodeBlock, id);
                _ = r;
                // For now, treat as opaque and produce undef
                const ty0 = self.getExprType(id) orelse self.context.type_store.tAny();
                const loc = self.exprOptLoc(a, id);
                break :blk self.undef(blk, ty0, loc);
            },
            .ComptimeBlock => blk: {
                break :blk try self.jitEvalComptimeBlock(a, env, f, blk, id);
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
        const loc = self.exprOptLoc(a, block_expr);
        if (stmts.len == 0) {
            try self.noteExprType(block_expr, expected_ty);
            return self.safeUndef(blk, expected_ty, loc);
        }

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
            try self.noteExprType(block_expr, expected_ty);
            // If the checker stamped a different type than expected, keep your existing
            // higher-level coercion behavior by not touching `v` here beyond scope-finalization.
            try self.runNormalDefersFrom(a, env, f, blk, mark);
            return v;
        } else {
            try self.lowerStmt(a, env, f, blk, last);
            // Natural fallthrough out of the block scope: run normal defers for this block.
            // Early exits (return/break/continue) won’t reach here and already run defers.
            try self.runNormalDefersFrom(a, env, f, blk, mark);
            try self.noteExprType(block_expr, expected_ty);
            return self.safeUndef(blk, expected_ty, loc);
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
        if (lit.kind != .string) return null;
        const sid = switch (lit.data) {
            .string => |str_id| str_id,
            else => return null,
        };
        const s_full = a.exprs.strs.get(sid);

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

    fn refineExprType(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        expr: ast.ExprId,
        stamped: ?types.TypeId,
    ) !?types.TypeId {
        if (stamped) |ty| {
            if (!self.isAny(ty)) {
                try self.noteExprType(expr, ty);
                return ty;
            }
        }

        const kind = a.exprs.index.kinds.items[expr.toRaw()];
        switch (kind) {
            .Ident => {
                const name = a.exprs.get(.Ident, expr).name;
                if (env.lookup(name)) |bnd| {
                    try self.noteExprType(expr, bnd.ty);
                    return bnd.ty;
                }

                var i: usize = self.monomorph_context_stack.items.len;
                while (i > 0) {
                    i -= 1;
                    const ctx = &self.monomorph_context_stack.items[i];
                    if (ctx.lookupValue(name)) |vp| {
                        try self.noteExprType(expr, vp.ty);
                        return vp.ty;
                    }
                    if (ctx.lookupType(name)) |ty| {
                        const type_ty = self.context.type_store.mkTypeType(ty);
                        try self.noteExprType(expr, type_ty);
                        return type_ty;
                    }
                }
            },
            else => {},
        }

        return stamped;
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
                const loc = self.exprOptLoc(&me.ast, eid);
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
                const v = blk.builder.structMake(blk, expected_ty, fields, loc);
                self.gpa.free(fields);
                return v;
            },
            .Literal => {
                const lit = me.ast.exprs.get(.Literal, eid);
                const k = self.context.type_store.getKind(expected_ty);
                const loc = self.exprOptLoc(&me.ast, eid);
                switch (k) {
                    .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64 => {
                        const info = switch (lit.data) {
                            .int => |int_info| int_info,
                            else => return null,
                        };
                        if (!info.valid) return null;
                        const value = std.math.cast(u64, info.value) orelse return null;
                        return blk.builder.tirValue(.ConstInt, blk, expected_ty, loc, .{ .value = value });
                    },
                    .Bool => {
                        const b = switch (lit.data) {
                            .bool => |val| val,
                            else => return null,
                        };
                        return blk.builder.tirValue(.ConstBool, blk, expected_ty, loc, .{ .value = b });
                    },
                    .String => {
                        const sid = switch (lit.data) {
                            .string => |str_id| str_id,
                            else => return null,
                        };
                        return blk.builder.tirValue(.ConstString, blk, expected_ty, loc, .{ .text = sid });
                    },
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
        if (self.lookupExprTypeOverride(id)) |override| return override;
        const i = id.toRaw();
        std.debug.assert(i < self.type_info.expr_types.items.len);
        std.debug.assert(self.type_info.module_id == self.module_id);
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
        const loc = self.patternOptLoc(a, pid);
        switch (k) {
            .Binding => {
                const nm = a.pats.get(.Binding, pid).name;
                try env.bind(self.gpa, a, nm, .{ .value = value, .ty = vty, .is_slot = false });
            },
            .At => {
                const at = a.pats.get(.At, pid);
                try env.bind(self.gpa, a, at.binder, .{ .value = value, .ty = vty, .is_slot = false });
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
                    const ev = blk.builder.extractElem(blk, ety, value, @intCast(i), loc);
                    try self.bindPattern(a, env, f, blk, pe, ev, ety);
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
                    try self.bindPattern(a, env, f, blk, pat_elem, elem_val, elem_ty);
                }

                if (sl.has_rest and !sl.rest_binding.isNone()) {
                    const rest_pat = sl.rest_binding.unwrap();
                    const slice_ty = self.context.type_store.mkSlice(elem_ty);
                    const start = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = sl.rest_index });

                    var len_val: tir.ValueId = undefined;
                    const vty_kind = self.context.type_store.getKind(vty);
                    if (vty_kind == .Array) {
                        const arr_ty = self.context.type_store.get(.Array, vty);
                        len_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = arr_ty.len });
                    } else {
                        len_val = blk.builder.extractFieldNamed(blk, self.context.type_store.tUsize(), value, f.builder.intern("len"), loc);
                    }

                    const range_ty = self.context.type_store.mkSlice(self.context.type_store.tUsize());
                    const inclusive = blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
                    const range_val = blk.builder.rangeMake(blk, range_ty, start, len_val, inclusive, loc);
                    const rest_slice = blk.builder.indexOp(blk, slice_ty, value, range_val, loc);
                    try self.bindPattern(a, env, f, blk, rest_pat, rest_slice, slice_ty);
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
                        try self.bindPattern(a, env, f, blk, pe, ev, ety);
                    }
                } else {
                    // Single non-tuple payload
                    const pv = blk.builder.tirValue(.UnionField, blk, payload_ty, loc, .{
                        .base = union_agg,
                        .field_index = tag_idx,
                    });
                    if (pelems.len > 0) {
                        try self.bindPattern(a, env, f, blk, pelems[0], pv, payload_ty);
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
                                try self.bindPattern(a, env, f, blk, pf.pattern, field_val, sf.ty);
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
                            try self.bindPattern(a, env, f, blk, pf.pattern, field_val, sf.ty);
                            break;
                        }
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
        const loc = self.patternOptLoc(a, pid);
        switch (pk) {
            .Binding => {
                const nm = a.pats.get(.Binding, pid).name;
                if (to_slots) {
                    const slot_ty = self.context.type_store.mkPtr(vty, false);
                    const slot = f.builder.tirValue(.Alloca, blk, slot_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });
                    _ = f.builder.tirValue(.Store, blk, vty, loc, .{ .ptr = slot, .value = value, .@"align" = 0 });
                    try env.bind(self.gpa, a, nm, .{ .value = slot, .ty = vty, .is_slot = true });
                } else {
                    try env.bind(self.gpa, a, nm, .{ .value = value, .ty = vty, .is_slot = false });
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
                    const ev = blk.builder.extractElem(blk, ety, value, @intCast(i), loc);
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
                                extracted = blk.builder.extractField(blk, fty, value, @intCast(j), loc);
                                found = true;
                                break;
                            }
                        }
                        if (!found) {
                            // name not present on this struct type; bind undef of Any
                            extracted = self.undef(blk, fty, loc);
                        }
                    } else {
                        // Unknown layout; fall back to by-name extraction in IR
                        extracted = blk.builder.extractFieldNamed(blk, fty, value, pf.name, loc);
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
            const elem_loc = self.patternOptLoc(a, elems_pat[i]);
            const uv = self.undef(blk, ety, elem_loc);
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
                const field_loc = self.patternOptLoc(a, pf.pattern);
                const uv = self.undef(blk, fty, field_loc);
                try self.destructureDeclPattern(a, env, f, blk, pf.pattern, uv, fty, to_slots);
            }
        }
    }

    fn destructureDeclFromExpr(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        pid: ast.PatternId,
        src_expr: ast.ExprId,
        target_ty: types.TypeId,
        to_slots: bool,
    ) anyerror!void {
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        const target_kind = self.context.type_store.index.kinds.items[target_ty.toRaw()];
        const src_ty_opt = self.getExprType(src_expr);
        const src_default_ty = src_ty_opt orelse target_ty;
        const vty = if (target_kind == .Any) src_default_ty else target_ty;
        const expr_loc = self.exprOptLoc(a, src_expr);

        if (target_kind == .TypeType) {
            const result_ty = src_ty_opt orelse target_ty;
            const resolved_ty = blk: {
                if (self.context.type_store.getKind(result_ty) == .TypeType) {
                    const tt = self.context.type_store.get(.TypeType, result_ty);
                    if (!self.isAny(tt.of)) break :blk tt.of;
                    const computed = try self.runComptimeExpr(a, src_expr, result_ty, &[_]Pipeline.ComptimeBinding{});
                    break :blk switch (computed) {
                        .Type => |ty| ty,
                        else => return error.UnsupportedComptimeType,
                    };
                }
                const type_wrapper = self.context.type_store.mkTypeType(result_ty);
                const computed = try self.runComptimeExpr(a, src_expr, type_wrapper, &[_]Pipeline.ComptimeBinding{});
                break :blk switch (computed) {
                    .Type => |ty| ty,
                    else => return error.UnsupportedComptimeType,
                };
            };
            const type_ty = self.context.type_store.mkTypeType(resolved_ty);
            try self.noteExprType(src_expr, type_ty);
            const placeholder = self.safeUndef(blk, type_ty, expr_loc);
            try self.destructureDeclPattern(a, env, f, blk, pid, placeholder, type_ty, to_slots);
            return;
        }

        switch (pk) {
            .Binding => {
                const guess_ty = src_ty_opt orelse target_ty;
                const expect_ty = if (target_kind == .Any) guess_ty else target_ty;
                var raw = try self.lowerExpr(a, env, f, blk, src_expr, expect_ty, .rvalue);

                const refined = try self.refineExprType(a, env, src_expr, self.getExprType(src_expr));
                const src_ty = refined orelse guess_ty;
                const eff_ty = if (target_kind == .Any and !self.isAny(src_ty)) src_ty else target_ty;

                if (!src_ty.eq(eff_ty)) {
                    raw = self.emitCoerce(blk, raw, src_ty, eff_ty, expr_loc);
                }

                return try self.destructureDeclPattern(a, env, f, blk, pid, raw, eff_ty, to_slots);
            },
            .Tuple => {
                // If RHS is a tuple-literal, lower elements individually to avoid creating a temporary aggregate.
                if (a.exprs.index.kinds.items[src_expr.toRaw()] == .TupleLit) {
                    const src_ty = src_ty_opt orelse target_ty;
                    const eff_ty = if (target_kind == .Any) src_ty else target_ty;
                    try self.destructureDeclFromTupleLit(a, env, f, blk, pid, src_expr, eff_ty, to_slots);
                    return;
                }
                // Fallback: lower full expr once, then destructure via extracts.
                const src_ty = src_ty_opt orelse target_ty;
                const eff_ty = if (target_kind == .Any) src_ty else target_ty;
                const raw = try self.lowerExpr(a, env, f, blk, src_expr, eff_ty, .rvalue);
                const val = if (!src_ty.eq(eff_ty)) self.emitCoerce(blk, raw, src_ty, eff_ty, expr_loc) else raw;
                return try self.destructureDeclPattern(a, env, f, blk, pid, val, eff_ty, to_slots);
            },
            .Struct => {
                if (a.exprs.index.kinds.items[src_expr.toRaw()] == .StructLit) {
                    const src_ty = src_ty_opt orelse target_ty;
                    const eff_ty = if (target_kind == .Any) src_ty else target_ty;
                    try self.destructureDeclFromStructLit(a, env, f, blk, pid, src_expr, eff_ty, to_slots);
                    return;
                }
                // fallback: lower whole expr and destructure by field extraction
                const src_ty = src_ty_opt orelse target_ty;
                const eff_ty = if (target_kind == .Any) src_ty else target_ty;
                const raw = try self.lowerExpr(a, env, f, blk, src_expr, eff_ty, .rvalue);
                const val = if (!src_ty.eq(eff_ty)) self.emitCoerce(blk, raw, src_ty, eff_ty, expr_loc) else raw;
                return try self.destructureDeclPattern(a, env, f, blk, pid, val, eff_ty, to_slots);
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
                            const elem_loc = self.patternOptLoc(a, pelems[i]);
                            const uv = self.undef(blk, ety, elem_loc);
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
                    const elem_loc = self.patternOptLoc(a, pelems[i]);
                    const uv = self.undef(blk, ety, elem_loc);
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
                                    const field_loc = self.patternOptLoc(a, pf.pattern);
                                    const uv = self.undef(blk, fty, field_loc);
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
                    const field_loc = self.patternOptLoc(a, pf.pattern);
                    const uv = self.undef(blk, self.context.type_store.tAny(), field_loc);
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

    fn enumMemberValue(self: *const LowerTir, enum_ty: types.TypeId, name: StrId) ?u64 {
        const k = self.context.type_store.getKind(enum_ty);
        if (k != .Enum) return null;
        const er = self.context.type_store.get(.Enum, enum_ty);
        const members = self.context.type_store.enum_member_pool.slice(er.members);
        for (members, 0..) |mid, i| {
            const m = self.context.type_store.EnumMember.get(mid);
            if (m.name.eq(name)) return i;
        }
        return null;
    }

    /// Ensure `cond` is defined in `blk` and is i1.
    /// This always emits a local SSA (CastNormal) in `blk`, even if the source is already a bool.
    fn forceLocalCond(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        cond: tir.ValueId,
        loc: tir.OptLocId,
    ) tir.ValueId {
        const tBool = self.context.type_store.tBool();
        // Emit a bitcast to anchor `cond` in this block without changing its representation.
        return blk.builder.tirValue(.CastBit, blk, tBool, loc, .{ .value = cond });
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

    fn matchPattern(
        self: *LowerTir,
        a: *const ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        pid: ast.PatternId,
        scrut: tir.ValueId,
        scrut_ty: types.TypeId,
        loc: tir.OptLocId,
    ) !tir.ValueId {
        const k = a.pats.index.kinds.items[pid.toRaw()];
        switch (k) {
            .Wildcard => return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = true }),
            .Literal => {
                const pr = a.pats.get(.Literal, pid);
                const litv = try self.lowerExpr(a, env, f, blk, pr.expr, null, .rvalue);
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
                return try self.matchPattern(a, env, f, blk, node.pattern, scrut, scrut_ty, loc);
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
                    const elem_match = try self.matchPattern(a, env, f, blk, pat_elem, elem_val, elem_ty, loc);
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

                var result = try self.matchPattern(a, env, f, blk, alts[0], scrut, scrut_ty, loc);
                var i: usize = 1;
                while (i < alts.len) : (i += 1) {
                    const next_ok = try self.matchPattern(a, env, f, blk, alts[i], scrut, scrut_ty, loc);
                    result = blk.builder.binBool(blk, .LogicalOr, result, next_ok, loc);
                }
                return result;
            },
            .Range => {
                const range_pat = a.pats.get(.Range, pid);
                const bool_ty = self.context.type_store.tBool();
                var result = blk.builder.tirValue(.ConstBool, blk, bool_ty, loc, .{ .value = true });

                if (!range_pat.start.isNone()) {
                    const start_expr = range_pat.start.unwrap();
                    const start_val = try self.lowerExpr(a, env, f, blk, start_expr, scrut_ty, .rvalue);
                    const cmp = blk.builder.binBool(blk, .CmpGe, scrut, start_val, loc);
                    result = blk.builder.binBool(blk, .LogicalAnd, result, cmp, loc);
                }

                if (!range_pat.end.isNone()) {
                    const end_expr = range_pat.end.unwrap();
                    const end_val = try self.lowerExpr(a, env, f, blk, end_expr, scrut_ty, .rvalue);
                    const cmp = if (range_pat.inclusive_right)
                        blk.builder.binBool(blk, .CmpLe, scrut, end_val, loc)
                    else
                        blk.builder.binBool(blk, .CmpLt, scrut, end_val, loc);
                    result = blk.builder.binBool(blk, .LogicalAnd, result, cmp, loc);
                }

                return result;
            },
            .Binding, .Tuple, .Struct => {
                return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = true });
            },
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

pub fn evalComptimeExpr(
    gpa: std.mem.Allocator,
    context: *Context,
    pipeline: *Pipeline,
    type_info: *types.TypeInfo,
    module_id: usize,
    chk: *checker.Checker,
    ast_unit: *const ast.Ast,
    expr: ast.ExprId,
    result_ty: types.TypeId,
    bindings: []const Pipeline.ComptimeBinding,
) !comp.ComptimeValue {
    var lowerer = LowerTir.init(gpa, context, pipeline, type_info, module_id, chk);
    defer lowerer.deinit();
    return lowerer.runComptimeExpr(ast_unit, expr, result_ty, bindings);
}

// ============================
// Context structs
// ============================

const ContinueInfo = union(enum) {
    none,
    range: struct { update_block: tir.BlockId, idx_value: tir.ValueId },
};

const LoopCtx = struct { label: ast.OptStrId, break_block: tir.BlockId, continue_block: tir.BlockId, join_block: tir.BlockId, res_ty: ?types.TypeId, has_result: bool, res_param: tir.OptValueId, continue_info: ContinueInfo, defer_len_at_entry: u32 };

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

const ValueBinding = struct { value: tir.ValueId, ty: types.TypeId, is_slot: bool };
const DeferEntry = struct { expr: ast.ExprId, is_err: bool };
