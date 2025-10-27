const std = @import("std");
const ast = @import("ast.zig");
const cst = @import("cst.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const check_pattern_matching = @import("check_pattern_matching.zig");
const checker = @import("checker.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const codegen = @import("codegen_main.zig");
const comp = @import("comptime.zig");
const monomorphize = @import("monomorphize.zig");
const check_types = @import("check_types.zig");
const pipeline_mod = @import("pipeline.zig");
const cf = @import("lower_cf_tir.zig");
const package = @import("package.zig");

const StrId = @import("cst.zig").StrId;
const OptStrId = @import("cst.zig").OptStrId;
const Context = @import("compile.zig").Context;
const Pipeline = pipeline_mod.Pipeline;
const Builder = tir.Builder;
const List = std.ArrayList;

pub const ValueBinding = struct { value: tir.ValueId, ty: types.TypeId, is_slot: bool };

pub const BindingSnapshot = struct {
    name: ast.StrId,
    prev: ?ValueBinding,
};

const ExprTypeOverrideFrame = struct {
    map: std.AutoArrayHashMapUnmanaged(u32, types.TypeId) = .{},

    fn deinit(self: *ExprTypeOverrideFrame, gpa: std.mem.Allocator) void {
        self.map.deinit(gpa);
    }
};

const FunctionDeclContext = struct {
    ast: *ast.Ast,
    decl_id: ast.DeclId,
};

pub const LowerTir = @This();

gpa: std.mem.Allocator,
context: *Context,
pipeline: *Pipeline,
chk: *checker.Checker,
lower_context: List(*LowerContext) = .{},

// Simple loop stack to support break/continue in While/For (+ value loops)
pub const LowerContext = struct {
    loop_stack: List(cf.LoopCtx) = .{},
    module_call_cache: std.AutoHashMap(u64, StrId),
    method_lowered: std.AutoHashMap(usize, void),
    monomorphizer: monomorphize.Monomorphizer,
    monomorph_context_stack: List(monomorphize.MonomorphizationContext) = .{},
    expr_type_override_stack: List(ExprTypeOverrideFrame) = .{},
};

pub var g_mlir_inited: bool = false;
pub var g_mlir_ctx: mlir.Context = undefined;

pub fn init(
    gpa: std.mem.Allocator,
    context: *Context,
    pipeline: *Pipeline,
    chk: *checker.Checker,
) LowerTir {
    return .{
        .gpa = gpa,
        .context = context,
        .pipeline = pipeline,
        .chk = chk,
        .lower_context = .{},
    };
}

pub fn deinit(_: *LowerTir) void {
    //     ctx.loop_stack.deinit(self.gpa);
    //     ctx.module_call_cache.deinit();
    //     ctx.method_lowered.deinit();
    //     while (ctx.monomorph_context_stack.items.len > 0) {
    //         var ctx = ctx.monomorph_context_stack.pop().?;
    //         ctx.deinit(self.gpa);
    //     }
    //     ctx.monomorph_context_stack.deinit(self.gpa);
    //     while (ctx.expr_type_override_stack.items.len > 0) {
    //         ctx.expr_type_override_stack.items[ctx.expr_type_override_stack.items.len - 1].deinit(self.gpa);
    //         ctx.expr_type_override_stack.items.len -= 1;
    //     }
    //     ctx.expr_type_override_stack.deinit(self.gpa);
    //     self.monomorphizer.deinit();
}

pub fn run(self: *LowerTir, levels: *const compile.DependencyLevels) !*tir.TIR {
    var unit_by_file = std.AutoHashMap(u32, *package.FileUnit).init(self.gpa);
    defer unit_by_file.deinit();

    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var source_iter = pkg.value_ptr.sources.iterator();
        while (source_iter.next()) |unit| {
            try unit_by_file.put(unit.value_ptr.file_id, unit.value_ptr);
        }
    }

    var threads = std.ArrayList(struct { std.Thread, *tir.TIR }){};
    defer threads.deinit(self.gpa);

    for (levels.levels.items) |level| {
        threads.clearRetainingCapacity();
        if (level.items.len == 0) continue;

        for (level.items) |file_id| {
            const unit = unit_by_file.get(file_id) orelse continue;
            if (unit.ast == null) continue;
            const t = try self.gpa.create(tir.TIR);
            t.* = tir.TIR.init(self.gpa, self.context.type_store);
            const ctx = try self.gpa.create(LowerContext);
            ctx.* = LowerContext{
                .method_lowered = .init(self.gpa),
                .module_call_cache = .init(self.gpa),
                .monomorphizer = .init(self.gpa),
            };
            const thread = try std.Thread.spawn(.{}, runAst, .{ self, unit.ast.?, t, ctx });
            try threads.append(self.gpa, .{ thread, t });
        }

        for (threads.items, 0..) |item, i| {
            const thread, const t = item;
            thread.join();
            const unit = unit_by_file.get(level.items[i]) orelse continue;
            unit.tir = t;
        }
    }

    const main_pkg = self.context.compilation_unit.packages.getPtr("main") orelse return error.PackageNotFound;
    return main_pkg.sources.entries.get(0).value.tir.?;
}

pub fn runAst(self: *LowerTir, ast_unit: *ast.Ast, t: *tir.TIR, ctx: *LowerContext) !void {
    var b = Builder.init(self.gpa, t);

    try self.lowerGlobalMlir(ctx, ast_unit, &b);

    // Lower top-level decls: functions and globals
    const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
    for (decls) |did| try self.lowerTopDecl(ctx, ast_unit, &b, did);

    var method_it = self.context.type_store.method_table.iterator();
    while (method_it.next()) |entry| {
        const method = entry.value_ptr.*;
        if (method.decl_ast != ast_unit) continue;

        const decl_id = method.decl_id;
        if (ctx.method_lowered.contains(decl_id.toRaw())) continue;
        const name = try self.methodSymbolName(ast_unit, decl_id);
        try self.tryLowerNamedFunction(ctx, ast_unit, &b, decl_id, name, true);
    }

    try ctx.monomorphizer.run(self, ctx, &b, comp.monomorphLowerCallback);
}

fn pushExprTypeOverrideFrame(self: *LowerTir, ctx: *LowerContext) !void {
    try ctx.expr_type_override_stack.append(self.gpa, .{});
}

fn popExprTypeOverrideFrame(self: *LowerTir, ctx: *LowerContext) void {
    if (ctx.expr_type_override_stack.items.len == 0) return;
    const idx = ctx.expr_type_override_stack.items.len - 1;
    ctx.expr_type_override_stack.items[idx].deinit(self.gpa);
    ctx.expr_type_override_stack.items.len -= 1;
}

pub fn noteExprType(self: *LowerTir, ctx: *LowerContext, expr: ast.ExprId, ty: types.TypeId) !void {
    if (ctx.expr_type_override_stack.items.len == 0) return;
    if (self.isAny(ty)) return;
    var frame = &ctx.expr_type_override_stack.items[ctx.expr_type_override_stack.items.len - 1];
    try frame.map.put(self.gpa, expr.toRaw(), ty);
}

fn lookupExprTypeOverride(_: *const LowerTir, ctx: *LowerContext, expr: ast.ExprId) ?types.TypeId {
    var i: usize = ctx.expr_type_override_stack.items.len;
    while (i > 0) {
        i -= 1;
        const frame = &ctx.expr_type_override_stack.items[i];
        if (frame.map.get(expr.toRaw())) |entry| {
            return entry;
        }
    }
    return null;
}

fn constInitFromLiteral(self: *LowerTir, a: *ast.Ast, expr: ast.ExprId, ty: types.TypeId) ?tir.ConstInit {
    const kind = a.exprs.index.kinds.items[expr.toRaw()];
    if (kind != .Literal) return null;
    const lit = a.exprs.get(.Literal, expr);

    const ty_kind = self.context.type_store.getKind(ty);
    return switch (ty_kind) {
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => blk: {
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
            const value = switch (lit.data) {
                .bool => |b| b,
                else => return null,
            };
            break :blk tir.ConstInit{ .bool = value };
        },
        else => null,
    };
}

fn lowerDynArrayAppend(
    self: *LowerTir,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    loc: tir.OptLocId,
    binding: types.MethodBinding,
    args: []const tir.ValueId,
) !tir.ValueId {
    std.debug.assert(binding.builtin != null and binding.builtin.? == .dynarray_append);
    if (args.len < 2) return error.LoweringBug;

    const ts = self.context.type_store;
    const owner_kind = ts.getKind(binding.owner_type);
    if (owner_kind != .DynArray) return error.LoweringBug;

    const dyn_info = ts.get(.DynArray, binding.owner_type);
    const elem_ty = dyn_info.elem;
    const usize_ty = ts.tUsize();
    const ptr_elem_ty = ts.mkPtr(elem_ty, false);
    const ptr_ptr_elem_ty = ts.mkPtr(ptr_elem_ty, false);
    const ptr_usize_ty = ts.mkPtr(usize_ty, false);
    const ptr_void_ty = ts.mkPtr(ts.tVoid(), false);

    const array_ptr = args[0];
    const value = args[1];

    const data_ptr_ptr = blk.builder.gep(blk, ptr_ptr_elem_ty, array_ptr, &.{blk.builder.gepConst(0)}, loc);
    const len_ptr = blk.builder.gep(blk, ptr_usize_ty, array_ptr, &.{blk.builder.gepConst(1)}, loc);
    const cap_ptr = blk.builder.gep(blk, ptr_usize_ty, array_ptr, &.{blk.builder.gepConst(2)}, loc);

    const len_val = blk.builder.tirValue(.Load, blk, usize_ty, loc, .{ .ptr = len_ptr, .@"align" = 0 });
    const cap_val = blk.builder.tirValue(.Load, blk, usize_ty, loc, .{ .ptr = cap_ptr, .@"align" = 0 });

    const need_grow_raw = blk.builder.binBool(blk, .CmpEq, len_val, cap_val, loc);

    var grow_blk = try f.builder.beginBlock(f);
    const cont_blk = try f.builder.beginBlock(f);

    const grow_cond = self.forceLocalCond(blk, need_grow_raw, loc);
    try f.builder.condBr(blk, grow_cond, grow_blk.id, &.{}, cont_blk.id, &.{}, loc);
    {
        const old = blk.*;
        try f.builder.endBlock(f, old);
    }

    {
        // Growth path
        const data_ptr = grow_blk.builder.tirValue(.Load, &grow_blk, ptr_elem_ty, loc, .{ .ptr = data_ptr_ptr, .@"align" = 0 });
        const zero_const = grow_blk.builder.tirValue(.ConstInt, &grow_blk, usize_ty, loc, .{ .value = 0 });
        const cap_is_zero = grow_blk.builder.binBool(&grow_blk, .CmpEq, cap_val, zero_const, loc);
        const one_const = grow_blk.builder.tirValue(.ConstInt, &grow_blk, usize_ty, loc, .{ .value = 1 });
        const two_const = grow_blk.builder.tirValue(.ConstInt, &grow_blk, usize_ty, loc, .{ .value = 2 });
        const doubled = grow_blk.builder.bin(&grow_blk, .Mul, usize_ty, cap_val, two_const, loc);
        const new_cap = grow_blk.builder.tirValue(.Select, &grow_blk, usize_ty, loc, .{
            .cond = cap_is_zero,
            .then_value = one_const,
            .else_value = doubled,
        });

        const elem_size = check_types.typeSize(self.context, elem_ty) orelse unreachable;
        const elem_size_u64 = std.math.cast(u64, elem_size) orelse unreachable;
        const elem_size_const = grow_blk.builder.tirValue(.ConstInt, &grow_blk, usize_ty, loc, .{ .value = elem_size_u64 });
        const new_bytes = grow_blk.builder.bin(&grow_blk, .Mul, usize_ty, new_cap, elem_size_const, loc);

        const data_ptr_void = grow_blk.builder.tirValue(.CastBit, &grow_blk, ptr_void_ty, loc, .{ .value = data_ptr });
        const realloc_name = grow_blk.builder.intern("rt_realloc");
        const new_data_void = grow_blk.builder.call(&grow_blk, ptr_void_ty, realloc_name, &.{ data_ptr_void, new_bytes }, loc);
        const new_data_ptr = grow_blk.builder.tirValue(.CastBit, &grow_blk, ptr_elem_ty, loc, .{ .value = new_data_void });

        _ = grow_blk.builder.tirValue(.Store, &grow_blk, ptr_elem_ty, loc, .{ .ptr = data_ptr_ptr, .value = new_data_ptr, .@"align" = 0 });
        _ = grow_blk.builder.tirValue(.Store, &grow_blk, usize_ty, loc, .{ .ptr = cap_ptr, .value = new_cap, .@"align" = 0 });

        try f.builder.br(&grow_blk, cont_blk.id, &.{}, loc);
        try f.builder.endBlock(f, grow_blk);
    }

    blk.* = cont_blk;

    const data_ptr_cur = blk.builder.tirValue(.Load, blk, ptr_elem_ty, loc, .{ .ptr = data_ptr_ptr, .@"align" = 0 });
    const len_cur = blk.builder.tirValue(.Load, blk, usize_ty, loc, .{ .ptr = len_ptr, .@"align" = 0 });

    const len_index = blk.builder.gepValue(len_cur);
    const slot_ptr = blk.builder.gep(blk, ptr_elem_ty, data_ptr_cur, &.{len_index}, loc);
    _ = blk.builder.tirValue(.Store, blk, elem_ty, loc, .{ .ptr = slot_ptr, .value = value, .@"align" = 0 });

    const one_inc = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = 1 });
    const new_len = blk.builder.bin(blk, .Add, usize_ty, len_cur, one_inc, loc);
    _ = blk.builder.tirValue(.Store, blk, usize_ty, loc, .{ .ptr = len_ptr, .value = new_len, .@"align" = 0 });

    return self.safeUndef(blk, ts.tVoid(), loc);
}

fn lowerGlobalMlir(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, b: *Builder) !void {
    var global_mlir_decls: List(ast.DeclId) = .empty;
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
    var env = cf.Env{};
    defer env.deinit(self.gpa);

    for (global_mlir_decls.items) |did| {
        const d = a.exprs.Decl.get(did);
        _ = try self.lowerExpr(ctx, a, &env, &f, &blk, d.value, null, .rvalue);
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
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    loc: tir.OptLocId,
) !tir.ValueId {
    const row = a.exprs.get(.MlirBlock, id);
    const expr_ty = self.getExprType(ctx, a, id);
    var ty0 = expr_ty;
    if (self.isAny(ty0)) {
        ty0 = switch (row.kind) {
            .Module => self.context.type_store.tMlirModule(),
            .Attribute => self.context.type_store.tMlirAttribute(),
            .Type => self.context.type_store.tMlirType(),
            .Operation => ty0,
        };
    }
    if (expected_ty) |want| {
        if (self.isAny(expr_ty) and !self.isAny(want)) {
            ty0 = want;
        }
    }

    // Lower args
    const ast_piece_ids = a.exprs.mlir_piece_pool.slice(row.pieces);
    var tir_piece_ids = List(tir.MlirPieceId){};
    defer tir_piece_ids.deinit(self.gpa);
    for (ast_piece_ids) |pid| {
        const piece = a.exprs.MlirPiece.get(pid);
        var splice_value: comp.ComptimeValue = .Void;
        if (piece.kind == .splice) {
            splice_value = try self.resolveMlirSpliceValue(ctx, a, pid, piece.text, row.loc);
        }
        const new_id = blk.builder.t.instrs.addMlirPieceRow(
            .{ .kind = piece.kind, .text = piece.text, .value = splice_value },
        );
        tir_piece_ids.append(self.gpa, new_id) catch @panic("OOM");
    }
    const pieces_range = blk.builder.t.instrs.mlir_piece_pool.pushMany(self.gpa, tir_piece_ids.items);

    const arg_ids = a.exprs.expr_pool.slice(row.args);
    var arg_vals = try self.gpa.alloc(tir.ValueId, arg_ids.len);
    defer self.gpa.free(arg_vals);
    for (arg_ids, 0..) |arg_id, i| {
        arg_vals[i] = try self.lowerExpr(ctx, a, env, f, blk, arg_id, null, .rvalue);
    }
    const args_range = blk.builder.t.instrs.value_pool.pushMany(self.gpa, arg_vals);

    const result_id = blk.builder.freshValue();
    const iid = blk.builder.t.instrs.add(.MlirBlock, .{
        .result = .some(result_id),
        .ty = ty0,
        .kind = row.kind,
        .expr = id,
        .text = row.text,
        .pieces = pieces_range,
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

fn resolveMlirSpliceValue(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    piece_id: ast.MlirPieceId,
    name: StrId,
    loc_id: ast.LocId,
) !comp.ComptimeValue {
    const info = a.type_info.getMlirSpliceInfo(piece_id) orelse unreachable;
    const diag_loc = a.exprs.locs.get(loc_id);
    const name_str = a.exprs.strs.get(name);
    switch (info) {
        .decl => |decl_info| {
            const decl = a.exprs.Decl.get(decl_info.decl_id);
            const expect_ty = getDeclType(a, decl_info.decl_id) orelse
                self.getExprType(ctx, a, decl.value);
            return comp.evalComptimeExprValue(self, ctx, a, decl.value, expect_ty);
        },
        .value_param => |param_info| {
            var i: usize = ctx.monomorph_context_stack.items.len;
            while (i > 0) {
                i -= 1;
                const context = &ctx.monomorph_context_stack.items[i];
                if (context.lookupValue(param_info.name)) |binding| {
                    return comp.cloneComptimeValue(self, binding.value);
                }
            }
            try self.context.diags.addError(diag_loc, .mlir_splice_unbound, .{name_str});
            return error.LoweringBug;
        },
        .type_param => |param_info| {
            var i: usize = ctx.monomorph_context_stack.items.len;
            while (i > 0) {
                i -= 1;
                const context = &ctx.monomorph_context_stack.items[i];
                if (context.lookupType(param_info.name)) |ty| {
                    return comp.ComptimeValue{ .Type = ty };
                }
            }
            try self.context.diags.addError(diag_loc, .mlir_splice_unbound, .{name_str});
            return error.LoweringBug;
        },
    }
}

// ============================
// Utilities / common helpers
// ============================

pub fn resolveArrayLen(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    size_expr: ast.ExprId,
    loc: tir.OptLocId,
) !usize {
    const comptime_val = comp.runComptimeExpr(self, ctx, a, size_expr, self.context.type_store.tUsize(), &.{}) catch {
        try self.context.diags.addError(a.exprs.locs.get(loc.unwrap()), .array_size_not_integer_literal, .{});
        return error.ComptimeEvalFailed;
    };

    return switch (comptime_val) {
        .Int => |i| @intCast(i),
        else => {
            try self.context.diags.addError(a.exprs.locs.get(loc.unwrap()), .array_size_not_integer_literal, .{});
            return error.ComptimeEvalFailed;
        },
    };
}

const LowerMode = enum { rvalue, lvalue_addr };

pub fn isVoid(self: *const LowerTir, ty: types.TypeId) bool {
    return self.context.type_store.index.kinds.items[ty.toRaw()] == .Void;
}

pub fn optLoc(a: *ast.Ast, id: anytype) tir.OptLocId {
    const store, const Kind = switch (@TypeOf(id)) {
        ast.ExprId => .{ a.exprs, ast.ExprKind },
        ast.PatternId => .{ a.pats, ast.PatternKind },
        ast.StmtId => .{ a.stmts, ast.StmtKind },
        else => @compileError("invalid type"),
    };
    const kind = store.index.kinds.items[id.toRaw()];
    inline for (@typeInfo(Kind).@"enum".fields) |field| {
        const tag: Kind = @enumFromInt(field.value);
        if (tag == kind) {
            const row = store.get(tag, id);
            if (comptime @hasField(@TypeOf(row), "loc")) {
                return .some(row.loc);
            }
            return .none();
        }
    }
    return .none();
}

// Produce an undef that is never-void; if asked for void, give Any instead.
pub fn safeUndef(self: *LowerTir, blk: *Builder.BlockFrame, ty: types.TypeId, loc: tir.OptLocId) tir.ValueId {
    if (self.isVoid(ty)) {
        return blk.builder.tirValue(.ConstUndef, blk, self.context.type_store.tAny(), loc, .{});
    }
    return blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{});
}
/// Insert an explicit coercion that realizes what the checker proved assignable/castable.
pub fn emitCoerce(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    v: tir.ValueId,
    got: types.TypeId,
    want: types.TypeId,
    loc: tir.OptLocId,
) tir.ValueId {
    if (got.eq(want)) return v;

    const ts = self.context.type_store;
    const gk = ts.index.kinds.items[got.toRaw()];
    const wk = ts.index.kinds.items[want.toRaw()];

    switch (wk) {
        .ErrorSet => blk: {
            const es = ts.get(.ErrorSet, want);
            const tag_value: u32, const field_index: u32 = if (got.toRaw() == es.value_ty.toRaw())
                .{ 0, 0 } // Ok(T)
            else if (got.toRaw() == es.error_ty.toRaw())
                .{ 1, 1 } // Err(E)
            else
                break :blk; // (e.g., for anyerror -> !T).

            const i32_ty = ts.tI32();
            const payload_union_ty = ts.mkUnion(&[_]types.TypeStore.StructFieldArg{
                .{ .name = blk.builder.intern("Ok"), .ty = es.value_ty },
                .{ .name = blk.builder.intern("Err"), .ty = es.error_ty },
            });

            // Create the tag (0 or 1)
            const tag = blk.builder.tirValue(.ConstInt, blk, i32_ty, loc, .{ .value = tag_value });

            // Create the union payload: { Ok: T } or { Err: E }
            const payload = blk.builder.tirValue(.UnionMake, blk, payload_union_ty, loc, .{
                .field_index = field_index,
                .value = v,
            });

            // Create the final ErrorSet struct: { tag, payload }
            return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = tag },
                .{ .index = 1, .name = .none(), .value = payload },
            }, loc);
        },
        .Optional => {
            const opt = ts.get(.Optional, want);
            const bool_ty = ts.tBool();

            if (gk == .Optional) {
                // Case: ?U -> ?T
                const got_opt = ts.get(.Optional, got);
                if (got_opt.elem.eq(opt.elem)) return v; // ?T -> ?T (no-op)

                // Extract fields from ?U
                const flag = blk.builder.extractField(blk, bool_ty, v, 0, loc);
                var payload = blk.builder.extractField(blk, got_opt.elem, v, 1, loc);

                // Coerce payload U -> T
                payload = self.emitCoerce(blk, payload, got_opt.elem, opt.elem, loc);

                // Rebuild ?T
                return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = flag },
                    .{ .index = 1, .name = .none(), .value = payload },
                }, loc);
            } else {
                // Case: U -> ?T
                // Coerce payload U -> T
                const payload = self.emitCoerce(blk, v, got, opt.elem, loc);

                // Build ?T with a 'true' flag
                const some_flag = blk.builder.tirValue(.ConstBool, blk, bool_ty, loc, .{ .value = true });
                return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = some_flag },
                    .{ .index = 1, .name = .none(), .value = payload },
                }, loc);
            }
        },
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64 => {
            const is_num_got = switch (gk) {
                .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64 => true,
                else => false,
            };
            if (is_num_got)
                return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = v });
        },
        .Ptr => if (gk == .Ptr)
            return blk.builder.tirValue(.CastBit, blk, want, loc, .{ .value = v }),
        else => {},
    }
    // Fallback: materialize/assignable
    return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = v });
}

// ============================
// Top-level lowering
// ============================

fn tryLowerNamedFunction(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    b: *Builder,
    did: ast.DeclId,
    name: StrId,
    is_method: bool,
) !void {
    if (is_method and ctx.method_lowered.contains(did.toRaw())) return;

    const decl = a.exprs.Decl.get(did);
    const kind = a.exprs.index.kinds.items[decl.value.toRaw()];
    if (kind != .FunctionLit) return;

    const fn_ty = self.getExprType(ctx, a, decl.value);
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

    try self.lowerFunction(ctx, a, b, name, decl.value, null);

    if (is_method) {
        try ctx.method_lowered.put(did.toRaw(), {});
    }
}

fn bindingNameOfPattern(a: *ast.Ast, pid: ast.PatternId) ?StrId {
    const k = a.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Binding => a.pats.get(.Binding, pid).name,
        else => null,
    };
}

fn lowerTopDecl(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, b: *Builder, did: ast.DeclId) !void {
    const d = a.exprs.Decl.get(did);
    const kind = a.exprs.index.kinds.items[d.value.toRaw()];

    if (kind == .MlirBlock and d.pattern.isNone()) {
        return; // handled by lowerGlobalMlir
    }

    if (kind == .FunctionLit and !a.exprs.get(.FunctionLit, d.value).flags.is_extern) {
        var name_opt: ?StrId = null;
        if (!d.pattern.isNone()) {
            name_opt = bindingNameOfPattern(a, d.pattern.unwrap());
        } else if (!d.method_path.isNone()) {
            name_opt = try self.methodSymbolName(a, did);
        }

        if (name_opt) |nm| {
            const is_method = !d.method_path.isNone();
            try self.tryLowerNamedFunction(ctx, a, b, did, nm, is_method);
        }
        return;
    }
    // Global: record type
    if (!d.pattern.isNone()) {
        const nm = bindingNameOfPattern(a, d.pattern.unwrap()) orelse return;
        const ty = getDeclType(a, did) orelse return;
        if (self.constInitFromLiteral(a, d.value, ty)) |ci| {
            _ = b.addGlobalWithInit(nm, ty, ci);
        } else {
            _ = b.addGlobal(nm, ty);
        }
    }
}

fn lowerAttrs(
    self: *LowerTir,
    a: *ast.Ast,
    b: *Builder,
    range: ast.OptRangeAttr,
) !tir.RangeAttribute {
    if (range.isNone()) return .empty();
    const attrs = a.exprs.attr_pool.slice(range.asRange());
    var attr_list: List(tir.AttributeId) = .empty;
    defer attr_list.deinit(self.gpa);

    for (attrs) |aid| {
        const arow = a.exprs.Attribute.get(aid);
        // const value = try self.lowerExpr(ctx, a, env, f, blk, arow.value, null, .rvalue);
        try attr_list.append(self.gpa, b.t.instrs.Attribute.add(self.gpa, .{ .name = arow.name, .value = .none() }));
    }
    return b.t.instrs.attribute_pool.pushMany(self.gpa, attr_list.items);
}

pub fn lowerFunction(
    self: *LowerTir,
    lower_ctx: *LowerContext,
    a: *ast.Ast,
    b: *Builder,
    name: StrId,
    fun_eid: ast.ExprId,
    ctx: ?*const monomorphize.MonomorphizationContext,
) !void {
    const fid = if (ctx) |c|
        c.specialized_ty
    else
        self.getExprType(lower_ctx, a, fun_eid);
    if (self.context.type_store.index.kinds.items[fid.toRaw()] != .Function) return;
    const fnty = self.context.type_store.get(.Function, fid);

    const fnr = a.exprs.get(.FunctionLit, fun_eid);
    const fn_loc = tir.OptLocId.some(fnr.loc);

    try self.pushExprTypeOverrideFrame(lower_ctx);
    defer self.popExprTypeOverrideFrame(lower_ctx);

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
        const pname = if (!p.pat.isNone()) bindingNameOfPattern(a, p.pat.unwrap()) else null;
        _ = try b.addParam(&f, pname, pty);
        runtime_index += 1;
    }

    // Entry block + env
    var blk = try b.beginBlock(&f);
    var env = cf.Env{};
    defer env.deinit(self.gpa);

    if (ctx) |c| {
        for (c.bindings) |binding| {
            switch (binding.kind) {
                .type_param => {},
                .value_param => |vp| {
                    const const_val = try comp.constValueFromComptime(self, &blk, vp.ty, vp.value);
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
            const pname = bindingNameOfPattern(a, p.pat.unwrap()) orelse continue;
            const pty = runtime_param_tys[runtime_index];
            try env.bind(self.gpa, a, pname, .{ .value = param_vals[runtime_index], .ty = pty, .is_slot = false });
        }
        runtime_index += 1;
    }

    // Body
    if (!fnr.body.isNone()) {
        const body_id = fnr.body.unwrap();
        try env.pushScope(self.gpa);
        try self.lowerExprAsStmtList(lower_ctx, a, &env, &f, &blk, body_id);
        _ = env.popScope();
    }

    if (blk.term.isNone()) {
        try b.setReturn(&blk, tir.OptValueId.none(), fn_loc);
    }

    try b.endBlock(&f, blk);
    try b.endFunction(f);
}

// Lower a block or expression as a list of statements (ignores resulting value)
pub fn lowerExprAsStmtList(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
) !void {
    if (a.exprs.index.kinds.items[id.toRaw()] == .Block) {
        const b = a.exprs.get(.Block, id);
        const stmts = a.stmts.stmt_pool.slice(b.items);
        const start: u32 = @intCast(env.defers.items.len);
        try env.pushScope(self.gpa);
        for (stmts) |sid| {
            if (!blk.term.isNone()) break;
            try self.lowerStmt(ctx, a, env, f, blk, sid);
        }
        if (blk.term.isNone()) {
            const slice = env.defers.items[start..env.defers.items.len];
            if (slice.len > 0) try cf.emitDefers(self, ctx, a, env, f, blk, slice, false);
        }
        env.defers.items.len = start;
        _ = env.popScope();
    } else {
        _ = try self.lowerExpr(ctx, a, env, f, blk, id, null, .rvalue);
    }
}

fn lowerDecl(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    const drow = a.stmts.get(.Decl, sid);
    const d = a.exprs.Decl.get(drow.decl);
    const value_ty = self.getExprType(ctx, a, d.value);
    const decl_ty = getDeclType(a, drow.decl) orelse value_ty;
    if (!d.pattern.isNone()) {
        // Destructure once for all names: bind as values for const, or slots for mut.
        try self.destructureDeclFromExpr(ctx, a, env, f, blk, d.pattern.unwrap(), d.value, decl_ty, !d.flags.is_const);
    } else {
        if (!d.method_path.isNone()) {
            const vk = a.exprs.index.kinds.items[d.value.toRaw()];
            if (vk == .FunctionLit) return;
        }
        // No pattern: just evaluate for side-effects.
        _ = try self.lowerExpr(ctx, a, env, f, blk, d.value, decl_ty, .rvalue);
    }
}

fn lowerReturn(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    const r = a.stmts.get(.Return, sid);
    const stmt_loc = optLoc(a, sid);
    const defer_mark: u32 = 0;

    if (!r.value.isNone()) {
        const frow = f.builder.t.funcs.Function.get(f.id);
        const expect = frow.result;
        const want: ?types.TypeId = if (self.isVoid(expect)) null else expect;
        const value_expr = r.value.unwrap();
        const value_loc = optLoc(a, value_expr);
        const v_raw = try self.lowerExpr(ctx, a, env, f, blk, value_expr, want, .rvalue);
        var v = v_raw;
        if (!self.isVoid(expect)) {
            const got_ty = self.getExprType(ctx, a, value_expr);
            v = self.emitCoerce(blk, v_raw, got_ty, expect, value_loc);
        }

        const expect_kind = self.context.type_store.index.kinds.items[expect.toRaw()];
        const has_err_defers = expect_kind == .ErrorSet and cf.hasErrDefersFrom(self, env, defer_mark);

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

            try cf.emitDefers(self, ctx, a, env, f, &err_blk, defer_slice, true);
            try cf.emitDefers(self, ctx, a, env, f, &err_blk, defer_slice, false);
            try f.builder.setReturnVal(&err_blk, v, stmt_loc);
            try f.builder.endBlock(f, err_blk);

            try cf.emitDefers(self, ctx, a, env, f, &ok_blk, defer_slice, false);
            try f.builder.setReturnVal(&ok_blk, v, stmt_loc);
            try f.builder.endBlock(f, ok_blk);

            env.defers.items.len = defer_mark;
            return;
        } else {
            try cf.runNormalDefersFrom(self, ctx, a, env, f, blk, defer_mark);
            try f.builder.setReturnVal(blk, v, stmt_loc);
            return;
        }
    } else {
        try cf.runNormalDefersFrom(self, ctx, a, env, f, blk, defer_mark);
        try f.builder.setReturnVoid(blk, stmt_loc);
        return;
    }
}

fn lowerAssign(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    const as = a.stmts.get(.Assign, sid);
    const stmt_loc = optLoc(a, sid);
    const rty = self.getExprType(ctx, a, as.left);

    if (a.exprs.index.kinds.items[as.left.toRaw()] == .Ident) {
        const ident = a.exprs.get(.Ident, as.left);
        if (env.lookup(ident.name)) |bnd| {
            if (!bnd.is_slot) {
                const rhs = try self.lowerExpr(ctx, a, env, f, blk, as.right, rty, .rvalue);
                try env.bind(self.gpa, a, ident.name, .{ .value = rhs, .ty = rty, .is_slot = false });
                return;
            }
        }
    }

    const lhs_ptr = try self.lowerExpr(ctx, a, env, f, blk, as.left, null, .lvalue_addr);
    const rhs = try self.lowerExpr(ctx, a, env, f, blk, as.right, rty, .rvalue);
    _ = f.builder.tirValue(.Store, blk, rty, stmt_loc, .{ .ptr = lhs_ptr, .value = rhs, .@"align" = 0 });
}

fn lowerStmt(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    const k = a.stmts.index.kinds.items[sid.toRaw()];
    switch (k) {
        .Expr => {
            const e = a.stmts.get(.Expr, sid).expr;
            _ = try self.lowerExpr(ctx, a, env, f, blk, e, null, .rvalue);
        },
        .Defer => {
            const d = a.stmts.get(.Defer, sid);
            try env.defers.append(self.gpa, .{ .expr = d.expr, .is_err = false });
        },
        .ErrDefer => {
            const d = a.stmts.get(.ErrDefer, sid);
            try env.defers.append(self.gpa, .{ .expr = d.expr, .is_err = true });
        },
        .Break => try cf.lowerBreak(self, ctx, a, env, f, blk, sid),
        .Continue => try cf.lowerContinue(self, ctx, a, env, f, blk, sid),
        .Decl => try self.lowerDecl(ctx, a, env, f, blk, sid),
        .Assign => try self.lowerAssign(ctx, a, env, f, blk, sid),
        .Return => try self.lowerReturn(ctx, a, env, f, blk, sid),
        .Unreachable => try f.builder.setUnreachable(blk, optLoc(a, sid)),
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

fn resolveTypeArg(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, expr: ast.ExprId) ?types.TypeId {
    const ty = self.getExprType(ctx, a, expr);
    if (self.context.type_store.getKind(ty) != .TypeType) return null;
    return self.context.type_store.get(.TypeType, ty).of;
}

fn moduleCallKey(alias: ast.StrId, field: StrId) u64 {
    return (@as(u64, alias.toRaw()) << 32) | @as(u64, field.toRaw());
}

fn methodSymbolName(
    self: *LowerTir,
    a: *ast.Ast,
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

fn prepareMethodCall(
    self: *LowerTir,
    a: *ast.Ast,
    row: ast.Rows.Call,
    binding: types.MethodBinding,
    callee: *CalleeInfo,
    callee_name: *[]const u8,
    method_decl_id: *?ast.DeclId,
    method_binding_out: *?types.MethodBinding,
    arg_ids: *[]const ast.ExprId,
    method_arg_buf: *[]ast.ExprId,
) !void {
    if (binding.builtin) |_| {
        callee.fty = binding.func_type;
        method_decl_id.* = null;
        method_binding_out.* = binding;
        if (binding.requires_implicit_receiver) {
            std.debug.assert(a.exprs.index.kinds.items[row.callee.toRaw()] == .FieldAccess);
            const field_expr = a.exprs.get(.FieldAccess, row.callee);
            if (method_arg_buf.*.len != 0) {
                self.gpa.free(method_arg_buf.*);
                method_arg_buf.* = &.{};
            }
            method_arg_buf.* = try self.gpa.alloc(ast.ExprId, arg_ids.*.len + 1);
            method_arg_buf.*[0] = field_expr.parent;
            std.mem.copyForwards(ast.ExprId, method_arg_buf.*[1..], arg_ids.*);
            arg_ids.* = method_arg_buf.*;
        }
        return;
    }

    const symbol_ast = binding.decl_ast;

    const symbol = try self.methodSymbolName(symbol_ast, binding.decl_id);
    callee.name = symbol;
    callee.fty = binding.func_type;
    method_binding_out.* = binding;
    callee_name.* = self.context.type_store.strs.get(callee.name);

    if (binding.requires_implicit_receiver) {
        std.debug.assert(a.exprs.index.kinds.items[row.callee.toRaw()] == .FieldAccess);
        const field_expr = a.exprs.get(.FieldAccess, row.callee);
        if (method_arg_buf.*.len != 0) {
            self.gpa.free(method_arg_buf.*);
            method_arg_buf.* = &.{};
        }
        method_arg_buf.* = try self.gpa.alloc(ast.ExprId, arg_ids.*.len + 1);
        method_arg_buf.*[0] = field_expr.parent;
        std.mem.copyForwards(ast.ExprId, method_arg_buf.*[1..], arg_ids.*);
        arg_ids.* = method_arg_buf.*;
    }
}

fn synthesizeMethodBinding(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    field_expr_id: ast.ExprId,
) !?types.MethodBinding {
    if (a.exprs.index.kinds.items[field_expr_id.toRaw()] != .FieldAccess) return null;

    const field_expr = a.exprs.get(.FieldAccess, field_expr_id);
    const refined = try self.refineExprType(ctx, a, env, field_expr.parent, self.getExprType(ctx, a, field_expr.parent));
    if (refined == null) return null;

    var receiver_ty = refined.?;
    var owner_ty = receiver_ty;
    const parent_kind = self.context.type_store.getKind(receiver_ty);

    switch (parent_kind) {
        .Ptr => {
            const ptr_row = self.context.type_store.get(.Ptr, receiver_ty);
            owner_ty = ptr_row.elem;
        },
        .TypeType => {
            owner_ty = self.context.type_store.get(.TypeType, receiver_ty).of;
        },
        else => {},
    }

    const entry_opt = self.context.type_store.getMethod(owner_ty, field_expr.field);
    if (entry_opt == null) return null;

    const entry = entry_opt.?;
    const wants_receiver = entry.receiver_kind != .none;
    const implicit_receiver = wants_receiver and parent_kind != .TypeType;
    var needs_addr_of = false;

    if (implicit_receiver) {
        switch (entry.receiver_kind) {
            .none => {},
            .value => {
                if (!receiver_ty.eq(owner_ty)) return null;
            },
            .pointer, .pointer_const => {
                if (parent_kind == .Ptr) {
                    const ptr_row = self.context.type_store.get(.Ptr, receiver_ty);
                    if (!ptr_row.elem.eq(owner_ty)) return null;
                } else if (receiver_ty.eq(owner_ty)) {
                    needs_addr_of = true;
                } else {
                    return null;
                }
            },
        }
    }

    return types.MethodBinding{
        .owner_type = entry.owner_type,
        .method_name = entry.method_name,
        .decl_id = entry.decl_id,
        .decl_ast = entry.decl_ast,
        .func_type = entry.func_type,
        .self_param_type = entry.self_param_type,
        .receiver_kind = entry.receiver_kind,
        .requires_implicit_receiver = implicit_receiver,
        .needs_addr_of = needs_addr_of,
        .builtin = entry.builtin,
    };
}

fn resolveCallee(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, f: *Builder.FunctionFrame, row: ast.Rows.Call) !CalleeInfo {
    const ck = a.exprs.index.kinds.items[row.callee.toRaw()];
    if (ck == .Ident) {
        const nm = a.exprs.get(.Ident, row.callee).name;
        return .{ .name = nm, .fty = self.getExprType(ctx, a, row.callee) };
    }
    if (ck == .FieldAccess) {
        return .{
            .name = a.exprs.get(.FieldAccess, row.callee).field,
            .fty = self.getExprType(ctx, a, row.callee),
        };
    }
    return .{ .name = f.builder.intern("<indirect>"), .fty = self.getExprType(ctx, a, row.callee) };
}

fn buildVariantItem(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
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
                elems[i] = try self.lowerExpr(ctx, a, env, f, blk, arg_id, sty, .rvalue);
            }
            break :blk blk.builder.tupleMake(blk, payload_ty, elems, loc);
        },
        else => try self.lowerExpr(ctx, a, env, f, blk, args[0], payload_ty, .rvalue),
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

fn constValueFromLiteral(self: *LowerTir, a: *ast.Ast, expr: ast.ExprId) !?comp.ComptimeValue {
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

fn tryComptimeCall(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
) !?tir.ValueId {
    const row = a.exprs.get(.Call, id);
    const callee = try self.resolveCallee(ctx, a, f, row);
    const callee_name = a.exprs.strs.get(callee.name);
    if (!(std.mem.eql(u8, callee_name, "get_type_by_name") or
        std.mem.eql(u8, callee_name, "comptime_print") or
        std.mem.eql(u8, callee_name, "type_of")))
        return null;
    const loc = optLoc(a, id);
    const arg_ids = a.exprs.expr_pool.slice(row.args);
    const api_ptr_bnd = env.lookup(f.builder.intern("comptime_api_ptr")) orelse unreachable;
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

    var all_args: List(tir.ValueId) = .empty;
    defer all_args.deinit(self.gpa);
    try all_args.append(self.gpa, ctx_ptr);
    // For type_of, we need to pass the raw ExprId, not the lowered value.
    if (std.mem.eql(u8, callee_name, "type_of")) {
        // Ensure there's exactly one argument for type_of
        std.debug.assert(arg_ids.len == 1);
        const arg_type_id = self.getExprType(ctx, a, arg_ids[0]);
        try all_args.append(self.gpa, blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tU32(), loc, .{ .value = arg_type_id.toRaw() }));
    } else {
        for (arg_ids) |arg_id| {
            try all_args.append(self.gpa, try self.lowerExpr(ctx, a, env, f, blk, arg_id, null, .rvalue));
        }
    }

    const ret_ty = self.getExprType(ctx, a, id);
    return blk.builder.indirectCall(blk, ret_ty, fn_ptr, all_args.items, loc);
}

fn lowerCall(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected: ?types.TypeId,
    mode: LowerMode,
) !tir.ValueId {
    if (try self.tryComptimeCall(ctx, a, env, f, blk, id)) |v| return v;

    const row = a.exprs.get(.Call, id);
    const loc = optLoc(a, id);

    // Variant construction: if expected is a Variant/Error and callee is a path to a case, build VariantMake
    if (expected) |ety| {
        const k = self.context.type_store.getKind(ety);
        if (k == .Variant or k == .Error)
            return try self.buildVariantItem(ctx, a, env, f, blk, row, ety, k, loc);
    }

    var callee = try self.resolveCallee(ctx, a, f, row);
    var callee_name = a.exprs.strs.get(callee.name);
    var arg_ids = a.exprs.expr_pool.slice(row.args);
    var method_arg_buf: []ast.ExprId = &.{};
    var method_decl_id: ?ast.DeclId = null;
    var method_binding: ?types.MethodBinding = null;
    defer {
        if (method_arg_buf.len != 0) self.gpa.free(method_arg_buf);
    }
    if (a.type_info.getMethodBinding(row.callee)) |binding| {
        if (a.exprs.index.kinds.items[row.callee.toRaw()] == .FieldAccess) {
            try self.prepareMethodCall(
                a,
                row,
                binding,
                &callee,
                &callee_name,
                &method_decl_id,
                &method_binding,
                &arg_ids,
                &method_arg_buf,
            );
        }
    } else if (a.exprs.index.kinds.items[row.callee.toRaw()] == .FieldAccess) {
        if (try self.synthesizeMethodBinding(ctx, a, env, row.callee)) |binding| {
            try self.prepareMethodCall(
                a,
                row,
                binding,
                &callee,
                &callee_name,
                &method_decl_id,
                &method_binding,
                &arg_ids,
                &method_arg_buf,
            );
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
            var decl_ctx_opt: ?FunctionDeclContext = null;
            if (method_decl_id) |mid| {
                decl_ctx_opt = .{ .ast = a, .decl_id = mid };
            } else {
                decl_ctx_opt = self.findFunctionDeclForCall(a, row, callee.name);
            }
            if (decl_ctx_opt) |decl_ctx| {
                const decl_ast = decl_ctx.ast;
                const decl = decl_ast.exprs.Decl.get(decl_ctx.decl_id);
                const base_kind = decl_ast.exprs.index.kinds.items[decl.value.toRaw()];
                if (base_kind == .FunctionLit) {
                    const params = decl_ast.exprs.param_pool.slice(decl_ast.exprs.get(.FunctionLit, decl.value).params);
                    var skip_params: usize = 0;
                    while (skip_params < params.len and decl_ast.exprs.Param.get(params[skip_params]).is_comptime) : (skip_params += 1) {}

                    var binding_infos: List(monomorphize.BindingInfo) = .empty;
                    defer {
                        for (binding_infos.items) |*info| info.deinit(self.gpa);
                        binding_infos.deinit(self.gpa);
                    }

                    var ok = true;
                    if (arg_ids.len >= skip_params) {
                        var idx: usize = 0;
                        while (idx < skip_params) : (idx += 1) {
                            const param = decl_ast.exprs.Param.get(params[idx]);
                            if (param.pat.isNone()) {
                                ok = false;
                                break;
                            }

                            const pname = bindingNameOfPattern(decl_ast, param.pat.unwrap()) orelse {
                                ok = false;
                                break;
                            };

                            var param_ty = if (idx < param_tys.len)
                                param_tys[idx]
                            else
                                self.context.type_store.tAny();

                            if (!param.ty.isNone()) {
                                const ty_expr_id = param.ty.unwrap();
                                if (decl_ast.exprs.index.kinds.items[ty_expr_id.toRaw()] == .Ident) {
                                    const ident_name = decl_ast.exprs.get(.Ident, ty_expr_id).name;
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
                                const targ = self.resolveTypeArg(ctx, a, arg_expr) orelse {
                                    ok = false;
                                    break;
                                };
                                try binding_infos.append(self.gpa, monomorphize.BindingInfo.typeParam(pname, targ));
                            } else {
                                const comptime_val_opt = if (a.exprs.index.kinds.items[arg_expr.toRaw()] == .Literal)
                                    try self.constValueFromLiteral(a, arg_expr)
                                else
                                    null;

                                const comptime_val = if (comptime_val_opt) |cv|
                                    cv
                                else
                                    comp.evalComptimeExprValue(self, ctx, a, arg_expr, param_ty) catch {
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

                    var specialized_result_override: ?types.TypeId = null;

                    if (ok) {
                        const original_args = arg_ids;
                        var runtime_idx: usize = skip_params;
                        while (runtime_idx < params.len and runtime_idx < original_args.len) : (runtime_idx += 1) {
                            const param = decl_ast.exprs.Param.get(params[runtime_idx]);
                            if (param.pat.isNone()) continue;
                            const pname = bindingNameOfPattern(decl_ast, param.pat.unwrap()) orelse continue;

                            const param_ty = if (runtime_idx < param_tys.len)
                                param_tys[runtime_idx]
                            else
                                self.context.type_store.tAny();
                            if (!self.isAny(param_ty)) continue;

                            const arg_ty = self.getExprType(ctx, a, original_args[runtime_idx]);
                            if (self.isAny(arg_ty)) continue;

                            try binding_infos.append(self.gpa, monomorphize.BindingInfo.runtimeParam(pname, arg_ty));
                        }
                    }

                    if (ok and binding_infos.items.len > 0) {
                        var runtime_specs: List(checker.Checker.ParamSpecialization) = .empty;
                        defer runtime_specs.deinit(self.gpa);

                        for (binding_infos.items) |info| {
                            switch (info.kind) {
                                .runtime_param => |ty| try runtime_specs.append(self.gpa, .{ .name = info.name, .ty = ty }),
                                else => {},
                            }
                        }

                        if (runtime_specs.items.len > 0) {
                            if (decl_ast == a) {
                                const context = self.chk.checker_ctx.items[a.file_id];
                                const specialized_fn_ty = try self.chk.checkSpecializedFunction(context, decl_ast, decl.value, runtime_specs.items);
                                if (specialized_fn_ty) |fn_ty_override| {
                                    const fn_info_override = self.context.type_store.get(.Function, fn_ty_override);
                                    specialized_result_override = fn_info_override.result;
                                } else {
                                    ok = false;
                                }
                            } else {
                                ok = false;
                            }
                        }
                    }

                    if (ok and binding_infos.items.len > 0) {
                        const mangled = try comp.mangleMonomorphName(self, callee.name, binding_infos.items);
                        const result = try ctx.monomorphizer.request(
                            decl_ast,
                            self.context.type_store,
                            callee.name,
                            decl_ctx.decl_id,
                            fty,
                            binding_infos.items,
                            skip_params,
                            mangled,
                            specialized_result_override,
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
        const lower_mode: LowerMode = blk: {
            if (method_binding) |mb| {
                if (mb.requires_implicit_receiver and mb.needs_addr_of and i == 0) {
                    break :blk .lvalue_addr;
                }
            }
            break :blk .rvalue;
        };
        vals[i] = try self.lowerExpr(ctx, a, env, f, blk, arg_ids[i], want, lower_mode);
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
                break :blk self.getExprType(ctx, a, arg_ids[i]);
            };
            if (want.toRaw() != got.toRaw()) {
                const arg_loc = optLoc(a, arg_ids[i]);
                vals[i] = self.emitCoerce(blk, vals[i], got, want, arg_loc);
            }
        }
    }

    if (is_variadic and vals.len > fixed) {
        var j2: usize = fixed;
        while (j2 < vals.len) : (j2 += 1) {
            const got = self.getExprType(ctx, a, arg_ids[j2]);
            // Apply default argument promotions for C varargs interop.
            const want_promoted: ?types.TypeId = switch (self.context.type_store.getKind(got)) {
                .Bool, .I8, .U8, .I16, .U16 => self.context.type_store.tI32(),
                .F32 => self.context.type_store.tF64(),
                else => null,
            };
            if (want_promoted) |want_ty| {
                const arg_loc = optLoc(a, arg_ids[j2]);
                vals[j2] = self.emitCoerce(blk, vals[j2], got, want_ty, arg_loc);
                continue;
            }

            // If argument was typed as 'any', pick a concrete type consistent with promotions.
            if (self.isAny(got)) {
                const k = a.exprs.index.kinds.items[arg_ids[j2].toRaw()];
                const want_any: types.TypeId = switch (k) {
                    .Literal => blk: {
                        const lit = a.exprs.get(.Literal, arg_ids[j2]);
                        break :blk switch (lit.kind) {
                            .int, .char => self.context.type_store.tI64(),
                            .float, .imaginary => self.context.type_store.tF64(),
                            .bool => self.context.type_store.tI32(),
                            .string => self.context.type_store.tString(),
                        };
                    },
                    else => self.context.type_store.tUsize(),
                };
                vals[j2] = try self.lowerExpr(ctx, a, env, f, blk, arg_ids[j2], want_any, .rvalue);
            }
        }
    }

    if (method_binding) |mb| {
        if (mb.builtin) |builtin_kind| {
            switch (builtin_kind) {
                .dynarray_append => {
                    if (mode == .lvalue_addr) return error.LoweringBug;
                    return try self.lowerDynArrayAppend(f, blk, loc, mb, vals);
                },
            }
        }
    }

    // Choose a concrete return type: callee.fty.ret -> expected -> stamped -> void
    const ret_ty = blk: {
        if (callee.fty) |fty| {
            if (self.context.type_store.index.kinds.items[fty.toRaw()] == .Function) {
                const fr2 = self.context.type_store.get(.Function, fty);
                const rt = fr2.result;
                if (!self.isVoid(rt) and !self.isAny(rt)) break :blk rt;
            }
        }
        if (expected) |e| if (!self.isVoid(e) and !self.isAny(e)) break :blk e;
        break :blk self.getExprType(ctx, a, id);
    };

    if (!self.isAny(ret_ty)) {
        a.type_info.setExprType(id, ret_ty);
        try self.noteExprType(ctx, id, ret_ty);
    }
    const call_val = blk.builder.call(blk, ret_ty, callee.name, vals, loc);

    if (mode == .lvalue_addr) {
        const want_ptr_ty_opt: ?types.TypeId = blk: {
            if (expected) |want| {
                if (self.context.type_store.getKind(want) == .Ptr) break :blk want;
            }
            break :blk null;
        };
        const elem_ty = if (want_ptr_ty_opt) |want_ptr_ty|
            self.context.type_store.get(.Ptr, want_ptr_ty).elem
        else
            ret_ty;
        const slot_ty = self.context.type_store.mkPtr(elem_ty, false);
        const slot = f.builder.tirValue(
            .Alloca,
            blk,
            slot_ty,
            loc,
            .{ .count = tir.OptValueId.none(), .@"align" = 0 },
        );
        const stored = if (!elem_ty.eq(ret_ty))
            self.emitCoerce(blk, call_val, ret_ty, elem_ty, loc)
        else
            call_val;
        _ = f.builder.tirValue(.Store, blk, elem_ty, loc, .{ .ptr = slot, .value = stored, .@"align" = 0 });
        if (want_ptr_ty_opt) |want_ptr_ty| {
            if (!want_ptr_ty.eq(slot_ty)) {
                return self.emitCoerce(blk, slot, slot_ty, want_ptr_ty, loc);
            }
        }
        return slot;
    }

    return call_val;
}

fn lowerTypeExprOpaque(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) tir.ValueId {
    const ty0 = self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const v = self.safeUndef(blk, ty0, loc);
    if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
    return v;
}

fn lowerLiteral(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const lit = a.exprs.get(.Literal, id);
    // If the checker didn’t stamp a type, use the caller’s expected type.
    const ty0 = self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const base_ty = blk: {
        const kind = self.context.type_store.index.kinds.items[ty0.toRaw()];
        if (kind == .Optional) {
            const opt = self.context.type_store.get(.Optional, ty0);
            break :blk opt.elem;
        }
        break :blk ty0;
    };

    var literal_ty = base_ty;
    const v = switch (lit.kind) {
        .int => blk: {
            const info = switch (lit.data) {
                .int => |int_info| int_info,
                else => return error.LoweringBug,
            };
            if (!info.valid) return error.LoweringBug;
            const value64 = std.math.cast(u64, info.value) orelse unreachable;
            break :blk blk.builder.tirValue(.ConstInt, blk, base_ty, loc, .{ .value = value64 });
        },
        .imaginary => blk: {
            // ty0 must be Complex(elem). Build from (re=0, im=value)
            const tk = self.context.type_store.getKind(base_ty);
            if (tk != .Complex) break :blk blk.builder.tirValue(.ConstUndef, blk, ty0, loc, .{});
            const crow = self.context.type_store.get(.Complex, base_ty);
            const elem = crow.elem;
            literal_ty = base_ty;
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
            switch (self.context.type_store.getKind(base_ty)) {
                .F32, .F64 => literal_ty = base_ty,
                else => literal_ty = self.context.type_store.tF64(),
            }
            break :blk blk.builder.tirValue(.ConstFloat, blk, literal_ty, loc, .{ .value = info.value });
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
        }).? }),
    };
    const want_ty = expected_ty orelse ty0;
    if (!want_ty.eq(literal_ty)) return self.emitCoerce(blk, v, literal_ty, want_ty, loc);
    return v;
}

fn lowerUnary(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Unary, id);
    const loc = optLoc(a, id);
    const operand_loc = optLoc(a, row.expr);
    if (row.op == .address_of or mode == .lvalue_addr) {
        // compute address of the operand
        const ety = self.getExprType(ctx, a, row.expr);
        // When user asked address-of explicitly, produce pointer type
        if (row.op == .address_of) {
            const ptr = try self.lowerExpr(ctx, a, env, f, blk, row.expr, ety, .lvalue_addr);
            return ptr;
        }
        // lvalue address request falls through to .Ident/.FieldAccess/.IndexAccess implementations
    }
    // rvalue unary
    var ty0 = self.getExprType(ctx, a, id);

    // If the stamp is void/any or non-numeric for +/-, fall back to operand numeric (or i64)
    const is_num = self.isNumeric(ty0);
    if ((row.op == .pos or row.op == .neg) and (!is_num or self.isAny(ty0) or self.isVoid(ty0))) {
        const et = self.getExprType(ctx, a, row.expr);
        if (self.isNumeric(et)) {
            ty0 = et;
        }
        if (self.isAny(ty0) or self.isVoid(ty0)) ty0 = self.context.type_store.tI64();
    }

    const operand_expect: ?types.TypeId = switch (row.op) {
        .pos, .neg => ty0,
        .logical_not => self.context.type_store.tBool(),
        .address_of => null,
    };

    var v0 = try self.lowerExpr(ctx, a, env, f, blk, row.expr, operand_expect, .rvalue);

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
            const got = self.getExprType(ctx, a, row.expr);
            v0 = self.emitCoerce(blk, v0, got, bty, operand_loc);
            break :blk blk.builder.un1(blk, .LogicalNot, bty, v0, loc);
        },
        .address_of => unreachable,
    };
    if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
    return v;
}

fn lowerRange(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Range, id);
    const ty0 = self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const usize_ty = self.context.type_store.tUsize();
    const start_v = if (!row.start.isNone())
        try self.lowerExpr(ctx, a, env, f, blk, row.start.unwrap(), usize_ty, .rvalue)
    else
        blk.builder.tirValue(.ConstUndef, blk, usize_ty, loc, .{});
    const end_v = if (!row.end.isNone())
        try self.lowerExpr(ctx, a, env, f, blk, row.end.unwrap(), usize_ty, .rvalue)
    else
        blk.builder.tirValue(.ConstUndef, blk, usize_ty, loc, .{});
    const incl = blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = row.inclusive_right });
    // Materialize range as TIR RangeMake (typed as []usize)
    const v = blk.builder.rangeMake(blk, ty0, start_v, end_v, incl, loc);
    if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
    return v;
}

fn lowerDeref(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) !tir.ValueId {
    if (mode == .lvalue_addr) {
        // address of deref target is the pointer value itself
        const row = a.exprs.get(.Deref, id);
        return try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    }
    const ty0 = self.getExprType(ctx, a, id);
    const row = a.exprs.get(.Deref, id);
    const ptr = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    const loc = optLoc(a, id);
    const v = blk.builder.tirValue(.Load, blk, ty0, loc, .{ .ptr = ptr, .@"align" = 0 });
    if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
    return v;
}

fn lowerArrayLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.ArrayLit, id);
    const ty0 = expected_ty orelse (self.getExprType(ctx, a, id));
    const loc = optLoc(a, id);
    const vk = self.context.type_store.index.kinds.items[ty0.toRaw()];
    switch (vk) {
        .Array => {
            const array_ty = self.context.type_store.get(.Array, ty0);
            const len = switch (array_ty.len) {
                .Concrete => |l| l,
                .Unresolved => |expr_id| try self.resolveArrayLen(ctx, a, expr_id, loc),
            };

            const ids = a.exprs.expr_pool.slice(row.elems);
            std.debug.assert(len == ids.len);

            var vals = try self.gpa.alloc(tir.ValueId, ids.len);
            defer self.gpa.free(vals);
            const expect_elem = array_ty.elem;
            var i: usize = 0;
            while (i < ids.len) : (i += 1)
                vals[i] = try self.lowerExpr(ctx, a, env, f, blk, ids[i], expect_elem, .rvalue);
            const v = blk.builder.arrayMake(blk, ty0, vals, loc);
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
            return v;
        },
        .Simd => {
            const simd_ty = self.context.type_store.get(.Simd, ty0);
            const lanes: usize = @intCast(simd_ty.lanes);
            const ids = a.exprs.expr_pool.slice(row.elems);
            std.debug.assert(lanes == ids.len);
            var vals = try self.gpa.alloc(tir.ValueId, ids.len);
            defer self.gpa.free(vals);
            const expect_elem = simd_ty.elem;
            var i: usize = 0;
            while (i < ids.len) : (i += 1)
                vals[i] = try self.lowerExpr(ctx, a, env, f, blk, ids[i], expect_elem, .rvalue);
            const v = blk.builder.arrayMake(blk, ty0, vals, loc);
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
            return v;
        },
        .DynArray => {
            const dyn_ty = self.context.type_store.get(.DynArray, ty0);
            const elem_ty = dyn_ty.elem;
            const ptr_elem_ty = self.context.type_store.mkPtr(elem_ty, false);
            const usize_ty = self.context.type_store.tUsize();
            const ptr_void_ty = self.context.type_store.mkPtr(self.context.type_store.tVoid(), false);
            const ids = a.exprs.expr_pool.slice(row.elems);

            if (ids.len == 0) {
                const null_ptr = blk.builder.constNull(blk, ptr_elem_ty, loc);
                const zero = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = 0 });
                const fields = [_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = null_ptr },
                    .{ .index = 1, .name = .none(), .value = zero },
                    .{ .index = 2, .name = .none(), .value = zero },
                };
                const dyn_val = blk.builder.structMake(blk, ty0, &fields, loc);
                if (expected_ty) |want| return self.emitCoerce(blk, dyn_val, ty0, want, loc);
                return dyn_val;
            }

            const elem_size = check_types.typeSize(self.context, elem_ty) orelse unreachable;

            var elems = try self.gpa.alloc(tir.ValueId, ids.len);
            defer self.gpa.free(elems);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) {
                elems[i] = try self.lowerExpr(ctx, a, env, f, blk, ids[i], elem_ty, .rvalue);
            }

            const total_bytes = elem_size * ids.len;
            const total_bytes_u64 = std.math.cast(u64, total_bytes) orelse unreachable;
            const bytes_const = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = total_bytes_u64 });
            const alloc_name = blk.builder.intern("rt_alloc");
            const raw_ptr = blk.builder.call(blk, ptr_void_ty, alloc_name, &.{bytes_const}, loc);
            const data_ptr = blk.builder.tirValue(.CastBit, blk, ptr_elem_ty, loc, .{ .value = raw_ptr });

            var idx: usize = 0;
            while (idx < elems.len) : (idx += 1) {
                const idx_u64 = std.math.cast(u64, idx) orelse unreachable;
                const offset = blk.builder.gepConst(idx_u64);
                const elem_ptr = blk.builder.gep(blk, ptr_elem_ty, data_ptr, &.{offset}, loc);
                _ = blk.builder.tirValue(.Store, blk, elem_ty, loc, .{ .ptr = elem_ptr, .value = elems[idx], .@"align" = 0 });
            }

            const len_u64 = std.math.cast(u64, ids.len) orelse unreachable;
            const len_const = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = len_u64 });
            const fields = [_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = data_ptr },
                .{ .index = 1, .name = .none(), .value = len_const },
                .{ .index = 2, .name = .none(), .value = len_const },
            };
            const dyn_val = blk.builder.structMake(blk, ty0, &fields, loc);
            if (expected_ty) |want| return self.emitCoerce(blk, dyn_val, ty0, want, loc);
            return dyn_val;
        },
        .Tensor => {
            const v = try self.lowerTensorArrayLiteral(ctx, a, env, f, blk, id, ty0, loc);
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
            return v;
        },
        else => unreachable,
    }
}

fn lowerTensorArrayLiteral(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    tensor_ty: types.TypeId,
    loc: tir.OptLocId,
) !tir.ValueId {
    const tensor_row = self.context.type_store.get(.Tensor, tensor_ty);
    if (tensor_row.rank == 0) unreachable;

    var values: List(tir.ValueId) = .empty;
    defer values.deinit(self.gpa);

    try self.collectTensorLiteralValues(ctx, a, env, f, blk, id, tensor_ty, &values);

    const slice = try values.toOwnedSlice(self.gpa);
    defer self.gpa.free(slice);

    return blk.builder.arrayMake(blk, tensor_ty, slice, loc);
}

fn collectTensorLiteralValues(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    expr_id: ast.ExprId,
    current_ty: types.TypeId,
    out: *List(tir.ValueId),
) !void {
    const kind = self.context.type_store.getKind(current_ty);
    if (kind == .Tensor) {
        if (a.exprs.index.kinds.items[expr_id.toRaw()] != .ArrayLit) unreachable;
        const row = a.exprs.get(.ArrayLit, expr_id);
        const ids = a.exprs.expr_pool.slice(row.elems);
        const tensor_info = self.context.type_store.get(.Tensor, current_ty);
        std.debug.assert(tensor_info.rank > 0);
        const expected_len: usize = @intCast(tensor_info.dims[0]);
        std.debug.assert(ids.len == expected_len);

        var next_ty: types.TypeId = undefined;
        if (tensor_info.rank == 1) {
            next_ty = tensor_info.elem;
        } else {
            var dims_buf: [types.max_tensor_rank]usize = undefined;
            var i: usize = 0;
            while (i + 1 < tensor_info.rank) : (i += 1) {
                dims_buf[i] = tensor_info.dims[i + 1];
            }
            next_ty = self.context.type_store.mkTensor(tensor_info.elem, dims_buf[0 .. tensor_info.rank - 1]);
        }

        for (ids) |child_id| {
            try self.collectTensorLiteralValues(ctx, a, env, f, blk, child_id, next_ty, out);
        }
        return;
    }

    const value = try self.lowerExpr(ctx, a, env, f, blk, expr_id, current_ty, .rvalue);
    try out.append(self.gpa, value);
}

fn lowerTupleLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.TupleLit, id);
    const ty0 = expected_ty orelse self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
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
        vals[i] = try self.lowerExpr(ctx, a, env, f, blk, ids[i], expect_elem, .rvalue);
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
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.StructLit, id);
    var ty0 = expected_ty orelse self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);

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

        const v_val = try self.lowerExpr(ctx, a, env, f, blk, sfv.value, want, .rvalue);
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
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.MapLit, id);
    const ty0 = expected_ty orelse self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
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
        vals[j] = try self.lowerExpr(ctx, a, env, f, blk, kv.key, key_want, .rvalue);
        j += 1;
        vals[j] = try self.lowerExpr(ctx, a, env, f, blk, kv.value, val_want, .rvalue);
        j += 1;
    }
    const make = blk.builder.intern("builtin.map.from_kv");
    const v = blk.builder.call(blk, ty0, make, vals, loc);
    if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
    return v;
}

fn lowerIndexAccess(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const loc = optLoc(a, id);
    if (mode == .lvalue_addr) {
        const row = a.exprs.get(.IndexAccess, id);
        const base_ptr = try self.lowerExpr(ctx, a, env, f, blk, row.collection, null, .lvalue_addr);
        // Prefer a usize constant for literal indices to avoid casts in TIR
        const idx_v = blk: {
            const ik = a.exprs.index.kinds.items[row.index.toRaw()];
            if (ik == .Literal) {
                const lit = a.exprs.get(.Literal, row.index);
                if (lit.kind == .int) {
                    const info = switch (lit.data) {
                        .int => |int_info| int_info,
                        else => unreachable,
                    };
                    std.debug.assert(info.valid);
                    const value = std.math.cast(u64, info.value) orelse unreachable;
                    const uv = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{
                        .value = value,
                    });
                    break :blk uv;
                }
            }
            break :blk try self.lowerExpr(ctx, a, env, f, blk, row.index, self.context.type_store.tUsize(), .rvalue);
        };
        const idx = blk.builder.gepValue(idx_v);
        const rty = self.context.type_store.mkPtr(self.getExprType(ctx, a, id), false);
        return blk.builder.gep(blk, rty, base_ptr, &.{idx}, loc);
    } else {
        const row = a.exprs.get(.IndexAccess, id);
        const ty0 = self.getExprType(ctx, a, id);
        const base = try self.lowerExpr(ctx, a, env, f, blk, row.collection, null, .rvalue);
        // If result is a slice, the index expression should be a range ([]usize);
        // otherwise, index is a single usize.
        const idx = blk: {
            const rk = self.context.type_store.index.kinds.items[ty0.toRaw()];
            if (rk == .Slice) {
                const want = self.context.type_store.mkSlice(self.context.type_store.tUsize());
                break :blk try self.lowerExpr(ctx, a, env, f, blk, row.index, want, .rvalue);
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
                        const value = std.math.cast(u64, info.value) orelse unreachable;
                        const uv = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{
                            .value = value,
                        });
                        break :blk uv;
                    }
                }
                break :blk try self.lowerExpr(ctx, a, env, f, blk, row.index, self.context.type_store.tUsize(), .rvalue);
            }
        };
        const v = blk.builder.indexOp(blk, ty0, base, idx, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
        return v;
    }
}

fn lowerEnumMember(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    parent_expr: ast.ExprId,
    expected_ty: ?types.TypeId,
) !?tir.ValueId {
    const parent_ty = self.getExprType(ctx, a, parent_expr);
    const parent_kind = self.context.type_store.getKind(parent_ty);
    if (parent_kind != .Enum and parent_kind != .TypeType) return null;
    if (parent_kind == .TypeType) {
        const tr = self.context.type_store.get(.TypeType, parent_ty);
        const of_kind = self.context.type_store.getKind(tr.of);
        if (of_kind != .Enum) return null;
    }
    const ty0 = self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const idx = a.type_info.getFieldIndex(id) orelse unreachable; // enum members should be indexed by the checker
    var ev = blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = idx });
    if (expected_ty) |want| ev = self.emitCoerce(blk, ev, ty0, want, loc);
    return ev;
}

fn lowerVariantTagLiteral(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
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
    const ty0 = self.getExprType(ctx, a, id) orelse (expected_ty orelse self.context.type_store.tAny());
    const loc = optLoc(a, id);
    if (self.context.type_store.getKind(payload_ty) != .Void) return null;
    const tag_val = blk.builder.extractField(blk, self.context.type_store.tI32(), self.safeUndef(blk, ty, loc), 0, loc);
    if (expected_ty) |want| return self.emitCoerce(blk, tag_val, ty0, want, loc);
    return tag_val;
}

fn lowerFieldAccess(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.FieldAccess, id);
    const loc = optLoc(a, id);

    const parent_ty = self.getExprType(ctx, a, row.parent);
    const parent_kind = self.context.type_store.getKind(parent_ty);
    const field_name = a.exprs.strs.get(row.field);
    if (std.mem.eql(u8, field_name, "len")) {
        switch (parent_kind) {
            .Array, .Slice, .DynArray, .String => {
                const base = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, .rvalue);
                const ty0 = self.context.type_store.tUsize();
                const v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
                return v;
            },
            else => {},
        }
    } else if (std.mem.eql(u8, field_name, "capacity")) {
        switch (parent_kind) {
            .DynArray => {
                const base = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, .rvalue);
                const ty0 = self.context.type_store.tUsize();
                const v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
                return v;
            },
            else => {},
        }
    }

    // 1) imported module member (rvalue only)
    if (mode == .rvalue and a.exprs.index.kinds.items[row.parent.toRaw()] == .Ident) {
        // if (try self.lowerImportedModuleMember(a, blk, row.parent, row.field, expected_ty, loc)) |v| {
        //     return v;
        // }
    }

    const idx_maybe = a.type_info.getFieldIndex(id);

    // 2) EnumName.Member => constant (rvalue)
    if (mode == .rvalue) {
        if (try self.lowerEnumMember(ctx, a, blk, id, row.parent, expected_ty)) |v| {
            return v;
        }
    }

    // 3) address path (needs concrete field index)
    if (mode == .lvalue_addr) {
        const parent_lower_mode: LowerMode = blk: {
            if (parent_kind == .Ptr) break :blk .rvalue;
            break :blk .lvalue_addr;
        };
        const parent_ptr = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, parent_lower_mode);
        const elem_ty = self.getExprType(ctx, a, id);
        const idx = idx_maybe orelse unreachable;
        const rptr_ty = self.context.type_store.mkPtr(elem_ty, false);
        if (parent_kind == .Union) {
            return blk.builder.tirValue(.UnionFieldPtr, blk, rptr_ty, loc, .{
                .base = parent_ptr,
                .field_index = idx,
            });
        }
        if (parent_kind == .Ptr)
            return blk.builder.gep(blk, rptr_ty, parent_ptr, &.{blk.builder.gepConst(@intCast(idx))}, loc);
        return blk.builder.gep(blk, rptr_ty, parent_ptr, &.{blk.builder.gepConst(@intCast(idx))}, loc);
    }

    // 4) rvalue extraction
    const ty0 = self.getExprType(ctx, a, id);
    var base = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, .rvalue);

    const is_tuple =
        self.context.type_store.index.kinds.items[parent_ty.toRaw()] == .Tuple;

    var v: tir.ValueId = undefined;
    if (idx_maybe) |resolved_idx| {
        v = if (parent_kind == .Variant) blk: {
            if (row.is_tuple) {
                // Runtime variant struct exposes tag (field 0) and payload union (field 1).
                break :blk blk.builder.extractField(blk, ty0, base, resolved_idx, loc);
            }
            // accessing the payload field out of a runtime variant value via case name
            const variants = self.context.type_store.get(.Variant, parent_ty).variants;
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
        } else if (parent_kind == .Ptr) blk: {
            const field_ptr = try self.lowerExpr(ctx, a, env, f, blk, id, null, .lvalue_addr);
            break :blk blk.builder.tirValue(.Load, blk, ty0, loc, .{
                .ptr = field_ptr,
                .@"align" = 0,
            });
        } else if (parent_kind == .TypeType) blk: {
            // VariantType.C  => construct the value (void payload must NOT use UnionMake)
            const of_ty = self.context.type_store.get(.TypeType, parent_ty).of;
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
                        .value = self.safeUndef(blk, payload_ty, loc),
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
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Ident, id);
    const name = row.name;
    const loc = optLoc(a, id);

    // Pre-lift a couple things we end up consulting a few times.
    var expr_ty = self.getExprType(ctx, a, id);
    const did_opt = self.findTopLevelDeclByName(a, name);

    if (ctx.monomorph_context_stack.items.len > 0) {
        const context = &ctx.monomorph_context_stack.items[ctx.monomorph_context_stack.items.len - 1];
        if (context.lookupType(name)) |bound_ty| {
            expr_ty = self.context.type_store.mkTypeType(bound_ty);
        }
    }

    // Helper: when an expected type is a pointer, use its element;
    // otherwise fall back to the expression type (or Any).
    const want_elem = blk: {
        if (expected_ty) |want| {
            if (self.context.type_store.getKind(want) == .Ptr)
                break :blk self.context.type_store.get(.Ptr, want).elem;
        }
        break :blk expr_ty;
    };

    if (mode == .lvalue_addr) {
        // 1) If it's already a slot, we're done.
        if (env.lookup(name)) |bnd| {
            if (bnd.is_slot) return bnd.value;

            // For pointer-typed bindings we can reuse the SSA value directly as the
            // address; no temporary slot required.
            if (self.context.type_store.getKind(bnd.ty) == .Ptr) {
                return bnd.value;
            }
        }

        // 2) If it's a top-level decl, bind its address as a slot and return.
        if (did_opt) |did| {
            const d = a.exprs.Decl.get(did);
            const gty = getDeclType(a, did) orelse unreachable;
            const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
            const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = name });
            try env.bind(self.gpa, a, name, .{ .value = addr, .ty = gty, .is_slot = true });
            return addr;
        }

        // 3) Otherwise it must be a local value binding that needs a slot.
        if (env.lookup(name)) |bnd| {
            const slot_ty = self.context.type_store.mkPtr(want_elem, false);
            const slot = f.builder.tirValue(.Alloca, blk, slot_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });

            const src_ty = if (!self.isAny(expr_ty)) expr_ty else bnd.ty;
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
            const gty = getDeclType(a, did) orelse unreachable;
            const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
            const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = name });
            try env.bind(self.gpa, a, name, .{ .value = addr, .ty = gty, .is_slot = true });
            break :blk env.lookup(name).?;
        }

        // Not a value binding or top-level decl (likely a type name etc.).
        // Bind a safe placeholder so downstream code can keep going.
        const ty0 = expr_ty;
        const placeholder = self.safeUndef(blk, ty0, loc);
        try env.bind(self.gpa, a, name, .{ .value = placeholder, .ty = ty0, .is_slot = false });
        break :blk env.lookup(name).?;
    };

    if (bnd.is_slot) {
        const load_ty = if (!self.isAny(expr_ty)) expr_ty else bnd.ty;
        // else if (expected_ty) |want|
        //     want
        // else
        //     bnd.ty;
        var loaded = blk.builder.tirValue(.Load, blk, load_ty, loc, .{ .ptr = bnd.value, .@"align" = 0 });
        if (expected_ty) |want| loaded = self.emitCoerce(blk, loaded, load_ty, want, loc);
        return loaded;
    }

    // Non-slot: coerce if a target type was requested.
    const got_ty = if (!self.isAny(expr_ty)) expr_ty else bnd.ty;
    // else if (expected_ty) |want|
    //     want
    // else
    //     bnd.ty;
    return if (expected_ty) |want| self.emitCoerce(blk, bnd.value, got_ty, want, loc) else bnd.value;
}

fn lowerBinary(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Binary, id);
    const loc = optLoc(a, id);

    // --- fast-path: variant/error equality against a tag literal (e.g. err == MyErr.NotFound) ---
    if (row.op == .eq or row.op == .neq) {
        const l_ty = self.getExprType(ctx, a, row.left);
        const r_ty = self.getExprType(ctx, a, row.right);

        // left is value, right is tag literal
        if (self.isVariantLike(l_ty)) {
            if (self.tagConstFromTypePath(ctx, a, row.right)) |info| {
                if (info.of_ty.toRaw() == l_ty.toRaw()) {
                    const lhs_val = try self.lowerExpr(ctx, a, env, f, blk, row.left, l_ty, .rvalue);
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
        if (self.isVariantLike(r_ty)) {
            if (self.tagConstFromTypePath(ctx, a, row.left)) |info| {
                if (info.of_ty.toRaw() == r_ty.toRaw()) {
                    const rhs_val = try self.lowerExpr(ctx, a, env, f, blk, row.right, r_ty, .rvalue);
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

    const lhs_stamped = self.getExprType(ctx, a, row.left);
    const rhs_stamped = self.getExprType(ctx, a, row.right);
    const lhs_hint = try self.refineExprType(ctx, a, env, row.left, lhs_stamped);
    const rhs_hint = try self.refineExprType(ctx, a, env, row.right, rhs_stamped);

    const stamped_result = self.getExprType(ctx, a, id);
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
                const ts = self.context.type_store;
                const lh = lhs_hint orelse lhs_stamped;
                const rh = rhs_hint orelse rhs_stamped;
                const lhs_kind = ts.index.kinds.items[lh.toRaw()];
                if (lhs_kind == .Optional) {
                    const rhs_kind = ts.index.kinds.items[rh.toRaw()];
                    if (rhs_kind != .Optional) {
                        lhs_expect = lh;
                        rhs_expect = ts.get(.Optional, lh).elem;
                    }
                }
                const rhs_kind = ts.index.kinds.items[rh.toRaw()];
                if (rhs_kind == .Optional) {
                    if (lhs_kind != .Optional) {
                        rhs_expect = rh;
                        lhs_expect = ts.get(.Optional, rh).elem;
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
            lhs_expect = self.getExprType(ctx, a, row.left);
            rhs_expect = expected_ty;
            if (op_ty == null or self.isVoid(op_ty.?)) op_ty = (expected_ty orelse self.context.type_store.tAny());
        },
    }

    const l = try self.lowerExpr(ctx, a, env, f, blk, row.left, lhs_expect, .rvalue);
    const r = try self.lowerExpr(ctx, a, env, f, blk, row.right, rhs_expect, .rvalue);

    // --- Handle Optional(T) equality/inequality cases ---
    const l_ty = self.getExprType(ctx, a, row.left);
    const r_ty = self.getExprType(ctx, a, row.right);

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
                self.getExprType(ctx, a, row.right)
            else
                self.getExprType(ctx, a, row.left);

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
        const want = self.commonNumeric(self.getExprType(ctx, a, row.left), self.getExprType(ctx, a, row.right)) orelse self.context.type_store.tI64();
        break :blk want;
    };
    try self.noteExprType(ctx, id, ty0);

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
            const lhs_ty = self.getExprType(ctx, a, row.left);
            if (self.context.type_store.index.kinds.items[lhs_ty.toRaw()] != .Optional) return error.LoweringBug;
            const opt_info = self.context.type_store.get(.Optional, lhs_ty);
            const flag = blk.builder.extractField(blk, bool_ty, l, 0, loc);
            const payload = blk.builder.extractField(blk, opt_info.elem, l, 1, loc);

            const elem_kind = self.context.type_store.getKind(opt_info.elem);

            if (elem_kind != .ErrorSet) {
                // Optional(T) orelse R -> T
                const then_param = try f.builder.addBlockParam(&then_blk, null, opt_info.elem);
                const res_ty = expected_ty orelse opt_info.elem;
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
                try f.builder.condBr(blk, flag, then_blk.id, &.{payload}, else_blk.id, &.{}, loc);
                const orig_blk = blk.*;
                try f.builder.endBlock(f, orig_blk);

                var unwrapped = then_param;
                if (expected_ty) |want| unwrapped = self.emitCoerce(&then_blk, unwrapped, opt_info.elem, want, loc);
                try f.builder.br(&then_blk, join_blk.id, &.{unwrapped}, loc);

                var rhs_v = r;
                const rhs_ty = self.getExprType(ctx, a, row.right);
                rhs_v = self.emitCoerce(&else_blk, rhs_v, rhs_ty, res_ty, loc);
                try f.builder.br(&else_blk, join_blk.id, &.{rhs_v}, loc);
                try f.builder.endBlock(f, then_blk);
                try f.builder.endBlock(f, else_blk);
                blk.* = join_blk;
                break :blk res_param;
            } else {
                // Optional(ErrorSet(V,E)) orelse R -> ErrorSet(V,E)
                const es = self.context.type_store.get(.ErrorSet, opt_info.elem);
                const res_es_ty = self.context.type_store.mkErrorSet(es.value_ty, es.error_ty);
                const res_param = try f.builder.addBlockParam(&join_blk, null, res_es_ty);
                // Prepare then param to receive the ErrorSet payload
                const then_param = try f.builder.addBlockParam(&then_blk, null, res_es_ty);
                // Branch on optional flag; forward payload on then
                try f.builder.condBr(blk, flag, then_blk.id, &.{payload}, else_blk.id, &.{}, loc);
                const orig_blk = blk.*;
                try f.builder.endBlock(f, orig_blk);

                // then: pass through the ErrorSet value received as param
                try f.builder.br(&then_blk, join_blk.id, &.{then_param}, loc);
                try f.builder.endBlock(f, then_blk);

                // else: wrap default RHS as Ok in ErrorSet
                var rhs_v = r;
                const rhs_ty = self.getExprType(ctx, a, row.right);
                if (rhs_ty.toRaw() != es.value_ty.toRaw()) rhs_v = self.emitCoerce(&else_blk, rhs_v, rhs_ty, es.value_ty, loc);
                // Build union payload {Ok: V, Err: E}
                const ok_name = f.builder.intern("Ok");
                const err_name = f.builder.intern("Err");
                const union_ty = self.context.type_store.mkUnion(&.{ .{ .name = ok_name, .ty = es.value_ty }, .{ .name = err_name, .ty = es.error_ty } });
                const union_val = else_blk.builder.tirValue(.UnionMake, &else_blk, union_ty, loc, .{ .field_index = 0, .value = rhs_v });
                const tag0 = else_blk.builder.tirValue(.ConstInt, &else_blk, self.context.type_store.tI32(), loc, .{ .value = 0 });
                const fields = [_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = tag0 },
                    .{ .index = 1, .name = .none(), .value = union_val },
                };
                const es_val = else_blk.builder.structMake(&else_blk, res_es_ty, &fields, loc);
                try f.builder.br(&else_blk, join_blk.id, &.{es_val}, loc);
                try f.builder.endBlock(f, else_blk);

                blk.* = join_blk;
                break :blk res_param;
            }
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
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Catch, id);
    const loc = optLoc(a, id);
    const out_ty_guess = expected_ty orelse self.getExprType(ctx, a, id);
    const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

    const lhs_val = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    const lhs_ty0 = self.getExprType(ctx, a, row.expr);
    const lhs_kind = self.context.type_store.index.kinds.items[lhs_ty0.toRaw()];
    var es_ty = lhs_ty0;
    var is_optional_es = false;
    if (lhs_kind == .Optional) {
        const opt = self.context.type_store.get(.Optional, lhs_ty0);
        es_ty = opt.elem;
        is_optional_es = true;
    }
    const es = self.context.type_store.get(.ErrorSet, es_ty);
    const expr_loc = optLoc(a, row.expr);

    if (is_optional_es) {
        // Optional(ErrorSet(V,E)) catch handler -> Optional(V)
        // optional info not required explicitly here
        const some_flag = blk.builder.extractField(blk, self.context.type_store.tBool(), lhs_val, 0, expr_loc);
        const es_payload = blk.builder.extractField(blk, es_ty, lhs_val, 1, expr_loc);

        var some_blk = try f.builder.beginBlock(f);
        var none_blk = try f.builder.beginBlock(f);
        var join_blk = try f.builder.beginBlock(f);

        const res_opt_ty = self.context.type_store.mkOptional(es.value_ty);
        try self.noteExprType(ctx, id, res_opt_ty);
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_opt_ty);

        const brc = self.forceLocalCond(blk, some_flag, expr_loc);
        try f.builder.condBr(blk, brc, some_blk.id, &.{}, none_blk.id, &.{}, loc);
        {
            const old = blk.*;
            try f.builder.endBlock(f, old);
        }

        // In some-block: apply catch to inner error-set and produce Optional(V) directly
        const tag = some_blk.builder.extractField(&some_blk, self.context.type_store.tI32(), es_payload, 0, expr_loc);
        const zero = some_blk.builder.tirValue(.ConstInt, &some_blk, self.context.type_store.tI32(), expr_loc, .{ .value = 0 });
        const is_ok_inner = some_blk.builder.binBool(&some_blk, .CmpEq, tag, zero, expr_loc);

        var ok_blk = try f.builder.beginBlock(f);
        var err_blk = try f.builder.beginBlock(f);
        try f.builder.condBr(&some_blk, is_ok_inner, ok_blk.id, &.{}, err_blk.id, &.{}, loc);
        try f.builder.endBlock(f, some_blk);

        const one = self.context.type_store.tBool();
        // ok: unwrap value from union and wrap as Some(value)
        const payload_union_ok = ok_blk.builder.extractField(
            &ok_blk,
            self.context.type_store.mkUnion(&.{
                .{ .name = f.builder.intern("Ok"), .ty = es.value_ty },
                .{ .name = f.builder.intern("Err"), .ty = es.error_ty },
            }),
            es_payload,
            1,
            expr_loc,
        );
        const ok_v = ok_blk.builder.tirValue(.UnionField, &ok_blk, es.value_ty, loc, .{ .base = payload_union_ok, .field_index = 0 });
        const true_v_ok = ok_blk.builder.tirValue(.ConstBool, &ok_blk, one, loc, .{ .value = true });
        const ok_fields = [_]tir.Rows.StructFieldInit{
            .{ .index = 0, .name = .none(), .value = true_v_ok },
            .{ .index = 1, .name = .none(), .value = ok_v },
        };
        const some_opt_ok = ok_blk.builder.structMake(&ok_blk, res_opt_ty, &ok_fields, loc);
        try f.builder.br(&ok_blk, join_blk.id, &.{some_opt_ok}, loc);
        try f.builder.endBlock(f, ok_blk);

        // err: bind error and run handler producing V (unless noreturn); wrap as Some(value)
        const payload_union_err = err_blk.builder.extractField(&err_blk, self.context.type_store.mkUnion(&.{ .{ .name = f.builder.intern("Ok"), .ty = es.value_ty }, .{ .name = f.builder.intern("Err"), .ty = es.error_ty } }), es_payload, 1, expr_loc);
        const err_val = err_blk.builder.tirValue(.UnionField, &err_blk, es.error_ty, loc, .{ .base = payload_union_err, .field_index = 1 });
        if (!row.binding_name.isNone()) {
            const nm = row.binding_name.unwrap();
            try env.bind(self.gpa, a, nm, .{ .value = err_val, .ty = es.error_ty, .is_slot = false });
        }
        // Evaluate handler exactly once as a block expression to both run side-effects
        // and produce the resulting value.
        if (err_blk.term.isNone()) {
            const hv = try self.lowerBlockExprValue(ctx, a, env, f, &err_blk, row.handler, es.value_ty);
            const true_v_err = err_blk.builder.tirValue(.ConstBool, &err_blk, one, loc, .{ .value = true });
            const err_fields = [_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = true_v_err },
                .{ .index = 1, .name = .none(), .value = hv },
            };
            const some_opt_err = err_blk.builder.structMake(&err_blk, res_opt_ty, &err_fields, loc);
            try f.builder.br(&err_blk, join_blk.id, &.{some_opt_err}, loc);
        }
        try f.builder.endBlock(f, err_blk);

        // none branch: wrap as None Optional(V)
        const false_v = none_blk.builder.tirValue(.ConstBool, &none_blk, one, loc, .{ .value = false });
        const undef_payload = self.safeUndef(&none_blk, es.value_ty, loc);
        const nfields = [_]tir.Rows.StructFieldInit{
            .{ .index = 0, .name = .none(), .value = false_v },
            .{ .index = 1, .name = .none(), .value = undef_payload },
        };
        const none_opt = none_blk.builder.structMake(&none_blk, res_opt_ty, &nfields, loc);
        try f.builder.br(&none_blk, join_blk.id, &.{none_opt}, loc);
        try f.builder.endBlock(f, none_blk);

        blk.* = join_blk;
        return res_param;
    }

    const lhs = lhs_val;
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
        try self.noteExprType(ctx, id, res_ty);
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
        // Evaluate handler exactly once and branch with the produced value.
        if (else_blk.term.isNone()) {
            const hv = try self.lowerBlockExprValue(ctx, a, env, f, &else_blk, row.handler, res_ty);
            try f.builder.br(&else_blk, join_blk.id, &.{hv}, loc);
        }
        _ = env.popScope(); // Pop scope after handler

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
        try self.lowerExprAsStmtList(ctx, a, env, f, &else_blk, row.handler);
        _ = env.popScope(); // Pop scope after handler
        if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{}, loc);
        try f.builder.endBlock(f, else_blk);

        blk.* = exit_blk;
        return self.safeUndef(blk, self.context.type_store.tAny(), loc);
    }
}

fn lowerCast(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Cast, id);
    const ty0 = self.getExprType(ctx, a, id);
    const v = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    const loc = optLoc(a, id);
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

pub fn lowerExpr(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const expr_kind = a.exprs.index.kinds.items[id.toRaw()];

    _ = try self.refineExprType(ctx, a, env, id, self.getExprType(ctx, a, id));

    return switch (expr_kind) {
        .Literal => self.lowerLiteral(ctx, a, blk, id, expected_ty),
        .NullLit => {
            const loc = optLoc(a, id);
            const ty0 = self.getExprType(ctx, a, id);
            const v = blk.builder.constNull(blk, ty0, loc);
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
            return v;
        },
        .UndefLit => {
            const loc = optLoc(a, id);
            const ty0 = self.getExprType(ctx, a, id);
            const v = blk.builder.tirValue(.ConstUndef, blk, ty0, loc, .{});
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
            return v;
        },
        .Unary => self.lowerUnary(ctx, a, env, f, blk, id, expected_ty, mode),
        .Range => self.lowerRange(ctx, a, env, f, blk, id, expected_ty),
        .Deref => self.lowerDeref(ctx, a, env, f, blk, id, expected_ty, mode),
        .TupleLit => self.lowerTupleLit(ctx, a, env, f, blk, id, expected_ty),
        .ArrayLit => self.lowerArrayLit(ctx, a, env, f, blk, id, expected_ty),
        .StructLit => self.lowerStructLit(ctx, a, env, f, blk, id, expected_ty),
        .MapLit => self.lowerMapLit(ctx, a, env, f, blk, id, expected_ty),
        .IndexAccess => self.lowerIndexAccess(ctx, a, env, f, blk, id, expected_ty, mode),
        .FieldAccess => self.lowerFieldAccess(ctx, a, env, f, blk, id, expected_ty, mode),
        .Block => {
            const res_ty = expected_ty orelse self.getExprType(ctx, a, id);
            return try self.lowerBlockExprValue(ctx, a, env, f, blk, id, res_ty);
        },
        .Ident => self.lowerIdent(ctx, a, env, f, blk, id, expected_ty, mode),
        .Binary => self.lowerBinary(ctx, a, env, f, blk, id, expected_ty),
        .Catch => self.lowerCatch(ctx, a, env, f, blk, id, expected_ty),
        .If => cf.lowerIf(self, ctx, a, env, f, blk, id, expected_ty),
        .Call => self.lowerCall(ctx, a, env, f, blk, id, expected_ty, mode),
        .Cast => self.lowerCast(ctx, a, env, f, blk, id, expected_ty),
        .OptionalUnwrap => cf.lowerOptionalUnwrap(self, ctx, a, env, f, blk, id, expected_ty),
        .ErrUnwrap => cf.lowerErrUnwrap(self, ctx, a, env, f, blk, id, expected_ty),
        .UnionType => self.lowerTypeExprOpaque(ctx, a, blk, id, expected_ty),
        .Match => cf.lowerMatch(self, ctx, a, env, f, blk, id, expected_ty),
        .While => cf.lowerWhile(self, ctx, a, env, f, blk, id, expected_ty),
        .For => cf.lowerFor(self, ctx, a, env, f, blk, id, expected_ty),
        .MlirBlock => blk: {
            if (mode == .lvalue_addr) return error.LoweringBug;
            const loc = optLoc(a, id);
            break :blk try self.lowerMlirBlock(ctx, a, env, f, blk, id, expected_ty, loc);
        },
        .Import => blk: {
            const loc = optLoc(a, id);
            break :blk blk.builder.tirValue(
                .ConstUndef,
                blk,
                self.getExprType(ctx, a, id),
                loc,
                .{},
            );
        },
        .VariantType, .EnumType, .StructType => self.lowerTypeExprOpaque(ctx, a, blk, id, expected_ty),
        .CodeBlock => blk: {
            // For now, treat as opaque and produce undef
            const ty0 = self.getExprType(ctx, a, id);
            const loc = optLoc(a, id);
            break :blk self.safeUndef(blk, ty0, loc);
        },
        .ComptimeBlock => comp.jitEvalComptimeBlock(self, ctx, a, blk, id),
        else => {
            std.debug.print("lowerExpr: unhandled expr kind {}\n", .{expr_kind});
            return error.LoweringBug;
        },
    };
}

// Compute the value of a block expression (value position)
pub fn lowerBlockExprValue(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    block_expr: ast.ExprId,
    expected_ty: types.TypeId,
) anyerror!tir.ValueId {
    if (a.exprs.index.kinds.items[block_expr.toRaw()] != .Block) {
        return self.lowerExpr(ctx, a, env, f, blk, block_expr, expected_ty, .rvalue);
    }
    const b = a.exprs.get(.Block, block_expr);
    const stmts = a.stmts.stmt_pool.slice(b.items);
    const loc = optLoc(a, block_expr);
    if (stmts.len == 0) {
        try self.noteExprType(ctx, block_expr, expected_ty);
        return self.safeUndef(blk, expected_ty, loc);
    }

    // Remember where this block's scope begins on the defer stack.
    const mark: u32 = @intCast(env.defers.items.len);
    var i: usize = 0;
    while (i + 1 < stmts.len) : (i += 1) {
        try self.lowerStmt(ctx, a, env, f, blk, stmts[i]);
    }
    const last = stmts[stmts.len - 1];
    const lk = a.stmts.index.kinds.items[last.toRaw()];
    if (lk == .Expr) {
        const le = a.stmts.get(.Expr, last).expr;
        // Evaluate the last expression value-first, then run defers belonging to this block,
        // then return the computed value. This preserves the "defer runs at scope exit" rule.
        const v = try self.lowerExpr(ctx, a, env, f, blk, le, expected_ty, .rvalue);
        try self.noteExprType(ctx, block_expr, expected_ty);
        // If the checker stamped a different type than expected, keep your existing
        // higher-level coercion behavior by not touching `v` here beyond scope-finalization.
        try cf.runNormalDefersFrom(self, ctx, a, env, f, blk, mark);
        return v;
    } else {
        try self.lowerStmt(ctx, a, env, f, blk, last);
        // Natural fallthrough out of the block scope: run normal defers for this block.
        // Early exits (return/break/continue) won’t reach here and already run defers.
        try cf.runNormalDefersFrom(self, ctx, a, env, f, blk, mark);
        try self.noteExprType(ctx, block_expr, expected_ty);
        return self.safeUndef(blk, expected_ty, loc);
    }
}

// ============================
// Import materialization
// ============================

fn findTopLevelDeclByName(self: *const LowerTir, a: *ast.Ast, name: ast.StrId) ?ast.DeclId {
    const target = a.exprs.strs.get(name);
    return self.findTopLevelDeclByNameSlice(a, target);
}

fn findTopLevelDeclByNameSlice(self: *const LowerTir, a: *ast.Ast, target: []const u8) ?ast.DeclId {
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    var i: usize = 0;
    while (i < decls.len) : (i += 1) {
        const d = a.exprs.Decl.get(decls[i]);
        if (d.pattern.isNone()) continue;
        const pid = d.pattern.unwrap();
        if (self.patternContainsNameStr(a, pid, target)) return decls[i];
    }
    return null;
}

fn patternContainsNameStr(
    self: *const LowerTir,
    a: *ast.Ast,
    pid: ast.PatternId,
    target: []const u8,
) bool {
    const pk = a.pats.index.kinds.items[pid.toRaw()];
    return switch (pk) {
        .Binding => {
            const nm = a.pats.get(.Binding, pid).name;
            return std.mem.eql(u8, a.exprs.strs.get(nm), target);
        },
        .Tuple => {
            const row = a.pats.get(.Tuple, pid);
            const elems = a.pats.pat_pool.slice(row.elems);
            for (elems) |eid| if (self.patternContainsNameStr(a, eid, target)) return true;
            return false;
        },
        .Struct => {
            const row = a.pats.get(.Struct, pid);
            const fields = a.pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const frow = a.pats.StructField.get(fid);
                if (self.patternContainsNameStr(a, frow.pattern, target)) return true;
            }
            return false;
        },
        .VariantTuple => {
            const row = a.pats.get(.VariantTuple, pid);
            const elems = a.pats.pat_pool.slice(row.elems);
            for (elems) |eid| if (self.patternContainsNameStr(a, eid, target)) return true;
            return false;
        },
        .VariantStruct => {
            const row = a.pats.get(.VariantStruct, pid);
            const fields = a.pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const frow = a.pats.StructField.get(fid);
                if (self.patternContainsNameStr(a, frow.pattern, target)) return true;
            }
            return false;
        },
        .Slice => {
            const row = a.pats.get(.Slice, pid);
            const elems = a.pats.pat_pool.slice(row.elems);
            for (elems) |eid| if (self.patternContainsNameStr(a, eid, target)) return true;
            if (!row.rest_binding.isNone()) {
                if (self.patternContainsNameStr(a, row.rest_binding.unwrap(), target)) return true;
            }
            return false;
        },
        .Or => {
            const row = a.pats.get(.Or, pid);
            const alts = a.pats.pat_pool.slice(row.alts);
            for (alts) |aid| if (self.patternContainsNameStr(a, aid, target)) return true;
            return false;
        },
        .At => {
            const row = a.pats.get(.At, pid);
            const binder = a.exprs.strs.get(row.binder);
            if (std.mem.eql(u8, binder, target)) return true;
            return self.patternContainsNameStr(a, row.pattern, target);
        },
        else => false,
    };
}

fn findFunctionDeclForCall(
    self: *LowerTir,
    caller_ast: *ast.Ast,
    row: ast.Rows.Call,
    callee_name: ast.StrId,
) ?FunctionDeclContext {
    if (self.findTopLevelDeclByName(caller_ast, callee_name)) |decl_id| {
        return .{ .ast = caller_ast, .decl_id = decl_id };
    }

    const callee_kind = caller_ast.exprs.index.kinds.items[row.callee.toRaw()];
    if (callee_kind != .FieldAccess) return null;

    const fr = caller_ast.exprs.get(.FieldAccess, row.callee);
    const parent_kind = caller_ast.exprs.index.kinds.items[fr.parent.toRaw()];
    if (parent_kind != .Ident) return null;

    return null;
}
fn findTopLevelImportByName(self: *const LowerTir, a: *ast.Ast, name: ast.StrId) ?ast.DeclId {
    const did = self.findTopLevelDeclByName(a, name) orelse return null;
    const d = a.exprs.Decl.get(did);
    return if (a.exprs.index.kinds.items[d.value.toRaw()] == .Import) did else null;
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

pub fn isAny(self: *const LowerTir, ty: types.TypeId) bool {
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
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    expr: ast.ExprId,
    stamped: types.TypeId,
) !?types.TypeId {
    const kind = a.exprs.index.kinds.items[expr.toRaw()];
    switch (kind) {
        .Ident => {
            const name = a.exprs.get(.Ident, expr).name;
            if (env.lookup(name)) |bnd| {
                try self.noteExprType(ctx, expr, bnd.ty);
                return bnd.ty;
            }

            var i: usize = ctx.monomorph_context_stack.items.len;
            while (i > 0) {
                i -= 1;
                const context = &ctx.monomorph_context_stack.items[i];
                if (context.lookupValue(name)) |vp| {
                    try self.noteExprType(ctx, expr, vp.ty);
                    return vp.ty;
                }
                if (context.lookupType(name)) |ty| {
                    const type_ty = self.context.type_store.mkTypeType(ty);
                    try self.noteExprType(ctx, expr, type_ty);
                    return type_ty;
                }
            }
        },
        else => {},
    }

    return stamped;
}

// ============================
// Misc helpers
// ============================

pub fn getExprType(self: *const LowerTir, ctx: *LowerContext, a: *ast.Ast, id: ast.ExprId) types.TypeId {
    if (self.lookupExprTypeOverride(ctx, id)) |override| return override;
    const i = id.toRaw();
    std.debug.assert(i < a.type_info.expr_types.items.len);
    return a.type_info.expr_types.items[i] orelse unreachable;
}
fn getDeclType(a: *ast.Ast, did: ast.DeclId) ?types.TypeId {
    const i = did.toRaw();
    std.debug.assert(i < a.type_info.decl_types.items.len);

    return a.type_info.decl_types.items[i];
}

pub fn getUnionTypeFromVariant(self: *const LowerTir, vty: types.TypeId) ?types.TypeId {
    const ts = self.context.type_store;
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

// Destructure a declaration pattern and bind its sub-bindings either as values (const) or slots (mutable).
fn destructureDeclPattern(self: *LowerTir, a: *ast.Ast, env: *cf.Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, value: tir.ValueId, vty: types.TypeId, to_slots: bool) !void {
    const pk = a.pats.index.kinds.items[pid.toRaw()];
    const loc = optLoc(a, pid);
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
                        extracted = self.safeUndef(blk, fty, loc);
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
fn destructureDeclFromTupleLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    pid: ast.PatternId,
    src_expr: ast.ExprId,
    vty: types.TypeId,
    to_slots: bool,
) anyerror!void {
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
        try self.destructureDeclFromExpr(ctx, a, env, f, blk, elems_pat[i], elems_expr[i], ety, to_slots);
    }
    // If pattern has more elements than expr, fill remaining with undef of element type.
    while (i < elems_pat.len) : (i += 1) {
        const ety = if (i < etys.len) etys[i] else self.context.type_store.tAny();
        const elem_loc = optLoc(a, elems_pat[i]);
        const uv = self.safeUndef(blk, ety, elem_loc);
        try self.destructureDeclPattern(a, env, f, blk, elems_pat[i], uv, ety, to_slots);
    }
}

fn destructureDeclFromStructLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    pid: ast.PatternId,
    src_expr: ast.ExprId,
    vty: types.TypeId,
    to_slots: bool,
) !void {
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
            try self.destructureDeclFromExpr(ctx, a, env, f, blk, pf.pattern, ve, fty, to_slots);
        } else {
            // missing -> bind undef
            const field_loc = optLoc(a, pf.pattern);
            const uv = self.safeUndef(blk, fty, field_loc);
            try self.destructureDeclPattern(a, env, f, blk, pf.pattern, uv, fty, to_slots);
        }
    }
}

fn destructureDeclFromExpr(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    pid: ast.PatternId,
    src_expr: ast.ExprId,
    target_ty: types.TypeId,
    to_slots: bool,
) anyerror!void {
    const pk = a.pats.index.kinds.items[pid.toRaw()];
    const target_kind = self.context.type_store.index.kinds.items[target_ty.toRaw()];
    const src_ty = self.getExprType(ctx, a, src_expr);
    const vty = if (target_kind == .Any) src_ty else target_ty;
    const expr_loc = optLoc(a, src_expr);

    if (target_kind == .TypeType) {
        const result_ty = src_ty;
        const resolved_ty = blk: {
            if (self.context.type_store.getKind(result_ty) == .TypeType) {
                const tt = self.context.type_store.get(.TypeType, result_ty);
                if (!self.isAny(tt.of)) break :blk tt.of;
                const computed = try comp.runComptimeExpr(self, ctx, a, src_expr, result_ty, &[_]Pipeline.ComptimeBinding{});
                break :blk switch (computed) {
                    .Type => |ty| ty,
                    else => return error.UnsupportedComptimeType,
                };
            }
            const type_wrapper = self.context.type_store.mkTypeType(result_ty);
            const computed = try comp.runComptimeExpr(self, ctx, a, src_expr, type_wrapper, &[_]Pipeline.ComptimeBinding{});
            break :blk switch (computed) {
                .Type => |ty| ty,
                else => return error.UnsupportedComptimeType,
            };
        };
        const type_ty = self.context.type_store.mkTypeType(resolved_ty);
        try self.noteExprType(ctx, src_expr, type_ty);
        const placeholder = self.safeUndef(blk, type_ty, expr_loc);
        try self.destructureDeclPattern(a, env, f, blk, pid, placeholder, type_ty, to_slots);
        return;
    }

    switch (pk) {
        .Binding => {
            const guess_ty = src_ty;
            const expect_ty = if (target_kind == .Any) guess_ty else target_ty;
            var raw = try self.lowerExpr(ctx, a, env, f, blk, src_expr, expect_ty, .rvalue);

            const refined = try self.refineExprType(ctx, a, env, src_expr, self.getExprType(ctx, a, src_expr)) orelse unreachable;
            const eff_ty = if (target_kind == .Any and !self.isAny(refined)) refined else target_ty;

            if (!refined.eq(eff_ty)) {
                raw = self.emitCoerce(blk, raw, refined, eff_ty, expr_loc);
            }

            return try self.destructureDeclPattern(a, env, f, blk, pid, raw, eff_ty, to_slots);
        },
        .Tuple => {
            // If RHS is a tuple-literal, lower elements individually to avoid creating a temporary aggregate.
            if (a.exprs.index.kinds.items[src_expr.toRaw()] == .TupleLit) {
                const eff_ty = if (target_kind == .Any) src_ty else target_ty;
                try self.destructureDeclFromTupleLit(ctx, a, env, f, blk, pid, src_expr, eff_ty, to_slots);
                return;
            }
            // Fallback: lower full expr once, then destructure via extracts.
            const eff_ty = if (target_kind == .Any) src_ty else target_ty;
            const raw = try self.lowerExpr(ctx, a, env, f, blk, src_expr, eff_ty, .rvalue);
            const val = if (!src_ty.eq(eff_ty)) self.emitCoerce(blk, raw, src_ty, eff_ty, expr_loc) else raw;
            return try self.destructureDeclPattern(a, env, f, blk, pid, val, eff_ty, to_slots);
        },
        .Struct => {
            if (a.exprs.index.kinds.items[src_expr.toRaw()] == .StructLit) {
                const eff_ty = if (target_kind == .Any) src_ty else target_ty;
                try self.destructureDeclFromStructLit(ctx, a, env, f, blk, pid, src_expr, eff_ty, to_slots);
                return;
            }
            // fallback: lower whole expr and destructure by field extraction
            const eff_ty = if (target_kind == .Any) src_ty else target_ty;
            const raw = try self.lowerExpr(ctx, a, env, f, blk, src_expr, eff_ty, .rvalue);
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
                        try self.destructureDeclFromExpr(ctx, a, env, f, blk, pelems[i], args[i], ety, to_slots);
                    }
                    while (i < pelems.len) : (i += 1) {
                        const ety = if (i < elem_tys.len) elem_tys[i] else self.context.type_store.tAny();
                        const elem_loc = optLoc(a, pelems[i]);
                        const uv = self.safeUndef(blk, ety, elem_loc);
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
                const elem_loc = optLoc(a, pelems[i]);
                const uv = self.safeUndef(blk, ety, elem_loc);
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
                                try self.destructureDeclFromExpr(ctx, a, env, f, blk, pf.pattern, ve2, fty, to_slots);
                            } else {
                                const field_loc = optLoc(a, pf.pattern);
                                const uv = self.safeUndef(blk, fty, field_loc);
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
                const field_loc = optLoc(a, pf.pattern);
                const uv = self.safeUndef(blk, self.context.type_store.tAny(), field_loc);
                try self.destructureDeclPattern(a, env, f, blk, pf.pattern, uv, self.context.type_store.tAny(), to_slots);
            }
        },
        else => {
            // Default: lower entire expr and bind.
            const val = try self.lowerExpr(ctx, a, env, f, blk, src_expr, vty, .rvalue);
            return try self.destructureDeclPattern(a, env, f, blk, pid, val, vty, to_slots);
        },
    }
}

pub fn tagIndexForCase(self: *const LowerTir, case_ty: types.TypeId, name: StrId) ?u32 {
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

pub fn enumMemberValue(self: *const LowerTir, enum_ty: types.TypeId, name: StrId) ?u64 {
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
pub fn forceLocalCond(
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
    ctx: *LowerContext,
    a: *ast.Ast,
    expr: ast.ExprId,
) ?struct { of_ty: types.TypeId, tag_idx: u32 } {
    if (a.exprs.index.kinds.items[expr.toRaw()] != .FieldAccess) return null;
    const fr = a.exprs.get(.FieldAccess, expr);
    const pty = self.getExprType(ctx, a, fr.parent);
    if (self.context.type_store.getKind(pty) != .TypeType) return null;

    const of_ty = self.context.type_store.get(.TypeType, pty).of;
    const of_kind = self.context.type_store.getKind(of_ty);
    if (of_kind != .Variant and of_kind != .Error) return null;

    // We rely on the checker to have resolved the field index.
    const idx = a.type_info.getFieldIndex(expr) orelse return null;

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

pub fn restoreBindings(self: *LowerTir, env: *cf.Env, saved: []const BindingSnapshot) !void {
    var i: usize = saved.len;
    while (i > 0) : (i -= 1) {
        const entry = saved[i - 1];
        try env.restoreBinding(self.gpa, entry.name, entry.prev);
    }
}

pub fn evalComptimeExpr(
    gpa: std.mem.Allocator,
    ctx: *LowerContext,
    context: *Context,
    pipeline: *Pipeline,
    chk: *checker.Checker,
    ast_unit: *ast.Ast,
    expr: ast.ExprId,
    result_ty: types.TypeId,
    bindings: []const Pipeline.ComptimeBinding,
) !comp.ComptimeValue {
    var lowerer = LowerTir.init(gpa, context, pipeline, chk);
    // defer lowerer.deinit();
    return comp.runComptimeExpr(&lowerer, ctx, ast_unit, expr, result_ty, bindings);
}
