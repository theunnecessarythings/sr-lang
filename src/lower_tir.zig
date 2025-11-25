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
const interpreter = @import("interpreter.zig");
const check_types = @import("check_types.zig");
const pipeline_mod = @import("pipeline.zig");
const cf = @import("lower_cf_tir.zig");
const package = @import("package.zig");
const call_resolution = @import("call_resolution.zig");
const Loc = @import("lexer.zig").Token.Loc;

const StrId = @import("cst.zig").StrId;
const OptStrId = @import("cst.zig").OptStrId;
const Context = @import("compile.zig").Context;
const Pipeline = pipeline_mod.Pipeline;
const Builder = tir.Builder;
const List = std.ArrayList;
const MethodKey = types.MethodKey;
/// Links a previously captured binding snapshot with its interpreter instance.
const SnapshotEntry = struct {
    /// Captured binding snapshot paired with its interpreter.
    snapshot: interpreter.BindingSnapshot,
    /// Interpreter instance responsible for this snapshot.
    interp: *interpreter.Interpreter,
};

const SnapshotList = std.ArrayList(*SnapshotEntry);

/// Metadata for a value binding tracked during lowering (value id + type info).
pub const ValueBinding = struct {
    /// SSA value identifier produced for the binding.
    value: tir.ValueId,
    /// Declared or inferred type for the bound value.
    ty: types.TypeId,
    /// Indicates whether the binding refers to a storage slot instead of a pure value.
    is_slot: bool,
};

/// Snapshot entry showing the previous binding for a name so it can be restored.
pub const BindingSnapshot = struct {
    /// Identifier whose binding is being restored.
    name: ast.StrId,
    /// Prior binding that should be reinstated after specialization.
    prev: ?ValueBinding,
};

/// Tracks temporary expression type overrides introduced during lowering.
const ExprTypeOverrideFrame = struct {
    /// Stores temporary overrides from lowering heuristics keyed by expr ID.
    map: std.AutoArrayHashMapUnmanaged(u32, types.TypeId) = .{},

    /// Release the map that tracks temporary type overrides.
    fn deinit(self: *ExprTypeOverrideFrame, gpa: std.mem.Allocator) void {
        self.map.deinit(gpa);
    }
};

const FunctionDeclContext = call_resolution.FunctionDeclContext;

/// Driver for lowering AST units into TIR, managing interpreter state and builder contexts.
pub const LowerTir = @This();

/// Allocator for TIR lowering resources.
gpa: std.mem.Allocator,
/// Compilation context shared across pipeline stages.
context: *Context,
/// Pipeline configuration controlling which passes run.
pipeline: *Pipeline,
/// Checker used to validate AST nodes during lowering.
chk: *checker.Checker,
/// Stack of lowering contexts per file/function scope.
lower_context: List(*LowerContext) = .{},

/// Per-function/module lowering state that tracks loops, snapshots, and interpreter caches.
pub const LowerContext = struct {
    /// Stack of active loop contexts for control-flow lowering.
    loop_stack: List(cf.LoopCtx) = .{},
    /// Cache mapping method calls to symbol names to avoid re-lowering.
    module_call_cache: std.AutoHashMap(u64, StrId),
    /// Record whether a given method key has been lowered.
    method_lowered: std.AutoHashMap(MethodKey, void),
    /// Track functions that already have TIR emitted.
    lowered_functions: std.AutoHashMap(tir.StrId, void),
    /// Interpreter instance used for comptime evaluation (per file).
    interpreter: *interpreter.Interpreter,
    /// Stack of current binding snapshots for specialization contexts.
    specialization_stack: SnapshotList = .empty,
    /// Stack storing expression type overrides introduced by lowering heuristics.
    expr_type_override_stack: List(ExprTypeOverrideFrame) = .{},
    /// Cache of interpreters keyed by AST pointers.
    interp_cache: std.AutoHashMap(usize, *interpreter.Interpreter),
    /// Allocator owned by the lowering context.
    gpa: std.mem.Allocator,
    /// Active TIR builder emitting instructions for the current function.
    builder: ?*tir.Builder = null,

    /// Return the comptime value previously bound to `name` from active snapshots.
    pub fn lookupBindingValue(self: *LowerContext, name: ast.StrId) ?*const comp.ComptimeValue {
        var i: usize = self.specialization_stack.items.len;
        while (i > 0) {
            i -= 1;
            const entry = self.specialization_stack.items[i];
            if (entry.snapshot.lookup(name)) |binding| {
                return &binding.value;
            }
        }
        return null;
    }

    /// Return the type binding for `name` by inspecting the active binding stack.
    pub fn lookupBindingType(self: *LowerContext, name: ast.StrId) ?types.TypeId {
        if (self.lookupBindingValue(name)) |value| {
            return switch (value.*) {
                .Type => |ty| ty,
                else => null,
            };
        }
        return null;
    }

    /// Return the active binding snapshot if any.
    pub fn activeSnapshot(self: *LowerContext) ?*interpreter.BindingSnapshot {
        if (self.specialization_stack.items.len == 0) return null;
        return &self.specialization_stack.items[self.specialization_stack.items.len - 1].snapshot;
    }

    /// Push a new interpreter binding snapshot for the current specialization context.
    pub fn pushSnapshot(self: *LowerContext, snapshot: interpreter.BindingSnapshot, interp: *interpreter.Interpreter) anyerror!void {
        const entry = try self.gpa.create(SnapshotEntry);
        entry.* = SnapshotEntry{ .snapshot = snapshot, .interp = interp };
        try self.specialization_stack.append(self.gpa, entry);
    }

    /// Pop the most recent snapshot and release its interpreter resources.
    pub fn popSnapshot(self: *LowerContext) void {
        if (self.specialization_stack.pop()) |entry| {
            entry.snapshot.destroy(entry.interp.allocator);
            self.gpa.destroy(entry);
        }
    }

    /// Return a cached interpreter for `target_ast`, creating one if necessary.
    pub fn getInterpreterFor(self: *LowerContext, target_ast: *ast.Ast) anyerror!(*interpreter.Interpreter) {
        if (self.interpreter.ast == target_ast) return self.interpreter;
        const key = @intFromPtr(target_ast);
        if (self.interp_cache.get(key)) |entry| {
            return entry;
        }
        const interp = try self.gpa.create(interpreter.Interpreter);
        interp.* = try interpreter.Interpreter.init(self.gpa, target_ast, null, null);
        try self.interp_cache.put(key, interp);
        return interp;
    }

    /// Destroy all interpreter state and snapshots owned by this context.
    pub fn deinit(self: *LowerContext, gpa: std.mem.Allocator) void {
        self.loop_stack.deinit(gpa);
        self.module_call_cache.deinit();
        self.lowered_functions.deinit();
        self.method_lowered.deinit();
        while (self.expr_type_override_stack.items.len > 0) {
            self.expr_type_override_stack.items[self.expr_type_override_stack.items.len - 1].deinit(gpa);
            self.expr_type_override_stack.items.len -= 1;
        }
        self.expr_type_override_stack.deinit(gpa);
        while (self.specialization_stack.items.len > 0) {
            if (self.specialization_stack.pop()) |entry| {
                entry.snapshot.destroy(entry.interp.allocator);
                self.gpa.destroy(entry);
            }
        }
        self.specialization_stack.deinit(gpa);
        self.interpreter.deinit();
        self.gpa.destroy(self.interpreter);
        var iter = self.interp_cache.iterator();
        while (iter.next()) |entry| {
            entry.value_ptr.*.deinit(self.gpa);
            self.gpa.destroy(entry.value_ptr.*);
        }
        self.interp_cache.deinit();
    }
};

/// Prefix exported symbols with their package name unless they belong to `main`.
pub fn qualifySymbolName(self: *LowerTir, a: *ast.Ast, base: StrId) !StrId {
    if (a.unit.package_name.isNone()) return base;
    const pkg_id = a.unit.package_name.unwrap();
    const pkg_name = self.context.type_store.strs.get(pkg_id);
    if (std.mem.eql(u8, pkg_name, "main")) return base;
    const base_name = self.context.type_store.strs.get(base);
    const symbol = try std.fmt.allocPrint(self.gpa, "{s}__{s}", .{ pkg_name, base_name });
    defer self.gpa.free(symbol);
    return self.context.type_store.strs.intern(symbol);
}

/// Global flag tracking whether MLIR dialect/pass registrations were initialized.
pub var g_mlir_inited: bool = false;
/// Cached MLIR context shared across lowering runs.
pub var g_mlir_ctx: mlir.Context = undefined;

/// Instantiate a TIR lowering driver with the provided context/pipeline/checker.
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

/// No-op teardown (LowerTir uses externally owned resources).
pub fn deinit(_: *LowerTir) void {}

/// Report a lowering failure at `loc`, emit a diagnostic, and surface `LoweringBug`.
fn throwErr(self: *LowerTir, loc: Loc) anyerror {
    std.debug.dumpCurrentStackTrace(null);
    try self.context.diags.addError(loc, .tir_lowering_failed, .{});
    return error.LoweringBug;
}

/// Lower every file in dependency order, producing a complete TIR module for main.
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

    var threads = std.ArrayList(struct { std.Thread, *tir.TIR, *bool }){};
    defer threads.deinit(self.gpa);

    for (levels.levels.items) |level| {
        threads.clearRetainingCapacity();
        if (level.items.len == 0) continue;

        for (level.items) |file_id| {
            const unit = unit_by_file.get(file_id) orelse continue;
            if (unit.ast == null) continue;
            const t = try self.gpa.create(tir.TIR);
            t.* = tir.TIR.init(self.gpa, self.context.type_store);
            const interp = try self.gpa.create(interpreter.Interpreter);
            interp.* = try interpreter.Interpreter.init(self.gpa, unit.ast.?, null, null);
            const ctx = try self.gpa.create(LowerContext);
            ctx.* = LowerContext{
                .method_lowered = .init(self.gpa),
                .module_call_cache = .init(self.gpa),
                .lowered_functions = std.AutoHashMap(tir.StrId, void).init(self.gpa),
                .interpreter = interp,
                .specialization_stack = .empty,
                .expr_type_override_stack = .{},
                .interp_cache = .init(self.gpa),
                .gpa = self.gpa,
                .builder = null,
            };
            const ok_ptr = try self.gpa.create(bool);
            ok_ptr.* = true;
            const thread = try std.Thread.spawn(.{}, runAstCatching, .{ self, unit.ast.?, t, ctx, ok_ptr });
            try threads.append(self.gpa, .{ thread, t, ok_ptr });
        }

        var any_failed = false;
        for (threads.items, 0..) |item, i| {
            const thread = item.@"0";
            const t = item.@"1";
            const ok_ptr = item.@"2";
            thread.join();
            const unit = unit_by_file.get(level.items[i]) orelse continue;
            unit.tir = t;
            if (!ok_ptr.*) {
                any_failed = true;
                // Emit a TIR-specific diagnostic at the file level for visibility
                const where = Loc.init(level.items[i], 0, 0);
                self.throwErr(where) catch {};
            }
            self.gpa.destroy(ok_ptr);
        }
        if (any_failed) {
            self.context.requestCancel();
            return error.TirLoweringFailed;
        }
    }

    const main_pkg = self.context.compilation_unit.packages.getPtr("main") orelse return error.PackageNotFound;
    return main_pkg.sources.entries.get(0).value.tir.?;
}

/// Wrap `runAst`, setting `ok_ptr` to false if an error occurs.
fn runAstCatching(self: *LowerTir, ast_unit: *ast.Ast, t: *tir.TIR, ctx: *LowerContext, ok_ptr: *bool) !void {
    ok_ptr.* = true;
    self.runAst(ast_unit, t, ctx) catch |err| {
        ok_ptr.* = false;
        return err;
    };
}

/// Lower a single AST unit into the provided TIR builder/context.
pub fn runAst(self: *LowerTir, ast_unit: *ast.Ast, t: *tir.TIR, ctx: *LowerContext) !void {
    var b = Builder.init(self.gpa, t);
    ctx.builder = &b;

    try self.lowerGlobalMlir(ctx, ast_unit, &b);

    // Lower top-level decls: functions and globals
    const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
    for (decls) |did| try self.lowerTopDecl(ctx, ast_unit, &b, did);

    var method_it = self.context.type_store.method_table.iterator();
    while (method_it.next()) |entry| {
        const method = entry.value_ptr.*;
        if (method.decl_ast != ast_unit) continue;

        const key = methodLowerKey(method.owner_type, method.method_name);
        if (ctx.method_lowered.contains(key)) continue;
        // Skip lowering generic Any variants; only lower specialized methods
        if (self.shouldSkipGenericMethod(method.func_type)) continue;
        _ = ast_unit.type_info.applyMethodExprSnapshot(method.owner_type, method.method_name);
        const base_name = try self.methodSymbolName(ast_unit, method.decl_id, method.owner_type);
        try self.tryLowerNamedFunction(ctx, ast_unit, &b, method.decl_id, base_name, true, true, key);
    }
}

/// Return true if the method type is fully generic (`Any`) and shouldn't be lowered.
fn shouldSkipGenericMethod(self: *const LowerTir, fn_ty: types.TypeId) bool {
    if (self.context.type_store.getKind(fn_ty) != .Function) return false;
    const info = self.context.type_store.get(.Function, fn_ty);
    if (self.isType(info.result, .Any)) {
        return true;
    }
    const params = self.context.type_store.type_pool.slice(info.params);
    var i: usize = 0;
    while (i < params.len) : (i += 1) {
        if (self.isType(params[i], .Any)) {
            return true;
        }
    }
    return false;
}

/// Check whether `fty` ends with an `Any` parameter that is not fully lowered.
fn hasTrailingAnyRuntimeParam(self: *const LowerTir, fty: types.TypeId) bool {
    if (self.context.type_store.getKind(fty) != .Function) return false;
    const info = self.context.type_store.get(.Function, fty);
    if (info.is_extern) return false;
    const params = self.context.type_store.type_pool.slice(info.params);
    if (params.len == 0) return false;
    return self.isType(params[params.len - 1], .Any);
}

/// Push a fresh expression-type override frame into `ctx`.
fn pushExprTypeOverrideFrame(self: *LowerTir, ctx: *LowerContext) !void {
    try ctx.expr_type_override_stack.append(self.gpa, .{});
}

/// Pop the last expression-type override frame.
fn popExprTypeOverrideFrame(self: *LowerTir, ctx: *LowerContext) void {
    if (ctx.expr_type_override_stack.items.len == 0) return;
    const idx = ctx.expr_type_override_stack.items.len - 1;
    ctx.expr_type_override_stack.items[idx].deinit(self.gpa);
    ctx.expr_type_override_stack.items.len -= 1;
}

/// Record that `expr` should temporarily be treated as `ty`.
pub fn noteExprType(self: *LowerTir, ctx: *LowerContext, expr: ast.ExprId, ty: types.TypeId) !void {
    if (ctx.expr_type_override_stack.items.len == 0) return;
    if (self.isType(ty, .Any)) return;
    var frame = &ctx.expr_type_override_stack.items[ctx.expr_type_override_stack.items.len - 1];
    try frame.map.put(self.gpa, expr.toRaw(), ty);
}

/// Look for an expression type override associated with `expr`.
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

/// Turn a literal expression into a `ConstInit` when it matches the desired `ty`.
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
        .F32, .F64 => blk: {
            const info = switch (lit.data) {
                .float => |float_info| float_info,
                else => return null,
            };
            if (!info.valid) break :blk null;
            break :blk tir.ConstInit{ .float = info.value };
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

/// Lower the built-in `dynarray.append` call by invoking the runtime helper.
fn lowerDynArrayAppend(
    self: *LowerTir,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    loc: tir.OptLocId,
    binding: types.MethodBinding,
    args: []const tir.ValueId,
) !tir.ValueId {
    std.debug.assert(binding.builtin != null and binding.builtin.? == .dynarray_append);
    std.debug.assert(args.len >= 2);

    const ts = self.context.type_store;
    const owner_kind = ts.getKind(binding.owner_type);
    std.debug.assert(owner_kind == .DynArray);

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

        const elem_size: u64 = @intCast(check_types.typeSize(self.context, elem_ty));
        const elem_size_const = grow_blk.builder.tirValue(.ConstInt, &grow_blk, usize_ty, loc, .{ .value = elem_size });
        const new_bytes = grow_blk.builder.bin(&grow_blk, .Mul, usize_ty, new_cap, elem_size_const, loc);

        const data_ptr_void = grow_blk.builder.tirValue(.CastBit, &grow_blk, ptr_void_ty, loc, .{ .value = data_ptr });
        const new_data_void = self.callRuntimeReallocPtr(&grow_blk, data_ptr_void, new_bytes, loc);
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

/// Attempt to lower `expr_id` to a `ConstInit` consistent with `ty`, consulting the checker if needed.
fn constInitFromExpr(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, expr_id: ast.ExprId, ty: types.TypeId) !?tir.ConstInit {
    if (self.constInitFromLiteral(a, expr_id, ty)) |ci| {
        return ci;
    }

    // General case: for simple scalar types, evaluate the expression at comptime and
    // materialize as a constant initializer.
    const result_kind = self.context.type_store.getKind(ty);
    const allow_ct_scalar = switch (result_kind) {
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64, .Bool => true,
        else => false,
    };
    if (allow_ct_scalar) {
        var cv = try self.getCachedComptimeValue(a, expr_id);
        if (cv) |*val| {
            defer val.destroy(self.gpa);
            switch (val.*) {
                .Int => |v| return tir.ConstInit{ .int = @intCast(v) },
                .Float => |v| return tir.ConstInit{ .float = v },
                .Bool => |v| return tir.ConstInit{ .bool = v },
                else => {},
            }
        }
    }

    const kind = a.exprs.index.kinds.items[expr_id.toRaw()];
    if (kind == .StructLit) {
        const struct_lit = a.exprs.get(.StructLit, expr_id);
        const struct_ty = self.context.type_store.get(.Struct, ty);
        const field_decls = self.context.type_store.field_pool.slice(struct_ty.fields);
        const field_inits = a.exprs.sfv_pool.slice(struct_lit.fields);

        var field_const_inits = std.ArrayList(tir.ConstInit){};
        defer field_const_inits.deinit(self.gpa);

        // This assumes fields are in order.
        for (field_inits, 0..) |sfv_id, i| {
            const field_init = a.exprs.StructFieldValue.get(sfv_id);
            const field_decl = self.context.type_store.Field.get(field_decls[i]);
            if (try self.constInitFromExpr(ctx, a, field_init.value, field_decl.ty)) |field_ci| {
                _ = try field_const_inits.append(self.gpa, field_ci);
            } else {
                return null; // Not a constant struct literal
            }
        }

        const owned_fields = try field_const_inits.toOwnedSlice(self.gpa);
        return tir.ConstInit{ .aggregate = owned_fields };
    }

    return null;
}

/// Emit an init function that lowers every global `mlir` declaration in `a`.
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

/// Lower a single `mlir` block expression, translating its pieces and args.
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
    if (self.isType(ty0, .Any)) {
        ty0 = switch (row.kind) {
            .Module => self.context.type_store.tMlirModule(),
            .Attribute => self.context.type_store.tMlirAttribute(),
            .Type => self.context.type_store.tMlirType(),
            .Operation => ty0,
        };
    }
    if (expected_ty) |want| {
        if (self.isType(expr_ty, .Any) and !self.isType(want, .Any)) {
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

/// Resolve the `ComptimeValue` that a splice `piece_id` should inject into the MLIR block.
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
            if (try self.getCachedComptimeValue(a, decl.value)) |value| {
                return value;
            }
            try self.context.diags.addError(diag_loc, .mlir_splice_not_comptime, .{name_str});
            return error.LoweringBug;
        },
        .value_param => |param_info| {
            if (ctx.lookupBindingValue(param_info.name)) |value| {
                return comp.cloneComptimeValue(self.gpa, value.*);
            }
            try self.context.diags.addError(diag_loc, .mlir_splice_unbound, .{name_str});
            return error.LoweringBug;
        },
        .type_param => |param_info| {
            if (ctx.lookupBindingType(param_info.name)) |ty| {
                return comp.ComptimeValue{ .Type = ty };
            }
            try self.context.diags.addError(diag_loc, .mlir_splice_unbound, .{name_str});
            return error.LoweringBug;
        },
    }
}

/// Return a cloned cached comptime value for `expr`, if the checker already computed one.
fn getCachedComptimeValue(self: *LowerTir, a: *ast.Ast, expr: ast.ExprId) !?comp.ComptimeValue {
    if (a.type_info.getComptimeValue(expr)) |cached| {
        const cloned = try comp.cloneComptimeValue(self.gpa, cached.*);
        return cloned;
    }
    return null;
}

// ============================
// Utilities / common helpers
// ============================

/// Distinguishes whether lowering expects an rvalue or the address of an lvalue.
const LowerMode = enum {
    /// Evaluate expressions to their computed value.
    rvalue,
    /// Produce the address/location of an lvalue.
    lvalue_addr,
};

/// Determine whether `ty` represents a void/`()` value.
pub fn isVoid(self: *const LowerTir, ty: types.TypeId) bool {
    return self.context.type_store.index.kinds.items[ty.toRaw()] == .Void;
}

/// Return the optional source location associated with `id` (expr/pattern/stmt), if any.
pub fn optLoc(a: *ast.Ast, id: anytype) tir.OptLocId {
    var store, const Kind = switch (@TypeOf(id)) {
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

/// Produce an undef value of `ty`, falling back to `Any` when `ty` is void so that SSA stays valid.
pub fn safeUndef(self: *LowerTir, blk: *Builder.BlockFrame, ty: types.TypeId, loc: tir.OptLocId) tir.ValueId {
    if (self.isVoid(ty)) {
        return blk.builder.tirValue(.ConstUndef, blk, self.context.type_store.tAny(), loc, .{});
    }
    return blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{});
}

/// Helper that returns an expression's source location for diagnostics.
fn exprDiagLoc(a: *ast.Ast, id: ast.ExprId) Loc {
    const loc_id = optLoc(a, id);
    if (!loc_id.isNone()) {
        return a.exprs.locs.get(loc_id.unwrap());
    }
    return Loc{ .file_id = @intCast(a.file_id), .start = 0, .end = 0 };
}

/// Confirm the recorded type for `id` is not a type error while lowering.
fn ensureExprTypeNotError(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, id: ast.ExprId) anyerror!void {
    const ty = self.getExprType(ctx, a, id);
    if (self.context.type_store.getKind(ty) == .TypeError) {
        const diag_loc = exprDiagLoc(a, id);
        try self.context.diags.addError(diag_loc, .tir_lowering_failed, .{});
        return error.LoweringBug;
    }
}

/// Call the runtime `rt_alloc` helper and unwrap the returned optional pointer.
fn callRuntimeAllocPtr(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    size_bytes: tir.ValueId,
    loc: tir.OptLocId,
) tir.ValueId {
    const ts = self.context.type_store;
    const void_ptr_ty = ts.mkPtr(ts.tVoid(), false);
    const opt_ptr_ty = ts.mkOptional(void_ptr_ty);
    const alloc_name = blk.builder.intern("rt_alloc");
    const alloc_result = blk.builder.call(blk, opt_ptr_ty, alloc_name, &.{size_bytes}, loc);
    return self.optionalPayload(blk, opt_ptr_ty, alloc_result, loc);
}

/// Call the runtime `rt_realloc` helper and return its normalized pointer result.
fn callRuntimeReallocPtr(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    old_ptr: tir.ValueId,
    size_bytes: tir.ValueId,
    loc: tir.OptLocId,
) tir.ValueId {
    const ts = self.context.type_store;
    const void_ptr_ty = ts.mkPtr(ts.tVoid(), false);
    const opt_ptr_ty = ts.mkOptional(void_ptr_ty);
    const realloc_name = blk.builder.intern("rt_realloc");
    const realloc_result = blk.builder.call(blk, opt_ptr_ty, realloc_name, &.{ old_ptr, size_bytes }, loc);
    return self.optionalPayload(blk, opt_ptr_ty, realloc_result, loc);
}

/// Cast the fixed-size array value into a dynarray representation for slicing.
fn coerceArrayToDynArray(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    array_value: tir.ValueId,
    array_ty: types.TypeId,
    dyn_ty: types.TypeId,
    loc: tir.OptLocId,
) ?tir.ValueId {
    const ts = self.context.type_store;
    const arr = ts.get(.Array, array_ty);
    const dyn = ts.get(.DynArray, dyn_ty);
    const ptr_ty = ts.mkPtr(dyn.elem, false);
    const usize_ty = ts.tUsize();

    if (arr.len == 0) {
        const null_ptr = blk.builder.constNull(blk, ptr_ty, loc);
        const zero = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = 0 });
        return blk.builder.structMake(blk, dyn_ty, &[_]tir.Rows.StructFieldInit{
            .{ .index = 0, .name = .none(), .value = null_ptr },
            .{ .index = 1, .name = .none(), .value = zero },
            .{ .index = 2, .name = .none(), .value = zero },
        }, loc);
    }

    const len_u64 = std.math.cast(u64, arr.len) orelse return null;
    const elem_size = check_types.typeSize(self.context, dyn.elem);
    const elem_size_u64 = std.math.cast(u64, elem_size) orelse return null;
    const total_bytes = std.math.mul(u64, elem_size_u64, len_u64) catch return null;

    const bytes_const = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = total_bytes });
    const raw_ptr = self.callRuntimeAllocPtr(blk, bytes_const, loc);
    const data_ptr = blk.builder.tirValue(.CastBit, blk, ptr_ty, loc, .{ .value = raw_ptr });

    var idx: usize = 0;
    while (idx < arr.len) : (idx += 1) {
        const idx_u64 = std.math.cast(u64, idx) orelse return null;
        const idx_val = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = idx_u64 });
        var elem_val = blk.builder.indexOp(blk, arr.elem, array_value, idx_val, loc);
        if (!arr.elem.eq(dyn.elem)) {
            elem_val = self.emitCoerce(blk, elem_val, arr.elem, dyn.elem, loc);
        }
        const offset = blk.builder.gepConst(idx_u64);
        const elem_ptr = blk.builder.gep(blk, ptr_ty, data_ptr, &.{offset}, loc);
        _ = blk.builder.tirValue(.Store, blk, dyn.elem, loc, .{ .ptr = elem_ptr, .value = elem_val, .@"align" = 0 });
    }

    const len_const = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = len_u64 });
    return blk.builder.structMake(blk, dyn_ty, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = data_ptr },
        .{ .index = 1, .name = .none(), .value = len_const },
        .{ .index = 2, .name = .none(), .value = len_const },
    }, loc);
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

    // Special-case: coercions between type handles (TypeType) are no-ops for lowering.
    const got_k0 = self.context.type_store.index.kinds.items[got.toRaw()];
    const want_k0 = self.context.type_store.index.kinds.items[want.toRaw()];
    if (got_k0 == .TypeType and want_k0 == .TypeType) return v;

    const ts = self.context.type_store;
    const gk = ts.index.kinds.items[got.toRaw()];
    const wk = ts.index.kinds.items[want.toRaw()];

    switch (wk) {
        else => {},
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
        .DynArray => {
            if (gk == .Array) {
                if (self.coerceArrayToDynArray(blk, v, got, want, loc)) |dyn_val| {
                    return dyn_val;
                }
            }
            // Fall through: no special coercion, let other cases handle
        },
        .Optional => {
            const opt = ts.get(.Optional, want);
            const bool_ty = ts.tBool();
            const want_ptr = ts.isOptionalPointer(want);

            if (gk == .Optional) {
                // Case: ?U -> ?T
                const got_opt = ts.get(.Optional, got);
                if (got_opt.elem.eq(opt.elem) and want_ptr == ts.isOptionalPointer(got)) {
                    return v; // identical layout
                }

                if (want_ptr) {
                    if (ts.isOptionalPointer(got)) {
                        var payload = blk.builder.tirValue(.CastBit, blk, got_opt.elem, loc, .{ .value = v });
                        if (!got_opt.elem.eq(opt.elem)) {
                            payload = self.emitCoerce(blk, payload, got_opt.elem, opt.elem, loc);
                        }
                        return blk.builder.tirValue(.CastBit, blk, want, loc, .{ .value = payload });
                    }
                    const flag = self.optionalFlag(blk, got, v, loc);
                    var payload = self.optionalPayload(blk, got, v, loc);
                    payload = self.emitCoerce(blk, payload, got_opt.elem, opt.elem, loc);
                    return self.optionalWrapWithFlag(blk, want, flag, payload, loc);
                }

                // Extract fields from ?U
                const flag = blk.builder.extractField(blk, bool_ty, v, 0, loc);
                var payload = blk.builder.extractField(blk, got_opt.elem, v, 1, loc);

                // Coerce payload U -> T. If source is ?any (commonly used for null),
                // avoid casting the undefined payload; use an undef of T instead.
                if (self.context.type_store.getKind(got_opt.elem) == .Any) {
                    payload = blk.builder.tirValue(.ConstUndef, blk, opt.elem, loc, .{});
                } else {
                    payload = self.emitCoerce(blk, payload, got_opt.elem, opt.elem, loc);
                }

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
                return self.optionalWrapSome(blk, want, payload, loc);
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
    }
    // Fallback: materialize/assignable
    return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = v });
}

// ============================
// Top-level lowering
// ============================

/// Attempt to lower a specific declaration `did` when it resolves to a function literal.
fn tryLowerNamedFunction(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    b: *Builder,
    did: ast.DeclId,
    base_name: StrId,
    should_mangle: bool,
    is_method: bool,
    method_key: ?MethodKey,
) !void {
    if (is_method and method_key != null) {
        if (ctx.method_lowered.contains(method_key.?)) return;
    }

    const decl = a.exprs.Decl.get(did);
    const kind = a.exprs.index.kinds.items[decl.value.toRaw()];
    if (kind != .FunctionLit) return;

    const fn_ty = self.getExprType(ctx, a, decl.value);
    if (self.context.type_store.getKind(fn_ty) != .Function) return;

    // const fn_ty_info = self.context.type_store.get(.Function, fn_ty);
    // Removed: for (param_tys) |param_ty| { if (self.isType(param_ty, .Any)) return; }

    const fn_lit = a.exprs.get(.FunctionLit, decl.value);
    const params = a.exprs.param_pool.slice(fn_lit.params);
    var skip_params: usize = 0;
    while (skip_params < params.len and a.exprs.Param.get(params[skip_params]).is_comptime) : (skip_params += 1) {}
    if (skip_params != 0) return;

    const name = if (should_mangle) try self.qualifySymbolName(a, base_name) else base_name;
    try self.lowerFunction(ctx, a, b, name, decl.value, null);

    if (is_method and method_key != null) {
        try ctx.method_lowered.put(method_key.?, {});
    }
}

/// Extract the binding name if `pid` is a simple identifier binding.
fn bindingNameOfPattern(a: *ast.Ast, pid: ast.PatternId) ?StrId {
    const k = a.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Binding => a.pats.get(.Binding, pid).name,
        else => null,
    };
}

/// Resolve a specialized type argument from bindings by inspecting `expr`.
fn resolveSpecializedType(
    _: *types.TypeStore,
    bindings: []const comp.BindingInfo,
    a: *ast.Ast,
    expr: ast.ExprId,
) ?types.TypeId {
    const kind = a.exprs.index.kinds.items[expr.toRaw()];
    switch (kind) {
        .Ident => {
            const name = a.exprs.get(.Ident, expr).name;
            for (bindings) |info| {
                if (!info.name.eq(name)) continue;
                return switch (info.kind) {
                    .type_param => |ty| ty,
                    .value_param => |vp| vp.ty,
                    .runtime_param => |_| null,
                };
            }
            return null;
        },
        else => return null,
    }
}

/// Lookup an override type provided by runtime-only bindings.
fn lookupRuntimeOverride(bindings: []const comp.BindingInfo, name: ast.StrId) ?types.TypeId {
    for (bindings) |info| {
        if (!info.name.eq(name)) continue;
        switch (info.kind) {
            .runtime_param => |ty| return ty,
            else => {},
        }
    }
    return null;
}

/// Extract the payload value from the optional `opt_val` (pointer or struct-backed).
pub fn optionalPayload(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    opt_ty: types.TypeId,
    opt_val: tir.ValueId,
    loc: tir.OptLocId,
) tir.ValueId {
    const opt = self.context.type_store.get(.Optional, opt_ty);
    if (self.context.type_store.isOptionalPointer(opt_ty)) {
        return blk.builder.tirValue(.CastBit, blk, opt.elem, loc, .{ .value = opt_val });
    }
    return blk.builder.extractField(blk, opt.elem, opt_val, 1, loc);
}

/// Read the flag that indicates whether `opt_val` actually contains a value.
pub fn optionalFlag(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    opt_ty: types.TypeId,
    opt_val: tir.ValueId,
    loc: tir.OptLocId,
) tir.ValueId {
    if (self.context.type_store.isOptionalPointer(opt_ty)) {
        const opt = self.context.type_store.get(.Optional, opt_ty);
        const payload = blk.builder.tirValue(.CastBit, blk, opt.elem, loc, .{ .value = opt_val });
        const usize_ty = self.context.type_store.tUsize();
        const payload_bits = blk.builder.tirValue(.CastBit, blk, usize_ty, loc, .{ .value = payload });
        const zero = blk.builder.constNull(blk, usize_ty, loc);
        return blk.builder.binBool(blk, .CmpNe, payload_bits, zero, loc);
    }
    const bool_ty = self.context.type_store.tBool();
    return blk.builder.extractField(blk, bool_ty, opt_val, 0, loc);
}

/// Build an optional value by combining an explicit `flag` with a `payload`.
pub fn optionalWrapWithFlag(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    opt_ty: types.TypeId,
    flag: tir.ValueId,
    payload: tir.ValueId,
    loc: tir.OptLocId,
) tir.ValueId {
    if (self.context.type_store.isOptionalPointer(opt_ty)) {
        const some_val = blk.builder.tirValue(.CastBit, blk, opt_ty, loc, .{ .value = payload });
        const none_val = blk.builder.constNull(blk, opt_ty, loc);
        return blk.builder.tirValue(.Select, blk, opt_ty, loc, .{
            .cond = flag,
            .then_value = some_val,
            .else_value = none_val,
        });
    }
    return blk.builder.structMake(blk, opt_ty, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = flag },
        .{ .index = 1, .name = .none(), .value = payload },
    }, loc);
}

/// Construct a `Some(payload)` optional value with the payload already available.
pub fn optionalWrapSome(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    opt_ty: types.TypeId,
    payload: tir.ValueId,
    loc: tir.OptLocId,
) tir.ValueId {
    if (self.context.type_store.isOptionalPointer(opt_ty)) {
        return blk.builder.tirValue(.CastBit, blk, opt_ty, loc, .{ .value = payload });
    }
    const bool_ty = self.context.type_store.tBool();
    const some_flag = blk.builder.tirValue(.ConstBool, blk, bool_ty, loc, .{ .value = true });
    return blk.builder.structMake(blk, opt_ty, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = some_flag },
        .{ .index = 1, .name = .none(), .value = payload },
    }, loc);
}

/// Determine whether the runtime bindings provide a consistent result type.
fn runtimeResultType(bindings: []const comp.BindingInfo) ?types.TypeId {
    var candidate: ?types.TypeId = null;
    for (bindings) |info| {
        if (info.kind == .runtime_param) {
            const ty = info.kind.runtime_param;
            if (candidate) |existing| {
                if (existing.toRaw() != ty.toRaw()) return null;
            } else {
                candidate = ty;
            }
        }
    }
    return candidate;
}

/// Handle top-level declarations (globals/methods) by emitting lowered functions or globals.
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
            name_opt = try methodSymbolShortName(self, a, did);
        }

        if (name_opt) |nm| {
            const is_method = !d.method_path.isNone();
            const method_info = if (is_method) self.methodKeyForDecl(did) else null;
            if (is_method and method_info == null) return;
            const method_key = if (method_info) |info| info.key else null;
            const base_name = if (method_info) |info|
                try self.methodSymbolName(a, did, info.owner_type)
            else
                nm;
            try self.tryLowerNamedFunction(ctx, a, b, did, base_name, true, is_method, method_key);
        }
        return;
    }
    // Global: emit only for value declarations. Type declarations (TypeType)
    // should not materialize runtime globals.
    if (!d.pattern.isNone()) {
        // Global names should be fully qualified to avoid clashes across packages.
        const nm = try self.symbolNameForDecl(a, did) orelse return;
        const ty = getDeclType(a, did) orelse return;
        if (self.context.type_store.getKind(ty) == .TypeType) {
            return; // skip type declarations
        }
        if (try self.constInitFromExpr(ctx, a, d.value, ty)) |ci| {
            _ = b.addGlobalWithInit(nm, ty, ci);
        } else {
            _ = b.addGlobal(nm, ty);
        }
    }
}

/// Lower the AST attribute range into a list of TIR attribute ids.
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

/// Lower a function literal into TIR and emit its body once per specialization.
pub fn lowerFunction(
    self: *LowerTir,
    lower_ctx: *LowerContext,
    a: *ast.Ast,
    b: *Builder,
    name: StrId,
    fun_eid: ast.ExprId,
    ctx: ?*const comp.SpecializationContext,
) !void {
    if (lower_ctx.lowered_functions.contains(name)) return;
    try lower_ctx.lowered_functions.put(name, {});

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

/// Evaluate `id` as a sequence of statements, running any defers and ignoring the final value.
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

/// Lower a declaration statement, destructuring patterns or evaluating the RHS for side effects.
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

/// Lower a `return` statement by computing the result value and emitting the terminator.
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
    try self.lowerReturnCommon(ctx, a, env, f, blk, r.value, stmt_loc);
}

/// Shared lowering logic for a `return` value that runs normal/err defers and emits the terminator.
fn lowerReturnCommon(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    value_opt: ast.OptExprId,
    stmt_loc: tir.OptLocId,
) !void {
    const defer_mark: u32 = 0;

    if (!value_opt.isNone()) {
        const frow = f.builder.t.funcs.Function.get(f.id);
        const expect = frow.result;
        const value_expr = value_opt.unwrap();
        const value_loc = optLoc(a, value_expr);
        const v = try self.lowerExpr(ctx, a, env, f, blk, value_expr, expect, .rvalue);

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

/// Emit stores/destructures for a top-level assignment, supporting `_` discard and slots.
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
    // Handle discard assignment: `_ = rhs` should only evaluate RHS for side-effects.
    if (a.exprs.index.kinds.items[as.left.toRaw()] == .Ident) {
        const ident = a.exprs.get(.Ident, as.left);
        if (std.mem.eql(u8, a.exprs.strs.get(ident.name), "_")) {
            // Do not attempt to read a type for the LHS or perform a store.
            _ = try self.lowerExpr(ctx, a, env, f, blk, as.right, null, .rvalue);
            return;
        }
    }
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

/// Lower a statement ID by dispatching to the appropriate handler (expr, loop, return, etc.).
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

/// Entry describing the callee metadata used by `lowerCall`.
const CalleeInfo = struct {
    /// Interned string representing the callee's unqualified name.
    name: StrId,
    /// Optional fully-qualified symbol name used for diagnostics.
    qualified_name: ?StrId,
    /// Optional type reported for the callee expression.
    fty: ?types.TypeId,
    /// AST node that triggered this call/lookup.
    expr: ast.ExprId,
};

/// Interpret `expr` as a type argument, returning the referenced type when possible.
fn resolveTypeArg(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, expr: ast.ExprId) ?types.TypeId {
    const ty = self.getExprType(ctx, a, expr);
    if (self.context.type_store.getKind(ty) != .TypeType) return null;
    return self.context.type_store.get(.TypeType, ty).of;
}

/// Build a key used to cache method lookups by module alias and member name.
fn moduleCallKey(alias: ast.StrId, field: StrId) u64 {
    return (@as(u64, alias.toRaw()) << 32) | @as(u64, field.toRaw());
}

/// Build a short symbol name combining the owner and method segments.
fn methodSymbolShortName(
    self: *LowerTir,
    a: *ast.Ast,
    did: ast.DeclId,
) !StrId {
    const decl = a.exprs.Decl.get(did);
    std.debug.assert(!decl.method_path.isNone());
    const seg_ids = a.exprs.method_path_pool.slice(decl.method_path.asRange());
    std.debug.assert(seg_ids.len >= 2);

    const owner_seg = a.exprs.MethodPathSeg.get(seg_ids[0]);
    const method_seg = a.exprs.MethodPathSeg.get(seg_ids[seg_ids.len - 1]);
    const owner_name = a.exprs.strs.get(owner_seg.name);
    const method_name = a.exprs.strs.get(method_seg.name);

    const symbol = try std.fmt.allocPrint(self.gpa, "{s}__{s}", .{ owner_name, method_name });
    defer self.gpa.free(symbol);
    return self.context.type_store.strs.intern(symbol);
}

/// Create a key identifying a lowered method based on owner type and method name.
fn methodLowerKey(owner_type: types.TypeId, method_name: ast.StrId) MethodKey {
    return MethodKey{ .owner = owner_type.toRaw(), .name = method_name.toRaw() };
}

/// Memoized data describing a previously lowered method symbol.
const MethodLowerInfo = struct {
    /// Derived key used to memoize lowered method declarations.
    key: MethodKey,
    /// Owner type that originally declared the method.
    owner_type: types.TypeId,
};

/// Compute a lowered symbol name for method `did` bound to `owner_type`, ensuring uniqueness.
pub fn methodSymbolName(
    self: *LowerTir,
    a: *ast.Ast,
    did: ast.DeclId,
    owner_type: types.TypeId,
) !StrId {
    const short_name = try methodSymbolShortName(self, a, did);
    const short_str = self.context.type_store.strs.get(short_name);
    const symbol = try std.fmt.allocPrint(self.gpa, "{s}_T{d}", .{ short_str, owner_type.toRaw() });
    defer self.gpa.free(symbol);
    return self.context.type_store.strs.intern(symbol);
}

/// Lookup the stored `MethodLowerInfo` for `decl_id` if it was previously lowered.
fn methodKeyForDecl(self: *LowerTir, decl_id: ast.DeclId) ?MethodLowerInfo {
    var it = self.context.type_store.method_table.iterator();
    while (it.next()) |entry| {
        const method = entry.value_ptr.*;
        if (method.decl_id.toRaw() == decl_id.toRaw()) {
            return MethodLowerInfo{
                .key = methodLowerKey(method.owner_type, method.method_name),
                .owner_type = method.owner_type,
            };
        }
    }
    return null;
}

/// Arrange arguments and runtime metadata before lowering a method or builtin call.
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

    const base_symbol = try self.methodSymbolName(symbol_ast, binding.decl_id, binding.owner_type);
    const symbol = try self.qualifySymbolName(symbol_ast, base_symbol);
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

/// Try to resolve the binding represented by a field-access into an actual method entry.
fn synthesizeMethodBinding(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    field_expr_id: ast.ExprId,
) !?types.MethodBinding {
    if (a.exprs.index.kinds.items[field_expr_id.toRaw()] != .FieldAccess) return null;

    const field_expr = a.exprs.get(.FieldAccess, field_expr_id);
    if (a.type_info.expr_types.items[field_expr.parent.toRaw()] == null) {
        const cctx = self.chk.checker_ctx.items[a.file_id];
        _ = try self.chk.checkExpr(cctx, a, field_expr.parent);
    }
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

/// Resolve the name that should be used when calling `field_expr_id`, accounting for imports.
fn resolveFieldAccessName(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, field_expr_id: ast.ExprId) ast.StrId {
    const field_access = a.exprs.get(.FieldAccess, field_expr_id);
    const parent_ty = self.getExprType(ctx, a, field_access.parent);

    if (self.context.type_store.getKind(parent_ty) == .Ast) {
        const ast_ty = self.context.type_store.get(.Ast, parent_ty);
        const pkg_name = self.context.interner.get(ast_ty.pkg_name);
        const filepath = self.context.interner.get(ast_ty.filepath);
        const pkg = self.context.compilation_unit.packages.getPtr(pkg_name) orelse
            unreachable;
        const parent_unit = pkg.sources.getPtr(filepath) orelse
            unreachable;

        if (parent_unit.ast) |imported_ast| {
            const field_name = a.exprs.strs.get(field_access.field);
            const target_sid = imported_ast.exprs.strs.intern(field_name);
            if (imported_ast.type_info.getExport(target_sid)) |ex| {
                const drow = imported_ast.exprs.Decl.get(ex.decl_id);
                return switch (imported_ast.exprs.index.kinds.items[drow.value.toRaw()]) {
                    .Ident => imported_ast.exprs.get(.Ident, drow.value).name,
                    .FieldAccess => self.resolveFieldAccessName(ctx, imported_ast, drow.value),
                    else => field_access.field,
                };
            }
        }
    }

    return field_access.field;
}

/// Trace a call expression to identify the callee symbol plus qualified name if any.
fn resolveCallee(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, f: *Builder.FunctionFrame, row: ast.Rows.Call) !CalleeInfo {
    const cctx = self.chk.checker_ctx.items[a.file_id];
    var current = row.callee;
    var depth: usize = 0;

    while (depth < 32) : (depth += 1) {
        const ck = a.exprs.index.kinds.items[current.toRaw()];
        switch (ck) {
            .Ident => {
                const ident = a.exprs.get(.Ident, current);
                if (cctx.symtab.lookup(cctx.symtab.currentId(), ident.name)) |sid| {
                    const srow = cctx.symtab.syms.get(sid);
                    if (!srow.origin_decl.isNone()) {
                        const did = srow.origin_decl.unwrap();
                        const drow = a.exprs.Decl.get(did);
                        const rhs_kind = a.exprs.index.kinds.items[drow.value.toRaw()];
                        switch (rhs_kind) {
                            .Ident, .FieldAccess => {
                                current = drow.value;
                                continue;
                            },
                            else => {},
                        }
                    }
                }
                return .{ .name = ident.name, .qualified_name = null, .fty = self.getExprType(ctx, a, row.callee), .expr = current };
            },
            .FieldAccess => {
                const resolved_name = self.resolveFieldAccessName(ctx, a, current);
                return .{ .name = resolved_name, .qualified_name = null, .fty = self.getExprType(ctx, a, row.callee), .expr = current };
            },
            else => break,
        }
    }

    return .{ .name = f.builder.intern("<indirect>"), .qualified_name = null, .fty = self.getExprType(ctx, a, row.callee), .expr = row.callee };
}

/// Create the payload value for a variant literal call based on the variant type `ety`.
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
    var first_field: ?StrId = null;
    while (a.exprs.index.kinds.items[cur.toRaw()] == .FieldAccess) {
        const fr = a.exprs.get(.FieldAccess, cur);
        if (first_field == null) first_field = fr.field; // take outermost field (the tag name)
        cur = fr.parent;
    }
    std.debug.assert(first_field != null);
    const lname = first_field.?;

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
    if (!found) {
        // Diagnostic: unknown variant tag at this call site (TIR-specific)
        const where: Loc = if (!loc.isNone()) a.exprs.locs.get(loc.unwrap()) else Loc.init(@intCast(a.file_id), 0, 0);
        // Compose message: "Tag 'Name' in <Type>"
        var buf = std.ArrayList(u8){};
        defer buf.deinit(self.gpa);
        const w = buf.writer(self.gpa);
        try w.print("tag '{s}' in ", .{a.exprs.strs.get(lname)});
        try self.context.type_store.fmt(ety, w);
        const sid = self.context.interner.intern(buf.items);
        _ = self.context.diags.addError(where, .tir_variant_tag_not_found, .{self.context.interner.get(sid)}) catch {};
        return error.LoweringBug;
    }

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

/// Convert a literal AST node into a `ComptimeValue` when possible.
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
            break :blk comp.ComptimeValue{ .Int = @as(i128, @intCast(info.value)) };
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

/// Attempt to evaluate a call expression at comptime so it can be folded into the lowered IR.
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
    // Avoid requiring a stamped callee type just to check the name.
    const ck = a.exprs.index.kinds.items[row.callee.toRaw()];
    const callee_name = blk: {
        if (ck == .Ident) break :blk a.exprs.strs.get(a.exprs.get(.Ident, row.callee).name);
        if (ck == .FieldAccess) break :blk a.exprs.strs.get(a.exprs.get(.FieldAccess, row.callee).field);
        break :blk a.exprs.strs.get(f.builder.intern("<indirect>"));
    };
    const loc = optLoc(a, id);
    const arg_ids = a.exprs.expr_pool.slice(row.args);

    if (std.mem.eql(u8, callee_name, "sizeof")) {
        if (arg_ids.len == 1) {
            const target_ty = self.getExprType(ctx, a, arg_ids[0]);
            const sz: u64 = @intCast(check_types.typeSize(self.context, target_ty));
            const want = self.getExprType(ctx, a, id);
            return blk.builder.tirValue(.ConstInt, blk, want, loc, .{ .value = sz });
        }
        return null;
    }

    if (!(std.mem.eql(u8, callee_name, "get_type_by_name") or
        std.mem.eql(u8, callee_name, "comptime_print") or
        std.mem.eql(u8, callee_name, "type_of")))
        return null;
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

/// Try to request a specialization for the target function when the call carries comptime bindings.
fn trySpecializeFunctionCall(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    callee: *CalleeInfo,
    _: ast.ExprId,
    callee_name_ptr: *[]const u8,
    _: ?ast.DeclId,
    method_binding: ?types.MethodBinding,
    arg_ids_ptr: *[]const ast.ExprId,
    param_tys_ptr: *[]const types.TypeId,
    fixed_ptr: *usize,
    is_variadic_ptr: *bool,
    treat_trailing_any_ptr: *bool,
    trailing_any_tuple_ty_ptr: *?types.TypeId,
    decl_ctx: call_resolution.FunctionDeclContext,
) !void {
    if (callee.fty == null) return;
    const callee_fty = callee.fty.?;
    if (self.context.type_store.index.kinds.items[callee_fty.toRaw()] != .Function) return;

    var param_tys = param_tys_ptr.*;
    var fixed = fixed_ptr.*;
    var is_variadic = is_variadic_ptr.*;
    var treat_trailing_any = treat_trailing_any_ptr.*;
    var trailing_any_tuple_ty = trailing_any_tuple_ty_ptr.*;
    var arg_ids = arg_ids_ptr.*;
    var callee_name = callee_name_ptr.*;
    defer {
        param_tys_ptr.* = param_tys;
        fixed_ptr.* = fixed;
        is_variadic_ptr.* = is_variadic;
        treat_trailing_any_ptr.* = treat_trailing_any;
        trailing_any_tuple_ty_ptr.* = trailing_any_tuple_ty;
        arg_ids_ptr.* = arg_ids;
        callee_name_ptr.* = callee_name;
    }

    const fty = self.context.type_store.get(.Function, callee_fty);
    param_tys = self.context.type_store.type_pool.slice(fty.params);
    is_variadic = fty.is_variadic;
    fixed = param_tys.len;
    if (is_variadic and fixed > 0) fixed -= 1; // last param is the vararg pack type
    if (!fty.is_extern and param_tys.len > 0 and self.isType(param_tys[param_tys.len - 1], .Any)) {
        treat_trailing_any = true;
    }
    const decl_ast = decl_ctx.ast;
    const decl = decl_ast.exprs.Decl.get(decl_ctx.decl_id);

    const base_kind = decl_ast.exprs.index.kinds.items[decl.value.toRaw()];
    if (callee.qualified_name == null) {
        if (try symbolNameForDecl(self, decl_ast, decl_ctx.decl_id)) |sym| {
            callee.qualified_name = sym;
        }
    }
    if (base_kind != .FunctionLit) return;
    const params = decl_ast.exprs.param_pool.slice(decl_ast.exprs.get(.FunctionLit, decl.value).params);
    var skip_params: usize = 0;
    while (skip_params < params.len and decl_ast.exprs.Param.get(params[skip_params]).is_comptime) : (skip_params += 1) {}

    var binding_infos: List(comp.BindingInfo) = .empty;
    var interpreter_bindings: List(interpreter.Binding) = .empty;
    defer {
        for (binding_infos.items) |*info| info.deinit(self.gpa);
        binding_infos.deinit(self.gpa);
        for (interpreter_bindings.items) |*binding| binding.value.destroy(self.gpa);
        interpreter_bindings.deinit(self.gpa);
    }

    if (method_binding) |mb| {
        const owner_sid = a.exprs.strs.intern("__owner");
        try binding_infos.append(self.gpa, comp.BindingInfo.runtimeParam(owner_sid, mb.owner_type));
        try interpreter_bindings.append(self.gpa, .{ .name = owner_sid, .value = comp.ComptimeValue{ .Type = mb.owner_type } });
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
                try binding_infos.append(self.gpa, comp.BindingInfo.typeParam(pname, targ));
                try interpreter_bindings.append(self.gpa, .{ .name = pname, .value = comp.ComptimeValue{ .Type = targ } });
            } else {
                const comptime_val_opt = if (a.exprs.index.kinds.items[arg_expr.toRaw()] == .Literal)
                    try self.constValueFromLiteral(a, arg_expr)
                else
                    null;

                const comptime_val = comptime_val_opt orelse blk: {
                    if (try self.getCachedComptimeValue(a, arg_expr)) |cached| break :blk cached;
                    ok = false;
                    break :blk comp.ComptimeValue{ .Void = {} };
                };

                var info = comp.BindingInfo.valueParam(self.gpa, pname, param_ty, comptime_val) catch {
                    ok = false;
                    break;
                };
                binding_infos.append(self.gpa, info) catch |err| {
                    info.deinit(self.gpa);
                    return err;
                };
                try interpreter_bindings.append(self.gpa, .{ .name = pname, .value = comptime_val });
            }
        }
    }

    var specialized_result_override: ?types.TypeId = null;

    if (ok) {
        const original_args = arg_ids;
        const trailing_start = if (treat_trailing_any and params.len > 0) params.len - 1 else params.len;
        var runtime_idx: usize = skip_params;
        while (runtime_idx < params.len and runtime_idx < original_args.len) : (runtime_idx += 1) {
            if (treat_trailing_any and runtime_idx >= trailing_start) break;

            const param = decl_ast.exprs.Param.get(params[runtime_idx]);
            if (param.pat.isNone()) continue;
            const pname = bindingNameOfPattern(decl_ast, param.pat.unwrap()) orelse continue;

            const param_ty_idx = runtime_idx - skip_params;
            const param_ty = if (param_ty_idx < param_tys.len)
                param_tys[param_ty_idx]
            else
                self.context.type_store.tAny();
            if (!self.isType(param_ty, .Any)) continue;

            const arg_ty = self.exprTypeWithEnv(ctx, a, env, original_args[runtime_idx]);
            if (self.isType(arg_ty, .Any)) continue;

            try binding_infos.append(self.gpa, comp.BindingInfo.runtimeParam(pname, arg_ty));
        }

        if (treat_trailing_any and params.len > 0) {
            const tuple_start = params.len - 1;
            const tuple_ty = try self.computeTrailingAnyTupleType(ctx, a, env, original_args, tuple_start);
            trailing_any_tuple_ty = tuple_ty;
            const tuple_kind = self.context.type_store.getKind(tuple_ty);
            const is_empty_tuple = tuple_kind == .Tuple and self.context.type_store.type_pool.slice(
                self.context.type_store.get(.Tuple, tuple_ty).elems,
            ).len == 0;
            if (!is_empty_tuple) {
                const last_param = decl_ast.exprs.Param.get(params[params.len - 1]);
                if (!last_param.pat.isNone()) {
                    if (bindingNameOfPattern(decl_ast, last_param.pat.unwrap())) |pname| {
                        try binding_infos.append(self.gpa, comp.BindingInfo.runtimeParam(pname, tuple_ty));
                    }
                }
            }
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
            const context = self.chk.checker_ctx.items[decl_ast.file_id];
            const specialized_fn_ty = try self.chk.checkSpecializedFunction(context, decl_ast, decl.value, runtime_specs.items);
            if (self.chk.typeKind(specialized_fn_ty) != .TypeError) {
                const fn_info_override = self.context.type_store.get(.Function, specialized_fn_ty);
                specialized_result_override = fn_info_override.result;
            } else {
                ok = false;
            }
        }
    }

    if (!ok or binding_infos.items.len <= 0) return;

    const mangled = try comp.mangleMonomorphName(self, callee.name, binding_infos.items);
    const qualified_mangled = try self.qualifySymbolName(decl_ast, mangled);

    const base_params = self.context.type_store.type_pool.slice(fty.params);
    std.debug.assert(skip_params <= base_params.len);

    const runtime_count = base_params.len - skip_params;
    var runtime_params = try self.gpa.alloc(types.TypeId, runtime_count);
    defer self.gpa.free(runtime_params);

    var idx: usize = 0;
    var i: usize = skip_params;
    while (i < base_params.len) : (i += 1) {
        const base_ty = base_params[i];
        const param = decl_ast.exprs.Param.get(params[i]);
        var specialized_ty = base_ty;
        if (!param.ty.isNone()) {
            if (resolveSpecializedType(self.context.type_store, binding_infos.items, decl_ast, param.ty.unwrap())) |resolved| {
                specialized_ty = resolved;
            }
        }
        if (!param.pat.isNone()) {
            if (bindingNameOfPattern(decl_ast, param.pat.unwrap())) |pname| {
                if (lookupRuntimeOverride(binding_infos.items, pname)) |override_ty| {
                    specialized_ty = override_ty;
                }
            }
        }
        const param_kind = self.context.type_store.getKind(specialized_ty);
        runtime_params[idx] = if (param_kind == .TypeType)
            self.context.type_store.get(.TypeType, specialized_ty).of
        else
            specialized_ty;
        idx += 1;
    }

    var result_ty = if (specialized_result_override) |override|
        override
    else blk: {
        if (!decl_ast.exprs.get(.FunctionLit, decl.value).result_ty.isNone()) {
            if (resolveSpecializedType(
                self.context.type_store,
                binding_infos.items,
                decl_ast,
                decl_ast.exprs.get(.FunctionLit, decl.value).result_ty.unwrap(),
            )) |resolved| {
                break :blk resolved;
            }
        }
        break :blk fty.result;
    };

    if (specialized_result_override == null and self.context.type_store.getKind(result_ty) == .Any) {
        if (runtimeResultType(binding_infos.items)) |override| {
            result_ty = override;
        }
    }

    if (self.context.type_store.getKind(result_ty) == .TypeType) {
        result_ty = self.context.type_store.get(.TypeType, result_ty).of;
    }

    const specialized_ty = self.context.type_store.mkFunction(
        runtime_params,
        result_ty,
        fty.is_variadic,
        fty.is_pure,
        fty.is_extern,
    );

    var req = comp.SpecializationRequest{
        .decl_id = decl_ctx.decl_id,
        .mangled_name = qualified_mangled,
        .specialized_ty = specialized_ty,
        .skip_params = skip_params,
        .bindings = binding_infos.items,
    };

    const target_interp = try ctx.getInterpreterFor(decl_ast);
    const specialized = try target_interp.specializeFunction(decl_ctx.decl_id, &interpreter_bindings);
    try ctx.pushSnapshot(specialized.snapshot, target_interp);
    defer ctx.popSnapshot();
    const builder = ctx.builder orelse unreachable;
    try comp.lowerSpecializedFunction(self, ctx, decl_ast, builder, &req);

    callee.name = mangled;
    callee.qualified_name = qualified_mangled;
    callee.fty = specialized_ty;
    callee_name = self.context.type_store.strs.get(callee.name);
    arg_ids = arg_ids[skip_params..];

    const spec_info = self.context.type_store.get(.Function, specialized_ty);
    param_tys = self.context.type_store.type_pool.slice(spec_info.params);
    is_variadic = spec_info.is_variadic;
    fixed = param_tys.len;
    if (is_variadic and fixed > 0) fixed -= 1;
}

/// Emit the TIR form of a call expression, handling attributes, comptime args, and lowering the callee.
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
    const callee_expr = callee.expr;
    if (callee.fty == null) {
        callee.fty = self.getExprType(ctx, a, callee_expr);
    }
    var arg_ids = a.exprs.expr_pool.slice(row.args);
    var method_arg_buf: []ast.ExprId = &.{};
    var method_decl_id: ?ast.DeclId = null;
    var method_binding: ?types.MethodBinding = null;
    defer {
        if (method_arg_buf.len != 0) self.gpa.free(method_arg_buf);
    }
    if (a.type_info.getMethodBinding(callee_expr)) |binding| {
        if (a.exprs.index.kinds.items[callee_expr.toRaw()] == .FieldAccess) {
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
    } else if (a.exprs.index.kinds.items[callee_expr.toRaw()] == .FieldAccess) {
        if (try self.synthesizeMethodBinding(ctx, a, env, callee_expr)) |binding| {
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
    var treat_trailing_any = false;
    var trailing_any_tuple_ty: ?types.TypeId = null;
    if (callee.fty) |fty| {
        treat_trailing_any = self.hasTrailingAnyRuntimeParam(fty);
    }
    if (a.type_info.getSpecializedCall(id)) |decl_ctx| {
        try self.trySpecializeFunctionCall(
            ctx,
            a,
            env,
            &callee,
            callee_expr,
            &callee_name,
            method_decl_id,
            method_binding,
            &arg_ids,
            &param_tys,
            &fixed,
            &is_variadic,
            &treat_trailing_any,
            &trailing_any_tuple_ty,
            decl_ctx,
        );
    }

    if (callee.qualified_name == null and method_decl_id == null) {
        if (call_resolution.findFunctionDeclForCall(self.context, a, callee_expr, callee.name)) |decl_ctx| {
            if (try symbolNameForDecl(self, decl_ctx.ast, decl_ctx.decl_id)) |sym| {
                callee.qualified_name = sym;
            }
        }
    }

    var vals_list: List(tir.ValueId) = .empty;
    defer vals_list.deinit(self.gpa);

    var fixed_params_count: usize = 0;
    var is_variadic_extern = false;
    if (callee.fty) |fty| {
        if (self.context.type_store.index.kinds.items[fty.toRaw()] == .Function) {
            const fnrow = self.context.type_store.get(.Function, fty);
            param_tys = self.context.type_store.type_pool.slice(fnrow.params);
            is_variadic_extern = fnrow.is_variadic and fnrow.is_extern;
            fixed_params_count = param_tys.len;
            if (is_variadic_extern and fixed_params_count > 0) fixed_params_count -= 1;
        }
    }
    const is_non_extern_any_variadic_candidate = treat_trailing_any;
    if (is_non_extern_any_variadic_candidate and fixed_params_count > 0) {
        fixed_params_count -= 1;
    }
    // Handle fixed arguments
    var i: usize = 0;
    while (i < arg_ids.len) : (i += 1) {
        if (is_non_extern_any_variadic_candidate and i >= fixed_params_count) {
            break; // Stop here, the 'any' parameter and subsequent args will be packed
        }

        const want: ?types.TypeId = if (i < fixed_params_count) param_tys[i] else null;
        const lower_mode: LowerMode = blk: {
            if (method_binding) |mb| {
                if (mb.requires_implicit_receiver and mb.needs_addr_of and i == 0) {
                    break :blk .lvalue_addr;
                }
            }
            break :blk .rvalue;
        };
        const v = try self.lowerExpr(ctx, a, env, f, blk, arg_ids[i], want, lower_mode);
        try vals_list.append(self.gpa, v);
    }

    try self.lowerRemainingArgs(
        ctx,
        a,
        env,
        f,
        blk,
        arg_ids,
        param_tys,
        &vals_list,
        fixed_params_count,
        is_non_extern_any_variadic_candidate,
        &trailing_any_tuple_ty,
        method_binding,
        loc,
        i,
    );

    try self.synthesizeDefaultTrailingArgs(
        ctx,
        a,
        env,
        f,
        blk,
        &callee,
        callee_expr,
        method_decl_id,
        param_tys,
        &vals_list,
        is_variadic_extern,
        is_non_extern_any_variadic_candidate,
    );

    if (is_variadic_extern and vals_list.items.len > fixed_params_count) {
        try self.handleExternVariadicArgs(
            ctx,
            a,
            env,
            f,
            blk,
            id,
            arg_ids,
            &vals_list,
            fixed_params_count,
        );
    }

    if (method_binding) |mb| {
        if (mb.builtin) |builtin_kind| {
            switch (builtin_kind) {
                .dynarray_append => {
                    std.debug.assert(mode != .lvalue_addr);
                    return try self.lowerDynArrayAppend(f, blk, loc, mb, vals_list.items);
                },
            }
        }
    }

    return self.emitCallValue(
        ctx,
        a,
        env,
        f,
        blk,
        id,
        row,
        &callee,
        callee_expr,
        expected,
        mode,
        vals_list.items,
        loc,
    );
}

/// Lower the remaining argument expressions, injecting a packed tuple for `any` trailing parameters.
fn lowerRemainingArgs(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    arg_ids: []const ast.ExprId,
    param_tys: []const types.TypeId,
    vals_list: *List(tir.ValueId),
    fixed_params_count: usize,
    is_non_extern_any_variadic_candidate: bool,
    trailing_any_tuple_ty_ptr: *?types.TypeId,
    method_binding: ?types.MethodBinding,
    loc: tir.OptLocId,
    start_index: usize,
) !void {
    if (is_non_extern_any_variadic_candidate) {
        const trailing_len = if (arg_ids.len > start_index) arg_ids.len - start_index else 0;
        if (trailing_len == 1) {
            const idx = start_index;
            if (!self.isSpreadArgExpr(ctx, a, env, arg_ids[idx])) {
                const single_val = try self.lowerExpr(ctx, a, env, f, blk, arg_ids[idx], null, .rvalue);
                try vals_list.append(self.gpa, single_val);
                return;
            }
        }

        var extra_vals: List(tir.ValueId) = .empty;
        defer extra_vals.deinit(self.gpa);

        var j = fixed_params_count;
        while (j < arg_ids.len) : (j += 1) {
            try extra_vals.append(self.gpa, try self.lowerExpr(ctx, a, env, f, blk, arg_ids[j], null, .rvalue));
        }

        const packed_tuple_ty = trailing_any_tuple_ty_ptr.* orelse blk: {
            const ty = try self.computeTrailingAnyTupleType(ctx, a, env, arg_ids, fixed_params_count);
            trailing_any_tuple_ty_ptr.* = ty;
            break :blk ty;
        };

        const packed_tuple_val = blk.builder.tupleMake(blk, packed_tuple_ty, extra_vals.items, loc);
        try vals_list.append(self.gpa, packed_tuple_val);
        return;
    }

    var idx = start_index;
    while (idx < arg_ids.len) : (idx += 1) {
        const want: ?types.TypeId = if (idx < fixed_params_count) param_tys[idx] else null;
        const lower_mode: LowerMode = blk: {
            if (method_binding) |mb| {
                if (mb.requires_implicit_receiver and mb.needs_addr_of and idx == 0) {
                    break :blk .lvalue_addr;
                }
            }
            break :blk .rvalue;
        };
        const v = try self.lowerExpr(ctx, a, env, f, blk, arg_ids[idx], want, lower_mode);
        try vals_list.append(self.gpa, v);
    }
}

/// Inject default trailing args for methods/functions when the caller omits them.
fn synthesizeDefaultTrailingArgs(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    callee: *CalleeInfo,
    callee_expr: ast.ExprId,
    method_decl_id: ?ast.DeclId,
    param_tys: []const types.TypeId,
    vals_list: *List(tir.ValueId),
    is_variadic_extern: bool,
    is_non_extern_any_variadic_candidate: bool,
) !void {
    if (is_variadic_extern or is_non_extern_any_variadic_candidate or param_tys.len <= vals_list.items.len) {
        return;
    }

    const dctx = if (method_decl_id) |mid|
        FunctionDeclContext{ .ast = a, .decl_id = mid }
    else if (callee.fty) |_|
        call_resolution.findFunctionDeclForCall(self.context, a, callee_expr, callee.name) orelse return
    else
        return;

    const decl_ast = dctx.ast;
    const decl = decl_ast.exprs.Decl.get(dctx.decl_id);
    if (decl_ast.exprs.index.kinds.items[decl.value.toRaw()] != .FunctionLit)
        return;

    const fnr = decl_ast.exprs.get(.FunctionLit, decl.value);
    const params2 = decl_ast.exprs.param_pool.slice(fnr.params);
    try env.pushScope(self.gpa);
    defer _ = env.popScope();

    var j: usize = 0;
    while (j < vals_list.items.len and j < params2.len and j < param_tys.len) : (j += 1) {
        const p = decl_ast.exprs.Param.get(params2[j]);
        if (!p.pat.isNone()) {
            if (bindingNameOfPattern(decl_ast, p.pat.unwrap())) |pname| {
                try env.bind(self.gpa, decl_ast, pname, .{
                    .value = vals_list.items[j],
                    .ty = param_tys[j],
                    .is_slot = false,
                });
            }
        }
    }
    while (vals_list.items.len < param_tys.len) {
        const idx: usize = vals_list.items.len;
        if (idx >= params2.len) break;
        const p = decl_ast.exprs.Param.get(params2[idx]);
        if (p.value.isNone()) break;
        const def_expr = p.value.unwrap();
        const want_ty = if (idx < param_tys.len) param_tys[idx] else null;
        const def_v = try self.lowerExpr(ctx, decl_ast, env, f, blk, def_expr, want_ty, .rvalue);
        try vals_list.append(self.gpa, def_v);
        if (!p.pat.isNone()) {
            if (bindingNameOfPattern(decl_ast, p.pat.unwrap())) |pname| {
                const bind_ty = if (want_ty) |wt| wt else self.getExprType(ctx, decl_ast, def_expr);
                try env.bind(self.gpa, decl_ast, pname, .{ .value = def_v, .ty = bind_ty, .is_slot = false });
            }
        }
    }
}

/// Detect whether `expr` references an imported module member via dotted access.
fn isImportMemberExpr(a: *ast.Ast, expr: ast.ExprId) bool {
    var current = expr;
    while (true) {
        const kind = a.exprs.index.kinds.items[current.toRaw()];
        switch (kind) {
            .FieldAccess => {
                const row = a.exprs.get(.FieldAccess, current);
                current = row.parent;
                continue;
            },
            .Ident => {
                const ident = a.exprs.get(.Ident, current);
                return call_resolution.findTopLevelImportByName(a, ident.name) != null;
            },
            .Import => return true,
            else => return false,
        }
    }
}

/// Emit the actual call instruction (direct or indirect) and adjust for `.lvalue_addr` mode.
fn emitCallValue(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    row: ast.Rows.Call,
    callee: *CalleeInfo,
    callee_expr: ast.ExprId,
    expected: ?types.TypeId,
    mode: LowerMode,
    vals: []tir.ValueId,
    loc: tir.OptLocId,
) !tir.ValueId {
    // Choose a concrete return type: callee.fty.ret -> expected -> stamped -> void
    const ret_ty = blk: {
        if (callee.fty) |fty| {
            if (self.context.type_store.index.kinds.items[fty.toRaw()] == .Function) {
                const fr2 = self.context.type_store.get(.Function, fty);
                const rt = fr2.result;
                if (!self.isVoid(rt) and !self.isType(rt, .Any)) break :blk rt;
            }
        }
        if (expected) |e| if (!self.isVoid(e) and !self.isType(e, .Any)) break :blk e;
        break :blk self.getExprType(ctx, a, id);
    };

    if (!self.isType(ret_ty, .Any)) {
        a.type_info.setExprType(id, ret_ty);
        try self.noteExprType(ctx, id, ret_ty);
    }

    const callee_ty = self.getExprType(ctx, a, row.callee);
    var call_val: tir.ValueId = undefined;
    const callee_name_str = self.context.type_store.strs.get(callee.name);
    const callee_kind = self.context.type_store.getKind(callee_ty);

    // Detect if callee is a module member function: mod.name(...)
    const callee_expr_kind = a.exprs.index.kinds.items[callee_expr.toRaw()];
    const callee_is_import_member = isImportMemberExpr(a, callee_expr);
    const callee_is_method_call = a.type_info.getMethodBinding(callee_expr) != null;
    const should_force_indirect = switch (callee_expr_kind) {
        .Ident => false,
        .FieldAccess => !callee_is_import_member and !callee_is_method_call,
        else => true,
    };

    if (should_force_indirect or (callee_kind == .Ptr and self.context.type_store.getKind(self.context.type_store.get(.Ptr, callee_ty).elem) == .Function)) {
        const fn_ptr_val = try self.lowerExpr(ctx, a, env, f, blk, row.callee, callee_ty, .rvalue);
        call_val = blk.builder.indirectCall(blk, ret_ty, fn_ptr_val, vals, loc);
    } else if (std.mem.eql(u8, callee_name_str, "<indirect>")) {
        const want_ptr_ty = self.context.type_store.mkPtr(callee_ty, false);
        const fn_ptr_val = try self.lowerExpr(ctx, a, env, f, blk, row.callee, want_ptr_ty, .lvalue_addr);
        call_val = blk.builder.indirectCall(blk, ret_ty, fn_ptr_val, vals, loc);
    } else {
        const callee_sym = if (callee.qualified_name) |sym| sym else callee.name;
        call_val = blk.builder.call(blk, ret_ty, callee_sym, vals, loc);
    }

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

/// Lower variadic arguments passed to extern functions, expanding spreads and promoting scalars.
fn handleExternVariadicArgs(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    arg_ids: []const ast.ExprId,
    vals_list: *List(tir.ValueId),
    fixed_params_count: usize,
) !void {
    // Tracks the lowered state of each variadic argument before emission.
    const VarArgEntry = struct {
        /// SSA value that carries the lowered argument.
        value: tir.ValueId,
        /// Recorded SR type for the argument value.
        ty: types.TypeId,
        /// Optional source location tied to this argument.
        loc: tir.OptLocId,
        /// Original AST identifier, if available.
        expr: ?ast.ExprId,
    };
    var var_entries: List(VarArgEntry) = .empty;
    defer var_entries.deinit(self.gpa);

    const total_len = vals_list.items.len;
    const original_vararg_count = total_len - fixed_params_count;
    var remove_index: usize = 0;
    while (remove_index < original_vararg_count) : (remove_index += 1) {
        const arg_pos = fixed_params_count + remove_index;
        const removed_val = vals_list.items[arg_pos];
        const expr_id: ?ast.ExprId = if (arg_pos < arg_ids.len) arg_ids[arg_pos] else null;
        const loc_entry = if (expr_id) |eid| optLoc(a, eid) else optLoc(a, id);
        const ty_entry = if (expr_id) |eid| self.exprTypeWithEnv(ctx, a, env, eid) else self.exprTypeWithEnv(ctx, a, env, id);
        try var_entries.append(self.gpa, .{
            .value = removed_val,
            .ty = ty_entry,
            .loc = loc_entry,
            .expr = expr_id,
        });
    }
    vals_list.items.len = fixed_params_count;

    var ve_idx: usize = 0;
    while (ve_idx < var_entries.items.len) {
        var entry = &var_entries.items[ve_idx];
        var entry_kind = self.context.type_store.getKind(entry.ty);

        if (entry_kind == .Any and entry.expr != null and self.isSpreadArgExpr(ctx, a, env, entry.expr)) {
            const expr_id = entry.expr.?;
            const range_row = a.exprs.get(.Range, expr_id);
            if (!range_row.end.isNone()) {
                const payload_expr = range_row.end.unwrap();
                const payload_ty = self.exprTypeWithEnv(ctx, a, env, payload_expr);
                if (self.context.type_store.getKind(payload_ty) == .Tuple) {
                    entry.value = try self.lowerExpr(ctx, a, env, f, blk, payload_expr, payload_ty, .rvalue);
                    entry.ty = payload_ty;
                    entry_kind = .Tuple;
                }
            }
        }

        if (entry_kind == .Tuple and self.isSpreadArgExpr(ctx, a, env, entry.expr)) {
            const tuple_value = entry.value;
            const tuple_loc = entry.loc;
            const tuple_expr = entry.expr;
            const tuple_ty = entry.ty;

            const tuple_row = self.context.type_store.get(.Tuple, tuple_ty);
            const elem_types = self.context.type_store.type_pool.slice(tuple_row.elems);
            var shift = ve_idx;
            while (shift + 1 < var_entries.items.len) : (shift += 1) {
                var_entries.items[shift] = var_entries.items[shift + 1];
            }
            var_entries.items.len -= 1;
            var elem_idx: usize = 0;
            while (elem_idx < elem_types.len) : (elem_idx += 1) {
                const elem_ty = elem_types[elem_idx];
                const elem_val = blk.builder.extractField(blk, elem_ty, tuple_value, @intCast(elem_idx), tuple_loc);
                try var_entries.insert(self.gpa, ve_idx + elem_idx, .{
                    .value = elem_val,
                    .ty = elem_ty,
                    .loc = tuple_loc,
                    .expr = tuple_expr,
                });
            }
            continue;
        }
        ve_idx += 1;
    }

    ve_idx = 0;
    while (ve_idx < var_entries.items.len) : (ve_idx += 1) {
        var entry = &var_entries.items[ve_idx];
        const entry_kind = self.context.type_store.getKind(entry.ty);
        const want_promoted: ?types.TypeId = switch (entry_kind) {
            .Bool, .I8, .U8, .I16, .U16 => self.context.type_store.tI32(),
            .F32 => self.context.type_store.tF64(),
            else => null,
        };
        if (want_promoted) |want_ty| {
            entry.value = self.emitCoerce(blk, entry.value, entry.ty, want_ty, entry.loc);
            entry.ty = want_ty;
            continue;
        }

        if (entry_kind == .Any) {
            if (entry.expr) |expr_id| {
                const expr_kind = a.exprs.index.kinds.items[expr_id.toRaw()];
                const want_any = switch (expr_kind) {
                    .Literal => switch (a.exprs.get(.Literal, expr_id).kind) {
                        .int, .char => self.context.type_store.tI64(),
                        .float, .imaginary => self.context.type_store.tF64(),
                        .bool => self.context.type_store.tI32(),
                        .string => self.context.type_store.tString(),
                    },
                    else => self.context.type_store.tUsize(),
                };
                entry.value = try self.lowerExpr(ctx, a, env, f, blk, expr_id, want_any, .rvalue);
                entry.ty = want_any;
            }
        }
    }

    for (var_entries.items) |entry| {
        try vals_list.append(self.gpa, entry.value);
    }
}

/// Return true if `expr` is `a..b` where the end expands to multiple arguments.
fn isSpreadRangeExpr(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    expr: ast.ExprId,
) bool {
    if (a.exprs.index.kinds.items[expr.toRaw()] != .Range) return false;
    if (a.type_info.isRangeSpread(expr)) return true;
    const row = a.exprs.get(.Range, expr);
    if (!row.start.isNone() or row.end.isNone()) return false;
    const end_expr = row.end.unwrap();
    const refined_ty = self.exprTypeWithEnv(ctx, a, env, end_expr);
    const refined_kind = self.context.type_store.getKind(refined_ty);
    if (refined_kind == .Tuple or refined_kind == .Any) return true;
    const stamped_ty = self.getExprType(ctx, a, end_expr);
    const stamped_kind = self.context.type_store.getKind(stamped_ty);
    return stamped_kind == .Any;
}

/// Check whether the optional `expr` should be treated as a spread argument.
fn isSpreadArgExpr(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    expr: ?ast.ExprId,
) bool {
    if (expr) |eid| return self.isSpreadRangeExpr(ctx, a, env, eid);
    return false;
}

/// Compute the tuple type to pack trailing `any` arguments starting at `start_index`.
fn computeTrailingAnyTupleType(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    args: []const ast.ExprId,
    start_index: usize,
) !types.TypeId {
    if (start_index >= args.len) {
        return self.context.type_store.mkTuple(&.{});
    }

    const trailing_len = args.len - start_index;
    if (trailing_len == 1 and !self.isSpreadArgExpr(ctx, a, env, args[start_index])) {
        return self.exprTypeWithEnv(ctx, a, env, args[start_index]);
    }

    var elem_types = std.ArrayList(types.TypeId){};
    defer elem_types.deinit(self.gpa);

    var idx = start_index;
    while (idx < args.len) : (idx += 1) {
        try elem_types.append(self.gpa, self.exprTypeWithEnv(ctx, a, env, args[idx]));
    }

    return self.context.type_store.mkTuple(elem_types.items);
}

/// Lower opaque type expressions by returning undef/expected type placeholders.
fn lowerTypeExprOpaque(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) tir.ValueId {
    const loc = optLoc(a, id);
    if (expected_ty) |want| {
        // For type expressions, materialize exactly the expected type to avoid
        // inserting redundant CastNormal on opaque type handles.
        return self.safeUndef(blk, want, loc);
    }
    const ty0 = self.getExprType(ctx, a, id);
    return self.safeUndef(blk, ty0, loc);
}

/// Lower literal expressions to the corresponding constant SSA values.
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
                else => unreachable,
            };
            std.debug.assert(info.valid);
            const value64: u64 = @intCast(info.value);
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
                else => unreachable,
            };
            std.debug.assert(info.valid);
            const parsed = info.value;
            const re0 = blk.builder.tirValue(.ConstFloat, blk, elem, loc, .{ .value = 0.0 });
            const imv = blk.builder.tirValue(.ConstFloat, blk, elem, loc, .{ .value = parsed });
            const cv = blk.builder.tirValue(.ComplexMake, blk, base_ty, loc, .{ .re = re0, .im = imv });
            break :blk cv;
        },
        .float => blk: {
            const info = switch (lit.data) {
                .float => |float_info| float_info,
                else => unreachable,
            };
            std.debug.assert(info.valid);
            switch (self.context.type_store.getKind(base_ty)) {
                .F32, .F64 => literal_ty = base_ty,
                else => literal_ty = self.context.type_store.tF64(),
            }
            break :blk blk.builder.tirValue(.ConstFloat, blk, literal_ty, loc, .{ .value = info.value });
        },
        .bool => blk.builder.tirValue(.ConstBool, blk, base_ty, loc, .{ .value = switch (lit.data) {
            .bool => |b| b,
            else => unreachable,
        } }),
        .string => blk.builder.tirValue(.ConstString, blk, base_ty, loc, .{ .text = switch (lit.data) {
            .string => |sid| sid,
            else => unreachable,
        } }),
        .char => blk.builder.tirValue(.ConstInt, blk, base_ty, loc, .{ .value = std.math.cast(u64, switch (lit.data) {
            .char => |codepoint| codepoint,
            else => unreachable,
        }).? }),
    };
    const want_ty = expected_ty orelse ty0;
    if (!want_ty.eq(literal_ty)) return self.emitCoerce(blk, v, literal_ty, want_ty, loc);
    return v;
}

/// Lower unary operations, handling address-of, numeric negation, and logical not.
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
    if ((row.op == .pos or row.op == .neg) and (!is_num or self.isType(ty0, .Any) or self.isVoid(ty0))) {
        const et = self.getExprType(ctx, a, row.expr);
        if (self.isNumeric(et)) {
            ty0 = et;
        }
        if (self.isType(ty0, .Any) or self.isVoid(ty0)) ty0 = self.context.type_store.tI64();
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
                if (self.isFloat(ty0))
                    break :zblk blk.builder.tirValue(.ConstFloat, blk, ty0, loc, .{ .value = 0.0 });
                if (self.isType(ty0, .Simd)) {
                    const simd_info = self.context.type_store.get(.Simd, ty0);
                    const elem_ty = simd_info.elem;
                    const elem_kind = self.context.type_store.index.kinds.items[elem_ty.toRaw()];
                    const zero_scalar = if (elem_kind == .F32 or elem_kind == .F64)
                        blk.builder.tirValue(.ConstFloat, blk, elem_ty, loc, .{ .value = 0.0 })
                    else
                        blk.builder.tirValue(.ConstInt, blk, elem_ty, loc, .{ .value = 0 });
                    break :zblk blk.builder.tirValue(.Broadcast, blk, ty0, loc, .{ .value = zero_scalar });
                }
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

/// Lower `range` expressions by materializing the tenable `RangeMake` value.
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
    if (self.isSpreadRangeExpr(ctx, a, env, id)) {
        const inner = row.end.unwrap();
        return self.lowerExpr(ctx, a, env, f, blk, inner, expected_ty, .rvalue);
    }
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

/// Lower dereference expressions, emitting a load or reusing pointer addresses when requested.
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

/// Lower array literals (including simd/slice/dynarray/tensor cases) into concrete TIR constructs.
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

            const ids = a.exprs.expr_pool.slice(row.elems);
            std.debug.assert(array_ty.len == ids.len);

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
        .Slice => {
            const slice_ty = self.context.type_store.get(.Slice, ty0);
            const elem_ty = slice_ty.elem;
            const ptr_ty = self.context.type_store.mkPtr(elem_ty, false);
            const usize_ty = self.context.type_store.tUsize();
            const ids = a.exprs.expr_pool.slice(row.elems);

            if (ids.len == 0) {
                const null_ptr = blk.builder.constNull(blk, ptr_ty, loc);
                const zero = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = 0 });
                const slice_val = blk.builder.structMake(blk, ty0, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = null_ptr },
                    .{ .index = 1, .name = .none(), .value = zero },
                }, loc);
                if (expected_ty) |want| return self.emitCoerce(blk, slice_val, ty0, want, loc);
                return slice_val;
            }

            const elem_size = check_types.typeSize(self.context, elem_ty);

            var elems = try self.gpa.alloc(tir.ValueId, ids.len);
            defer self.gpa.free(elems);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) {
                elems[i] = try self.lowerExpr(ctx, a, env, f, blk, ids[i], elem_ty, .rvalue);
            }

            const total_bytes: u64 = @intCast(elem_size * ids.len);
            const bytes_const = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = total_bytes });
            const raw_ptr = self.callRuntimeAllocPtr(blk, bytes_const, loc);
            const data_ptr = blk.builder.tirValue(.CastBit, blk, ptr_ty, loc, .{ .value = raw_ptr });

            var idx: usize = 0;
            while (idx < elems.len) : (idx += 1) {
                const idx_u64 = std.math.cast(u64, idx) orelse unreachable;
                const offset = blk.builder.gepConst(idx_u64);
                const elem_ptr = blk.builder.gep(blk, ptr_ty, data_ptr, &.{offset}, loc);
                _ = blk.builder.tirValue(.Store, blk, elem_ty, loc, .{ .ptr = elem_ptr, .value = elems[idx], .@"align" = 0 });
            }

            const len_u64 = std.math.cast(u64, ids.len) orelse unreachable;
            const len_const = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = len_u64 });
            const slice_val = blk.builder.structMake(blk, ty0, &[_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = data_ptr },
                .{ .index = 1, .name = .none(), .value = len_const },
            }, loc);
            if (expected_ty) |want| return self.emitCoerce(blk, slice_val, ty0, want, loc);
            return slice_val;
        },
        .DynArray => {
            const dyn_ty = self.context.type_store.get(.DynArray, ty0);
            const elem_ty = dyn_ty.elem;
            const ptr_elem_ty = self.context.type_store.mkPtr(elem_ty, false);
            const usize_ty = self.context.type_store.tUsize();
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

            const elem_size = check_types.typeSize(self.context, elem_ty);

            var elems = try self.gpa.alloc(tir.ValueId, ids.len);
            defer self.gpa.free(elems);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) {
                elems[i] = try self.lowerExpr(ctx, a, env, f, blk, ids[i], elem_ty, .rvalue);
            }

            const total_bytes: u64 = @intCast(elem_size * ids.len);
            const bytes_const = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = total_bytes });
            const raw_ptr = self.callRuntimeAllocPtr(blk, bytes_const, loc);
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

/// Lower tensor-style array literals by flattening nested arrays into element sequences.
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

/// Recursively collect element values for multi-dimensional tensor literals.
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

/// Lower tuple literals by constructing a struct-like aggregate with ordered fields.
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

/// Lower struct literals by computing each field init and applying defaults when needed.
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
    var field_inits = List(tir.Rows.StructFieldInit){};
    defer field_inits.deinit(self.gpa);

    const ty0_kind = self.context.type_store.getKind(ty0);
    var type_fields: []const types.FieldId = &.{};
    if (ty0_kind == .Struct) {
        type_fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, ty0).fields);
    } else if (ty0_kind == .Union) {
        type_fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Union, ty0).fields);
    }

    var provided_mask: ?[]bool = null;
    if (ty0_kind == .Struct and !row.ty.isNone()) {
        const count = type_fields.len;
        const mask = try self.gpa.alloc(bool, count);
        @memset(mask, false);
        provided_mask = mask;
    }
    defer if (provided_mask) |mask| self.gpa.free(mask);

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
        if (provided_mask) |mask| {
            if (field_idx) |idx| mask[idx] = true;
        }
        try field_inits.append(self.gpa, .{ .index = @intCast(final_idx), .name = sfv.name, .value = v_val });
    }

    if (provided_mask) |mask| {
        const type_expr = row.ty.unwrap();
        var j: usize = 0;
        while (j < mask.len) : (j += 1) {
            if (mask[j]) continue;
            const fid = type_fields[j];
            const field_def = self.context.type_store.Field.get(fid);
            if (self.structFieldDefaultExpr(a, type_expr, field_def.name)) |default_expr| {
                const default_val = try self.lowerExpr(ctx, a, env, f, blk, default_expr, field_def.ty, .rvalue);
                try field_inits.append(self.gpa, .{
                    .index = @intCast(j),
                    .name = ast.OptStrId.some(field_def.name),
                    .value = default_val,
                });
            }
        }
    }

    const field_slice = try field_inits.toOwnedSlice(self.gpa);
    defer self.gpa.free(field_slice);

    const v = if (ty0_kind == .Union) blk: {
        std.debug.assert(field_slice.len == 1);
        const field = field_slice[0];
        break :blk blk.builder.tirValue(.UnionMake, blk, ty0, loc, .{
            .field_index = field.index,
            .value = field.value,
        });
    } else blk.builder.structMake(blk, ty0, field_slice, loc);

    if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
    return v;
}

/// Lower map literals by emitting a runtime call that constructs the map from key/value pairs.
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

/// Lower index access expressions to the appropriate GEP/load or optional indexing form.
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
            if (rk == .Slice or rk == .String) {
                const want = self.context.type_store.mkSlice(self.context.type_store.tUsize(), false);
                break :blk try self.lowerExpr(ctx, a, env, f, blk, row.index, want, .rvalue);
            } else {
                // Prefer a usize constant for literal indices to avoid casts in TIR
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
            }
        };
        const v = blk.builder.indexOp(blk, ty0, base, idx, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
        return v;
    }
}

/// Lower an enum member reference to its integer discriminant constant.
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
    var enum_ty: types.TypeId = undefined;
    switch (parent_kind) {
        .Enum => enum_ty = parent_ty,
        .TypeType => {
            const tr = self.context.type_store.get(.TypeType, parent_ty);
            const of_kind = self.context.type_store.getKind(tr.of);
            if (of_kind != .Enum) return null;
            enum_ty = tr.of;
        },
        else => return null,
    }
    const ty0 = self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const row = a.exprs.get(.FieldAccess, id);
    const value = self.enumMemberValue(enum_ty, row.field) orelse return null;
    var ev = blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = value });
    if (expected_ty) |want| ev = self.emitCoerce(blk, ev, ty0, want, loc);
    return ev;
}

/// Lower a literal variant tag (`T::Case`) when its payload is void.
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

/// Lookup the position of `field_name` inside `parent_ty`, recursing through pointers.
fn getFieldIndex(
    self: *LowerTir,
    parent_ty: types.TypeId,
    field_name: ast.StrId,
) ?u32 {
    const ty_kind = self.context.type_store.getKind(parent_ty);
    switch (ty_kind) {
        inline .Struct, .Union => |x| {
            const tr = self.context.type_store.get(x, parent_ty);
            const fields = self.context.type_store.field_pool.slice(tr.fields);
            var i: usize = 0;
            while (i < fields.len) : (i += 1) {
                const f = self.context.type_store.Field.get(fields[i]);
                if (f.name.eq(field_name)) return @intCast(i);
            }
        },
        .Ptr => {
            const tr = self.context.type_store.get(.Ptr, parent_ty);
            const elem_ty = tr.elem;
            return self.getFieldIndex(elem_ty, field_name) orelse return null;
        },
        else => {},
    }
    return null;
}

/// Lower field access expressions, covering len/ptr/capacity, module members, variants, and structs.
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
        if (parent_kind == .Array) {
            const arr = self.context.type_store.get(.Array, parent_ty);
            const ty0 = self.context.type_store.tUsize();
            const v = blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = @as(u64, @intCast(arr.len)) });
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
            return v;
        }
        switch (parent_kind) {
            .Slice, .DynArray, .String => {
                const base = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, .rvalue);
                const ty0 = self.context.type_store.tUsize();
                const v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
                return v;
            },
            else => {},
        }
    } else if (std.mem.eql(u8, field_name, "ptr")) {
        const ptr_ty: ?types.TypeId = switch (parent_kind) {
            .Slice => self.context.type_store.mkPtr(self.context.type_store.get(.Slice, parent_ty).elem, false),
            .DynArray => self.context.type_store.mkPtr(self.context.type_store.get(.DynArray, parent_ty).elem, false),
            .String => self.context.type_store.mkPtr(self.context.type_store.tU8(), true),
            else => null,
        };
        if (ptr_ty) |ty0| {
            const base = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, .rvalue);
            const v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
            if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
            return v;
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

    // 1) imported module member (rvalue only): resolve `mod.name` to the imported
    //    unit’s export and materialize it directly instead of treating the module as
    //    a runtime struct value.
    if (mode == .rvalue) {
        const pk = a.exprs.index.kinds.items[row.parent.toRaw()];
        if (pk == .Ident or pk == .Import) {
            if (try self.tryLowerImportedModuleMember(ctx, a, env, f, blk, row.parent, row.field, expected_ty, loc)) |v| {
                return v;
            }
        }
    }

    const idx_maybe = a.type_info.getFieldIndex(id) orelse
        self.getFieldIndex(parent_ty, row.field);

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
        const idx = idx_maybe orelse return self.throwErr(a.exprs.locs.get(row.loc));
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
        std.debug.assert(!is_tuple);
        v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
    }

    if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
    return v;
}

// Try to lower `parent.field` where parent is an imported module to the exported
// declaration from the imported AST. Only used for rvalues.
fn tryLowerImportedModuleMember(
    self: *LowerTir,
    ctx: *LowerContext,
    caller_ast: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    parent_expr: ast.ExprId,
    field_name: ast.StrId,
    expected_ty: ?types.TypeId,
    loc: ast.OptLocId,
) !?tir.ValueId {
    _ = ctx; // unused for now
    _ = env;
    _ = f;

    const parent_kind = caller_ast.exprs.index.kinds.items[parent_expr.toRaw()];

    var target_ast: ?*ast.Ast = null;
    if (parent_kind == .Import) {
        const ir = caller_ast.exprs.get(.Import, parent_expr);
        const path = caller_ast.exprs.strs.get(ir.path);
        var it = self.context.compilation_unit.packages.iterator();
        while (it.next()) |pkg| {
            if (pkg.value_ptr.sources.get(path)) |unit_ref| {
                target_ast = unit_ref.ast;
                break;
            }
        }
    } else if (parent_kind == .Ident) {
        const parent_ident = caller_ast.exprs.get(.Ident, parent_expr);
        if (call_resolution.findTopLevelImportByName(caller_ast, parent_ident.name)) |import_decl_id| {
            const import_decl = caller_ast.exprs.Decl.get(import_decl_id);
            const ir = caller_ast.exprs.get(.Import, import_decl.value);
            const path = caller_ast.exprs.strs.get(ir.path);
            var it2 = self.context.compilation_unit.packages.iterator();
            while (it2.next()) |pkg| {
                if (pkg.value_ptr.sources.get(path)) |unit_ref| {
                    target_ast = unit_ref.ast;
                    break;
                }
            }
        }
    } else {
        return null;
    }

    const ta = target_ast orelse return null;
    // Ask the imported AST for an exported decl with this field name
    if (ta.type_info.getExport(field_name)) |ex| {
        // If the export is a function, let normal call resolution handle it.
        const ex_ty = ex.ty;
        if (self.context.type_store.getKind(ex_ty) == .Function) return null;

        // Materialize as a global load: &name then load, then coerce if needed.
        // Use the fully qualified symbol name so it matches the emitted global.
        const name = try self.qualifySymbolName(ta, field_name);
        const ptr_ty = self.context.type_store.mkPtr(ex_ty, false);
        const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = name });
        var val = blk.builder.tirValue(.Load, blk, ex_ty, loc, .{ .ptr = addr, .@"align" = 0 });
        if (expected_ty) |want| val = self.emitCoerce(blk, val, ex_ty, want, loc);
        return val;
    }
    return null;
}

/// Lower identifier expressions, resolving globals/locals/types/slots and emitting loads or errors.
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
    const did_opt = call_resolution.findTopLevelDeclByName(a, name);

    if (ctx.lookupBindingType(name)) |bound_ty| {
        expr_ty = self.context.type_store.mkTypeType(bound_ty);
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

        // 2) If it's a top-level decl that names a value, bind its address as a slot and return.
        //    Do NOT take an address of a type declaration (TypeType) — types are not lvalues.
        if (did_opt) |did| {
            const d = a.exprs.Decl.get(did);
            const gty = getDeclType(a, did) orelse unreachable;
            if (self.context.type_store.getKind(gty) != .TypeType) {
                const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
                const sym = (try self.symbolNameForDecl(a, did)) orelse name;
                const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = sym });
                try env.bind(self.gpa, a, name, .{ .value = addr, .ty = gty, .is_slot = true });
                return addr;
            }
            // Fall through for TypeType: no addressable storage for types.
        }

        // 3) Otherwise it must be a local value binding that needs a slot.
        if (env.lookup(name)) |bnd| {
            const slot_ty = self.context.type_store.mkPtr(want_elem, false);
            const slot = f.builder.tirValue(.Alloca, blk, slot_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });

            const src_ty = if (!self.isType(expr_ty, .Any)) expr_ty else bnd.ty;
            const to_store = self.emitCoerce(blk, bnd.value, src_ty, want_elem, loc);
            _ = f.builder.tirValue(.Store, blk, want_elem, loc, .{ .ptr = slot, .value = to_store, .@"align" = 0 });

            try env.bind(self.gpa, a, name, .{ .value = slot, .ty = want_elem, .is_slot = true });
            return slot;
        }

        // 4) Nowhere to get it from.
        const l = optLoc(a, id);
        try self.context.diags.addError(a.exprs.locs.get(l.unwrap()), .undefined_identifier, .{});
        return error.LoweringBug;
    }

    // ---- rvalue path -----------------------------------------------------

    // Acquire or synthesize a binding once, then decide how to produce a value.
    const bnd = env.lookup(name) orelse blk: {
        if (did_opt) |did| {
            const d = a.exprs.Decl.get(did);
            const gty = getDeclType(a, did) orelse unreachable;
            if (self.context.type_store.getKind(gty) != .TypeType) {
                const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
                const sym = (try self.symbolNameForDecl(a, did)) orelse name;
                const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = sym });
                // For function declarations, the global address is already the rvalue we want;
                // do not treat it as an addressable slot to avoid emitting a spurious load.
                const is_fn = self.context.type_store.getKind(gty) == .Function;
                try env.bind(self.gpa, a, name, .{ .value = addr, .ty = gty, .is_slot = !is_fn });
                break :blk env.lookup(name).?;
            }
            // For type declarations, synthesize a non-addressable placeholder value.
        }

        // Not a value binding or a value-like top-level decl (likely a type name etc.).
        // Bind a safe placeholder so downstream code can keep going.
        const ty0 = expr_ty;
        const placeholder = self.safeUndef(blk, ty0, loc);
        try env.bind(self.gpa, a, name, .{ .value = placeholder, .ty = ty0, .is_slot = false });
        break :blk env.lookup(name).?;
    };

    if (bnd.is_slot) {
        const load_ty = if (!self.isType(expr_ty, .Any)) expr_ty else bnd.ty;
        // else if (expected_ty) |want|
        //     want
        // else
        //     bnd.ty;
        var loaded = blk.builder.tirValue(.Load, blk, load_ty, loc, .{ .ptr = bnd.value, .@"align" = 0 });
        if (expected_ty) |want| loaded = self.emitCoerce(blk, loaded, load_ty, want, loc);
        return loaded;
    }

    // Non-slot: coerce if a target type was requested.
    const got_ty = if (!self.isType(expr_ty, .Any)) expr_ty else bnd.ty;
    // else if (expected_ty) |want|
    //     want
    // else
    //     bnd.ty;
    return if (expected_ty) |want| self.emitCoerce(blk, bnd.value, got_ty, want, loc) else bnd.value;
}

/// Lower binary expressions, including comparisons, arithmetic, and short-circuit helpers.
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
        else => unreachable,
        .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor => {
            // Decide the operation type first: prefer the stamped/checker type when meaningful,
            // otherwise fall back to a common numeric type (or expected type / i64).
            const chosen: types.TypeId = blk: {
                if (op_ty) |t| {
                    if (!self.isVoid(t) and !self.isType(t, .Any)) break :blk t;
                }
                break :blk (self.commonNumeric(lhs_hint, rhs_hint) orelse (expected_ty orelse self.context.type_store.tI64()));
            };

            // If Complex, both operands must be Complex of the same element type.
            if (self.context.type_store.index.kinds.items[chosen.toRaw()] == .Complex) {
                lhs_expect = chosen;
                rhs_expect = chosen;
            } else {
                // Otherwise coerce both operands to the chosen numeric type.
                lhs_expect = chosen;
                rhs_expect = chosen;

                // SIMD scalar promotion hints: if one side is SIMD, let the other be scalar element.
                const r_ty_promo = rhs_hint orelse rhs_stamped;
                const rk = self.context.type_store.getKind(r_ty_promo);
                const r_is_scalar_numeric = switch (rk) {
                    .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64, .Usize, .F32, .F64 => true,
                    else => false,
                };
                if (self.context.type_store.getKind(chosen) == .Simd and r_is_scalar_numeric) {
                    rhs_expect = null;
                }

                const l_ty_promo = lhs_hint orelse lhs_stamped;
                const lk = self.context.type_store.getKind(l_ty_promo);
                const l_is_scalar_numeric = switch (lk) {
                    .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64, .Usize, .F32, .F64 => true,
                    else => false,
                };
                if (self.context.type_store.getKind(chosen) == .Simd and l_is_scalar_numeric) {
                    lhs_expect = null;
                }
            }
            // Ensure the operation result type matches the chosen type.
            op_ty = chosen;
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
            // Short-circuited optional handling; lowered separately.
            return self.lowerOrelse(ctx, a, env, f, blk, id, expected_ty);
        },
    }

    var l = try self.lowerExpr(ctx, a, env, f, blk, row.left, lhs_expect, .rvalue);
    var r = try self.lowerExpr(ctx, a, env, f, blk, row.right, rhs_expect, .rvalue);

    if (lhs_expect) |l_want| {
        const l_got = self.getExprType(ctx, a, row.left);
        if (l_got.toRaw() != l_want.toRaw()) {
            l = self.emitCoerce(blk, l, l_got, l_want, optLoc(a, row.left));
        }
    }
    if (rhs_expect) |r_want| {
        const r_got = self.getExprType(ctx, a, row.right);
        if (r_got.toRaw() != r_want.toRaw()) {
            r = self.emitCoerce(blk, r, r_got, r_want, optLoc(a, row.right));
        }
    }

    // --- Handle SIMD-scalar promotion ---
    const l_ty_promo = self.getExprType(ctx, a, row.left);
    const r_ty_promo = self.getExprType(ctx, a, row.right);
    const lk_promo = self.context.type_store.getKind(l_ty_promo);
    const rk_promo = self.context.type_store.getKind(r_ty_promo);

    const r_is_scalar_numeric = switch (rk_promo) {
        .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64, .Usize, .F32, .F64 => true,
        else => false,
    };
    const l_is_scalar_numeric = switch (lk_promo) {
        .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64, .Usize, .F32, .F64 => true,
        else => false,
    };

    if (lk_promo == .Simd and r_is_scalar_numeric) {
        const simd_info = self.context.type_store.get(.Simd, l_ty_promo);
        const coerced_r = self.emitCoerce(blk, r, r_ty_promo, simd_info.elem, loc);
        r = blk.builder.tirValue(.Broadcast, blk, l_ty_promo, loc, .{ .value = coerced_r });
    } else if (rk_promo == .Simd and l_is_scalar_numeric) {
        const simd_info = self.context.type_store.get(.Simd, r_ty_promo);
        const coerced_l = self.emitCoerce(blk, l, l_ty_promo, simd_info.elem, loc);
        l = blk.builder.tirValue(.Broadcast, blk, r_ty_promo, loc, .{ .value = coerced_l });
    }

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
                const optional_ty = if (l_ty.eq(null_ty)) r_ty else l_ty;
                const flag = self.optionalFlag(blk, optional_ty, optional_val, loc); // Extract is_some flag

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

            const flag = self.optionalFlag(blk, opt_ty, opt_val, loc);
            const payload = self.optionalPayload(blk, opt_ty, opt_val, loc);

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
        else => unreachable,
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
            const flag = self.optionalFlag(blk, lhs_ty, l, loc);
            const payload = self.optionalPayload(blk, lhs_ty, l, loc);

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
                const rhs_kind = self.context.type_store.index.kinds.items[rhs_ty.toRaw()];
                if (rhs_kind == .Void) {
                    try f.builder.setReturnVoid(&else_blk, loc);
                } else if (rhs_kind == .Noreturn) {
                    // RHS already terminated the block (e.g., return/panic); nothing to branch.
                } else {
                    rhs_v = self.emitCoerce(&else_blk, rhs_v, rhs_ty, res_ty, loc);
                    try f.builder.br(&else_blk, join_blk.id, &.{rhs_v}, loc);
                }
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

/// Lower the `catch` expression by wiring error/result handlers and running defers.
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
        const some_flag = self.optionalFlag(blk, lhs_ty0, lhs_val, expr_loc);
        const es_payload = self.optionalPayload(blk, lhs_ty0, lhs_val, expr_loc);

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

/// Lower the `orelse` expression by evaluating the left side and branching on errors.
fn lowerOrelse(
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

    const lhs_ty = self.getExprType(ctx, a, row.left);
    if (self.context.type_store.index.kinds.items[lhs_ty.toRaw()] != .Optional) return error.LoweringBug;

    // Only compute the LHS eagerly; RHS is lowered lazily in the else branch to preserve short-circuiting.
    const lhs_val = try self.lowerExpr(ctx, a, env, f, blk, row.left, lhs_ty, .rvalue);
    const opt_info = self.context.type_store.get(.Optional, lhs_ty);
    const flag = self.optionalFlag(blk, lhs_ty, lhs_val, loc);
    const payload = self.optionalPayload(blk, lhs_ty, lhs_val, loc);

    var then_blk = try f.builder.beginBlock(f);
    var else_blk = try f.builder.beginBlock(f);
    var join_blk = try f.builder.beginBlock(f);

    const elem_kind = self.context.type_store.getKind(opt_info.elem);

    if (elem_kind != .ErrorSet) {
        const res_ty = expected_ty orelse opt_info.elem;
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);
        const then_param = try f.builder.addBlockParam(&then_blk, null, opt_info.elem);

        try f.builder.condBr(blk, flag, then_blk.id, &.{payload}, else_blk.id, &.{}, loc);
        const orig_blk = blk.*;
        try f.builder.endBlock(f, orig_blk);

        var unwrapped = then_param;
        if (expected_ty) |want| unwrapped = self.emitCoerce(&then_blk, unwrapped, opt_info.elem, want, loc);
        try f.builder.br(&then_blk, join_blk.id, &.{unwrapped}, loc);
        try f.builder.endBlock(f, then_blk);

        if (else_blk.term.isNone()) {
            const rhs_val = try self.lowerExpr(ctx, a, env, f, &else_blk, row.right, res_ty, .rvalue);
            const rhs_ty = self.getExprType(ctx, a, row.right);
            const rhs_kind = self.context.type_store.index.kinds.items[rhs_ty.toRaw()];
            if (else_blk.term.isNone()) {
                if (rhs_kind == .Void) {
                    try f.builder.setReturnVoid(&else_blk, loc);
                } else if (rhs_kind != .Noreturn) {
                    const coerced = self.emitCoerce(&else_blk, rhs_val, rhs_ty, res_ty, loc);
                    try f.builder.br(&else_blk, join_blk.id, &.{coerced}, loc);
                }
            }
            try f.builder.endBlock(f, else_blk);
        }

        blk.* = join_blk;
        try self.noteExprType(ctx, id, res_ty);
        return res_param;
    } else {
        // Optional(ErrorSet(V,E)) orelse R -> ErrorSet(V,E)
        const es = self.context.type_store.get(.ErrorSet, opt_info.elem);
        const res_es_ty = self.context.type_store.mkErrorSet(es.value_ty, es.error_ty);
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_es_ty);
        const then_param = try f.builder.addBlockParam(&then_blk, null, res_es_ty);

        try f.builder.condBr(blk, flag, then_blk.id, &.{payload}, else_blk.id, &.{}, loc);
        const orig_blk = blk.*;
        try f.builder.endBlock(f, orig_blk);

        try f.builder.br(&then_blk, join_blk.id, &.{then_param}, loc);
        try f.builder.endBlock(f, then_blk);

        if (else_blk.term.isNone()) {
            var rhs_val = try self.lowerExpr(ctx, a, env, f, &else_blk, row.right, es.value_ty, .rvalue);
            const rhs_ty = self.getExprType(ctx, a, row.right);
            if (rhs_ty.toRaw() != es.value_ty.toRaw()) {
                rhs_val = self.emitCoerce(&else_blk, rhs_val, rhs_ty, es.value_ty, loc);
            }

            const ok_name = f.builder.intern("Ok");
            const err_name = f.builder.intern("Err");
            const union_ty = self.context.type_store.mkUnion(&.{ .{ .name = ok_name, .ty = es.value_ty }, .{ .name = err_name, .ty = es.error_ty } });
            const union_val = else_blk.builder.tirValue(.UnionMake, &else_blk, union_ty, loc, .{ .field_index = 0, .value = rhs_val });
            const tag0 = else_blk.builder.tirValue(.ConstInt, &else_blk, self.context.type_store.tI32(), loc, .{ .value = 0 });
            const fields = [_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = tag0 },
                .{ .index = 1, .name = .none(), .value = union_val },
            };
            const es_val = else_blk.builder.structMake(&else_blk, res_es_ty, &fields, loc);
            try f.builder.br(&else_blk, join_blk.id, &.{es_val}, loc);
            try f.builder.endBlock(f, else_blk);
        }

        blk.* = join_blk;
        try self.noteExprType(ctx, id, res_es_ty);
        return res_param;
    }
}

/// Lower cast expressions by delegating to TypeKind-specific builders (normal/bitcast/etc.).
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

/// Lower expression `id` into TIR, targeting `expected_ty`/`mode` and respecting the current env.
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
    // Ensure we have a stamped type for this expression; if missing, invoke checker lazily.
    if (a.type_info.expr_types.items[id.toRaw()] == null) {
        const cctx = self.chk.checker_ctx.items[a.file_id];
        _ = try self.chk.checkExpr(cctx, a, id);
    }
    _ = try self.refineExprType(ctx, a, env, id, self.getExprType(ctx, a, id));
    try self.ensureExprTypeNotError(ctx, a, id);

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
            if (expected_ty) |want_raw| {
                const v = blk.builder.constNull(blk, want_raw, loc);
                return v;
            } else {
                const any_ty = self.context.type_store.tAny();
                return blk.builder.tirValue(.ConstUndef, blk, any_ty, loc, .{});
            }
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
        .Return => blk: {
            const row = a.exprs.get(.Return, id);
            const loc = optLoc(a, id);
            const ty0 = self.getExprType(ctx, a, id);
            const poison = self.safeUndef(blk, ty0, loc);
            try self.lowerReturnCommon(ctx, a, env, f, blk, row.value, loc);
            break :blk poison;
        },
        .Break => blk: {
            const row = a.exprs.get(.Break, id);
            const loc = optLoc(a, id);
            const ty0 = expected_ty orelse self.getExprType(ctx, a, id);
            const poison = self.safeUndef(blk, ty0, loc);
            try cf.lowerBreakCommon(self, ctx, a, env, f, blk, row.label, row.value, loc);
            break :blk poison;
        },
        .Continue => blk: {
            const row = a.exprs.get(.Continue, id);
            const loc = optLoc(a, id);
            const ty0 = expected_ty orelse self.getExprType(ctx, a, id);
            const poison = self.safeUndef(blk, ty0, loc);
            try cf.lowerContinueCommon(self, ctx, a, env, f, blk, row.label, loc);
            break :blk poison;
        },
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
        .VariantType, .EnumType, .StructType, .SimdType => self.lowerTypeExprOpaque(ctx, a, blk, id, expected_ty),
        .CodeBlock => blk: {
            // For now, treat as opaque and produce undef
            const ty0 = self.getExprType(ctx, a, id);
            const loc = optLoc(a, id);
            break :blk self.safeUndef(blk, ty0, loc);
        },
        .ComptimeBlock => {
            const cb = a.exprs.get(.ComptimeBlock, id);
            const result_ty = self.getExprType(ctx, a, cb.block);
            var cval = try self.getCachedComptimeValue(a, cb.block);
            if (cval) |*comptime_val| {
                defer comptime_val.destroy(self.gpa);
                return try comp.constValueFromComptime(self, blk, result_ty, comptime_val.*);
            }
            return error.LoweringBug;
        },
        else => {
            std.debug.print("lowerExpr: unhandled expr kind {}\n", .{expr_kind});
            return error.LoweringBug;
        },
    };
}

/// Evaluate the block expression `block_expr` and return its resulting TIR value.
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
/// Compute the symbol name representing `did` if it introduces a runtime value.
fn symbolNameForDecl(self: *LowerTir, decl_ast: *ast.Ast, did: ast.DeclId) !?StrId {
    const decl = decl_ast.exprs.Decl.get(did);
    const is_extern_fn = switch (decl_ast.exprs.index.kinds.items[decl.value.toRaw()]) {
        .FunctionLit => decl_ast.exprs.get(.FunctionLit, decl.value).flags.is_extern,
        else => false,
    };
    if (!decl.pattern.isNone()) {
        const pat = decl.pattern.unwrap();
        if (bindingNameOfPattern(decl_ast, pat)) |name| {
            return if (is_extern_fn) name else try self.qualifySymbolName(decl_ast, name);
        }
        return null;
    }
    if (!decl.method_path.isNone()) {
        const base = try methodSymbolShortName(self, decl_ast, did);
        return if (is_extern_fn) base else try self.qualifySymbolName(decl_ast, base);
    }
    return null;
}

/// Return the declared default expression for `field_name` in `type_expr`, if present.
fn structFieldDefaultExpr(self: *LowerTir, a: *ast.Ast, type_expr: ast.ExprId, field_name: ast.StrId) ?ast.ExprId {
    const struct_expr = self.structTypeExprFromTypeRef(a, type_expr) orelse return null;
    return structFieldDefaultInStructExpr(a, struct_expr, field_name);
}

/// Resolve a struct literal expression pointer from a type reference, if it names a struct.
fn structTypeExprFromTypeRef(_: *LowerTir, a: *ast.Ast, type_expr: ast.ExprId) ?ast.ExprId {
    const kind = a.exprs.index.kinds.items[type_expr.toRaw()];
    return switch (kind) {
        .StructType => type_expr,
        .Ident => blk: {
            const ident = a.exprs.get(.Ident, type_expr);
            if (call_resolution.findTopLevelDeclByName(a, ident.name)) |decl_id| {
                const decl = a.exprs.Decl.get(decl_id);
                if (a.exprs.index.kinds.items[decl.value.toRaw()] == .StructType) {
                    break :blk decl.value;
                }
            }
            break :blk null;
        },
        else => null,
    };
}

/// Look for a default initializer for `field_name` inside `struct_expr`.
fn structFieldDefaultInStructExpr(a: *ast.Ast, struct_expr: ast.ExprId, field_name: ast.StrId) ?ast.ExprId {
    const row = a.exprs.get(.StructType, struct_expr);
    const sfields = a.exprs.sfield_pool.slice(row.fields);
    for (sfields) |fid| {
        const sf = a.exprs.StructField.get(fid);
        if (sf.name.eq(field_name) and !sf.value.isNone()) {
            return sf.value.unwrap();
        }
    }
    return null;
}

/// True if `ty` is a numeric scalar type.
fn isNumeric(self: *const LowerTir, ty: types.TypeId) bool {
    if (self.isVoid(ty)) return false;
    const k = self.context.type_store.index.kinds.items[ty.toRaw()];
    return switch (k) {
        .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64, .Usize, .F32, .F64, .Simd, .Tensor => true,
        else => false,
    };
}

/// Return true when `ty` is either `f32` or `f64`.
fn isFloat(self: *const LowerTir, ty: types.TypeId) bool {
    return self.isType(ty, .F32) or self.isType(ty, .F64);
}

/// Test whether `ty` currently maps to `kind` in the type store index.
pub fn isType(self: *const LowerTir, ty: types.TypeId, kind: types.TypeKind) bool {
    return self.context.type_store.index.kinds.items[ty.toRaw()] == kind;
}

/// Choose a common numeric type for binary ops when the checker didn't provide one.
fn commonNumeric(
    self: *const LowerTir,
    l: ?types.TypeId,
    r: ?types.TypeId,
) ?types.TypeId {
    const ts = self.context.type_store;
    if (l) |lt| if (self.isNumeric(lt)) {
        if (r) |rt| {
            if (self.isNumeric(rt)) {
                // naive widening preference: floats > signed > unsigned; 64 > 32 > 16 > 8
                const kL = ts.index.kinds.items[lt.toRaw()];
                const kR = ts.index.kinds.items[rt.toRaw()];
                if (kL == .Simd) return lt;
                if (kR == .Simd) return rt;
                if (kL == .Tensor) return lt;
                if (kR == .Tensor) return rt;

                // if either side is float, pick the wider float
                if ((kL == .F64) or (kR == .F64)) return ts.tF64();
                if ((kL == .F32) or (kR == .F32)) return ts.tF32();
                // prefer signed width of the wider side
                const signedPref = [_]types.TypeId{ ts.tI64(), ts.tI32(), ts.tI16(), ts.tI8() };
                for (signedPref) |cand| {
                    if (lt.eq(cand) or rt.eq(cand)) return cand;
                }
                // otherwise fall back to the wider unsigned
                if (lt.eq(ts.tU64()) or rt.eq(ts.tU64())) return ts.tU64();
                if (lt.eq(ts.tU32()) or rt.eq(ts.tU32())) return ts.tU32();
                if (lt.eq(ts.tU16()) or rt.eq(ts.tU16())) return ts.tU16();
                if (lt.eq(ts.tU8()) or rt.eq(ts.tU8())) return ts.tU8();
                return lt;
            }
            return lt; // one numeric, one non-numeric → pick numeric side
        }
        return lt;
    } else if (r) |rt| if (self.isNumeric(rt)) return rt;
    return null;
}

/// Optionally adjust the type recorded for `expr` by considering surrounding bindings.
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

            if (ctx.lookupBindingType(name)) |ty| {
                const type_ty = self.context.type_store.mkTypeType(ty);
                try self.noteExprType(ctx, expr, type_ty);
                return type_ty;
            }
        },
        .Range => {
            if (self.isSpreadRangeExpr(ctx, a, env, expr)) {
                const row = a.exprs.get(.Range, expr);
                if (!row.end.isNone()) {
                    const inner = row.end.unwrap();
                    const inner_stamped = self.getExprType(ctx, a, inner);
                    if (try self.refineExprType(ctx, a, env, inner, inner_stamped)) |inner_refined| {
                        try self.noteExprType(ctx, expr, inner_refined);
                        return inner_refined;
                    }
                    try self.noteExprType(ctx, expr, inner_stamped);
                    return inner_stamped;
                }
            }
        },
        else => {},
    }

    return stamped;
}

/// Compute the effective type for `expr` by combining stamped type and any local refinements.
fn exprTypeWithEnv(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    expr: ast.ExprId,
) types.TypeId {
    const stamped = self.getExprType(ctx, a, expr);
    const refined = self.refineExprType(ctx, a, env, expr, stamped) catch return stamped;
    return refined orelse stamped;
}

// ============================
// Misc helpers
// ============================

/// Return the recorded type for expression `id`, honoring any override entries in `ctx`.
pub fn getExprType(self: *const LowerTir, ctx: *LowerContext, a: *ast.Ast, id: ast.ExprId) types.TypeId {
    if (self.lookupExprTypeOverride(ctx, id)) |override| return override;
    const i = id.toRaw();
    std.debug.assert(i < a.type_info.expr_types.items.len);
    return a.type_info.expr_types.items[i] orelse unreachable;
}
/// Return the recorded type for declaration `did`, if the checker produced one.
fn getDeclType(a: *ast.Ast, did: ast.DeclId) ?types.TypeId {
    const i = did.toRaw();
    std.debug.assert(i < a.type_info.decl_types.items.len);

    return a.type_info.decl_types.items[i];
}

/// Construct the anonymous union that represents the payload fields of `vty` (variant/error).
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
/// Walk `pid` and bind every leaf to `value`, optionally storing into slots for mut bindings.
fn destructureDeclPattern(self: *LowerTir, a: *ast.Ast, env: *cf.Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, value: tir.ValueId, vty: types.TypeId, to_slots: bool) !void {
    const pk = a.pats.index.kinds.items[pid.toRaw()];
    const loc = optLoc(a, pid);
    switch (pk) {
        .Binding => {
            const nm = a.pats.get(.Binding, pid).name;
            if (self.isVoid(vty)) {
                // Nothing to bind: expression already evaluated for side effects.
                return;
            }
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
/// When the RHS is a tuple literal, destructure its elements directly into the pattern.
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

/// When the RHS is a struct literal, match named fields against the pattern to bind them.
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

/// Destructure an arbitrary expression `src_expr` according to `pid`, emitting stores and binds.
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
                if (!self.isType(tt.of, .Any)) break :blk tt.of;
            }
            var cval = try self.getCachedComptimeValue(a, src_expr);
            if (cval) |*computed| {
                defer computed.destroy(self.gpa);
                break :blk switch (computed.*) {
                    .Type => |ty| ty,
                    else => return error.UnsupportedComptimeType,
                };
            }
            return error.UnsupportedComptimeType;
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
            // Ensure type info for source expr before lowering in case checker didn’t stamp it yet.
            if (a.type_info.expr_types.items[src_expr.toRaw()] == null) {
                const cctx2 = self.chk.checker_ctx.items[a.file_id];
                _ = try self.chk.checkExpr(cctx2, a, src_expr);
            }
            var raw = try self.lowerExpr(ctx, a, env, f, blk, src_expr, expect_ty, .rvalue);

            const refined = try self.refineExprType(ctx, a, env, src_expr, self.getExprType(ctx, a, src_expr)) orelse unreachable;
            const eff_ty = if (target_kind == .Any and !self.isType(refined, .Any)) refined else target_ty;

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

/// Look up the tag index for `name` within the variant/error `case_ty`, if it exists.
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

/// Return the numeric value assigned to enum member `name`, or null if missing.
pub fn enumMemberValue(self: *const LowerTir, enum_ty: types.TypeId, name: StrId) ?i64 {
    const k = self.context.type_store.getKind(enum_ty);
    if (k != .Enum) return null;
    const er = self.context.type_store.get(.Enum, enum_ty);
    const members = self.context.type_store.enum_member_pool.slice(er.members);
    for (members) |mid| {
        const m = self.context.type_store.EnumMember.get(mid);
        if (m.name.eq(name)) return @intCast(m.value);
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

/// Return true when `ty` represents either a variant or error type.
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

/// Reapply a snapshot of symbol bindings (e.g., after destructuring) in reverse order.
pub fn restoreBindings(self: *LowerTir, env: *cf.Env, saved: []const BindingSnapshot) !void {
    var i: usize = saved.len;
    while (i > 0) : (i -= 1) {
        const entry = saved[i - 1];
        try env.restoreBinding(self.gpa, entry.name, entry.prev);
    }
}
