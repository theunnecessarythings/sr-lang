const std = @import("std");
const Context = @import("compile.zig").Context;
const tir = @import("tir.zig");
const types = @import("types.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const LowerTir = @import("lower_tir.zig");
const Pipeline = @import("pipeline.zig").Pipeline;
const monomorphize = @import("monomorphize.zig");
const checker = @import("checker.zig");
const codegen = @import("codegen_main.zig");
const ast = @import("ast.zig");
const cf = @import("lower_cf_tir.zig");
const List = std.ArrayList;

pub const ComptimeApi = struct {
    context: ?*anyopaque,
    print: *const fn (context: ?*anyopaque, format: [*c]const u8, ...) callconv(.c) void,
    get_type_by_name: *const fn (context: ?*anyopaque, name: [*c]const u8) callconv(.c) u32,
    type_of: *const fn (context: ?*anyopaque, expr_id: u32) callconv(.c) u32,
};

pub const ComptimeValue = union(enum) {
    Void,
    Int: i128,
    Float: f64,
    Bool: bool,
    String: []const u8,
    Type: types.TypeId,
    MlirType: mlir.Type,
    MlirAttribute: mlir.Attribute,
    MlirModule: mlir.Module,

    pub fn destroy(self: *ComptimeValue, gpa: std.mem.Allocator) void {
        switch (self.*) {
            .String => |s| {
                gpa.free(s);
            },
            .MlirModule => |*mod| {
                mod.destroy();
            },
            else => {},
        }
        self.* = .Void;
    }
};

pub fn type_of_impl(context: ?*anyopaque, type_id_raw: u32) callconv(.c) u32 {
    const ctx: *Context = @ptrCast(@alignCast(context.?));
    const type_id = types.TypeId.fromRaw(type_id_raw);
    const kind = ctx.type_store.getKind(type_id);
    std.debug.print("comptime> type_of_impl: type_id_raw={}, kind={s}\n", .{ type_id_raw, @tagName(kind) });
    return @intFromEnum(kind);
}

pub fn comptime_print_impl(context: ?*anyopaque, format: [*c]const u8, ...) callconv(.c) void {
    _ = context;
    std.debug.print("comptime> {s}\n", .{@as([]const u8, std.mem.sliceTo(format, 0))});
}

pub fn get_type_by_name_impl(context: ?*anyopaque, name: [*c]const u8) callconv(.c) u32 {
    const ctx: *Context = @ptrCast(@alignCast(context.?));
    const name_slice = std.mem.sliceTo(name, 0);
    const ts = ctx.type_store;

    if (std.mem.eql(u8, name_slice, "bool")) return ts.tBool().toRaw();
    if (std.mem.eql(u8, name_slice, "i8")) return ts.tI8().toRaw();
    if (std.mem.eql(u8, name_slice, "i16")) return ts.tI16().toRaw();
    if (std.mem.eql(u8, name_slice, "i32")) return ts.tI32().toRaw();
    if (std.mem.eql(u8, name_slice, "i64")) return ts.tI64().toRaw();
    if (std.mem.eql(u8, name_slice, "u8")) return ts.tU8().toRaw();
    if (std.mem.eql(u8, name_slice, "u16")) return ts.tU16().toRaw();
    if (std.mem.eql(u8, name_slice, "u32")) return ts.tU32().toRaw();
    if (std.mem.eql(u8, name_slice, "u64")) return ts.tU64().toRaw();
    if (std.mem.eql(u8, name_slice, "f32")) return ts.tF32().toRaw();
    if (std.mem.eql(u8, name_slice, "f64")) return ts.tF64().toRaw();
    if (std.mem.eql(u8, name_slice, "usize")) return ts.tUsize().toRaw();
    if (std.mem.eql(u8, name_slice, "char")) return ts.tU32().toRaw();
    if (std.mem.eql(u8, name_slice, "string")) return ts.tString().toRaw();
    if (std.mem.eql(u8, name_slice, "void")) return ts.tVoid().toRaw();
    if (std.mem.eql(u8, name_slice, "any")) return ts.tAny().toRaw();

    return ts.tVoid().toRaw(); // Return void if not found
}

// =============================
// Comptime Lower TIR API
// =============================

pub fn pushComptimeBindings(self: *LowerTir, ctx: *LowerTir.LowerContext, bindings: []const Pipeline.ComptimeBinding) !bool {
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
        infos[i] = switch (binding) {
            .type_param => |tp| monomorphize.BindingInfo.typeParam(tp.name, tp.ty),
            .value_param => |vp| try monomorphize.BindingInfo.valueParam(self.gpa, vp.name, vp.ty, vp.value),
        };
        init_count = i + 1;
    }

    var context = try monomorphize.MonomorphizationContext.init(
        self.gpa,
        infos[0..init_count],
        0,
        self.context.type_store.tVoid(),
    );
    errdefer context.deinit(self.gpa);
    try ctx.monomorph_context_stack.append(self.gpa, context);
    return true;
}

pub fn runComptimeExpr(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    expr: ast.ExprId,
    result_ty: types.TypeId,
    bindings: []const Pipeline.ComptimeBinding,
) !ComptimeValue {
    const pushed = try pushComptimeBindings(self, ctx, bindings);
    defer if (pushed) {
        var popped = ctx.monomorph_context_stack.pop();
        if (popped) |*context| context.deinit(self.gpa);
    };

    const result_kind = self.context.type_store.getKind(result_ty);
    if (result_kind == .TypeType) {
        const tt = self.context.type_store.get(.TypeType, result_ty);
        if (!self.isType(tt.of, .Any)) return .{ .Type = tt.of };
        // Otherwise, fall through and evaluate the expression to compute the concrete type.
    }

    var tmp_tir = tir.TIR.init(self.gpa, self.context.type_store);
    defer tmp_tir.deinit();
    var tmp_builder = tir.Builder.init(self.gpa, &tmp_tir);

    const ptr_ty = self.context.type_store.mkPtr(self.context.type_store.tU8(), false);
    const thunk_name = tmp_builder.intern("__comptime_thunk");
    const expr_loc = LowerTir.optLoc(a, expr);

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
    defer thunk_fn.deinit(self.gpa);
    const api_ptr_val = try tmp_builder.addParam(&thunk_fn, tmp_builder.intern("api_ptr"), ptr_ty);
    var thunk_blk = try tmp_builder.beginBlock(&thunk_fn);
    defer thunk_blk.deinit(self.gpa);

    var tmp_env = cf.Env{};
    defer tmp_env.deinit(self.gpa);
    try tmp_env.bind(self.gpa, a, tmp_builder.intern("comptime_api_ptr"), .{ .value = api_ptr_val, .ty = ptr_ty, .is_slot = false });

    const result_val_id = try self.lowerExpr(ctx, a, &tmp_env, &thunk_fn, &thunk_blk, expr, result_ty, .rvalue);
    try ctx.monomorphizer.run(self, ctx, &tmp_builder, monomorphLowerCallback);
    if (result_kind != .Void) {
        if (thunk_blk.term.isNone()) {
            try tmp_builder.setReturnVal(&thunk_blk, result_val_id, expr_loc);
        }
    } else if (thunk_blk.term.isNone()) {
        try tmp_builder.setReturnVoid(&thunk_blk, expr_loc);
    }
    try tmp_builder.endBlock(&thunk_fn, thunk_blk);
    try tmp_builder.endFunction(thunk_fn);

    if (!LowerTir.g_mlir_inited) {
        LowerTir.g_mlir_ctx = compile.initMLIR(self.gpa);
        LowerTir.g_mlir_inited = true;
    }
    var gen = codegen.Codegen.init(self.gpa, self.context, LowerTir.g_mlir_ctx);
    defer gen.deinit();
    const prev_debug_flag = codegen.enable_debug_info;
    codegen.enable_debug_info = false;
    defer codegen.enable_debug_info = prev_debug_flag;
    var mlir_module = try gen.emitModule(&tmp_tir);

    try compile.run_passes(&gen.mlir_ctx, &mlir_module);
    _ = mlir.c.LLVMInitializeNativeTarget();
    _ = mlir.c.LLVMInitializeNativeAsmPrinter();
    const engine = mlir.c.mlirExecutionEngineCreate(mlir_module.handle, 2, 0, null, false);
    defer mlir.c.mlirExecutionEngineDestroy(engine);

    var comptime_api = ComptimeApi{
        .context = self.context,
        .print = comptime_print_impl,
        .get_type_by_name = get_type_by_name_impl,
        .type_of = type_of_impl,
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
        return ComptimeValue{ .Bool = raw };
    }

    if (result_kind == .F64) {
        const raw = callComptimeThunk(f64, non_null_ptr, &comptime_api);
        return ComptimeValue{ .Float = raw };
    }

    if (result_kind == .F32) {
        const raw = callComptimeThunk(f32, non_null_ptr, &comptime_api);
        return ComptimeValue{ .Float = @floatCast(raw) };
    }

    if (result_kind == .MlirType) {
        const raw = callComptimeThunk(mlir.c.MlirType, non_null_ptr, &comptime_api);
        return ComptimeValue{ .MlirType = .{ .handle = raw } };
    }

    if (result_kind == .MlirAttribute) {
        const raw = callComptimeThunk(mlir.c.MlirAttribute, non_null_ptr, &comptime_api);
        return ComptimeValue{ .MlirAttribute = .{ .handle = raw } };
    }

    if (result_kind == .MlirModule) {
        const raw = callComptimeThunk(mlir.c.MlirModule, non_null_ptr, &comptime_api);
        return ComptimeValue{ .MlirModule = .{ .handle = raw } };
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
            const casted: i128 = castIntThunkResultToI128(raw);
            return ComptimeValue{ .Int = casted };
        }
    }

    return error.UnsupportedComptimeType;
}

fn callComptimeThunk(comptime Ret: type, func_ptr: *anyopaque, api: *ComptimeApi) Ret {
    const FnPtr = *const fn (*ComptimeApi) callconv(.c) Ret;
    const typed: FnPtr = @ptrCast(@alignCast(func_ptr));
    return typed(api);
}

fn castIntThunkResultToI128(value: anytype) i128 {
    const info = @typeInfo(@TypeOf(value)).int;
    if (info.signedness == .signed) {
        return @as(i128, value);
    } else {
        return @as(i128, @intCast(value));
    }
}

pub fn jitEvalComptimeBlock(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    blk: *tir.Builder.BlockFrame,
    id: ast.ExprId,
) !tir.ValueId {
    const cb = a.exprs.get(.ComptimeBlock, id);
    const result_ty = self.getExprType(ctx, a, cb.block);
    const comptime_value = try runComptimeExpr(self, ctx, a, cb.block, result_ty, &[_]Pipeline.ComptimeBinding{});
    const loc = LowerTir.optLoc(a, id);

    return switch (comptime_value) {
        .Int => |val| blk: {
            const kind = self.context.type_store.getKind(result_ty);
            const u: u64 = switch (kind) {
                .I32 => blk32: {
                    const s: i32 = @intCast(val);
                    const bits: u32 = @bitCast(s);
                    break :blk32 @as(u64, bits);
                },
                .I64 => blk64: {
                    const s: i64 = @intCast(val);
                    const bits: u64 = @bitCast(s);
                    break :blk64 bits;
                },
                .U32 => @as(u64, @intCast(@as(u32, @intCast(val)))),
                .U64, .Usize => @as(u64, @intCast(val)),
                else => @as(u64, @intCast(val)),
            };
            break :blk blk.builder.tirValue(.ConstInt, blk, result_ty, loc, .{ .value = u });
        },
        .Float => |val| blk.builder.tirValue(.ConstFloat, blk, result_ty, loc, .{ .value = val }),
        .Bool => |val| blk.builder.tirValue(.ConstBool, blk, result_ty, loc, .{ .value = val }),
        .Void => blk.builder.tirValue(.ConstUndef, blk, self.context.type_store.tVoid(), loc, .{}),
        .String => |s| blk.builder.tirValue(.ConstString, blk, result_ty, loc, .{ .text = blk.builder.intern(s) }),
        .Type => return error.UnsupportedComptimeType,
        .MlirType => blk.builder.tirValue(.ConstUndef, blk, result_ty, loc, .{}),
        .MlirAttribute => blk.builder.tirValue(.ConstUndef, blk, result_ty, loc, .{}),
        .MlirModule => blk.builder.tirValue(.ConstUndef, blk, result_ty, loc, .{}),
    };
}

pub fn evalComptimeExprValue(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    expr: ast.ExprId,
    result_ty: types.TypeId,
) !ComptimeValue {
    return runComptimeExpr(self, ctx, a, expr, result_ty, &[_]Pipeline.ComptimeBinding{});
}

pub fn constValueFromComptime(
    self: *LowerTir,
    blk: *tir.Builder.BlockFrame,
    ty: types.TypeId,
    value: ComptimeValue,
) !tir.ValueId {
    // These values are synthesized from specialization metadata; no source location is available.
    return switch (value) {
        .Int => |val| blk: {
            const kind = self.context.type_store.getKind(ty);
            const u: u64 = switch (kind) {
                .I32 => blk32: {
                    const s: i32 = @intCast(val);
                    const bits: u32 = @bitCast(s);
                    break :blk32 @as(u64, bits);
                },
                .I64 => blk64: {
                    const s: i64 = @intCast(val);
                    const bits: u64 = @bitCast(s);
                    break :blk64 bits;
                },
                .U32 => @as(u64, @intCast(@as(u32, @intCast(val)))),
                .U64, .Usize => @as(u64, @intCast(val)),
                else => @as(u64, @intCast(val)),
            };
            break :blk blk.builder.tirValue(.ConstInt, blk, ty, tir.OptLocId.none(), .{ .value = u });
        },
        .Float => |val| blk.builder.tirValue(.ConstFloat, blk, ty, tir.OptLocId.none(), .{ .value = val }),
        .Bool => |val| blk.builder.tirValue(.ConstBool, blk, ty, tir.OptLocId.none(), .{ .value = val }),
        .Void => blk.builder.tirValue(.ConstUndef, blk, ty, tir.OptLocId.none(), .{}),
        .String => |s| blk.builder.tirValue(.ConstString, blk, ty, tir.OptLocId.none(), .{ .text = blk.builder.intern(s) }),
        .Type => return error.UnsupportedComptimeType,
        .MlirType => blk.builder.tirValue(.ConstUndef, blk, ty, tir.OptLocId.none(), .{}),
        .MlirAttribute => blk.builder.tirValue(.ConstUndef, blk, ty, tir.OptLocId.none(), .{}),
        .MlirModule => blk.builder.tirValue(.ConstUndef, blk, ty, tir.OptLocId.none(), .{}),
    };
}

pub fn cloneComptimeValue(self: *LowerTir, value: ComptimeValue) !ComptimeValue {
    return switch (value) {
        .Void => .Void,
        .Int => |v| .{ .Int = v },
        .Float => |v| .{ .Float = v },
        .Bool => |v| .{ .Bool = v },
        .String => |s| .{ .String = try self.gpa.dupe(u8, s) },
        .Type => |ty| .{ .Type = ty },
        .MlirType => |ty| .{ .MlirType = ty },
        .MlirAttribute => |attr| .{ .MlirAttribute = attr },
        .MlirModule => |mod| blk: {
            const cloned_op = mlir.Operation.clone(mod.getOperation());
            break :blk .{ .MlirModule = mlir.Module.fromOperation(cloned_op) };
        },
    };
}

fn hashComptimeValue(value: ComptimeValue) u64 {
    var hasher = std.hash.Wyhash.init(0);
    const tag: u8 = @intFromEnum(value);
    hasher.update(&.{tag});
    switch (value) {
        .Void => {},
        .Int => |val| hasher.update(std.mem.asBytes(&val)),
        .Float => |val| {
            const bits: u64 = @bitCast(val);
            hasher.update(std.mem.asBytes(&bits));
        },
        .Bool => |val| {
            const b: u8 = if (val) 1 else 0;
            hasher.update(&.{b});
        },
        .String => |s| {
            const len: usize = s.len;
            hasher.update(std.mem.asBytes(&len));
            hasher.update(s);
        },
        .Type => |ty| {
            const raw = ty.toRaw();
            hasher.update(std.mem.asBytes(&raw));
        },
        .MlirType => |ty| hasher.update(std.mem.asBytes(&ty.handle)),
        .MlirAttribute => |attr| hasher.update(std.mem.asBytes(&attr.handle)),
        .MlirModule => |mod| hasher.update(std.mem.asBytes(&mod.handle)),
    }
    return hasher.final();
}

pub fn mangleMonomorphName(
    self: *LowerTir,
    base: tir.StrId,
    bindings: []const monomorphize.BindingInfo,
) !tir.StrId {
    var buf: List(u8) = .empty;
    defer buf.deinit(self.gpa);

    try buf.appendSlice(self.gpa, self.context.type_store.strs.get(base));
    if (bindings.len == 0) return self.context.type_store.strs.intern(buf.items);

    try buf.appendSlice(self.gpa, "_M");
    for (bindings) |info| {
        try buf.append(self.gpa, '_');
        var w = buf.writer(self.gpa);
        switch (info.kind) {
            .type_param => |ty| try w.print("T{}", .{ty.toRaw()}),
            .value_param => |vp| {
                const hash = hashComptimeValue(vp.value);
                try w.print("V{}x{X}", .{ vp.ty.toRaw(), hash });
            },
            .runtime_param => |ty| try w.print("R{}", .{ty.toRaw()}),
        }
    }

    return self.context.type_store.strs.intern(buf.items);
}

fn lowerSpecializedFunction(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    b: *tir.Builder,
    req: *const monomorphize.MonomorphizationRequest,
) !void {
    var context = try monomorphize.MonomorphizationContext.init(
        self.gpa,
        req.bindings,
        req.skip_params,
        req.specialized_ty,
    );

    ctx.monomorph_context_stack.append(self.gpa, context) catch |err| {
        context.deinit(self.gpa);
        return err;
    };
    defer {
        var popped = ctx.monomorph_context_stack.pop();
        if (popped) |*p|
            p.deinit(self.gpa);
    }

    const active_ctx = &ctx.monomorph_context_stack.items[ctx.monomorph_context_stack.items.len - 1];
    const decl = a.exprs.Decl.get(req.decl_id);
    try self.lowerFunction(ctx, a, b, req.mangled_name, decl.value, active_ctx);
}

pub fn monomorphLowerCallback(
    ctx: ?*anyopaque,
    lower_ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    b: *tir.Builder,
    req: *const monomorphize.MonomorphizationRequest,
) anyerror!void {
    std.debug.assert(ctx != null);
    const self: *LowerTir = @ptrCast(@alignCast(ctx.?));
    try lowerSpecializedFunction(self, lower_ctx, a, b, req);
}
