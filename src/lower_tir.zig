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
const lower_mlir = @import("lower_mlir.zig");

const StrId = @import("cst.zig").StrId;
const OptStrId = @import("cst.zig").OptStrId;
const Context = @import("compile.zig").Context;
const Pipeline = pipeline_mod.Pipeline;
const Builder = tir.Builder;

pub const LowerTir = struct {
    pub const Inputs = struct {
        allocator: std.mem.Allocator,
        context: *Context,
        pipeline: *Pipeline,
        checker: *checker.Checker,
    };

    gpa: std.mem.Allocator,
    context: *Context,
    pipeline: *Pipeline,
    chk: *checker.Checker,

    // Simple loop stack to support break/continue in While/For (+ value loops)
    loop_stack: LoopStack = .{},

    module_call_cache: std.AutoHashMap(u64, StrId),
    method_lowered: std.AutoHashMap(usize, void),
    variant_tag_cache: std.AutoHashMap(u64, u32),
    enum_value_cache: std.AutoHashMap(u64, u64),
    monomorphizer: monomorphize.Monomorphizer,
    monomorph_context_stack: std.ArrayListUnmanaged(monomorphize.MonomorphizationContext) = .{},
    expr_type_override_stack: std.ArrayListUnmanaged(ExprTypeOverrideFrame) = .{},
    mlir_lower: lower_mlir.LowerMlir,

    pub fn init(inputs: Inputs) LowerTir {
        return .{
            .gpa = inputs.allocator,
            .context = inputs.context,
            .pipeline = inputs.pipeline,
            .chk = inputs.checker,
            .module_call_cache = std.AutoHashMap(u64, StrId).init(inputs.allocator),
            .method_lowered = std.AutoHashMap(usize, void).init(inputs.allocator),
            .variant_tag_cache = std.AutoHashMap(u64, u32).init(inputs.allocator),
            .enum_value_cache = std.AutoHashMap(u64, u64).init(inputs.allocator),
            .monomorphizer = monomorphize.Monomorphizer.init(inputs.allocator),
            .mlir_lower = lower_mlir.LowerMlir.init(inputs.allocator, inputs.context),
        };
    }

    pub fn deinit(self: *LowerTir) void {
        self.loop_stack.deinit(self.gpa);
        self.module_call_cache.deinit();
        self.method_lowered.deinit();
        self.variant_tag_cache.deinit();
        self.enum_value_cache.deinit();
        while (self.monomorph_context_stack.items.len > 0) self.popMonomorphContext();
        self.monomorph_context_stack.deinit(self.gpa);
        while (self.expr_type_override_stack.items.len > 0) self.releaseTopOverrideFrame();
        self.expr_type_override_stack.deinit(self.gpa);
        self.monomorphizer.deinit();
        self.mlir_lower.deinit();
    }

    const ModuleState = struct {
        tir: tir.TIR,
        builder: Builder,

        fn init(allocator: std.mem.Allocator, type_store: *types.TypeStore) ModuleState {
            var state = ModuleState{
                .tir = tir.TIR.init(allocator, type_store),
                .builder = undefined,
            };
            state.builder = Builder.init(allocator, &state.tir);
            return state;
        }

        fn intoResult(self: ModuleState) tir.TIR {
            return self.tir;
        }
    };

    const BindingSnapshot = struct {
        name: ast.StrId,
        prev: ?ValueBinding,
    };

    const ExprTypeOverrideFrame = struct {
        map: std.AutoArrayHashMapUnmanaged(u32, types.TypeId) = .{},
    };

    const ExprTypeOverrideScope = struct {
        lowerer: *LowerTir,
        active: bool,

        fn begin(lowerer: *LowerTir) !ExprTypeOverrideScope {
            try lowerer.expr_type_override_stack.append(lowerer.gpa, .{});
            return .{ .lowerer = lowerer, .active = true };
        }

        pub fn end(self: *ExprTypeOverrideScope) void {
            if (!self.active) return;
            self.lowerer.releaseTopOverrideFrame();
            self.active = false;
        }

        pub fn deinit(self: *ExprTypeOverrideScope) void {
            self.end();
        }
    };

    const MonomorphScope = struct {
        lowerer: *LowerTir,
        active: bool,

        fn init(lowerer: *LowerTir, active: bool) MonomorphScope {
            return .{ .lowerer = lowerer, .active = active };
        }

        pub fn end(self: *MonomorphScope) void {
            if (!self.active) return;
            self.lowerer.popMonomorphContext();
            self.active = false;
        }

        pub fn deinit(self: *MonomorphScope) void {
            self.end();
        }
    };

    const BindingInfoBuffer = struct {
        allocator: std.mem.Allocator,
        items: []monomorphize.BindingInfo,
        len: usize,

        fn init(allocator: std.mem.Allocator, count: usize) !BindingInfoBuffer {
            if (count == 0) {
                return .{ .allocator = allocator, .items = &[_]monomorphize.BindingInfo{}, .len = 0 };
            }
            return .{ .allocator = allocator, .items = try allocator.alloc(monomorphize.BindingInfo, count), .len = 0 };
        }

        fn append(self: *BindingInfoBuffer, info: monomorphize.BindingInfo) void {
            std.debug.assert(self.len < self.items.len);
            self.items[self.len] = info;
            self.len += 1;
        }

        fn slice(self: *const BindingInfoBuffer) []const monomorphize.BindingInfo {
            return self.items[0..self.len];
        }

        fn deinit(self: *BindingInfoBuffer) void {
            var i: usize = 0;
            while (i < self.len) : (i += 1) {
                self.items[i].deinit(self.allocator);
            }
            if (self.items.len != 0) {
                self.allocator.free(self.items);
            }
            self.items = &[_]monomorphize.BindingInfo{};
            self.len = 0;
        }
    };

    const ComptimeThunk = struct {
        tir: tir.TIR,
        builder: Builder,
        func: Builder.FunctionFrame,
        block: Builder.BlockFrame,
        env: Env,
        finalized: bool = false,

        fn init(
            lowerer: *LowerTir,
            a: *ast.Ast,
            result_ty: types.TypeId,
            result_kind: types.TypeKind,
        ) !ComptimeThunk {
            var tir_mod = tir.TIR.init(lowerer.gpa, lowerer.context.type_store);
            errdefer tir_mod.deinit();

            var builder = tir.Builder.init(lowerer.gpa, &tir_mod);

            const attr_id = tir_mod.instrs.Attribute.add(lowerer.gpa, .{
                .name = builder.intern("llvm.emit_c_interface"),
                .value = .none(),
            });
            const attrs = tir_mod.instrs.attribute_pool.pushMany(lowerer.gpa, &.{attr_id});

            const thunk_ret_ty = if (result_kind == .Void)
                lowerer.context.type_store.tVoid()
            else
                result_ty;

            var func = try builder.beginFunction(builder.intern("__comptime_thunk"), thunk_ret_ty, false, attrs);
            errdefer func.deinit(lowerer.gpa);

            const ptr_ty = lowerer.context.type_store.mkPtr(lowerer.context.type_store.tU8(), false);
            const api_ptr_val = try builder.addParam(&func, builder.intern("api_ptr"), ptr_ty);

            var block = try builder.beginBlock(&func);
            errdefer block.deinit(lowerer.gpa);

            var env = Env.init(lowerer.gpa);
            errdefer env.deinit();

            try env.bind(builder.intern("comptime_api_ptr"), .{
                .value = api_ptr_val,
                .ty = ptr_ty,
                .is_slot = false,
            });

            return .{
                .tir = tir_mod,
                .builder = builder,
                .func = func,
                .block = block,
                .env = env,
            };
        }

        fn lowerExpr(
            self: *ComptimeThunk,
            lowerer: *LowerTir,
            a: *ast.Ast,
            expr: ast.ExprId,
            result_ty: types.TypeId,
        ) !tir.ValueId {
            return lowerer.lowerExpr(a, &self.env, &self.func, &self.block, expr, result_ty, .rvalue);
        }

        fn finalize(
            self: *ComptimeThunk,
            result_kind: types.TypeKind,
            value: ?tir.ValueId,
            loc: tir.OptLocId,
        ) !void {
            if (self.finalized) return;
            const builder = &self.builder;
            if (result_kind != .Void) {
                const val = value orelse return error.LoweringBug;
                if (self.block.term.isNone()) {
                    try builder.setReturnVal(&self.block, val, loc);
                }
            } else if (self.block.term.isNone()) {
                try builder.setReturnVoid(&self.block, loc);
            }
            try builder.endBlock(&self.func, self.block);
            try builder.endFunction(self.func);
            self.finalized = true;
        }

        fn deinit(self: *ComptimeThunk, gpa: std.mem.Allocator) void {
            self.block.deinit(gpa);
            self.func.deinit(gpa);
            self.env.deinit();
            self.tir.deinit();
        }
    };

    const ComptimeRuntime = struct {
        pub fn run(
            allocator: std.mem.Allocator,
            context: *Context,
            pipeline: *Pipeline,
            chk: *checker.Checker,
            ast_unit: *ast.Ast,
            expr: ast.ExprId,
            result_ty: types.TypeId,
            bindings: []const Pipeline.ComptimeBinding,
        ) !comp.ComptimeValue {
            var lowerer = LowerTir.init(.{
                .allocator = allocator,
                .context = context,
                .pipeline = pipeline,
                .checker = chk,
            });
            defer lowerer.deinit();
            return lowerer.runComptimeExpr(ast_unit, expr, result_ty, bindings);
        }

        fn decode(result_kind: types.TypeKind, func_ptr: *anyopaque, api: *comp.ComptimeApi) !comp.ComptimeValue {
            if (result_kind == .Void) {
                call(void, func_ptr, api);
                return .Void;
            }

            if (result_kind == .Bool) {
                const raw = call(bool, func_ptr, api);
                return comp.ComptimeValue{ .Bool = raw };
            }

            if (result_kind == .F64) {
                const raw = call(f64, func_ptr, api);
                return comp.ComptimeValue{ .Float = raw };
            }

            if (result_kind == .F32) {
                const raw = call(f32, func_ptr, api);
                return comp.ComptimeValue{ .Float = @floatCast(raw) };
            }

            if (result_kind == .MlirType) {
                const raw = call(mlir.c.MlirType, func_ptr, api);
                return comp.ComptimeValue{ .MlirType = .{ .handle = raw } };
            }

            if (result_kind == .MlirAttribute) {
                const raw = call(mlir.c.MlirAttribute, func_ptr, api);
                return comp.ComptimeValue{ .MlirAttribute = .{ .handle = raw } };
            }

            if (result_kind == .MlirModule) {
                const raw = call(mlir.c.MlirModule, func_ptr, api);
                return comp.ComptimeValue{ .MlirModule = .{ .handle = raw } };
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
                    const raw = call(entry.T, func_ptr, api);
                    if (castInt(raw)) |casted| {
                        return comp.ComptimeValue{ .Int = casted };
                    }
                    return error.UnsupportedComptimeType;
                }
            }

            return error.UnsupportedComptimeType;
        }

        fn call(comptime Ret: type, func_ptr: *anyopaque, api: *comp.ComptimeApi) Ret {
            const FnPtr = *const fn (*comp.ComptimeApi) callconv(.c) Ret;
            const typed: FnPtr = @ptrCast(@alignCast(func_ptr));
            return typed(api);
        }

        fn castInt(value: anytype) ?u128 {
            const info = @typeInfo(@TypeOf(value)).int;
            if (info.signedness == .signed) {
                return std.math.cast(u128, value);
            }
            return @as(u128, value);
        }
    };


    const FunctionDeclContext = struct {
        ast: *ast.Ast,
        decl_id: ast.DeclId,
    };

    fn beginExprTypeOverrideScope(self: *LowerTir) !ExprTypeOverrideScope {
        return ExprTypeOverrideScope.begin(self);
    }

    fn currentOverrideFrame(self: *LowerTir) ?*ExprTypeOverrideFrame {
        if (self.expr_type_override_stack.items.len == 0) return null;
        const idx = self.expr_type_override_stack.items.len - 1;
        return &self.expr_type_override_stack.items[idx];
    }

    fn releaseTopOverrideFrame(self: *LowerTir) void {
        if (self.expr_type_override_stack.items.len == 0) return;
        const idx = self.expr_type_override_stack.items.len - 1;
        self.expr_type_override_stack.items[idx].map.deinit(self.gpa);
        self.expr_type_override_stack.items.len = idx;
    }

    fn popMonomorphContext(self: *LowerTir) void {
        if (self.monomorph_context_stack.items.len == 0) return;
        const idx = self.monomorph_context_stack.items.len - 1;
        var ctx = self.monomorph_context_stack.items[idx];
        self.monomorph_context_stack.items.len = idx;
        ctx.deinit(self.gpa);
    }

    fn currentMonomorphContext(self: *LowerTir) ?*monomorphize.MonomorphizationContext {
        if (self.monomorph_context_stack.items.len == 0) return null;
        const idx = self.monomorph_context_stack.items.len - 1;
        return &self.monomorph_context_stack.items[idx];
    }

    fn collectBindingInfos(
        self: *LowerTir,
        bindings: []const Pipeline.ComptimeBinding,
    ) !BindingInfoBuffer {
        var buffer = try BindingInfoBuffer.init(self.gpa, bindings.len);
        errdefer buffer.deinit();

        for (bindings) |binding| {
            const info = switch (binding) {
                .type_param => |tp| monomorphize.BindingInfo.typeParam(tp.name, tp.ty),
                .value_param => |vp| try monomorphize.BindingInfo.valueParam(self.gpa, vp.name, vp.ty, vp.value),
            };
            buffer.append(info);
        }

        return buffer;
    }

    fn enterMonomorphScope(
        self: *LowerTir,
        infos: []const monomorphize.BindingInfo,
    ) !MonomorphScope {
        if (infos.len == 0) {
            return MonomorphScope.init(self, false);
        }

        var ctx = try monomorphize.MonomorphizationContext.init(
            self.gpa,
            infos,
            0,
            self.context.type_store.tVoid(),
        );
        errdefer ctx.deinit(self.gpa);

        try self.monomorph_context_stack.append(self.gpa, ctx);
        return MonomorphScope.init(self, true);
    }

    fn pushComptimeBindings(
        self: *LowerTir,
        bindings: []const Pipeline.ComptimeBinding,
    ) !MonomorphScope {
        if (bindings.len == 0) return MonomorphScope.init(self, false);

        var infos = try self.collectBindingInfos(bindings);
        defer infos.deinit();

        var scope = try self.enterMonomorphScope(infos.slice());
        if (!scope.active) return scope;

        // The context clones the binding infos; they can be dropped now.
        return scope;
    }

    fn pushMonomorphRequest(
        self: *LowerTir,
        req: *const monomorphize.MonomorphizationRequest,
    ) !MonomorphScope {
        var ctx = try monomorphize.MonomorphizationContext.init(
            self.gpa,
            req.bindings,
            req.skip_params,
            req.specialized_ty,
        );
        errdefer ctx.deinit(self.gpa);

        try self.monomorph_context_stack.append(self.gpa, ctx);
        return MonomorphScope.init(self, true);
    }

    fn noteExprType(self: *LowerTir, expr: ast.ExprId, ty: types.TypeId) !void {
        const frame = self.currentOverrideFrame() orelse return;
        if (self.isAny(ty)) return;
        const entry = try frame.map.getOrPut(self.gpa, expr.toRaw());
        entry.value_ptr.* = ty;
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

    const LiteralPayload = union(enum) {
        int: u128,
        float: f64,
        bool: bool,
        string: ast.StrId,
    };

    fn literalPayload(a: *ast.Ast, expr: ast.ExprId) ?LiteralPayload {
        const kind = a.exprs.index.kinds.items[expr.toRaw()];
        if (kind != .Literal) return null;
        const lit = a.exprs.get(.Literal, expr);

        return switch (lit.kind) {
            .int => blk: {
                const info = switch (lit.data) {
                    .int => |int_info| int_info,
                    else => return null,
                };
                if (!info.valid) break :blk null;
                break :blk LiteralPayload{ .int = info.value };
            },
            .float => blk: {
                const info = switch (lit.data) {
                    .float => |float_info| float_info,
                    else => return null,
                };
                if (!info.valid) break :blk null;
                break :blk LiteralPayload{ .float = info.value };
            },
            .bool => blk: {
                const value = switch (lit.data) {
                    .bool => |b| b,
                    else => return null,
                };
                break :blk LiteralPayload{ .bool = value };
            },
            .string => blk: {
                const sid = switch (lit.data) {
                    .string => |s_id| s_id,
                    else => return null,
                };
                break :blk LiteralPayload{ .string = sid };
            },
            else => null,
        };
    }

    fn constInitFromLiteral(
        self: *LowerTir,
        a: *ast.Ast,
        expr: ast.ExprId,
        ty: types.TypeId,
    ) ?tir.ConstInit {
        const payload = literalPayload(a, expr) orelse return null;
        const ty_kind = self.context.type_store.getKind(ty);
        return switch (ty_kind) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => switch (payload) {
                .int => |value| blk: {
                    const max_i64: u128 = @intCast(std.math.maxInt(i64));
                    if (value > max_i64) break :blk null;
                    break :blk tir.ConstInit{ .int = @intCast(value) };
                },
                else => null,
            },
            .Bool => switch (payload) {
                .bool => |b| tir.ConstInit{ .bool = b },
                else => null,
            },
            else => null,
        };
    }

    const DynArrayView = struct {
        elem_ty: types.TypeId,
        usize_ty: types.TypeId,
        ptr_elem_ty: types.TypeId,
        ptr_ptr_elem_ty: types.TypeId,
        ptr_usize_ty: types.TypeId,
        ptr_void_ty: types.TypeId,
        data_ptr_ptr: tir.ValueId,
        len_ptr: tir.ValueId,
        cap_ptr: tir.ValueId,

        fn init(
            lowerer: *LowerTir,
            blk: *Builder.BlockFrame,
            owner_ty: types.TypeId,
            array_ptr: tir.ValueId,
            loc: tir.OptLocId,
        ) !DynArrayView {
            const ts = lowerer.context.type_store;
            if (ts.getKind(owner_ty) != .DynArray) return error.LoweringBug;

            const dyn_info = ts.get(.DynArray, owner_ty);
            const elem_ty = dyn_info.elem;
            const usize_ty = ts.tUsize();
            const ptr_elem_ty = ts.mkPtr(elem_ty, false);
            const ptr_ptr_elem_ty = ts.mkPtr(ptr_elem_ty, false);
            const ptr_usize_ty = ts.mkPtr(usize_ty, false);
            const ptr_void_ty = ts.mkPtr(ts.tVoid(), false);

            return .{
                .elem_ty = elem_ty,
                .usize_ty = usize_ty,
                .ptr_elem_ty = ptr_elem_ty,
                .ptr_ptr_elem_ty = ptr_ptr_elem_ty,
                .ptr_usize_ty = ptr_usize_ty,
                .ptr_void_ty = ptr_void_ty,
                .data_ptr_ptr = blk.builder.gep(blk, ptr_ptr_elem_ty, array_ptr, &.{blk.builder.gepConst(0)}, loc),
                .len_ptr = blk.builder.gep(blk, ptr_usize_ty, array_ptr, &.{blk.builder.gepConst(1)}, loc),
                .cap_ptr = blk.builder.gep(blk, ptr_usize_ty, array_ptr, &.{blk.builder.gepConst(2)}, loc),
            };
        }

        fn loadLen(self: *const DynArrayView, blk: *Builder.BlockFrame, loc: tir.OptLocId) tir.ValueId {
            return blk.builder.tirValue(.Load, blk, self.usize_ty, loc, .{ .ptr = self.len_ptr, .@"align" = 0 });
        }

        fn loadCap(self: *const DynArrayView, blk: *Builder.BlockFrame, loc: tir.OptLocId) tir.ValueId {
            return blk.builder.tirValue(.Load, blk, self.usize_ty, loc, .{ .ptr = self.cap_ptr, .@"align" = 0 });
        }

        fn loadDataPtr(self: *const DynArrayView, blk: *Builder.BlockFrame, loc: tir.OptLocId) tir.ValueId {
            return blk.builder.tirValue(.Load, blk, self.ptr_elem_ty, loc, .{ .ptr = self.data_ptr_ptr, .@"align" = 0 });
        }

        fn storeDataPtr(self: *const DynArrayView, blk: *Builder.BlockFrame, value: tir.ValueId, loc: tir.OptLocId) void {
            _ = blk.builder.tirValue(.Store, blk, self.ptr_elem_ty, loc, .{ .ptr = self.data_ptr_ptr, .value = value, .@"align" = 0 });
        }

        fn storeElement(
            self: *const DynArrayView,
            blk: *Builder.BlockFrame,
            ptr: tir.ValueId,
            value: tir.ValueId,
            loc: tir.OptLocId,
        ) void {
            _ = blk.builder.tirValue(.Store, blk, self.elem_ty, loc, .{ .ptr = ptr, .value = value, .@"align" = 0 });
        }

        fn storeLen(self: *const DynArrayView, blk: *Builder.BlockFrame, value: tir.ValueId, loc: tir.OptLocId) void {
            _ = blk.builder.tirValue(.Store, blk, self.usize_ty, loc, .{ .ptr = self.len_ptr, .value = value, .@"align" = 0 });
        }

        fn storeCap(self: *const DynArrayView, blk: *Builder.BlockFrame, value: tir.ValueId, loc: tir.OptLocId) void {
            _ = blk.builder.tirValue(.Store, blk, self.usize_ty, loc, .{ .ptr = self.cap_ptr, .value = value, .@"align" = 0 });
        }

        fn constUsize(self: *const DynArrayView, blk: *Builder.BlockFrame, value: u64, loc: tir.OptLocId) tir.ValueId {
            return blk.builder.tirValue(.ConstInt, blk, self.usize_ty, loc, .{ .value = value });
        }

        fn elementPtr(
            self: *const DynArrayView,
            blk: *Builder.BlockFrame,
            data_ptr: tir.ValueId,
            index_val: tir.ValueId,
            loc: tir.OptLocId,
        ) tir.ValueId {
            const idx = blk.builder.gepValue(index_val);
            return blk.builder.gep(blk, self.ptr_elem_ty, data_ptr, &.{idx}, loc);
        }

        fn ensureCapacity(
            self: *const DynArrayView,
            lowerer: *LowerTir,
            f: *Builder.FunctionFrame,
            blk: *Builder.BlockFrame,
            len_val: tir.ValueId,
            cap_val: tir.ValueId,
            elem_size: u64,
            loc: tir.OptLocId,
        ) !void {
            const need_grow = blk.builder.binBool(blk, .CmpEq, len_val, cap_val, loc);
            var grow_blk = try f.builder.beginBlock(f);
            const cont_blk = try f.builder.beginBlock(f);

            const cond = lowerer.forceLocalCond(blk, need_grow, loc);
            try f.builder.condBr(blk, cond, grow_blk.id, &.{}, cont_blk.id, &.{}, loc);

            const prev = blk.*;
            try f.builder.endBlock(f, prev);

            self.emitGrowBlock(f, &grow_blk, cap_val, elem_size, loc, cont_blk.id);

            blk.* = cont_blk;
        }

        fn emitGrowBlock(
            self: *const DynArrayView,
            f: *Builder.FunctionFrame,
            grow_blk: *Builder.BlockFrame,
            cap_val: tir.ValueId,
            elem_size: u64,
            loc: tir.OptLocId,
            cont_id: Builder.BlockId,
        ) !void {
            const data_ptr = self.loadDataPtr(grow_blk, loc);
            const zero_const = self.constUsize(grow_blk, 0, loc);
            const cap_is_zero = grow_blk.builder.binBool(grow_blk, .CmpEq, cap_val, zero_const, loc);
            const doubled = grow_blk.builder.bin(grow_blk, .Mul, self.usize_ty, cap_val, self.constUsize(grow_blk, 2, loc), loc);
            const new_cap = grow_blk.builder.tirValue(.Select, grow_blk, self.usize_ty, loc, .{
                .cond = cap_is_zero,
                .then_value = self.constUsize(grow_blk, 1, loc),
                .else_value = doubled,
            });

            const elem_size_const = self.constUsize(grow_blk, elem_size, loc);
            const new_bytes = grow_blk.builder.bin(grow_blk, .Mul, self.usize_ty, new_cap, elem_size_const, loc);

            const data_ptr_void = grow_blk.builder.tirValue(.CastBit, grow_blk, self.ptr_void_ty, loc, .{ .value = data_ptr });
            const realloc_name = grow_blk.builder.intern("rt_realloc");
            const new_data_void = grow_blk.builder.call(grow_blk, self.ptr_void_ty, realloc_name, &.{ data_ptr_void, new_bytes }, loc);
            const new_data_ptr = grow_blk.builder.tirValue(.CastBit, grow_blk, self.ptr_elem_ty, loc, .{ .value = new_data_void });

            self.storeDataPtr(grow_blk, new_data_ptr, loc);
            self.storeCap(grow_blk, new_cap, loc);

            try f.builder.br(grow_blk, cont_id, &.{}, loc);
            try f.builder.endBlock(f, grow_blk.*);
        }
    };

    fn lowerDynArrayAppend(
        self: *LowerTir,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        loc: tir.OptLocId,
        binding: types.TypeInfo.MethodBinding,
        args: []const tir.ValueId,
    ) !tir.ValueId {
        std.debug.assert(binding.builtin != null and binding.builtin.? == .dynarray_append);
        if (args.len < 2) return error.LoweringBug;

        var view = try DynArrayView.init(self, blk, binding.owner_type, args[0], loc);
        const elem_size = check_types.typeSize(self.chk, view.elem_ty) orelse return error.LoweringBug;
        const elem_size_u64 = std.math.cast(u64, elem_size) orelse return error.LoweringBug;

        const len_val = view.loadLen(blk, loc);
        const cap_val = view.loadCap(blk, loc);
        try view.ensureCapacity(self, f, blk, len_val, cap_val, elem_size_u64, loc);

        const data_ptr = view.loadDataPtr(blk, loc);
        const len_cur = view.loadLen(blk, loc);
        const slot_ptr = view.elementPtr(blk, data_ptr, len_cur, loc);
        view.storeElement(blk, slot_ptr, args[1], loc);

        const new_len = blk.builder.bin(
            blk,
            .Add,
            view.usize_ty,
            len_cur,
            view.constUsize(blk, 1, loc),
            loc,
        );
        view.storeLen(blk, new_len, loc);

        return self.emitUndefValue(blk, self.context.type_store.tVoid(), loc, false);
    }

    fn mlirHooks(self: *LowerTir) lower_mlir.Hooks {
        return .{
            .host = self,
            .lowerExprValue = mlirLowerExprValue,
            .evalComptimeExpr = mlirEvalComptimeExpr,
            .emitCoerce = mlirEmitCoerce,
            .getExprType = mlirGetExprType,
            .getDeclType = mlirGetDeclType,
            .isAny = mlirIsAny,
            .lookupMonomorphValue = mlirLookupMonomorphValue,
            .lookupMonomorphType = mlirLookupMonomorphType,
            .createEnv = mlirCreateEnv,
            .destroyEnv = mlirDestroyEnv,
        };
    }

    fn mlirLowerExprValue(
        ctx: *anyopaque,
        a: *ast.Ast,
        env_ptr: *anyopaque,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        expr: ast.ExprId,
        expected: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        const env: *Env = @ptrCast(@alignCast(env_ptr));
        return self.lowerExpr(a, env, f, blk, expr, expected, .rvalue);
    }

    fn mlirEvalComptimeExpr(
        ctx: *anyopaque,
        a: *ast.Ast,
        env_ptr: *anyopaque,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        expr: ast.ExprId,
        result_ty: types.TypeId,
    ) anyerror!comp.ComptimeValue {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        const env: *Env = @ptrCast(@alignCast(env_ptr));
        return self.evalComptimeExprValue(a, env, f, blk, expr, result_ty);
    }

    fn mlirEmitCoerce(
        ctx: *anyopaque,
        blk: *Builder.BlockFrame,
        value: tir.ValueId,
        from_ty: types.TypeId,
        to_ty: types.TypeId,
        loc: tir.OptLocId,
    ) anyerror!tir.ValueId {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        return self.emitCoerce(blk, value, from_ty, to_ty, loc);
    }

    fn mlirGetExprType(ctx: *anyopaque, a: *ast.Ast, expr: ast.ExprId) ?types.TypeId {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        return self.getExprType(a, expr);
    }

    fn mlirGetDeclType(ctx: *anyopaque, a: *ast.Ast, decl: ast.DeclId) ?types.TypeId {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        return getDeclType(a, decl);
    }

    fn mlirIsAny(ctx: *anyopaque, ty: types.TypeId) bool {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        return self.isAny(ty);
    }

    fn mlirLookupMonomorphValue(ctx: *anyopaque, name: ast.StrId) anyerror!?comp.ComptimeValue {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        var i: usize = self.monomorph_context_stack.items.len;
        while (i > 0) {
            i -= 1;
            if (self.monomorph_context_stack.items[i].lookupValue(name)) |binding| {
                return try comp.cloneValue(self.gpa, binding.value);
            }
        }
        return null;
    }

    fn mlirLookupMonomorphType(ctx: *anyopaque, name: ast.StrId) ?types.TypeId {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        var i: usize = self.monomorph_context_stack.items.len;
        while (i > 0) {
            i -= 1;
            if (self.monomorph_context_stack.items[i].lookupType(name)) |ty| {
                return ty;
            }
        }
        return null;
    }

    fn mlirCreateEnv(ctx: *anyopaque) anyerror!*anyopaque {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        const env = try self.gpa.create(Env);
        env.* = Env.init(self.gpa);
        return @ptrCast(env);
    }

    fn mlirDestroyEnv(ctx: *anyopaque, env_ptr: *anyopaque) void {
        const self: *LowerTir = @ptrCast(@alignCast(ctx));
        const env: *Env = @ptrCast(@alignCast(env_ptr));
        env.deinit();
        self.gpa.destroy(env);
    }

    pub fn run(self: *LowerTir) !tir.TIR {
        return self.runAst(try self.requireMainAst());
    }

    pub fn runAst(self: *LowerTir, ast_unit: *ast.Ast) !tir.TIR {
        var module = try self.prepareModule(ast_unit);
        try self.lowerTopDecls(ast_unit, &module);
        try self.lowerDeferredMethods(ast_unit, &module);
        try self.monomorphizer.run(self, ast_unit, &module.builder, monomorphLowerCallback);
        return self.finishModule(module);
    }

    fn requireMainAst(self: *LowerTir) !*ast.Ast {
        const main_pkg = self.context.compilation_unit.packages.getPtr("main") orelse return error.PackageNotFound;
        return main_pkg.sources.entries.get(0).value.ast.?;
    }

    fn prepareModule(self: *LowerTir, ast_unit: *ast.Ast) !ModuleState {
        self.resetModuleCaches();
        var module = ModuleState.init(self.gpa, self.context.type_store);
        try self.mlir_lower.emitGlobalInit(self.mlirHooks(), ast_unit, &module.builder);
        return module;
    }

    fn lowerTopDecls(self: *LowerTir, ast_unit: *ast.Ast, module: *ModuleState) !void {
        const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
        for (decls) |decl_id| try self.lowerTopDecl(ast_unit, &module.builder, decl_id);
    }

    fn lowerDeferredMethods(self: *LowerTir, ast_unit: *ast.Ast, module: *ModuleState) !void {
        var method_it = ast_unit.type_info.method_table.iterator();
        while (method_it.next()) |entry| {
            const method = entry.value_ptr.*;
            const decl_id = method.decl_id;
            if (self.method_lowered.contains(decl_id.toRaw())) continue;
            const name = try self.methodSymbolName(ast_unit, decl_id);
            try self.tryLowerNamedFunction(ast_unit, &module.builder, decl_id, name, true);
        }
    }

    fn finishModule(self: *LowerTir, module: ModuleState) tir.TIR {
        _ = self;
        return module.intoResult();
    }

    fn resetModuleCaches(self: *LowerTir) void {
        self.module_call_cache.clearRetainingCapacity();
        self.method_lowered.clearRetainingCapacity();
    }

    // ============================
    // Utilities / common helpers
    // ============================

    fn resolveArrayLen(self: *LowerTir, a: *ast.Ast, size_expr: ast.ExprId, loc: tir.OptLocId) !usize {
        const value = self.runComptimeExpr(a, size_expr, self.context.type_store.tUsize(), &[_]Pipeline.ComptimeBinding{}) catch {
            try self.reportArrayLenError(a, loc);
            return error.ComptimeEvalFailed;
        };

        return switch (value) {
            .Int => |i| @intCast(i),
            else => blk: {
                try self.reportArrayLenError(a, loc);
                break :blk error.ComptimeEvalFailed;
            },
        };
    }

    fn reportArrayLenError(self: *LowerTir, a: *ast.Ast, loc: tir.OptLocId) !void {
        if (loc.isNone()) return;
        try self.context.diags.addError(a.exprs.locs.get(loc.unwrap()), .array_size_not_integer_literal, .{});
    }

    const LowerMode = enum { rvalue, lvalue_addr };

    fn isVoid(self: *const LowerTir, ty: types.TypeId) bool {
        return self.context.type_store.index.kinds.items[ty.toRaw()] == .Void;
    }

    const DefaultLocResolver = struct {
        fn resolve(
            _: *const LowerTir,
            _: *ast.Ast,
            comptime _: anytype,
            row: anytype,
        ) tir.OptLocId {
            if (comptime @hasField(@TypeOf(row), "loc")) {
                return tir.OptLocId.some(@field(row, "loc"));
            }
            if (comptime @hasField(@TypeOf(row), "opt_loc")) {
                const opt_loc = @field(row, "opt_loc");
                return if (opt_loc.isNone()) tir.OptLocId.none() else tir.OptLocId.some(opt_loc.unwrap());
            }
            return tir.OptLocId.none();
        }
    };

    const StmtLocResolver = struct {
        fn resolve(self: *const LowerTir, a: *ast.Ast, comptime tag: ast.StmtKind, row: anytype) tir.OptLocId {
            return switch (tag) {
                .Expr => self.exprOptLoc(a, row.expr),
                .Decl => blk: {
                    const decl_row = a.exprs.Decl.get(row.decl);
                    break :blk tir.OptLocId.some(decl_row.loc);
                },
                else => DefaultLocResolver.resolve(self, a, tag, row),
            };
        }
    };

    fn optNodeLoc(
        self: *const LowerTir,
        a: *ast.Ast,
        arena: anytype,
        id: anytype,
        comptime KindEnum: type,
        comptime Resolver: type,
    ) tir.OptLocId {
        const kind = arena.index.kinds.items[id.toRaw()];
        inline for (@typeInfo(KindEnum).@"enum".fields) |field| {
            const tag: KindEnum = @enumFromInt(field.value);
            if (tag == kind) {
                const row = arena.get(tag, id);
                return Resolver.resolve(self, a, tag, row);
            }
        }
        return tir.OptLocId.none();
    }

    fn exprOptLoc(self: *const LowerTir, a: *ast.Ast, id: ast.ExprId) tir.OptLocId {
        return self.optNodeLoc(a, a.exprs, id, ast.ExprKind, DefaultLocResolver);
    }

    fn optExprOptLoc(self: *const LowerTir, a: *ast.Ast, id: ast.OptExprId) tir.OptLocId {
        return if (id.isNone()) tir.OptLocId.none() else self.exprOptLoc(a, id.unwrap());
    }

    fn patternOptLoc(self: *const LowerTir, a: *ast.Ast, id: ast.PatternId) tir.OptLocId {
        return self.optNodeLoc(a, a.pats, id, ast.PatternKind, DefaultLocResolver);
    }

    fn optPatternOptLoc(self: *const LowerTir, a: *ast.Ast, id: ast.OptPatternId) tir.OptLocId {
        return if (id.isNone()) tir.OptLocId.none() else self.patternOptLoc(a, id.unwrap());
    }

    fn stmtOptLoc(self: *const LowerTir, a: *ast.Ast, id: ast.StmtId) tir.OptLocId {
        return self.optNodeLoc(a, a.stmts, id, ast.StmtKind, StmtLocResolver);
    }

    fn emitUndefValue(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        ty: types.TypeId,
        loc: tir.OptLocId,
        allow_void: bool,
    ) tir.ValueId {
        if (!allow_void and self.isVoid(ty)) {
            return blk.builder.tirValue(.ConstUndef, blk, self.context.type_store.tAny(), loc, .{});
        }
        return blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{});
    }

    fn tryWrapIntoErrorSet(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        value: tir.ValueId,
        got: types.TypeId,
        want: types.TypeId,
        loc: tir.OptLocId,
    ) ?tir.ValueId {
        const ts = self.context.type_store;
        if (ts.index.kinds.items[want.toRaw()] != .ErrorSet) return null;

        const es = ts.get(.ErrorSet, want);
        var fields = [_]types.TypeStore.StructFieldArg{
            .{ .name = blk.builder.intern("Ok"), .ty = es.value_ty },
            .{ .name = blk.builder.intern("Err"), .ty = es.error_ty },
        };
        const payload_ty = ts.mkUnion(fields[0..]);

        if (got.toRaw() == es.value_ty.toRaw()) {
            const ok_tag = blk.builder.tirValue(.ConstInt, blk, ts.tI32(), loc, .{ .value = 0 });
            const payload = blk.builder.tirValue(.UnionMake, blk, payload_ty, loc, .{
                .field_index = 0,
                .value = value,
            });
            return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = ok_tag },
                .{ .index = 1, .name = .none(), .value = payload },
            }, loc);
        }

        if (got.toRaw() == es.error_ty.toRaw()) {
            const err_tag = blk.builder.tirValue(.ConstInt, blk, ts.tI32(), loc, .{ .value = 1 });
            const payload = blk.builder.tirValue(.UnionMake, blk, payload_ty, loc, .{
                .field_index = 1,
                .value = value,
            });
            return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = err_tag },
                .{ .index = 1, .name = .none(), .value = payload },
            }, loc);
        }

        return null;
    }

    fn tryCoerceOptional(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        value: tir.ValueId,
        got: types.TypeId,
        want: types.TypeId,
        loc: tir.OptLocId,
    ) ?tir.ValueId {
        const ts = self.context.type_store;
        if (ts.index.kinds.items[want.toRaw()] != .Optional) return null;

        const opt = ts.get(.Optional, want);
        const bool_ty = ts.tBool();

        if (ts.index.kinds.items[got.toRaw()] == .Optional) {
            const got_opt = ts.get(.Optional, got);
            if (got_opt.elem.eq(opt.elem)) return value;

            const flag = blk.builder.extractField(blk, bool_ty, value, 0, loc);
            var payload = blk.builder.extractField(blk, got_opt.elem, value, 1, loc);
            payload = self.emitCoerce(blk, payload, got_opt.elem, opt.elem, loc);
            return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = flag },
                .{ .index = 1, .name = .none(), .value = payload },
            }, loc);
        }

        const payload = self.emitCoerce(blk, value, got, opt.elem, loc);
        const tag = blk.builder.tirValue(.ConstBool, blk, bool_ty, loc, .{ .value = true });
        return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
            .{ .index = 0, .name = .none(), .value = tag },
            .{ .index = 1, .name = .none(), .value = payload },
        }, loc);
    }

    fn tryCoerceNumeric(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        value: tir.ValueId,
        got: types.TypeId,
        want: types.TypeId,
        loc: tir.OptLocId,
    ) ?tir.ValueId {
        const ts = self.context.type_store;
        if (!isNumericKind(ts.index.kinds.items[got.toRaw()])) return null;
        if (!isNumericKind(ts.index.kinds.items[want.toRaw()])) return null;
        return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = value });
    }

    fn tryCoercePointer(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        value: tir.ValueId,
        got: types.TypeId,
        want: types.TypeId,
        loc: tir.OptLocId,
    ) ?tir.ValueId {
        const ts = self.context.type_store;
        if (ts.index.kinds.items[got.toRaw()] != .Ptr) return null;
        if (ts.index.kinds.items[want.toRaw()] != .Ptr) return null;
        return blk.builder.tirValue(.CastBit, blk, want, loc, .{ .value = value });
    }

    inline fn isNumericKind(kind: types.TypeKind) bool {
        return switch (kind) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64 => true,
            else => false,
        };
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

        if (self.tryWrapIntoErrorSet(blk, v, got, want, loc)) |coerced| return coerced;
        if (self.tryCoerceOptional(blk, v, got, want, loc)) |coerced| return coerced;
        if (self.tryCoerceNumeric(blk, v, got, want, loc)) |coerced| return coerced;
        if (self.tryCoercePointer(blk, v, got, want, loc)) |coerced| return coerced;

        return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = v });
    }

    // ============================
    // Top-level lowering
    // ============================

    fn lowerTopDecl(self: *LowerTir, a: *ast.Ast, b: *Builder, did: ast.DeclId) !void {
        const d = a.exprs.Decl.get(did);
        const kind = a.exprs.index.kinds.items[d.value.toRaw()];

        if (kind == .MlirBlock and d.pattern.isNone()) {
            return; // handled by MLIR global initializer synthesis
        }

        if (kind == .FunctionLit) {
            try self.lowerFunctionDecl(a, b, did, d);
            return;
        }

        if (!d.pattern.isNone()) {
            try self.lowerGlobalDecl(a, b, did, d);
        }
    }

    fn lowerFunctionDecl(
        self: *LowerTir,
        a: *ast.Ast,
        b: *Builder,
        did: ast.DeclId,
        decl: ast.Rows.Decl,
    ) !void {
        const fn_lit = a.exprs.get(.FunctionLit, decl.value);
        if (fn_lit.flags.is_extern) return;

        const is_method = !decl.method_path.isNone();
        if (is_method and self.method_lowered.contains(did.toRaw())) return;

        const name = if (!decl.pattern.isNone())
            self.bindingNameOfPattern(a, decl.pattern.unwrap())
        else if (is_method)
            try self.methodSymbolName(a, did)
        else
            null;

        const symbol = name orelse return;
        if (!self.canLowerNamedFunction(a, decl.value)) return;

        try self.lowerFunction(a, b, symbol, decl.value, null);

        if (is_method) {
            try self.method_lowered.put(did.toRaw(), {});
        }
    }

    fn canLowerNamedFunction(self: *LowerTir, a: *ast.Ast, expr_id: ast.ExprId) bool {
        const fn_ty_opt = self.getExprType(a, expr_id) orelse return false;
        if (self.context.type_store.getKind(fn_ty_opt) != .Function) return false;

        const fn_ty_info = self.context.type_store.get(.Function, fn_ty_opt);
        const param_tys = self.context.type_store.type_pool.slice(fn_ty_info.params);
        for (param_tys) |param_ty| {
            if (self.isAny(param_ty)) return false;
        }

        const fn_lit = a.exprs.get(.FunctionLit, expr_id);
        const params = a.exprs.param_pool.slice(fn_lit.params);
        var leading_comptime: usize = 0;
        while (leading_comptime < params.len and a.exprs.Param.get(params[leading_comptime]).is_comptime)
            leading_comptime += 1;

        return leading_comptime == 0;
    }

    fn lowerGlobalDecl(
        self: *LowerTir,
        a: *ast.Ast,
        b: *Builder,
        did: ast.DeclId,
        decl: ast.Rows.Decl,
    ) !void {
        const name = self.bindingNameOfPattern(a, decl.pattern.unwrap()) orelse return;
        const ty = getDeclType(a, did) orelse return;
        if (self.constInitFromLiteral(a, decl.value, ty)) |ci| {
            _ = b.addGlobalWithInit(name, ty, ci);
        } else {
            _ = b.addGlobal(name, ty);
        }
    }

    fn lowerAttrs(
        self: *LowerTir,
        a: *ast.Ast,
        b: *Builder,
        range: ast.OptRangeAttr,
    ) !tir.RangeAttribute {
        if (range.isNone()) return .empty();
        const attr_ids = a.exprs.attr_pool.slice(range.asRange());
        if (attr_ids.len == 0) return .empty();

        const tmp = try self.gpa.alloc(tir.AttributeId, attr_ids.len);
        defer self.gpa.free(tmp);

        for (attr_ids, 0..) |aid, idx| {
            const row = a.exprs.Attribute.get(aid);
            tmp[idx] = b.t.instrs.Attribute.add(self.gpa, .{ .name = row.name, .value = .none() });
        }

        return b.t.instrs.attribute_pool.pushMany(self.gpa, tmp);
    }

    const FunctionLoweringData = struct {
        type_info: types.TypeStore.Rows.Function,
        literal: ast.Rows.FunctionLit,
        skip_params: usize,
    };

    const FunctionFrame = struct {
        block: Builder.Block,
        env: Env,

        fn deinit(self: *FunctionFrame) void {
            self.env.deinit();
        }
    };

    fn prepareFunctionLowering(
        self: *LowerTir,
        a: *ast.Ast,
        fun_eid: ast.ExprId,
        ctx: ?*const monomorphize.MonomorphizationContext,
    ) ?FunctionLoweringData {
        const fid = if (ctx) |c|
            c.specialized_ty
        else
            (self.getExprType(a, fun_eid) orelse return null);
        if (self.context.type_store.index.kinds.items[fid.toRaw()] != .Function) return null;

        return .{
            .type_info = self.context.type_store.get(.Function, fid),
            .literal = a.exprs.get(.FunctionLit, fun_eid),
            .skip_params = if (ctx) |c| c.skip_params else 0,
        };
    }

    fn beginFunctionFrame(
        self: *LowerTir,
        b: *Builder,
        f: *Builder.Function,
    ) !FunctionFrame {
        return .{
            .block = try b.beginBlock(f),
            .env = Env.init(self.gpa),
        };
    }

    fn shouldSkipMlirLowering(self: *LowerTir, a: *ast.Ast, fn_lit: ast.Rows.FunctionLit) bool {
        if (fn_lit.attrs.isNone()) return false;
        const attrs = a.exprs.attr_pool.slice(fn_lit.attrs.asRange());
        if (attrs.len == 0) return false;
        const mlir_fn_str = a.exprs.strs.intern("mlir_fn");
        for (attrs) |aid| {
            const row = a.exprs.Attribute.get(aid);
            if (row.name.eq(mlir_fn_str)) return true;
        }
        return false;
    }

    fn bindMonomorphizationValues(
        self: *LowerTir,
        a: *ast.Ast,
        frame: *FunctionFrame,
        ctx: ?*const monomorphize.MonomorphizationContext,
    ) !void {
        if (ctx == null) return;
        for (ctx.?.bindings) |binding| {
            switch (binding.kind) {
                .type_param => {},
                .value_param => |vp| {
                    const const_val = try self.constValueFromComptime(&frame.block, vp.ty, vp.value);
                    try frame.env.bind(binding.name, .{
                        .value = const_val,
                        .ty = vp.ty,
                        .is_slot = false,
                    });
                },
                .runtime_param => {},
            }
        }
    }

    fn bindRuntimeParams(
        self: *LowerTir,
        a: *ast.Ast,
        frame: *FunctionFrame,
        f: *Builder.Function,
        runtime_param_tys: []const types.TypeId,
        params: []const ast.ParamId,
        skip_params: usize,
    ) !void {
        var runtime_index: usize = 0;
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            if (i < skip_params) continue;
            const param_row = a.exprs.Param.get(params[i]);
            if (param_row.pat.isNone()) {
                runtime_index += 1;
                continue;
            }
            const pname = self.bindingNameOfPattern(a, param_row.pat.unwrap()) orelse {
                runtime_index += 1;
                continue;
            };
            const pty = runtime_param_tys[runtime_index];
            const value = f.param_vals.items[runtime_index];
            try frame.env.bind(pname, .{ .value = value, .ty = pty, .is_slot = false });
            runtime_index += 1;
        }
    }

    fn lowerFunction(
        self: *LowerTir,
        a: *ast.Ast,
        b: *Builder,
        name: StrId,
        fun_eid: ast.ExprId,
        ctx: ?*const monomorphize.MonomorphizationContext,
    ) !void {
        const data = self.prepareFunctionLowering(a, fun_eid, ctx) orelse return;

        var override_scope = try self.beginExprTypeOverrideScope();
        defer override_scope.deinit();

        if (self.shouldSkipMlirLowering(a, data.literal)) return;

        const attrs = try self.lowerAttrs(a, b, data.literal.attrs);
        var f = try b.beginFunction(name, data.type_info.result, data.type_info.is_variadic, attrs);

        const params = a.exprs.param_pool.slice(data.literal.params);
        const runtime_param_tys = self.context.type_store.type_pool.slice(data.type_info.params);
        var runtime_index: usize = 0;
        var i: usize = 0;
        while (i < params.len) : (i += 1) {
            if (i < data.skip_params) continue;
            const p = a.exprs.Param.get(params[i]);
            const pname = if (!p.pat.isNone()) self.bindingNameOfPattern(a, p.pat.unwrap()) else null;
            _ = try b.addParam(&f, pname, runtime_param_tys[runtime_index]);
            runtime_index += 1;
        }

        var frame = try self.beginFunctionFrame(b, &f);
        defer frame.deinit();

        try self.bindMonomorphizationValues(a, &frame, ctx);
        try self.bindRuntimeParams(a, &frame, &f, runtime_param_tys, params, data.skip_params);

        if (!data.literal.body.isNone()) {
            const body_id = data.literal.body.unwrap();
            {
                var scope = try frame.env.pushScope();
                defer scope.deinit();
                try self.lowerExprAsStmtList(a, &frame.env, &f, &frame.block, body_id);
            }
        }

        const fn_loc = tir.OptLocId.some(data.literal.loc);
        if (frame.block.term.isNone()) {
            try b.setReturn(&frame.block, tir.OptValueId.none(), fn_loc);
        }

        try b.endBlock(&f, frame.block);
        try b.endFunction(f);
    }

    fn lowerSpecializedFunction(
        self: *LowerTir,
        a: *ast.Ast,
        b: *Builder,
        req: *const monomorphize.MonomorphizationRequest,
    ) !void {
        var scope = try self.pushMonomorphRequest(req);
        defer scope.deinit();

        const active_ctx = self.currentMonomorphContext() orelse return error.LoweringBug;
        const decl = a.exprs.Decl.get(req.decl_id);
        try self.lowerFunction(a, b, req.mangled_name, decl.value, active_ctx);
    }

    fn monomorphLowerCallback(
        ctx: ?*anyopaque,
        a: *ast.Ast,
        b: *Builder,
        req: *const monomorphize.MonomorphizationRequest,
    ) anyerror!void {
        if (ctx == null) return error.LoweringBug;
        const self: *LowerTir = @ptrCast(@alignCast(ctx.?));
        try self.lowerSpecializedFunction(a, b, req);
    }

    // Lower a block or expression as a list of statements (ignores resulting value)
    fn lowerExprAsStmtList(self: *LowerTir, a: *ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId) !void {
        if (a.exprs.index.kinds.items[id.toRaw()] == .Block) {
            const b = a.exprs.get(.Block, id);
            const stmts = a.stmts.stmt_pool.slice(b.items);
            const defer_mark = env.deferMark();
            {
                var scope = try env.pushScope();
                defer scope.deinit();
                for (stmts) |sid| {
                    if (!blk.term.isNone()) break;
                    try self.lowerStmt(a, env, f, blk, sid);
                }
                if (blk.term.isNone()) {
                    const slice = env.pendingDefers(defer_mark);
                    if (slice.len > 0) try self.emitDeferSlice(a, env, f, blk, slice, false);
                }
                env.truncateDefers(defer_mark);
            }
        } else {
            _ = try self.lowerExpr(a, env, f, blk, id, null, .rvalue);
        }
    }

    /// Run "normal" (non-err) defers scheduled at or after `from`, in reverse order,
    /// and then truncate the defer stack back to `from`.
    fn runNormalDefersFrom(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        mark: DeferMark,
    ) !void {
        const slice = env.pendingDefers(mark);
        if (slice.len > 0) {
            try self.emitDeferSlice(a, env, f, blk, slice, false);
        }
        env.truncateDefers(mark);
    }

    fn hasErrDefersSince(_: *LowerTir, env: *Env, mark: DeferMark) bool {
        return env.hasErrDefersSince(mark);
    }

    fn emitDeferSlice(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        slice: []const DeferEntry,
        want_err: bool,
    ) !void {
        var idx: usize = slice.len;
        while (idx > 0) {
            idx -= 1;
            const ent = slice[idx];
            if (ent.is_err == want_err) {
                _ = try self.lowerExpr(a, env, f, blk, ent.expr, null, .rvalue);
            }
        }
    }

    fn runDefersForLoopExit(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        lc: LoopCtx,
    ) !void {
        const slice = env.pendingDefers(lc.defer_mark);
        if (slice.len == 0) return;
        var idx: usize = slice.len;
        while (idx > 0) {
            idx -= 1;
            const ent = slice[idx];
            if (!ent.is_err) {
                _ = try self.lowerExpr(a, env, f, blk, ent.expr, null, .rvalue);
            }
        }
    }

    fn lowerBreak(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        sid: ast.StmtId,
    ) !void {
        const br = a.stmts.get(.Break, sid);
        const loc = self.stmtOptLoc(a, sid);
        const lc_ptr = self.loop_stack.find(br.label) orelse return error.LoweringBug;
        const lc = lc_ptr.*;
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
    }

    fn lowerContinue(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        sid: ast.StmtId,
    ) !void {
        const cid = a.stmts.get(.Continue, sid);
        const loc = self.stmtOptLoc(a, sid);
        const lc = self.loop_stack.find(cid.label) orelse return error.LoweringBug;
        try self.runDefersForLoopExit(a, env, f, blk, lc.*);
        switch (lc.continue_info) {
            .none => try f.builder.br(blk, lc.continue_block, &.{}, loc),
            .range => |info| try f.builder.br(blk, info.update_block, &.{info.idx_value}, loc),
        }
    }

    fn lowerDecl(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        sid: ast.StmtId,
    ) !void {
        const drow = a.stmts.get(.Decl, sid);
        const d = a.exprs.Decl.get(drow.decl);
        const value_ty = self.getExprType(a, d.value) orelse self.context.type_store.tAny();
        const decl_ty = getDeclType(a, drow.decl) orelse value_ty;
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
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        sid: ast.StmtId,
    ) !void {
        const r = a.stmts.get(.Return, sid);
        const stmt_loc = self.stmtOptLoc(a, sid);
        const defer_mark = env.rootDeferMark();

        if (!r.value.isNone()) {
            const frow = f.builder.t.funcs.Function.get(f.id);
            const expect = frow.result;
            const want: ?types.TypeId = if (self.isVoid(expect)) null else expect;
            const value_expr = r.value.unwrap();
            const value_loc = self.exprOptLoc(a, value_expr);
            const v_raw = try self.lowerExpr(a, env, f, blk, value_expr, want, .rvalue);
            var v = v_raw;
            if (!self.isVoid(expect)) {
                const got_ty = self.getExprType(a, value_expr) orelse expect;
                v = self.emitCoerce(blk, v_raw, got_ty, expect, value_loc);
            }

            const expect_kind = self.context.type_store.index.kinds.items[expect.toRaw()];
            const has_err_defers = expect_kind == .ErrorSet and self.hasErrDefersSince(env, defer_mark);

            if (has_err_defers) {
                var err_blk = try f.builder.beginBlock(f);
                var ok_blk = try f.builder.beginBlock(f);
                const tag_ty = self.context.type_store.tI32();
                const tag = blk.builder.extractField(blk, tag_ty, v, 0, value_loc);
                const zero = blk.builder.tirValue(.ConstInt, blk, tag_ty, value_loc, .{ .value = 0 });
                const is_err = blk.builder.binBool(blk, .CmpNe, tag, zero, value_loc);
                const br_cond = self.forceLocalCond(blk, is_err, value_loc);
                try f.builder.condBr(blk, br_cond, err_blk.id, &.{}, ok_blk.id, &.{}, stmt_loc);

                const defer_slice = env.pendingDefers(defer_mark);

                try self.emitDeferSlice(a, env, f, &err_blk, defer_slice, true);
                try self.emitDeferSlice(a, env, f, &err_blk, defer_slice, false);
                try f.builder.setReturnVal(&err_blk, v, stmt_loc);
                try f.builder.endBlock(f, err_blk);

                try self.emitDeferSlice(a, env, f, &ok_blk, defer_slice, false);
                try f.builder.setReturnVal(&ok_blk, v, stmt_loc);
                try f.builder.endBlock(f, ok_blk);

                env.truncateDefers(defer_mark);
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

    fn lowerAssign(self: *LowerTir, a: *ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, sid: ast.StmtId) !void {
        const as = a.stmts.get(.Assign, sid);
        const stmt_loc = self.stmtOptLoc(a, sid);
        const rty = self.getExprType(a, as.left) orelse return error.LoweringBug;

        if (a.exprs.index.kinds.items[as.left.toRaw()] == .Ident) {
            const ident = a.exprs.get(.Ident, as.left);
            if (env.lookup(ident.name)) |bnd| {
                if (!bnd.is_slot) {
                    const rhs = try self.lowerExpr(a, env, f, blk, as.right, rty, .rvalue);
                    try env.bind(ident.name, .{ .value = rhs, .ty = rty, .is_slot = false });
                    return;
                }
            }
        }

        const lhs_ptr = try self.lowerExpr(a, env, f, blk, as.left, null, .lvalue_addr);
        const rhs = try self.lowerExpr(a, env, f, blk, as.right, rty, .rvalue);
        _ = f.builder.tirValue(.Store, blk, rty, stmt_loc, .{ .ptr = lhs_ptr, .value = rhs, .@"align" = 0 });
    }

    fn lowerStmt(self: *LowerTir, a: *ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, sid: ast.StmtId) !void {
        const k = a.stmts.index.kinds.items[sid.toRaw()];
        switch (k) {
            .Expr => {
                const e = a.stmts.get(.Expr, sid).expr;
                _ = try self.lowerExpr(a, env, f, blk, e, null, .rvalue);
            },
            .Defer => {
                const d = a.stmts.get(.Defer, sid);
                try env.addDefer(d.expr, false);
            },
            .ErrDefer => {
                const d = a.stmts.get(.ErrDefer, sid);
                try env.addDefer(d.expr, true);
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

    const MethodCallContext = struct {
        binding: types.TypeInfo.MethodBinding,
        decl: ?ast.DeclId,
        args: []const ast.ExprId,
        owned_args: []ast.ExprId = @constCast(&[_]ast.ExprId{}),

        fn deinit(self: *MethodCallContext, gpa: std.mem.Allocator) void {
            if (self.owned_args.len != 0) gpa.free(self.owned_args);
        }
    };

    const PreparedCall = struct {
        callee: CalleeInfo,
        args: []const ast.ExprId,
        method_ctx: MethodCallContext = undefined,
        has_method_ctx: bool = false,
        has_method_binding: bool = false,
        method_binding: types.TypeInfo.MethodBinding = undefined,
        method_decl: ?ast.DeclId = null,
        param_tys: []const types.TypeId = &.{},
        fixed_count: usize = 0,
        is_variadic: bool = false,

        fn release(self: *PreparedCall, gpa: std.mem.Allocator) void {
            if (self.has_method_ctx) self.method_ctx.deinit(gpa);
        }

        fn setMethodCtx(self: *PreparedCall, ctx: MethodCallContext) void {
            self.method_ctx = ctx;
            self.has_method_ctx = true;
            self.setMethodBinding(ctx.binding);
            self.method_decl = ctx.decl;
            self.args = ctx.args;
        }

        fn setMethodBinding(self: *PreparedCall, binding: types.TypeInfo.MethodBinding) void {
            self.method_binding = binding;
            self.has_method_binding = true;
        }

        fn binding(self: *PreparedCall) ?*types.TypeInfo.MethodBinding {
            if (!self.has_method_binding) return null;
            return &self.method_binding;
        }

        fn bindingConst(self: *const PreparedCall) ?*const types.TypeInfo.MethodBinding {
            if (!self.has_method_binding) return null;
            return &self.method_binding;
        }
    };

    const CallArgBuffer = struct {
        allocator: std.mem.Allocator,
        values: []tir.ValueId,

        fn init(allocator: std.mem.Allocator, count: usize) !CallArgBuffer {
            if (count == 0) {
                return .{ .allocator = allocator, .values = &[_]tir.ValueId{} };
            }
            return .{ .allocator = allocator, .values = try allocator.alloc(tir.ValueId, count) };
        }

        fn deinit(self: *CallArgBuffer) void {
            if (self.values.len != 0) self.allocator.free(self.values);
            self.values = &[_]tir.ValueId{};
        }
    };

    fn mangleMonomorphName(
        self: *LowerTir,
        base: StrId,
        bindings: []const monomorphize.BindingInfo,
    ) !StrId {
        var buf = std.ArrayList(u8).init(self.gpa);
        defer buf.deinit();

        try buf.appendSlice(self.gpa, self.context.type_store.strs.get(base));
        if (bindings.len == 0) return self.context.type_store.strs.intern(buf.items);

        var writer = buf.writer(self.gpa);
        try writer.print("_M", .{});
        for (bindings) |info| {
            try writer.print("_", .{});
            switch (info.kind) {
                .type_param => |ty| try writer.print("T{}", .{ty.toRaw()}),
                .runtime_param => |ty| try writer.print("R{}", .{ty.toRaw()}),
                .value_param => |vp| {
                    const hash = comp.hashValue(vp.value);
                    try writer.print("V{}x{X}", .{ vp.ty.toRaw(), hash });
                },
            }
        }

        return self.context.type_store.strs.intern(buf.items);
    }

    fn methodSymbolName(
        self: *LowerTir,
        binding: types.TypeInfo.MethodBinding,
    ) !StrId {
        var buf = std.ArrayList(u8).init(self.gpa);
        defer buf.deinit();

        var writer = buf.writer(self.gpa);
        try self.context.type_store.fmt(binding.owner_type, writer);
        try writer.print("__{s}", .{self.context.type_store.strs.get(binding.method_name)});
        return self.context.type_store.strs.intern(buf.items);
    }

    fn resolveMethodCall(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        row: ast.Rows.Call,
        callee: *CalleeInfo,
    ) !?MethodCallContext {
        if (a.exprs.index.kinds.items[row.callee.toRaw()] != .FieldAccess) return null;

        var binding = a.type_info.getMethodBinding(row.callee);
        if (binding == null) {
            binding = try self.computeMethodBinding(a, env, row.callee);
            if (binding == null) return null;
            a.type_info.setMethodBinding(row.callee, binding.?) catch {};
        }
        const resolved = binding.?;

        var ctx = MethodCallContext{
            .binding = resolved,
            .decl = if (resolved.builtin != null) null else resolved.decl_id,
            .args = a.exprs.expr_pool.slice(row.args),
        };

        if (resolved.requires_implicit_receiver) {
            const field_expr = a.exprs.get(.FieldAccess, row.callee);
            ctx.owned_args = try self.gpa.alloc(ast.ExprId, ctx.args.len + 1);
            ctx.owned_args[0] = field_expr.parent;
            std.mem.copyForwards(ast.ExprId, ctx.owned_args[1..], ctx.args);
            ctx.args = ctx.owned_args;
        }

        callee.fty = resolved.func_type;
        if (resolved.builtin != null) return ctx;

        const symbol = try self.methodSymbolName(resolved);
        callee.name = symbol;

        return ctx;
    }

    fn computeMethodBinding(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        field_expr_id: ast.ExprId,
    ) !?types.TypeInfo.MethodBinding {
        if (a.exprs.index.kinds.items[field_expr_id.toRaw()] != .FieldAccess) return null;

        const field_expr = a.exprs.get(.FieldAccess, field_expr_id);
        const refined = try self.refineExprType(a, env, field_expr.parent, self.getExprType(a, field_expr.parent));
        const receiver_ty = refined orelse return null;

        const owner = self.deriveMethodOwner(receiver_ty);
        const entry = a.type_info.getMethod(owner.owner, field_expr.field) orelse return null;

        const match = self.matchReceiver(entry, receiver_ty, owner) orelse return null;

        return types.TypeInfo.MethodBinding{
            .owner_type = entry.owner_type,
            .method_name = entry.method_name,
            .decl_id = entry.decl_id,
            .func_type = entry.func_type,
            .self_param_type = entry.self_param_type,
            .receiver_kind = entry.receiver_kind,
            .requires_implicit_receiver = match.implicit,
            .needs_addr_of = match.needs_addr,
            .builtin = entry.builtin,
        };
    }

    const MethodOwner = struct {
        owner: types.TypeId,
        parent_kind: types.TypeKind,
    };

    fn deriveMethodOwner(self: *LowerTir, receiver_ty: types.TypeId) MethodOwner {
        const ts = self.context.type_store;
        const parent_kind = ts.getKind(receiver_ty);
        return switch (parent_kind) {
            .Ptr => .{ .owner = ts.get(.Ptr, receiver_ty).elem, .parent_kind = parent_kind },
            .TypeType => .{ .owner = ts.get(.TypeType, receiver_ty).of, .parent_kind = parent_kind },
            else => .{ .owner = receiver_ty, .parent_kind = parent_kind },
        };
    }

    fn matchReceiver(
        self: *LowerTir,
        entry: types.TypeInfo.MethodEntry,
        receiver_ty: types.TypeId,
        owner: MethodOwner,
    ) ?struct { implicit: bool, needs_addr: bool } {
        const ts = self.context.type_store;
        if (entry.receiver_kind == .none) return .{ .implicit = false, .needs_addr = false };

        if (owner.parent_kind == .TypeType) return .{ .implicit = false, .needs_addr = false };

        var needs_addr = false;
        switch (entry.receiver_kind) {
            .value => {
                if (!receiver_ty.eq(owner.owner)) return null;
            },
            .pointer, .pointer_const => {
                if (owner.parent_kind == .Ptr) {
                    if (!ts.get(.Ptr, receiver_ty).elem.eq(owner.owner)) return null;
                } else if (receiver_ty.eq(owner.owner)) {
                    needs_addr = true;
                } else {
                    return null;
                }
            },
            .none => unreachable,
        }

        return .{ .implicit = true, .needs_addr = needs_addr };
    }

    // fn resolveModuleFieldCallee(
    //     self: *LowerTir,
    //     a: *ast.Ast,
    //     f: *Builder.FunctionFrame,
    //     field_access: ast.ExprId,
    // ) !?StrId {
    //     const fr = a.exprs.get(.FieldAccess, field_access);
    //     const parent_kind = a.exprs.index.kinds.items[fr.parent.toRaw()];
    //     if (parent_kind != .Ident) return null;
    //
    //     const ident = a.exprs.get(.Ident, fr.parent);
    //     const alias_name = a.exprs.strs.get(ident.name);
    //     // const info_ptr = self.module_aliases.get(alias_name) orelse return null;
    //     const info = info_ptr;
    //
    //     const key = moduleCallKey(ident.name, fr.field);
    //     if (self.module_call_cache.get(key)) |existing| return existing;
    //
    //     const field_name = a.exprs.strs.get(fr.field);
    //
    //     var interned: StrId = undefined;
    //     if (self.moduleFieldIsExtern(info, field_name)) {
    //         interned = f.builder.intern(field_name);
    //     } else {
    //         interned = f.builder.intern(field_name);
    //     }
    //
    //     if ((self.getExprType(field_access)) == null) {
    //         const lookup_res = self.context.module_graph.lookupExport(
    //             self.import_base_dir,
    //             info.import_path,
    //             field_name,
    //             .tir,
    //         ) catch null;
    //         if (lookup_res) |lu| {
    //             if (lu.ty) |ty| {
    //                 self.type_info.ensureExpr(self.gpa, field_access) catch {};
    //                 self.type_info.setExprType(field_access, ty);
    //             }
    //         }
    //     }
    //
    //     try self.module_call_cache.put(key, interned);
    //     return interned;
    // }

    fn resolveCallee(self: *LowerTir, a: *ast.Ast, f: *Builder.FunctionFrame, row: ast.Rows.Call) !CalleeInfo {
        const ck = a.exprs.index.kinds.items[row.callee.toRaw()];
        if (ck == .Ident) {
            const nm = a.exprs.get(.Ident, row.callee).name;
            return .{ .name = nm, .fty = self.getExprType(a, row.callee) };
        }
        if (ck == .FieldAccess) {
            // if (try self.resolveModuleFieldCallee(a, f, row.callee)) |mangled|
            //     return .{ .name = mangled, .fty = self.getExprType(row.callee) };

            return .{
                .name = a.exprs.get(.FieldAccess, row.callee).field,
                .fty = self.getExprType(a, row.callee),
            };
        }
        return .{ .name = f.builder.intern("<indirect>"), .fty = self.getExprType(a, row.callee) };
    }

    // fn moduleFieldIsExtern(
    //     self: *LowerTir,
    //     info: ModuleAliasInfo,
    //     member_name: []const u8,
    // ) bool {
    //     const me = self.context.module_graph.ensureModule(self.import_base_dir, info.import_path, .tir) catch return false;
    //     const imported_ast = me.astRef();
    //     const decls = imported_ast.exprs.decl_pool.slice(imported_ast.unit.decls);
    //     var i: usize = 0;
    //     while (i < decls.len) : (i += 1) {
    //         const d = imported_ast.exprs.Decl.get(decls[i]);
    //         if (d.pattern.isNone()) continue;
    //         const pid = d.pattern.unwrap();
    //         const pk = imported_ast.pats.index.kinds.items[pid.toRaw()];
    //         if (pk != .Binding) continue;
    //         const binding = imported_ast.pats.get(.Binding, pid);
    //         const binding_name = imported_ast.exprs.strs.get(binding.name);
    //         if (!std.mem.eql(u8, binding_name, member_name)) continue;
    //
    //         const kind = imported_ast.exprs.index.kinds.items[d.value.toRaw()];
    //         if (kind != .FunctionLit) return false;
    //         const fn_lit = imported_ast.exprs.get(.FunctionLit, d.value);
    //         if (fn_lit.flags.is_extern) return true;
    //         // Treat function declarations without a body as extern. This covers
    //         // imported prototypes that were parsed via `extern proc` but lost
    //         // their flag metadata while being serialized through the module graph.
    //         if (fn_lit.body.isNone()) return true;
    //         return false;
    //     }
    //     return false;
    // }

    fn buildVariantItem(
        self: *LowerTir,
        a: *ast.Ast,
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
        a: *ast.Ast,
        expr: ast.ExprId,
        result_ty: types.TypeId,
        bindings: []const Pipeline.ComptimeBinding,
    ) !comp.ComptimeValue {
        var monomorph_scope = try self.pushComptimeBindings(bindings);
        defer monomorph_scope.deinit();

        const result_kind = self.context.type_store.getKind(result_ty);
        if (result_kind == .TypeType) {
            const tt = self.context.type_store.get(.TypeType, result_ty);
            if (!self.isAny(tt.of)) return .{ .Type = tt.of };
        }

        const expr_loc = self.exprOptLoc(a, expr);
        var thunk = try ComptimeThunk.init(self, a, result_ty, result_kind);
        defer thunk.deinit(self.gpa);

        const result_val = try thunk.lowerExpr(self, a, expr, result_ty);
        try self.monomorphizer.run(self, a, &thunk.builder, monomorphLowerCallback);
        try thunk.finalize(result_kind, if (result_kind == .Void) null else result_val, expr_loc);

        return try self.executeComptimeThunk(&thunk, result_kind);
    }

    fn executeComptimeThunk(
        self: *LowerTir,
        thunk: *ComptimeThunk,
        result_kind: types.TypeKind,
    ) !comp.ComptimeValue {
        const mlir_ctx = self.mlir_lower.ensureContext();
        var gen = codegen.Codegen.init(self.gpa, self.context, mlir_ctx);
        defer gen.deinit();

        const prev_debug_flag = codegen.enable_debug_info;
        codegen.enable_debug_info = false;
        defer codegen.enable_debug_info = prev_debug_flag;

        var mlir_module = try gen.emitModule(&thunk.tir);
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

        return ComptimeRuntime.decode(result_kind, func_ptr.?, &comptime_api);
    }

    fn emitConstValue(
        self: *LowerTir,
        blk: *Builder.BlockFrame,
        ty: types.TypeId,
        loc: tir.OptLocId,
        value: comp.ComptimeValue,
    ) !tir.ValueId {
        return switch (value) {
            .Int => |val| blk: {
                const casted = std.math.cast(u64, val) orelse return error.LoweringBug;
                break :blk blk.builder.tirValue(.ConstInt, blk, ty, loc, .{ .value = casted });
            },
            .Float => |val| blk.builder.tirValue(.ConstFloat, blk, ty, loc, .{ .value = val }),
            .Bool => |val| blk.builder.tirValue(.ConstBool, blk, ty, loc, .{ .value = val }),
            .Void => blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{}),
            .String => |s| blk.builder.tirValue(.ConstString, blk, ty, loc, .{ .text = blk.builder.intern(s) }),
            .Type => return error.UnsupportedComptimeType,
            .MlirType => blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{}),
            .MlirAttribute => blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{}),
            .MlirModule => blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{}),
        };
    }

    fn jitEvalComptimeBlock(
        self: *LowerTir,
        a: *ast.Ast,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
    ) !tir.ValueId {
        const cb = a.exprs.get(.ComptimeBlock, id);
        const result_ty = self.getExprType(a, cb.block) orelse return error.LoweringBug;
        const comptime_value = try self.runComptimeExpr(a, cb.block, result_ty, &[_]Pipeline.ComptimeBinding{});
        const loc = self.exprOptLoc(a, id);
        return self.emitConstValue(blk, result_ty, loc, comptime_value);
    }

    fn evalComptimeExprValue(
        self: *LowerTir,
        a: *ast.Ast,
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
        return self.emitConstValue(blk, ty, tir.OptLocId.none(), value);
    }

    fn constValueFromLiteral(self: *LowerTir, a: *ast.Ast, expr: ast.ExprId) !?comp.ComptimeValue {
        const payload = literalPayload(a, expr) orelse return null;
        return switch (payload) {
            .int => |value| comp.ComptimeValue{ .Int = value },
            .float => |value| comp.ComptimeValue{ .Float = value },
            .bool => |value| comp.ComptimeValue{ .Bool = value },
            .string => |sid| blk: {
                const text = a.exprs.strs.get(sid);
                const owned = try self.gpa.dupe(u8, text);
                break :blk comp.ComptimeValue{ .String = owned };
            },
        };
    }

    fn tryLowerComptimeApiCall(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        row: ast.Rows.Call,
        callee: CalleeInfo,
    ) !?tir.ValueId {
        const callee_name = self.context.type_store.strs.get(callee.name);
        if (!std.mem.eql(u8, callee_name, "get_type_by_name") and
            !std.mem.eql(u8, callee_name, "comptime_print") and
            !std.mem.eql(u8, callee_name, "type_of"))
        {
            return null;
        }

        const loc = self.exprOptLoc(a, id);
        const api_ptr_name = f.builder.intern("comptime_api_ptr");
        const api_ptr_bnd = env.lookup(api_ptr_name) orelse return error.LoweringBug;

        const ptr_ty = self.context.type_store.mkPtr(self.context.type_store.tU8(), false);
        const fn_ptr_ty = self.context.type_store.mkPtr(self.context.type_store.tVoid(), false);

        const comptime_api_struct_ty = self.context.type_store.mkStruct(&.{
            .{ .name = f.builder.intern("context"), .ty = ptr_ty },
            .{ .name = f.builder.intern("print"), .ty = fn_ptr_ty },
            .{ .name = f.builder.intern("get_type_by_name"), .ty = fn_ptr_ty },
            .{ .name = f.builder.intern("type_of"), .ty = fn_ptr_ty },
        });

        const comptime_api_ptr_ty = self.context.type_store.mkPtr(comptime_api_struct_ty, false);
        const typed_api_ptr = blk.builder.tirValue(.CastBit, blk, comptime_api_ptr_ty, loc, .{ .value = api_ptr_bnd.value });

        const ctx_ptr_ptr = blk.builder.gep(
            blk,
            self.context.type_store.mkPtr(ptr_ty, false),
            typed_api_ptr,
            &.{blk.builder.gepConst(0)},
            loc,
        );
        const ctx_ptr = blk.builder.tirValue(.Load, blk, ptr_ty, loc, .{ .ptr = ctx_ptr_ptr, .@"align" = 0 });

        const fn_ptr_idx: u64 = if (std.mem.eql(u8, callee_name, "comptime_print"))
            1
        else if (std.mem.eql(u8, callee_name, "get_type_by_name"))
            2
        else
            3;

        const fn_ptr_ptr = blk.builder.gep(
            blk,
            self.context.type_store.mkPtr(fn_ptr_ty, false),
            typed_api_ptr,
            &.{blk.builder.gepConst(fn_ptr_idx)},
            loc,
        );
        const fn_ptr = blk.builder.tirValue(.Load, blk, fn_ptr_ty, loc, .{ .ptr = fn_ptr_ptr, .@"align" = 0 });

        var all_args: std.ArrayList(tir.ValueId) = .empty;
        defer all_args.deinit(self.gpa);

        try all_args.append(self.gpa, ctx_ptr);

        const arg_ids = a.exprs.expr_pool.slice(row.args);
        if (std.mem.eql(u8, callee_name, "type_of")) {
            std.debug.assert(arg_ids.len == 1);
            const arg_type_id = self.getExprType(a, arg_ids[0]) orelse return error.LoweringBug;
            try all_args.append(self.gpa, blk.builder.tirValue(
                .ConstInt,
                blk,
                self.context.type_store.tU32(),
                loc,
                .{ .value = arg_type_id.toRaw() },
            ));
        } else {
            for (arg_ids) |arg_id| {
                try all_args.append(self.gpa, try self.lowerExpr(a, env, f, blk, arg_id, null, .rvalue));
            }
        }

        const ret_ty = self.getExprType(a, id) orelse self.context.type_store.tAny();
        return blk.builder.indirectCall(blk, ret_ty, fn_ptr, all_args.items, loc);
    }

    fn tryLowerVariantConstructor(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        row: ast.Rows.Call,
        expected: ?types.TypeId,
    ) !?tir.ValueId {
        if (expected) |ety| {
            const k = self.context.type_store.getKind(ety);
            if (k == .Variant or k == .Error) {
                const loc = self.exprOptLoc(a, id);
                return try self.buildVariantItem(a, env, f, blk, row, ety, k, loc);
            }
        }
        return null;
    }

    fn prepareCall(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        row: ast.Rows.Call,
        callee: CalleeInfo,
    ) !PreparedCall {
        var prepared = PreparedCall{
            .callee = callee,
            .args = a.exprs.expr_pool.slice(row.args),
        };

        if (try self.resolveMethodCall(a, env, row, &prepared.callee)) |ctx| {
            prepared.setMethodCtx(ctx);
        }

        self.applyFunctionSignature(&prepared);
        try self.maybeMonomorphizeCall(a, env, f, blk, row, &prepared);
        return prepared;
    }

    fn applyFunctionSignature(self: *LowerTir, prepared: *PreparedCall) void {
        prepared.param_tys = &.{};
        prepared.fixed_count = 0;
        prepared.is_variadic = false;

        const opt_fty = prepared.callee.fty orelse return;
        if (self.context.type_store.index.kinds.items[opt_fty.toRaw()] != .Function) return;

        const fn_info = self.context.type_store.get(.Function, opt_fty);
        prepared.param_tys = self.context.type_store.type_pool.slice(fn_info.params);
        prepared.is_variadic = fn_info.is_variadic;
        prepared.fixed_count = prepared.param_tys.len;
        if (prepared.is_variadic and prepared.fixed_count > 0) prepared.fixed_count -= 1;
    }

    fn maybeMonomorphizeCall(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        row: ast.Rows.Call,
        prepared: *PreparedCall,
    ) !void {
        const opt_fty = prepared.callee.fty orelse return;
        if (self.context.type_store.index.kinds.items[opt_fty.toRaw()] != .Function) return;

        var decl_ctx_opt: ?FunctionDeclContext = null;
        if (prepared.method_decl) |mid| {
            decl_ctx_opt = .{ .ast = a, .decl_id = mid };
        } else {
            decl_ctx_opt = self.findFunctionDeclForCall(a, row, prepared.callee.name);
        }
        const decl_ctx = decl_ctx_opt orelse return;
        const decl_ast = decl_ctx.ast;
        const decl = decl_ast.exprs.Decl.get(decl_ctx.decl_id);
        const base_kind = decl_ast.exprs.index.kinds.items[decl.value.toRaw()];
        if (base_kind != .FunctionLit) return;

        const params = decl_ast.exprs.param_pool.slice(decl_ast.exprs.get(.FunctionLit, decl.value).params);
        var skip_params: usize = 0;
        while (skip_params < params.len and decl_ast.exprs.Param.get(params[skip_params]).is_comptime) : (skip_params += 1) {}

        var binding_infos: std.ArrayList(monomorphize.BindingInfo) = .empty;
        defer {
            for (binding_infos.items) |*info| info.deinit(self.gpa);
            binding_infos.deinit(self.gpa);
        };

        var ok = true;
        if (prepared.args.len >= skip_params) {
            var idx: usize = 0;
            while (idx < skip_params) : (idx += 1) {
                const param = decl_ast.exprs.Param.get(params[idx]);
                if (param.pat.isNone()) {
                    ok = false;
                    break;
                }

                const pname = self.bindingNameOfPattern(decl_ast, param.pat.unwrap()) orelse {
                    ok = false;
                    break;
                };

                var param_ty = if (idx < prepared.param_tys.len)
                    prepared.param_tys[idx]
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

                const arg_expr = prepared.args[idx];
                const param_kind = self.context.type_store.getKind(param_ty);

                if (param_kind == .TypeType) {
                    const arg_ty = try self.refineExprType(a, env, arg_expr, self.getExprType(a, arg_expr));
                    const targ = switch (arg_ty) {
                        null => null,
                        else => blk: {
                            const actual = arg_ty.?;
                            if (self.context.type_store.getKind(actual) != .TypeType) break :blk null;
                            break :blk self.context.type_store.get(.TypeType, actual).of;
                        },
                    };
                    if (targ == null) {
                        ok = false;
                        break;
                    }
                    try binding_infos.append(self.gpa, monomorphize.BindingInfo.typeParam(pname, targ.?));
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

        var specialized_result_override: ?types.TypeId = null;

        if (ok) {
            const original_args = prepared.args;
            var runtime_idx: usize = skip_params;
            while (runtime_idx < params.len and runtime_idx < original_args.len) : (runtime_idx += 1) {
                const param = decl_ast.exprs.Param.get(params[runtime_idx]);
                if (param.pat.isNone()) continue;
                const pname = self.bindingNameOfPattern(decl_ast, param.pat.unwrap()) orelse continue;

                const param_ty = if (runtime_idx < prepared.param_tys.len)
                    prepared.param_tys[runtime_idx]
                else
                    self.context.type_store.tAny();
                if (!self.isAny(param_ty)) continue;

                const arg_ty = self.getExprType(a, original_args[runtime_idx]) orelse continue;
                if (self.isAny(arg_ty)) continue;

                try binding_infos.append(self.gpa, monomorphize.BindingInfo.runtimeParam(pname, arg_ty));
            }
        }

        if (ok and binding_infos.items.len > 0) {
            var runtime_specs: std.ArrayList(checker.Checker.ParamSpecialization) = .empty;
            defer runtime_specs.deinit(self.gpa);

            for (binding_infos.items) |info| {
                switch (info.kind) {
                    .runtime_param => |ty| try runtime_specs.append(self.gpa, .{ .name = info.name, .ty = ty }),
                    else => {},
                }
            }

            if (runtime_specs.items.len > 0) {
                if (decl_ast == a) {
                    const specialized_fn_ty = try self.chk.checkSpecializedFunction(decl_ast, decl.value, runtime_specs.items);
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

        if (!(ok and binding_infos.items.len > 0)) return;

        const mangled = try self.mangleMonomorphName(prepared.callee.name, binding_infos.items);
        const result = try self.monomorphizer.request(
            decl_ast,
            self.context.type_store,
            prepared.callee.name,
            decl_ctx.decl_id,
            opt_fty,
            binding_infos.items,
            skip_params,
            mangled,
            specialized_result_override,
        );

        prepared.callee.name = result.mangled_name;
        prepared.callee.fty = result.specialized_ty;
        prepared.args = prepared.args[skip_params..];
        if (prepared.has_method_ctx) prepared.method_ctx.args = prepared.args;
        if (prepared.binding()) |binding_ptr| binding_ptr.func_type = result.specialized_ty;

        self.applyFunctionSignature(prepared);
    }

    fn lowerCallArgs(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        prepared: *PreparedCall,
    ) !CallArgBuffer {
        var buffer = try CallArgBuffer.init(self.gpa, prepared.args.len);
        var i: usize = 0;
        while (i < prepared.args.len) : (i += 1) {
            const want: ?types.TypeId = if (i < prepared.fixed_count) prepared.param_tys[i] else null;
            const lower_mode: LowerMode = blk: {
                if (prepared.bindingConst()) |binding| {
                    if (binding.requires_implicit_receiver and binding.needs_addr_of and i == 0) {
                        break :blk .lvalue_addr;
                    }
                }
                break :blk .rvalue;
            };
            buffer.values[i] = try self.lowerExpr(a, env, f, blk, prepared.args[i], want, lower_mode);
        }
        return buffer;
    }

    fn coerceCallArguments(
        self: *LowerTir,
        a: *ast.Ast,
        blk: *Builder.BlockFrame,
        prepared: *const PreparedCall,
        buffer: *CallArgBuffer,
    ) void {
        if (prepared.param_tys.len == 0) return;

        var i: usize = 0;
        while (i < buffer.values.len and i < prepared.fixed_count) : (i += 1) {
            const want = prepared.param_tys[i];
            const got = blk: {
                if (prepared.bindingConst()) |binding| {
                    if (binding.requires_implicit_receiver and binding.needs_addr_of and i == 0) {
                        break :blk binding.self_param_type orelse want;
                    }
                }
                break :blk self.getExprType(a, prepared.args[i]) orelse want;
            };

            if (want.toRaw() != got.toRaw()) {
                const arg_loc = self.exprOptLoc(a, prepared.args[i]);
                buffer.values[i] = self.emitCoerce(blk, buffer.values[i], got, want, arg_loc);
            }
        }
    }

    fn adjustVariadicAnyArgs(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        prepared: *const PreparedCall,
        buffer: *CallArgBuffer,
    ) !void {
        if (!(prepared.is_variadic and buffer.values.len > prepared.fixed_count)) return;

        var i: usize = prepared.fixed_count;
        while (i < buffer.values.len) : (i += 1) {
            const expr_id = prepared.args[i];
            const got = self.getExprType(a, expr_id) orelse self.context.type_store.tAny();
            if (!self.isAny(got)) continue;

            const kind = a.exprs.index.kinds.items[expr_id.toRaw()];
            const want: types.TypeId = switch (kind) {
                .Literal => blk: {
                    const lit = a.exprs.get(.Literal, expr_id);
                    break :blk switch (lit.kind) {
                        .int, .char => self.context.type_store.tI64(),
                        .float, .imaginary => self.context.type_store.tF64(),
                        .bool => self.context.type_store.tBool(),
                        .string => self.context.type_store.tString(),
                    };
                },
                else => self.context.type_store.tUsize(),
            };
            buffer.values[i] = try self.lowerExpr(a, env, f, blk, expr_id, want, .rvalue);
        }
    }

    fn tryLowerMethodBuiltin(
        self: *LowerTir,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        loc: tir.OptLocId,
        prepared: *const PreparedCall,
        args: []const tir.ValueId,
        mode: LowerMode,
    ) !?tir.ValueId {
        const binding = prepared.bindingConst() orelse return null;
        if (binding.builtin) |builtin_kind| {
            switch (builtin_kind) {
                .dynarray_append => {
                    if (mode == .lvalue_addr) return error.LoweringBug;
                    return try self.lowerDynArrayAppend(f, blk, loc, binding.*, args);
                },
            }
        }
        return null;
    }

    fn selectCallResultType(
        self: *LowerTir,
        a: *ast.Ast,
        id: ast.ExprId,
        expected: ?types.TypeId,
        callee_fty: ?types.TypeId,
    ) types.TypeId {
        if (callee_fty) |fty| {
            if (self.context.type_store.index.kinds.items[fty.toRaw()] == .Function) {
                const fn_info = self.context.type_store.get(.Function, fty);
                const rt = fn_info.result;
                if (!self.isVoid(rt) and !self.isAny(rt)) return rt;
            }
        }
        if (expected) |want| {
            if (!self.isVoid(want) and !self.isAny(want)) return want;
        }
        if (self.getExprType(a, id)) |stamped| {
            if (!self.isVoid(stamped) and !self.isAny(stamped)) return stamped;
        }
        return self.context.type_store.tVoid();
    }

    fn cacheCallResultType(
        self: *LowerTir,
        a: *ast.Ast,
        id: ast.ExprId,
        ty: types.TypeId,
    ) !void {
        if (self.isAny(ty)) return;
        a.type_info.setExprType(id, ty);
        try self.noteExprType(id, ty);
    }

    fn materializeCallResult(
        self: *LowerTir,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        call_val: tir.ValueId,
        ret_ty: types.TypeId,
        expected: ?types.TypeId,
        mode: LowerMode,
        loc: tir.OptLocId,
    ) tir.ValueId {
        if (mode != .lvalue_addr) return call_val;

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

        const stored = if (elem_ty.toRaw() != ret_ty.toRaw())
            self.emitCoerce(blk, call_val, ret_ty, elem_ty, loc)
        else
            call_val;
        _ = f.builder.tirValue(.Store, blk, elem_ty, loc, .{ .ptr = slot, .value = stored, .@"align" = 0 });

        if (want_ptr_ty_opt) |want_ptr_ty| {
            if (want_ptr_ty.toRaw() != slot_ty.toRaw()) {
                return self.emitCoerce(blk, slot, slot_ty, want_ptr_ty, loc);
            }
        }

        return slot;
    }

    fn lowerCall(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected: ?types.TypeId,
        mode: LowerMode,
    ) !tir.ValueId {
        const row = a.exprs.get(.Call, id);
        var callee = try self.resolveCallee(a, f, row);
        const loc = self.exprOptLoc(a, id);

        if (try self.tryLowerComptimeApiCall(a, env, f, blk, id, row, callee)) |value| return value;
        if (try self.tryLowerVariantConstructor(a, env, f, blk, id, row, expected)) |variant_val| return variant_val;

        var prepared = try self.prepareCall(a, env, f, blk, row, callee);
        defer prepared.release(self.gpa);

        var arg_vals = try self.lowerCallArgs(a, env, f, blk, &prepared);
        defer arg_vals.deinit();

        self.coerceCallArguments(a, blk, &prepared, &arg_vals);
        try self.adjustVariadicAnyArgs(a, env, f, blk, &prepared, &arg_vals);

        if (try self.tryLowerMethodBuiltin(f, blk, loc, &prepared, arg_vals.values, mode)) |handled| return handled;

        const ret_ty = self.selectCallResultType(a, id, expected, prepared.callee.fty);
        try self.cacheCallResultType(a, id, ret_ty);

        const call_val = blk.builder.call(blk, ret_ty, prepared.callee.name, arg_vals.values, loc);
        return self.materializeCallResult(f, blk, call_val, ret_ty, expected, mode, loc);
    }
    fn lowerTypeExprOpaque(
        self: *LowerTir,
        a: *ast.Ast,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) tir.ValueId {
        const ty0 = self.getExprType(a, id) orelse self.context.type_store.tAny();
        const loc = self.exprOptLoc(a, id);
        const v = self.emitUndefValue(blk, ty0, loc, false);
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
        return v;
    }

    fn lowerLiteral(
        self: *LowerTir,
        a: *ast.Ast,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const lit = a.exprs.get(.Literal, id);
        // If the checker didn’t stamp a type, use the caller’s expected type.
        const ty0 = self.getExprType(a, id) orelse (expected_ty orelse return error.LoweringBug);
        const loc = self.exprOptLoc(a, id);
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
                const value64 = std.math.cast(u64, info.value) orelse return error.LoweringBug;
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
            }) orelse return error.LoweringBug }),
        };
        const want_ty = expected_ty orelse ty0;
        if (!want_ty.eq(literal_ty)) return self.emitCoerce(blk, v, literal_ty, want_ty, loc);
        return v;
    }

    fn lowerUnary(
        self: *LowerTir,
        a: *ast.Ast,
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
            const ety = self.getExprType(a, row.expr) orelse return error.LoweringBug;
            // When user asked address-of explicitly, produce pointer type
            if (row.op == .address_of) {
                const ptr = try self.lowerExpr(a, env, f, blk, row.expr, ety, .lvalue_addr);
                return ptr;
            }
            // lvalue address request falls through to .Ident/.FieldAccess/.IndexAccess implementations
        }
        // rvalue unary
        var ty0 = self.getExprType(a, id) orelse self.getExprType(a, row.expr) orelse self.context.type_store.tI64();

        // If the stamp is void/any or non-numeric for +/-, fall back to operand numeric (or i64)
        const is_num = self.isNumeric(ty0);
        if ((row.op == .pos or row.op == .neg) and (!is_num or self.isAny(ty0) or self.isVoid(ty0))) {
            if (self.getExprType(a, row.expr)) |et| {
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
                const got = self.getExprType(a, row.expr) orelse bty;
                v0 = self.emitCoerce(blk, v0, got, bty, operand_loc);
                break :blk blk.builder.un1(blk, .LogicalNot, bty, v0, loc);
            },
            .address_of => unreachable,
        };
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
        return v;
    }

    fn lowerRange(self: *LowerTir, a: *ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, id: ast.ExprId, expected_ty: ?types.TypeId) anyerror!tir.ValueId {
        const row = a.exprs.get(.Range, id);
        const ty0 = self.getExprType(a, id) orelse return error.LoweringBug;
        const loc = self.exprOptLoc(a, id);
        const usize_ty = self.context.type_store.tUsize();
        const start_v = if (!row.start.isNone())
            try self.lowerExpr(a, env, f, blk, row.start.unwrap(), usize_ty, .rvalue)
        else
            blk.builder.tirValue(.ConstUndef, blk, usize_ty, loc, .{});
        const end_v = if (!row.end.isNone())
            try self.lowerExpr(a, env, f, blk, row.end.unwrap(), usize_ty, .rvalue)
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
        a: *ast.Ast,
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
        const ty0 = self.getExprType(a, id) orelse return error.LoweringBug;
        const row = a.exprs.get(.Deref, id);
        const ptr = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const loc = self.exprOptLoc(a, id);
        const v = blk.builder.tirValue(.Load, blk, ty0, loc, .{ .ptr = ptr, .@"align" = 0 });
        if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
        return v;
    }

    fn lowerArrayLit(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.ArrayLit, id);
        const ty0 = expected_ty orelse (self.getExprType(a, id) orelse return error.LoweringBug);
        const loc = self.exprOptLoc(a, id);
        const vk = self.context.type_store.index.kinds.items[ty0.toRaw()];
        switch (vk) {
            .Array => {
                const array_ty = self.context.type_store.get(.Array, ty0);
                const len = switch (array_ty.len) {
                    .Concrete => |l| l,
                    .Unresolved => |expr_id| try self.resolveArrayLen(a, expr_id, loc),
                };

                const ids = a.exprs.expr_pool.slice(row.elems);
                if (len != ids.len) {
                    // TODO: better diagnostic
                    return error.LoweringBug;
                }

                var vals = try self.gpa.alloc(tir.ValueId, ids.len);
                defer self.gpa.free(vals);
                const expect_elem = array_ty.elem;
                var i: usize = 0;
                while (i < ids.len) : (i += 1)
                    vals[i] = try self.lowerExpr(a, env, f, blk, ids[i], expect_elem, .rvalue);
                const v = blk.builder.arrayMake(blk, ty0, vals, loc);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
                return v;
            },
            .Simd => {
                const simd_ty = self.context.type_store.get(.Simd, ty0);
                const lanes: usize = @intCast(simd_ty.lanes);
                const ids = a.exprs.expr_pool.slice(row.elems);
                if (lanes != ids.len) {
                    return error.LoweringBug;
                }

                var vals = try self.gpa.alloc(tir.ValueId, ids.len);
                defer self.gpa.free(vals);
                const expect_elem = simd_ty.elem;
                var i: usize = 0;
                while (i < ids.len) : (i += 1)
                    vals[i] = try self.lowerExpr(a, env, f, blk, ids[i], expect_elem, .rvalue);
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

                const elem_size = check_types.typeSize(self.chk, elem_ty) orelse return error.LoweringBug;

                var elems = try self.gpa.alloc(tir.ValueId, ids.len);
                defer self.gpa.free(elems);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    elems[i] = try self.lowerExpr(a, env, f, blk, ids[i], elem_ty, .rvalue);
                }

                const total_bytes = elem_size * ids.len;
                const total_bytes_u64 = std.math.cast(u64, total_bytes) orelse return error.LoweringBug;
                const bytes_const = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = total_bytes_u64 });
                const alloc_name = blk.builder.intern("rt_alloc");
                const raw_ptr = blk.builder.call(blk, ptr_void_ty, alloc_name, &.{bytes_const}, loc);
                const data_ptr = blk.builder.tirValue(.CastBit, blk, ptr_elem_ty, loc, .{ .value = raw_ptr });

                var idx: usize = 0;
                while (idx < elems.len) : (idx += 1) {
                    const idx_u64 = std.math.cast(u64, idx) orelse return error.LoweringBug;
                    const offset = blk.builder.gepConst(idx_u64);
                    const elem_ptr = blk.builder.gep(blk, ptr_elem_ty, data_ptr, &.{offset}, loc);
                    _ = blk.builder.tirValue(.Store, blk, elem_ty, loc, .{ .ptr = elem_ptr, .value = elems[idx], .@"align" = 0 });
                }

                const len_u64 = std.math.cast(u64, ids.len) orelse return error.LoweringBug;
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
                const v = try self.lowerTensorArrayLiteral(a, env, f, blk, id, ty0, loc);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
                return v;
            },
            else => return error.LoweringBug,
        }
    }

    fn lowerTensorArrayLiteral(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        tensor_ty: types.TypeId,
        loc: tir.OptLocId,
    ) !tir.ValueId {
        const tensor_row = self.context.type_store.get(.Tensor, tensor_ty);
        if (tensor_row.rank == 0) return error.LoweringBug;

        var values: std.ArrayList(tir.ValueId) = .empty;
        defer values.deinit(self.gpa);

        try self.collectTensorLiteralValues(a, env, f, blk, id, tensor_ty, &values);

        const slice = try values.toOwnedSlice(self.gpa);
        defer self.gpa.free(slice);

        return blk.builder.arrayMake(blk, tensor_ty, slice, loc);
    }

    fn collectTensorLiteralValues(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        expr_id: ast.ExprId,
        current_ty: types.TypeId,
        out: *std.ArrayList(tir.ValueId),
    ) !void {
        const kind = self.context.type_store.getKind(current_ty);
        if (kind == .Tensor) {
            if (a.exprs.index.kinds.items[expr_id.toRaw()] != .ArrayLit) return error.LoweringBug;
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
                try self.collectTensorLiteralValues(a, env, f, blk, child_id, next_ty, out);
            }
            return;
        }

        const value = try self.lowerExpr(a, env, f, blk, expr_id, current_ty, .rvalue);
        try out.append(self.gpa, value);
    }

    fn lowerTupleLit(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.TupleLit, id);
        const ty0 = expected_ty orelse (self.getExprType(a, id) orelse self.context.type_store.tAny());
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
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.StructLit, id);
        var ty0 = expected_ty orelse (self.getExprType(a, id) orelse self.context.type_store.tAny());
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
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.MapLit, id);
        const ty0 = expected_ty orelse (self.getExprType(a, id) orelse self.context.type_store.tAny());
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
        a: *ast.Ast,
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
            const rty = self.context.type_store.mkPtr(self.getExprType(a, id) orelse return error.LoweringBug, false);
            return blk.builder.gep(blk, rty, base_ptr, &.{idx}, loc);
        } else {
            const row = a.exprs.get(.IndexAccess, id);
            const ty0 = self.getExprType(a, id) orelse return error.LoweringBug;
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

    // fn lowerImportedModuleMember(
    //     self: *LowerTir,
    //     a: *ast.Ast,
    //     blk: *Builder.BlockFrame,
    //     parent_id: ast.ExprId,
    //     field_name: StrId,
    //     expected_ty: ?types.TypeId,
    //     loc: tir.OptLocId,
    // ) !?tir.ValueId {
    //     const idr = a.exprs.get(.Ident, parent_id);
    //     if (self.findTopLevelImportByName(a, idr.name)) |imp_decl| {
    //         const ty0 = self.getExprType(parent_id) orelse (expected_ty orelse self.context.type_store.tAny());
    //         if (self.materializeImportedConst(&self.context.module_graph, a, imp_decl, field_name, ty0, blk, self.pipeline)) |vv| {
    //             if (expected_ty) |want| return self.emitCoerce(blk, vv, ty0, want, loc);
    //             return vv;
    //         }
    //         const v = blk.builder.tirValue(.ConstUndef, blk, ty0, loc, .{});
    //         if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
    //         return v;
    //     }
    //     return null;
    // }

    fn lowerEnumMember(
        self: *LowerTir,
        a: *ast.Ast,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        parent_expr: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) !?tir.ValueId {
        const parent_ty = self.getExprType(a, parent_expr) orelse return null;
        const parent_kind = self.context.type_store.getKind(parent_ty);
        if (parent_kind != .Enum and parent_kind != .TypeType) return null;
        if (parent_kind == .TypeType) {
            const tr = self.context.type_store.get(.TypeType, parent_ty);
            const of_kind = self.context.type_store.getKind(tr.of);
            if (of_kind != .Enum) return null;
        }
        const ty0 = self.getExprType(a, id) orelse (expected_ty orelse self.context.type_store.tAny());
        const loc = self.exprOptLoc(a, id);
        const idx = a.type_info.getFieldIndex(id) orelse return error.LoweringBug; // enum members should be indexed by the checker
        var ev = blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = idx });
        if (expected_ty) |want| ev = self.emitCoerce(blk, ev, ty0, want, loc);
        return ev;
    }

    fn lowerVariantTagLiteral(
        self: *LowerTir,
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
        const ty0 = self.getExprType(a, id) orelse (expected_ty orelse self.context.type_store.tAny());
        const loc = self.exprOptLoc(a, id);
        if (self.context.type_store.getKind(payload_ty) != .Void) return null;
        const tag_val = blk.builder.extractField(blk, self.context.type_store.tI32(), self.emitUndefValue(blk, ty, loc, false), 0, loc);
        if (expected_ty) |want| return self.emitCoerce(blk, tag_val, ty0, want, loc);
        return tag_val;
    }

    fn lowerFieldAccess(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        mode: LowerMode,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.FieldAccess, id);
        const loc = self.exprOptLoc(a, id);

        const parent_ty_opt = self.getExprType(a, row.parent);
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
            } else if (std.mem.eql(u8, field_name, "capacity")) {
                switch (parent_kind) {
                    .DynArray => {
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
            // if (try self.lowerImportedModuleMember(a, blk, row.parent, row.field, expected_ty, loc)) |v| {
            //     return v;
            // }
        }

        const idx_maybe = a.type_info.getFieldIndex(id);

        // 2) EnumName.Member => constant (rvalue)
        if (mode == .rvalue) {
            if (try self.lowerEnumMember(a, blk, id, row.parent, expected_ty)) |v| {
                return v;
            }
        }

        // 3) address path (needs concrete field index)
        if (mode == .lvalue_addr) {
            const parent_lower_mode: LowerMode = blk: {
                if (parent_ty_opt) |parent_ty| {
                    const parent_kind = self.context.type_store.getKind(parent_ty);
                    if (parent_kind == .Ptr) break :blk .rvalue;
                }
                break :blk .lvalue_addr;
            };
            const parent_ptr = try self.lowerExpr(a, env, f, blk, row.parent, null, parent_lower_mode);
            const elem_ty = self.getExprType(a, id) orelse return error.LoweringBug;
            const idx = idx_maybe orelse return error.LoweringBug;
            const rptr_ty = self.context.type_store.mkPtr(elem_ty, false);
            if (parent_ty_opt) |parent_ty| {
                const parent_kind = self.context.type_store.getKind(parent_ty);
                if (parent_kind == .Union) {
                    return blk.builder.tirValue(.UnionFieldPtr, blk, rptr_ty, loc, .{
                        .base = parent_ptr,
                        .field_index = idx,
                    });
                }
                if (parent_kind == .Ptr)
                    return blk.builder.gep(blk, rptr_ty, parent_ptr, &.{blk.builder.gepConst(@intCast(idx))}, loc);
            }
            return blk.builder.gep(blk, rptr_ty, parent_ptr, &.{blk.builder.gepConst(@intCast(idx))}, loc);
        }

        // 4) rvalue extraction
        const ty0 = self.getExprType(a, id) orelse (expected_ty orelse self.context.type_store.tAny());
        var base = try self.lowerExpr(a, env, f, blk, row.parent, null, .rvalue);

        const is_tuple = if (parent_ty_opt) |pt|
            self.context.type_store.index.kinds.items[pt.toRaw()] == .Tuple
        else
            false;

        var v: tir.ValueId = undefined;
        if (idx_maybe) |resolved_idx| {
            const parent_kind = self.context.type_store.getKind(parent_ty_opt orelse self.context.type_store.tAny());
            v = if (parent_kind == .Variant) blk: {
                if (row.is_tuple) {
                    // Runtime variant struct exposes tag (field 0) and payload union (field 1).
                    break :blk blk.builder.extractField(blk, ty0, base, resolved_idx, loc);
                }
                // accessing the payload field out of a runtime variant value via case name
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
            } else if (parent_kind == .Ptr) blk: {
                const field_ptr = try self.lowerExpr(a, env, f, blk, id, null, .lvalue_addr);
                break :blk blk.builder.tirValue(.Load, blk, ty0, loc, .{
                    .ptr = field_ptr,
                    .@"align" = 0,
                });
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
                            .value = self.emitUndefValue(blk, payload_ty, loc, true),
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
        a: *ast.Ast,
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
        var expr_ty_opt = self.getExprType(a, id);
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
                const gty = getDeclType(a, did) orelse return error.LoweringBug;
                const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
                const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = name });
                try env.bind(name, .{ .value = addr, .ty = gty, .is_slot = true });
                return addr;
            }

            // 3) Otherwise it must be a local value binding that needs a slot.
            if (env.lookup(name)) |bnd| {
                const slot_ty = self.context.type_store.mkPtr(want_elem, false);
                const slot = f.builder.tirValue(.Alloca, blk, slot_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });

                const src_ty = if (expr_ty_opt) |ty| if (!self.isAny(ty)) ty else bnd.ty else bnd.ty;
                const to_store = self.emitCoerce(blk, bnd.value, src_ty, want_elem, loc);
                _ = f.builder.tirValue(.Store, blk, want_elem, loc, .{ .ptr = slot, .value = to_store, .@"align" = 0 });

                try env.bind(name, .{ .value = slot, .ty = want_elem, .is_slot = true });
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
                const gty = getDeclType(a, did) orelse return error.LoweringBug;
                const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
                const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = name });
                try env.bind(name, .{ .value = addr, .ty = gty, .is_slot = true });
                break :blk env.lookup(name).?;
            }

            // Not a value binding or top-level decl (likely a type name etc.).
            // Bind a safe placeholder so downstream code can keep going.
            const ty0 = expr_ty_opt orelse self.context.type_store.tAny();
            const placeholder = self.emitUndefValue(blk, ty0, loc, false);
            try env.bind(name, .{ .value = placeholder, .ty = ty0, .is_slot = false });
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
        a: *ast.Ast,
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
            const l_ty = self.getExprType(a, row.left);
            const r_ty = self.getExprType(a, row.right);

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

        const lhs_stamped = self.getExprType(a, row.left);
        const rhs_stamped = self.getExprType(a, row.right);
        const lhs_hint = try self.refineExprType(a, env, row.left, lhs_stamped);
        const rhs_hint = try self.refineExprType(a, env, row.right, rhs_stamped);

        const stamped_result = self.getExprType(a, id);
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
                lhs_expect = self.getExprType(a, row.left);
                rhs_expect = expected_ty;
                if (op_ty == null or self.isVoid(op_ty.?)) op_ty = (expected_ty orelse self.context.type_store.tAny());
            },
        }

        const l = try self.lowerExpr(a, env, f, blk, row.left, lhs_expect, .rvalue);
        const r = try self.lowerExpr(a, env, f, blk, row.right, rhs_expect, .rvalue);

        // --- Handle Optional(T) equality/inequality cases ---
        const l_ty = self.getExprType(a, row.left) orelse return error.LoweringBug;
        const r_ty = self.getExprType(a, row.right) orelse return error.LoweringBug;

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
                    (self.getExprType(a, row.right) orelse (rhs_expect orelse opt_info.elem))
                else
                    (self.getExprType(a, row.left) orelse (lhs_expect orelse opt_info.elem));

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
            const want = self.commonNumeric(self.getExprType(a, row.left), self.getExprType(a, row.right)) orelse self.context.type_store.tI64();
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
                const lhs_ty = self.getExprType(a, row.left) orelse return error.LoweringBug;
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
                    const rhs_ty = self.getExprType(a, row.right) orelse res_ty;
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
                    const rhs_ty = self.getExprType(a, row.right) orelse es.value_ty;
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
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.Catch, id);
        const loc = self.exprOptLoc(a, id);
        const out_ty_guess = expected_ty orelse (self.getExprType(a, id) orelse self.context.type_store.tVoid());
        const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

        const lhs_val = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const lhs_ty0 = self.getExprType(a, row.expr).?;
        const lhs_kind = self.context.type_store.index.kinds.items[lhs_ty0.toRaw()];
        var es_ty = lhs_ty0;
        var is_optional_es = false;
        if (lhs_kind == .Optional) {
            const opt = self.context.type_store.get(.Optional, lhs_ty0);
            es_ty = opt.elem;
            is_optional_es = true;
        }
        const es = self.context.type_store.get(.ErrorSet, es_ty);
        const expr_loc = self.exprOptLoc(a, row.expr);

        if (is_optional_es) {
            // Optional(ErrorSet(V,E)) catch handler -> Optional(V)
            // optional info not required explicitly here
            const some_flag = blk.builder.extractField(blk, self.context.type_store.tBool(), lhs_val, 0, expr_loc);
            const es_payload = blk.builder.extractField(blk, es_ty, lhs_val, 1, expr_loc);

            var some_blk = try f.builder.beginBlock(f);
            var none_blk = try f.builder.beginBlock(f);
            var join_blk = try f.builder.beginBlock(f);

            const res_opt_ty = self.context.type_store.mkOptional(es.value_ty);
            try self.noteExprType(id, res_opt_ty);
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
                try env.bind(nm, .{ .value = err_val, .ty = es.error_ty, .is_slot = false });
            }
            try self.lowerExprAsStmtList(a, env, f, &err_blk, row.handler);
            if (err_blk.term.isNone()) {
                const hv = try self.lowerBlockExprValue(a, env, f, &err_blk, row.handler, es.value_ty);
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
            const undef_payload = self.emitUndefValue(&none_blk, es.value_ty, loc, false);
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
            {
                var handler_scope = try env.pushScope();
                defer handler_scope.deinit();
                const payload_union_err = else_blk.builder.extractField(&else_blk, payload_union_ty, lhs, 1, expr_loc);
                const err_val = else_blk.builder.tirValue(.UnionField, &else_blk, es.error_ty, loc, .{
                    .base = payload_union_err,
                    .field_index = 1,
                });
                if (!row.binding_name.isNone()) {
                    const name = row.binding_name.unwrap();
                    try env.bind(name, .{ .value = err_val, .ty = es.error_ty, .is_slot = false });
                }
                try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
                if (else_blk.term.isNone()) {
                    const hv = try self.lowerBlockExprValue(a, env, f, &else_blk, row.handler, res_ty);
                    try f.builder.br(&else_blk, join_blk.id, &.{hv}, loc);
                }
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
            {
                var handler_scope = try env.pushScope();
                defer handler_scope.deinit();
                const payload_union_err = else_blk.builder.extractField(&else_blk, payload_union_ty, lhs, 1, expr_loc);
                const err_val = else_blk.builder.tirValue(.UnionField, &else_blk, es.error_ty, loc, .{
                    .base = payload_union_err,
                    .field_index = 1,
                });
                if (!row.binding_name.isNone()) {
                    const name = row.binding_name.unwrap();
                    try env.bind(name, .{ .value = err_val, .ty = es.error_ty, .is_slot = false });
                }
                try self.lowerExprAsStmtList(a, env, f, &else_blk, row.handler);
            }
            if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{}, loc);
            try f.builder.endBlock(f, else_blk);

            blk.* = exit_blk;
            return self.emitUndefValue(blk, self.context.type_store.tAny(), loc, false);
        }
    }

    fn lowerIf(
        self: *LowerTir,
        a: *ast.Ast,
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

        const out_ty_guess = expected_ty orelse (self.getExprType(a, id) orelse self.context.type_store.tVoid());
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
                if (expected_ty) |want| v_then = self.emitCoerce(&then_blk, v_then, self.getExprType(a, row.then_block) orelse res_ty, want, loc);
                try f.builder.br(&then_blk, join_blk.id, &.{v_then}, loc);
            }

            // else
            if (!row.else_block.isNone()) {
                try self.lowerExprAsStmtList(a, env, f, &else_blk, row.else_block.unwrap());
                if (else_blk.term.isNone()) {
                    var v_else = try self.lowerBlockExprValue(a, env, f, &else_blk, row.else_block.unwrap(), res_ty);
                    if (expected_ty) |want| v_else = self.emitCoerce(&else_blk, v_else, self.getExprType(a, row.else_block.unwrap()) orelse res_ty, want, loc);
                    try f.builder.br(&else_blk, join_blk.id, &.{v_else}, loc);
                }
            } else {
                if (else_blk.term.isNone()) {
                    const uv = self.emitUndefValue(&else_blk, res_ty, loc, false);
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
            return self.emitUndefValue(blk, self.context.type_store.tAny(), loc, false);
        }
    }

    fn lowerCast(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.Cast, id);
        const ty0 = self.getExprType(a, id) orelse return error.LoweringBug;
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
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.OptionalUnwrap, id);
        const elem_ty = self.getExprType(a, id) orelse return error.LoweringBug;
        const opt_ty = self.getExprType(a, row.expr) orelse return error.LoweringBug;
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
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
    ) anyerror!tir.ValueId {
        const row = a.exprs.get(.ErrUnwrap, id);
        const result_ty = self.getExprType(a, id) orelse return error.LoweringBug; // Ok payload type
        const loc = self.exprOptLoc(a, id);
        const expr_loc = self.exprOptLoc(a, row.expr);

        // Lower the error-union expression
        const es_val = try self.lowerExpr(a, env, f, blk, row.expr, null, .rvalue);
        const es_ty = self.getExprType(a, row.expr) orelse return error.LoweringBug;
        if (self.context.type_store.index.kinds.items[es_ty.toRaw()] != .ErrorSet)
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
        try self.noteExprType(id, res_ty);
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
        if (!self.isVoid(expect) and expect.toRaw() != es_ty.toRaw()) {
            ret_val = self.emitCoerce(&else_blk, es_val, es_ty, expect, loc);
        }
        try f.builder.setReturnVal(&else_blk, ret_val, loc);
        try f.builder.endBlock(f, else_blk);

        // Continue after join with the unwrapped value
        blk.* = join_blk;
        return res_param;
    }

    fn isAllIntMatch(_: *LowerTir, a: *ast.Ast, arms_slice: []const ast.MatchArmId, values_buf: []u64) bool {
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
        a: *ast.Ast,
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
        const out_ty_guess = expected_ty orelse (self.getExprType(a, id) orelse self.context.type_store.tVoid());
        const produce_value = (expected_ty != null) and !self.isVoid(out_ty_guess);

        if (produce_value) {
            // ------- value-producing path -------
            const res_ty = out_ty_guess;

            // Join block (phi-like param carries the match result)
            var join_blk = try f.builder.beginBlock(f);
            const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

            const arms = a.exprs.arm_pool.slice(row.arms);
            if (arms.len == 0) {
                const uv = self.emitUndefValue(blk, res_ty, loc, false);
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
                        v = self.emitCoerce(&bodies[i], v, self.getExprType(a, arm.body) orelse res_ty, res_ty, loc);
                        try f.builder.br(&bodies[i], join_blk.id, &.{v}, loc);
                    }
                    try f.builder.endBlock(f, bodies[i]);
                }

                const uv = self.emitUndefValue(&default_blk, res_ty, loc, false);
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
                const arm_scrut_ty = self.getExprType(a, row.expr) orelse self.context.type_store.tAny();
                const ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut, arm_scrut_ty, loc);

                // if last arm fails, feed an undef to the join
                const else_args = if (next_blk.id.toRaw() == join_blk.id.toRaw()) blkargs: {
                    const uv = self.emitUndefValue(&test_blk, res_ty, loc, false);
                    break :blkargs &.{uv};
                } else &.{};

                var binding_names = std.ArrayListUnmanaged(ast.StrId){};

                // Collect bindings for lowering

                try check_pattern_matching.collectPatternBindings(self.chk, a, arm.pattern, &binding_names);
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
                const scrut_ty = self.getExprType(a, row.expr) orelse self.context.type_store.tAny();
                try self.bindPattern(a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);

                if (body_blk.term.isNone()) {
                    var v2 = try self.lowerBlockExprValue(a, env, f, &body_blk, arm.body, res_ty);
                    v2 = self.emitCoerce(&body_blk, v2, self.getExprType(a, arm.body) orelse res_ty, res_ty, loc);
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
                return self.emitUndefValue(blk, self.context.type_store.tAny(), loc, false);
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
                return self.emitUndefValue(blk, self.context.type_store.tAny(), loc, false);
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

                const arm_scrut_ty = self.getExprType(a, row.expr) orelse self.context.type_store.tAny();
                const ok = try self.matchPattern(a, env, f, &test_blk, arm.pattern, scrut, arm_scrut_ty, loc);

                if (!arm.guard.isNone()) {
                    var guard_blk = try f.builder.beginBlock(f);
                    const br_cond = self.forceLocalCond(&test_blk, ok, loc);
                    try f.builder.condBr(&test_blk, br_cond, guard_blk.id, &.{}, next_blk.id, &.{}, loc);
                    try f.builder.endBlock(f, test_blk);

                    var binding_names = std.ArrayListUnmanaged(ast.StrId){};
                    defer binding_names.deinit(self.gpa);
                    try check_pattern_matching.collectPatternBindings(self.chk, a, arm.pattern, &binding_names);

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

                const scrut_ty = self.getExprType(a, row.expr) orelse self.context.type_store.tAny();
                try self.bindPattern(a, env, f, &body_blk, arm.pattern, scrut, scrut_ty);

                try self.lowerExprAsStmtList(a, env, f, &body_blk, arm.body);
                if (body_blk.term.isNone()) try f.builder.br(&body_blk, exit_blk.id, &.{}, loc);

                try f.builder.endBlock(f, body_blk);
                cur = next_blk;
            }

            blk.* = exit_blk;
            return self.emitUndefValue(blk, self.context.type_store.tAny(), loc, false);
        }
    }

    fn lowerWhile(
        self: *LowerTir,
        a: *ast.Ast,
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

        const out_ty_guess = expected_ty orelse (self.getExprType(a, id) orelse self.context.type_store.tVoid());
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
                const subj_ty = self.getExprType(a, row.cond.unwrap()) orelse self.context.type_store.tAny();

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

            const loop_mark = env.deferMark();
            _ = try self.loop_stack.push(self.gpa, .{
                .label = row.label,
                .continue_block = header.id,
                .break_block = exit_blk.id,
                .has_result = true,
                .join_block = join_blk.id,
                .res_param = .some(res_param),
                .res_ty = res_ty,
                .continue_info = .none,
                .defer_mark = loop_mark,
            });

            try self.lowerExprAsStmtList(a, env, f, &body, row.body);
            if (body.term.isNone()) try f.builder.br(&body, header.id, &.{}, loc);
            try f.builder.endBlock(f, header);
            try f.builder.endBlock(f, body);

            const uv = self.emitUndefValue(&exit_blk, res_ty, loc, false);
            try f.builder.br(&exit_blk, join_blk.id, &.{uv}, loc);
            try f.builder.endBlock(f, exit_blk);

            self.loop_stack.pop(self.gpa);
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
                const subj_ty = self.getExprType(a, row.cond.unwrap()) orelse self.context.type_store.tAny();

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

            const loop_mark = env.deferMark();
            _ = try self.loop_stack.push(self.gpa, .{
                .label = row.label,
                .continue_block = header.id,
                .break_block = exit_blk.id,
                .has_result = false,
                .join_block = exit_blk.id,
                .res_ty = null,
                .res_param = .none(),
                .continue_info = .none,
                .defer_mark = loop_mark,
            });

            try self.lowerExprAsStmtList(a, env, f, &body, row.body);
            if (body.term.isNone()) try f.builder.br(&body, header.id, &.{}, loc);
            try f.builder.endBlock(f, header);
            try f.builder.endBlock(f, body);

            self.loop_stack.pop(self.gpa);
            blk.* = exit_blk;
            return self.emitUndefValue(blk, self.context.type_store.tAny(), loc, false);
        }
    }

    fn getIterableLen(
        self: *LowerTir,
        a: *ast.Ast,
        blk: *Builder.BlockFrame,
        iterable_val: tir.ValueId,
        iter_ty: types.TypeId,
        idx_ty: types.TypeId,
        loc: tir.OptLocId,
    ) !tir.ValueId {
        const iter_ty_kind = self.context.type_store.index.kinds.items[iter_ty.toRaw()];
        return switch (iter_ty_kind) {
            .Array => blk: {
                const at = self.context.type_store.get(.Array, iter_ty);
                const len = switch (at.len) {
                    .Concrete => |l| l,
                    .Unresolved => |expr_id| try self.resolveArrayLen(a, expr_id, loc),
                };
                break :blk blk.builder.tirValue(.ConstInt, blk, idx_ty, loc, .{ .value = @as(u64, @intCast(len)) });
            },
            .Slice, .DynArray => blk: {
                const v = blk.builder.extractField(blk, idx_ty, iterable_val, 1, loc);
                break :blk v;
            },
            else => return error.LoweringBug,
        };
    }

    fn lowerFor(
        self: *LowerTir,
        a: *ast.Ast,
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
        const out_ty_guess = expected_ty orelse (self.getExprType(a, id) orelse self.context.type_store.tVoid());
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
            const loop_mark = env.deferMark();
            const loop_entry = try self.loop_stack.push(self.gpa, .{
                .label = row.label,
                .continue_block = header.id,
                .break_block = exit_blk.id,
                .has_result = true,
                .join_block = join_blk.id,
                .res_param = .some(res_param),
                .res_ty = res_ty,
                .continue_info = .none,
                .defer_mark = loop_mark,
            });
            if (a.exprs.index.kinds.items[row.iterable.toRaw()] == .Range) {
                // for i in start..end
                const rg = a.exprs.get(.Range, row.iterable);
                if (rg.start.isNone() or rg.end.isNone()) return error.LoweringBug;

                const start_v = try self.lowerExpr(a, env, f, blk, rg.start.unwrap(), null, .rvalue);
                const end_v = try self.lowerExpr(a, env, f, blk, rg.end.unwrap(), null, .rvalue);
                const idx_ty = self.getExprType(a, rg.start.unwrap()) orelse return error.LoweringBug;

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

                loop_entry.continue_block = update_block_id;
                loop_entry.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param}, loc);

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            } else {
                const arr_v = try self.lowerExpr(a, env, f, blk, row.iterable, null, .rvalue);
                const idx_ty = self.context.type_store.tUsize();
                const iter_ty = self.getExprType(a, row.iterable) orelse return error.LoweringBug;
                const len_v = try self.getIterableLen(a, blk, arr_v, iter_ty, idx_ty, iterable_loc);

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
                if (self.getExprType(a, row.iterable)) |it_ty| {
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

                loop_entry.continue_block = update_block_id;
                loop_entry.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param}, loc);

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            }

            // Exit -> join with a safe undef of the result type
            const uv = self.emitUndefValue(&exit_blk, res_ty, loc, false);
            try f.builder.br(&exit_blk, join_blk.id, &.{uv}, loc);
            try f.builder.endBlock(f, exit_blk);

            self.loop_stack.pop(self.gpa);
            blk.* = join_blk;
            return res_param;
        } else {
            // statement-position for (no value)
            const exit_blk = try f.builder.beginBlock(f);

            // Loop stack entry (no value carried)
            const loop_mark = env.deferMark();
            const loop_entry = try self.loop_stack.push(self.gpa, .{
                .label = row.label,
                .continue_block = header.id,
                .break_block = exit_blk.id,
                .has_result = false,
                .join_block = exit_blk.id,
                .res_ty = null,
                .res_param = .none(),
                .continue_info = .none,
                .defer_mark = loop_mark,
            });

            if (a.exprs.index.kinds.items[row.iterable.toRaw()] == .Range) {
                const rg = a.exprs.get(.Range, row.iterable);
                if (rg.start.isNone() or rg.end.isNone()) return error.LoweringBug;

                const start_v = try self.lowerExpr(a, env, f, blk, rg.start.unwrap(), null, .rvalue);
                const end_v = try self.lowerExpr(a, env, f, blk, rg.end.unwrap(), null, .rvalue);
                const idx_ty = self.getExprType(a, rg.start.unwrap()) orelse return error.LoweringBug;

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

                loop_entry.continue_block = update_block_id;
                loop_entry.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);

                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param}, loc);

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            } else {
                const arr_v = try self.lowerExpr(a, env, f, blk, row.iterable, null, .rvalue);
                const idx_ty = self.context.type_store.tUsize();
                const iter_ty = self.getExprType(a, row.iterable) orelse return error.LoweringBug;
                const len_v = try self.getIterableLen(a, blk, arr_v, iter_ty, idx_ty, iterable_loc);

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
                if (self.getExprType(a, row.iterable)) |it_ty| {
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

                loop_entry.continue_block = update_block_id;
                loop_entry.continue_info = .{ .range = .{ .update_block = update_block_id, .idx_value = idx_param } };

                try self.lowerExprAsStmtList(a, env, f, &body, row.body);
                if (body.term.isNone())
                    try f.builder.br(&body, update_block_id, &.{idx_param}, loc);

                try f.builder.endBlock(f, header);
                try f.builder.endBlock(f, body);
            }

            self.loop_stack.pop(self.gpa);
            blk.* = exit_blk;
            return self.emitUndefValue(blk, self.context.type_store.tAny(), loc, false);
        }
    }

    fn lowerExpr(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        mode: LowerMode,
    ) anyerror!tir.ValueId {
        const expr_kind = a.exprs.index.kinds.items[id.toRaw()];

        _ = try self.refineExprType(a, env, id, self.getExprType(a, id));

        return switch (expr_kind) {
            .Literal => self.lowerLiteral(a, blk, id, expected_ty),
            .NullLit => {
                const loc = self.exprOptLoc(a, id);
                const ty0 = self.getExprType(a, id) orelse return error.LoweringBug;
                const v = blk.builder.constNull(blk, ty0, loc);
                if (expected_ty) |want| return self.emitCoerce(blk, v, ty0, want, loc);
                return v;
            },
            .UndefLit => {
                const loc = self.exprOptLoc(a, id);
                const ty0 = self.getExprType(a, id) orelse return error.LoweringBug;
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
                const res_ty = expected_ty orelse (self.getExprType(a, id) orelse self.context.type_store.tVoid());
                return try self.lowerBlockExprValue(a, env, f, blk, id, res_ty);
            },
            .Ident => self.lowerIdent(a, env, f, blk, id, expected_ty, mode),
            .Binary => self.lowerBinary(a, env, f, blk, id, expected_ty),
            .Catch => self.lowerCatch(a, env, f, blk, id, expected_ty),
            .If => self.lowerIf(a, env, f, blk, id, expected_ty),
            .Call => self.lowerCall(a, env, f, blk, id, expected_ty, mode),
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
                break :blk try self.mlir_lower.lowerBlock(self.mlirHooks(), a, @ptrCast(@alignCast(env)), f, blk, id, expected_ty, loc);
            },
            .Import => blk: {
                const loc = self.exprOptLoc(a, id);
                break :blk blk.builder.tirValue(
                    .ConstUndef,
                    blk,
                    self.getExprType(a, id) orelse self.context.type_store.tAny(),
                    loc,
                    .{},
                );
            },
            .VariantType, .EnumType, .StructType => self.lowerTypeExprOpaque(a, blk, id, expected_ty),
            .CodeBlock => blk: {
                // For now, treat as opaque and produce undef
                const ty0 = self.getExprType(a, id) orelse self.context.type_store.tAny();
                const loc = self.exprOptLoc(a, id);
                break :blk self.emitUndefValue(blk, ty0, loc, true);
            },
            .ComptimeBlock => self.jitEvalComptimeBlock(a, blk, id),
            else => {
                std.debug.print("lowerExpr: unhandled expr kind {}\n", .{expr_kind});
                return error.LoweringBug;
            },
        };
    }

    // Compute the value of a block expression (value position)
    fn lowerBlockExprValue(self: *LowerTir, a: *ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, block_expr: ast.ExprId, expected_ty: types.TypeId) anyerror!tir.ValueId {
        if (a.exprs.index.kinds.items[block_expr.toRaw()] != .Block) {
            return self.lowerExpr(a, env, f, blk, block_expr, expected_ty, .rvalue);
        }
        const b = a.exprs.get(.Block, block_expr);
        const stmts = a.stmts.stmt_pool.slice(b.items);
        const loc = self.exprOptLoc(a, block_expr);
        if (stmts.len == 0) {
            try self.noteExprType(block_expr, expected_ty);
            return self.emitUndefValue(blk, expected_ty, loc, false);
        }

        // Remember where this block's scope begins on the defer stack.
        const mark = env.deferMark();
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
            return self.emitUndefValue(blk, expected_ty, loc, false);
        }
    }

    // ============================
    // Import materialization
    // ============================

    inline fn visitPatternChildren(
        _: *const LowerTir,
        a: *ast.Ast,
        pid: ast.PatternId,
        visitor: anytype,
    ) bool {
        const pk = a.pats.index.kinds.items[pid.toRaw()];
        switch (pk) {
            .Tuple => {
                const row = a.pats.get(.Tuple, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                for (elems) |child| if (visitor.call(child)) return true;
            },
            .Struct => {
                const row = a.pats.get(.Struct, pid);
                const fields = a.pats.field_pool.slice(row.fields);
                for (fields) |fid| {
                    const frow = a.pats.StructField.get(fid);
                    if (visitor.call(frow.pattern)) return true;
                }
            },
            .VariantTuple => {
                const row = a.pats.get(.VariantTuple, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                for (elems) |child| if (visitor.call(child)) return true;
            },
            .VariantStruct => {
                const row = a.pats.get(.VariantStruct, pid);
                const fields = a.pats.field_pool.slice(row.fields);
                for (fields) |fid| {
                    const frow = a.pats.StructField.get(fid);
                    if (visitor.call(frow.pattern)) return true;
                }
            },
            .Slice => {
                const row = a.pats.get(.Slice, pid);
                const elems = a.pats.pat_pool.slice(row.elems);
                for (elems, 0..) |child, idx| {
                    if (row.has_rest and idx == row.rest_index) continue;
                    if (visitor.call(child)) return true;
                }
                if (row.has_rest and !row.rest_binding.isNone()) {
                    if (visitor.call(row.rest_binding.unwrap())) return true;
                }
            },
            .Or => {
                const row = a.pats.get(.Or, pid);
                const alts = a.pats.pat_pool.slice(row.alts);
                for (alts) |alt| if (visitor.call(alt)) return true;
            },
            .At => {
                const row = a.pats.get(.At, pid);
                return visitor.call(row.pattern);
            },
            else => {},
        }
        return false;
    }

    const TopLevelLookup = struct {
        lower: *const LowerTir,
        ast: *ast.Ast,
        target: []const u8,

        const Mode = enum { any, import_only };

        fn init(lower: *const LowerTir, ast: *ast.Ast, target: []const u8) TopLevelLookup {
            return .{ .lower = lower, .ast = ast, .target = target };
        }

        fn run(self: TopLevelLookup, mode: Mode) ?ast.DeclId {
            const decls = self.ast.exprs.decl_pool.slice(self.ast.unit.decls);
            for (decls) |did| {
                if (!self.matches(did)) continue;
                if (mode == .import_only and !self.isImport(did)) continue;
                return did;
            }
            return null;
        }

        fn matches(self: TopLevelLookup, did: ast.DeclId) bool {
            const decl = self.ast.exprs.Decl.get(did);
            if (decl.pattern.isNone()) return false;
            var finder = PatternNameFinder{ .lower = self.lower, .ast = self.ast, .target = self.target };
            return finder.contains(decl.pattern.unwrap());
        }

        fn isImport(self: TopLevelLookup, did: ast.DeclId) bool {
            const decl = self.ast.exprs.Decl.get(did);
            return self.ast.exprs.index.kinds.items[decl.value.toRaw()] == .Import;
        }
    };

    const PatternNameFinder = struct {
        lower: *const LowerTir,
        ast: *ast.Ast,
        target: []const u8,

        fn contains(self: *const PatternNameFinder, pid: ast.PatternId) bool {
            const pk = self.ast.pats.index.kinds.items[pid.toRaw()];
            switch (pk) {
                .Binding => {
                    const nm = self.ast.pats.get(.Binding, pid).name;
                    return std.mem.eql(u8, self.ast.exprs.strs.get(nm), self.target);
                },
                .At => {
                    const row = self.ast.pats.get(.At, pid);
                    if (std.mem.eql(u8, self.ast.exprs.strs.get(row.binder), self.target)) return true;
                    return self.contains(row.pattern);
                },
                else => {
                    return self.lower.visitPatternChildren(self.ast, pid, struct {
                        finder: *const PatternNameFinder,
                        fn call(self: *const @This(), child: ast.PatternId) bool {
                            return self.finder.contains(child);
                        }
                    }{ .finder = self });
                },
            }
        }
    };

    fn findTopLevelDeclByName(self: *const LowerTir, a: *ast.Ast, name: ast.StrId) ?ast.DeclId {
        return self.findTopLevelDeclByNameSlice(a, a.exprs.strs.get(name));
    }

    fn findTopLevelDeclByNameSlice(self: *const LowerTir, a: *ast.Ast, target: []const u8) ?ast.DeclId {
        var lookup = TopLevelLookup.init(self, a, target);
        return lookup.run(.any);
    }

    fn findTopLevelImportByName(self: *const LowerTir, a: *ast.Ast, name: ast.StrId) ?ast.DeclId {
        var lookup = TopLevelLookup.init(self, a, a.exprs.strs.get(name));
        return lookup.run(.import_only);
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

    const TypeTraits = struct {
        store: *types.TypeStore,

        const NumericInfo = struct {
            ty: types.TypeId,
            kind: types.TypeKind,
        };

        fn init(store: *types.TypeStore) TypeTraits {
            return .{ .store = store };
        }

        fn kind(self: TypeTraits, ty: types.TypeId) types.TypeKind {
            return self.store.index.kinds.items[ty.toRaw()];
        }

        fn numericInfo(self: TypeTraits, ty: types.TypeId) ?NumericInfo {
            const kind = self.kind(ty);
            return if (isNumericKind(kind)) .{ .ty = ty, .kind = kind } else null;
        }

        fn isNumeric(self: TypeTraits, ty: types.TypeId) bool {
            return self.numericInfo(ty) != null;
        }

        fn isFloat(self: TypeTraits, ty: types.TypeId) bool {
            const kind = self.kind(ty);
            return kind == .F32 or kind == .F64;
        }

        fn isAny(self: TypeTraits, ty: types.TypeId) bool {
            return self.kind(ty) == .Any;
        }

        fn commonNumeric(self: TypeTraits, l: ?types.TypeId, r: ?types.TypeId) ?types.TypeId {
            const left = if (l) |ty| self.numericInfo(ty) else null;
            const right = if (r) |ty| self.numericInfo(ty) else null;
            if (left == null) return if (right) |info| info.ty else null;
            if (right == null) return left.?.ty;

            const li = left.?;
            const ri = right.?;
            if (li.kind == .F64 or ri.kind == .F64) return self.store.tF64();
            if (li.kind == .F32 or ri.kind == .F32) return self.store.tF32();

            inline for ([_]types.TypeKind{ .I64, .I32, .I16, .I8 }) |kind| {
                if (li.kind == kind or ri.kind == kind) switch (kind) {
                    .I64 => return self.store.tI64(),
                    .I32 => return self.store.tI32(),
                    .I16 => return self.store.tI16(),
                    .I8 => return self.store.tI8(),
                    else => unreachable,
                };
            }

            inline for ([_]types.TypeId{
                self.store.tU64(),
                self.store.tU32(),
                self.store.tU16(),
                self.store.tU8(),
            }) |unsigned_ty| {
                if (li.ty.eq(unsigned_ty) or ri.ty.eq(unsigned_ty)) return unsigned_ty;
            }

            if (li.kind == .Usize or ri.kind == .Usize) return self.store.tUsize();
            return li.ty;
        }
    };

    inline fn typeTraits(self: *const LowerTir) TypeTraits {
        return TypeTraits.init(self.context.type_store);
    }

    /// True if `ty` is a numeric scalar type.
    fn isNumeric(self: *const LowerTir, ty: types.TypeId) bool {
        if (self.isVoid(ty)) return false;
        return self.typeTraits().isNumeric(ty);
    }

    fn isFloat(self: *const LowerTir, ty: types.TypeId) bool {
        return self.typeTraits().isFloat(ty);
    }

    fn isAny(self: *const LowerTir, ty: types.TypeId) bool {
        return self.typeTraits().isAny(ty);
    }

    /// Choose a common numeric type for binary ops when the checker didn't provide one.
    fn commonNumeric(
        self: *const LowerTir,
        l: ?types.TypeId,
        r: ?types.TypeId,
    ) ?types.TypeId {
        return self.typeTraits().commonNumeric(l, r);
    }

    const TypeInspector = struct {
        lower: *LowerTir,
        ast: ?*ast.Ast,
        traits: TypeTraits,

        fn init(lower: *LowerTir, ast: *ast.Ast) TypeInspector {
            return .{ .lower = lower, .ast = ast, .traits = lower.typeTraits() };
        }

        fn initWithoutAst(lower: *LowerTir) TypeInspector {
            return .{ .lower = lower, .ast = null, .traits = lower.typeTraits() };
        }

        fn expectAst(self: *const TypeInspector) *ast.Ast {
            std.debug.assert(self.ast != null);
            return self.ast.?;
        }

        fn expr(self: *TypeInspector, id: ast.ExprId) ?types.TypeId {
            if (self.lower.lookupExprTypeOverride(id)) |override| return override;
            const ast_unit = self.expectAst();
            const idx = id.toRaw();
            std.debug.assert(idx < ast_unit.type_info.expr_types.items.len);
            return ast_unit.type_info.expr_types.items[idx];
        }

        fn decl(self: *TypeInspector, did: ast.DeclId) ?types.TypeId {
            const ast_unit = self.expectAst();
            const idx = did.toRaw();
            std.debug.assert(idx < ast_unit.type_info.decl_types.items.len);
            return ast_unit.type_info.decl_types.items[idx];
        }

        fn unionPayload(self: *TypeInspector, vty: types.TypeId) ?types.TypeId {
            const ts = self.lower.context.type_store;
            const kind = ts.getKind(vty);

            if (kind == .Variant or kind == .Error) {
                const fields = if (kind == .Variant)
                    ts.field_pool.slice(ts.get(.Variant, vty).variants)
                else
                    ts.field_pool.slice(ts.get(.Error, vty).variants);

                var args = self.lower.gpa.alloc(types.TypeStore.StructFieldArg, fields.len) catch return null;
                defer self.lower.gpa.free(args);

                for (fields, 0..) |fid, i| {
                    const f = ts.Field.get(fid);
                    args[i] = .{ .name = f.name, .ty = f.ty };
                }
                return ts.mkUnion(args);
            }

            if (kind == .Struct) {
                const sfields = ts.field_pool.slice(ts.get(.Struct, vty).fields);
                if (sfields.len != 2) return null;
                return ts.Field.get(sfields[1]).ty;
            }

            return null;
        }

        fn refine(
            self: *TypeInspector,
            env: *Env,
            expr: ast.ExprId,
            stamped: ?types.TypeId,
        ) !?types.TypeId {
            if (stamped) |ty| {
                if (!self.traits.isAny(ty)) {
                    try self.lower.noteExprType(expr, ty);
                    return ty;
                }
            }

            const ast_unit = self.expectAst();
            const kind = ast_unit.exprs.index.kinds.items[expr.toRaw()];
            switch (kind) {
                .Ident => {
                    const name = ast_unit.exprs.get(.Ident, expr).name;
                    if (env.lookup(name)) |bnd| {
                        try self.lower.noteExprType(expr, bnd.ty);
                        return bnd.ty;
                    }

                    var i: usize = self.lower.monomorph_context_stack.items.len;
                    while (i > 0) {
                        i -= 1;
                        const ctx = &self.lower.monomorph_context_stack.items[i];
                        if (ctx.lookupValue(name)) |vp| {
                            try self.lower.noteExprType(expr, vp.ty);
                            return vp.ty;
                        }
                        if (ctx.lookupType(name)) |ty| {
                            const type_ty = self.lower.context.type_store.mkTypeType(ty);
                            try self.lower.noteExprType(expr, type_ty);
                            return type_ty;
                        }
                    }
                },
                else => {},
            }

            return stamped;
        }
    };

    fn refineExprType(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        expr: ast.ExprId,
        stamped: ?types.TypeId,
    ) !?types.TypeId {
        var inspector = TypeInspector.init(self, a);
        return inspector.refine(env, expr, stamped);
    }

    const VariantView = struct {
        store: *types.TypeStore,
        ty: types.TypeId,
        kind: Kind,
        fields: []const types.FieldId,
        members: []const types.EnumMemberId,

        const Kind = enum { none, variant, error, enum };

        fn init(store: *types.TypeStore, ty: types.TypeId) VariantView {
            const kind = store.getKind(ty);
            return switch (kind) {
                .Variant => .{
                    .store = store,
                    .ty = ty,
                    .kind = .variant,
                    .fields = store.field_pool.slice(store.get(.Variant, ty).variants),
                    .members = &[_]types.EnumMemberId{},
                },
                .Error => .{
                    .store = store,
                    .ty = ty,
                    .kind = .error,
                    .fields = store.field_pool.slice(store.get(.Error, ty).variants),
                    .members = &[_]types.EnumMemberId{},
                },
                .Enum => .{
                    .store = store,
                    .ty = ty,
                    .kind = .enum,
                    .fields = &[_]types.FieldId{},
                    .members = store.enum_member_pool.slice(store.get(.Enum, ty).members),
                },
                else => .{
                    .store = store,
                    .ty = ty,
                    .kind = .none,
                    .fields = &[_]types.FieldId{},
                    .members = &[_]types.EnumMemberId{},
                },
            };
        }

        fn isVariantLike(self: VariantView) bool {
            return self.kind == .variant or self.kind == .error;
        }

        fn caseCount(self: VariantView) usize {
            return self.fields.len;
        }

        fn tagIndex(self: VariantView, name: StrId) ?u32 {
            if (!self.isVariantLike()) return null;
            for (self.fields, 0..) |fid, i| {
                const field = self.store.Field.get(fid);
                if (field.name.eq(name)) return @intCast(i);
            }
            return null;
        }

        fn payloadTypeAt(self: VariantView, index: usize) types.TypeId {
            return self.store.Field.get(self.fields[index]).ty;
        }

        fn payloadType(self: VariantView, name: StrId) ?types.TypeId {
            if (!self.isVariantLike()) return null;
            if (self.tagIndex(name)) |idx| {
                const pos: usize = @intCast(idx);
                return self.payloadTypeAt(pos);
            }
            return null;
        }

        fn enumValue(self: VariantView, name: StrId) ?u64 {
            if (self.kind != .enum) return null;
            for (self.members, 0..) |mid, i| {
                const member = self.store.EnumMember.get(mid);
                if (member.name.eq(name)) return i;
            }
            return null;
        }
    };

    // ============================
    // Misc helpers
    // ============================

    fn getExprType(self: *const LowerTir, a: *ast.Ast, id: ast.ExprId) ?types.TypeId {
        var inspector = TypeInspector.init(@constCast(self), a);
        return inspector.expr(id);
    }
    fn getDeclType(a: *ast.Ast, did: ast.DeclId) ?types.TypeId {
        const idx = did.toRaw();
        std.debug.assert(idx < a.type_info.decl_types.items.len);
        return a.type_info.decl_types.items[idx];
    }

    fn getUnionTypeFromVariant(self: *LowerTir, vty: types.TypeId) ?types.TypeId {
        var inspector = TypeInspector.initWithoutAst(self);
        return inspector.unionPayload(vty);
    }

    fn bindingNameOfPattern(_: *const LowerTir, a: *ast.Ast, pid: ast.PatternId) ?StrId {
        const k = a.pats.index.kinds.items[pid.toRaw()];
        return switch (k) {
            .Binding => a.pats.get(.Binding, pid).name,
            else => null,
        };
    }

    const PatternBinder = struct {
        lower: *LowerTir,
        ast: *ast.Ast,
        env: *Env,
        func: *Builder.FunctionFrame,
        block: *Builder.BlockFrame,

        fn init(
            lower: *LowerTir,
            ast: *ast.Ast,
            env: *Env,
            func: *Builder.FunctionFrame,
            block: *Builder.BlockFrame,
        ) PatternBinder {
            return .{ .lower = lower, .ast = ast, .env = env, .func = func, .block = block };
        }

        fn bindValue(self: *PatternBinder, pid: ast.PatternId, value: tir.ValueId, vty: types.TypeId) !void {
            const ts = self.lower.context.type_store;
            const a = self.ast;
            const env = self.env;
            const blk = self.block;
            const f = self.func;
            const loc = self.lower.patternOptLoc(a, pid);
            switch (a.pats.index.kinds.items[pid.toRaw()]) {
                .Binding => {
                    const nm = a.pats.get(.Binding, pid).name;
                    try env.bind(nm, .{ .value = value, .ty = vty, .is_slot = false });
                },
                .At => {
                    const at = a.pats.get(.At, pid);
                    try env.bind(at.binder, .{ .value = value, .ty = vty, .is_slot = false });
                    try self.bindValue(at.pattern, value, vty);
                },
                .Tuple => {
                    const row = a.pats.get(.Tuple, pid);
                    const elems = a.pats.pat_pool.slice(row.elems);
                    var elem_tys: []const types.TypeId = &[_]types.TypeId{};
                    if (ts.getKind(vty) == .Tuple) {
                        const tr = ts.get(.Tuple, vty);
                        elem_tys = ts.type_pool.slice(tr.elems);
                    }
                    for (elems, 0..) |pe, i| {
                        const ety = if (i < elem_tys.len) elem_tys[i] else ts.tAny();
                        const ev = blk.builder.extractElem(blk, ety, value, @intCast(i), loc);
                        try self.bindValue(pe, ev, ety);
                    }
                },
                .Slice => {
                    const sl = a.pats.get(.Slice, pid);
                    const elems = a.pats.pat_pool.slice(sl.elems);
                    const elem_ty = if (ts.getKind(vty) == .Array)
                        ts.get(.Array, vty).elem
                    else if (ts.getKind(vty) == .Slice)
                        ts.get(.Slice, vty).elem
                    else
                        ts.tAny();

                    for (elems, 0..) |pat_elem, i| {
                        if (sl.has_rest and i == sl.rest_index) continue;
                        const index_val = blk.builder.tirValue(.ConstInt, blk, ts.tUsize(), loc, .{ .value = i });
                        const elem_val = blk.builder.indexOp(blk, elem_ty, value, index_val, loc);
                        try self.bindValue(pat_elem, elem_val, elem_ty);
                    }

                    if (sl.has_rest and !sl.rest_binding.isNone()) {
                        const rest_pat = sl.rest_binding.unwrap();
                        const slice_ty = ts.mkSlice(elem_ty);
                        const start = blk.builder.tirValue(.ConstInt, blk, ts.tUsize(), loc, .{ .value = sl.rest_index });

                        var len_val: tir.ValueId = undefined;
                        const vty_kind = ts.getKind(vty);
                        if (vty_kind == .Array) {
                            const arr_ty = ts.get(.Array, vty);
                            const len = switch (arr_ty.len) {
                                .Concrete => |l| l,
                                .Unresolved => |expr_id| try self.lower.resolveArrayLen(a, expr_id, loc),
                            };
                            len_val = blk.builder.tirValue(.ConstInt, blk, ts.tUsize(), loc, .{ .value = len });
                        } else {
                            len_val = blk.builder.extractFieldNamed(blk, ts.tUsize(), value, f.builder.intern("len"), loc);
                        }

                        const range_ty = ts.mkSlice(ts.tUsize());
                        const inclusive = blk.builder.tirValue(.ConstBool, blk, ts.tBool(), loc, .{ .value = false });
                        const range_val = blk.builder.rangeMake(blk, range_ty, start, len_val, inclusive, loc);
                        const rest_slice = blk.builder.indexOp(blk, slice_ty, value, range_val, loc);
                        try self.bindValue(rest_pat, rest_slice, slice_ty);
                    }
                },
                .VariantTuple => {
                    const pr = a.pats.get(.VariantTuple, pid);
                    const segs = a.pats.seg_pool.slice(pr.path);
                    if (segs.len == 0) return;
                    const case_name = a.pats.PathSeg.get(segs[segs.len - 1]).name;

                    const tag_idx = self.lower.tagIndexForCase(vty, case_name) orelse return;
                    const union_ty = self.lower.getUnionTypeFromVariant(vty) orelse return;

                    const union_agg = blk.builder.extractField(blk, union_ty, value, 1, loc);
                    const payload_fields = ts.field_pool.slice(ts.get(.Union, union_ty).fields);
                    const fld = ts.Field.get(payload_fields[tag_idx]);
                    const payload_ty = fld.ty;

                    const pelems = a.pats.pat_pool.slice(pr.elems);

                    if (ts.getKind(payload_ty) == .Tuple) {
                        const tuple_val = blk.builder.tirValue(.UnionField, blk, payload_ty, loc, .{
                            .base = union_agg,
                            .field_index = tag_idx,
                        });

                        const tr = ts.get(.Tuple, payload_ty);
                        const subtys = ts.type_pool.slice(tr.elems);

                        for (pelems, 0..) |pe, i| {
                            const ety = if (i < subtys.len) subtys[i] else ts.tAny();
                            const ev = blk.builder.extractElem(blk, ety, tuple_val, @intCast(i), loc);
                            try self.bindValue(pe, ev, ety);
                        }
                    } else if (pelems.len > 0) {
                        const pv = blk.builder.tirValue(.UnionField, blk, payload_ty, loc, .{
                            .base = union_agg,
                            .field_index = tag_idx,
                        });
                        try self.bindValue(pelems[0], pv, payload_ty);
                    }
                },
                .VariantStruct => {
                    const vs = a.pats.get(.VariantStruct, pid);
                    const vk = ts.getKind(vty);
                    if (vk == .Struct) {
                        const pfields = a.pats.field_pool.slice(vs.fields);
                        for (pfields) |pfid| {
                            const pf = a.pats.StructField.get(pfid);
                            const struct_ty = ts.get(.Struct, vty);
                            const sfields = ts.field_pool.slice(struct_ty.fields);
                            for (sfields, 0..) |sfid, i| {
                                const sf = ts.Field.get(sfid);
                                if (sf.name.eq(pf.name)) {
                                    const field_val = blk.builder.extractField(blk, sf.ty, value, @intCast(i), loc);
                                    try self.bindValue(pf.pattern, field_val, sf.ty);
                                    break;
                                }
                            }
                        }
                        return;
                    }

                    const segs = a.pats.seg_pool.slice(vs.path);
                    if (segs.len == 0) return;
                    const case_name = a.pats.PathSeg.get(segs[segs.len - 1]).name;

                    const tag_idx = self.lower.tagIndexForCase(vty, case_name) orelse return;
                    const union_ty = self.lower.getUnionTypeFromVariant(vty) orelse return;
                    const union_agg = blk.builder.extractField(blk, union_ty, value, 1, loc);

                    const payload_fields = ts.field_pool.slice(ts.get(.Union, union_ty).fields);
                    const fld = ts.Field.get(payload_fields[tag_idx]);
                    const payload_ty = fld.ty;

                    const struct_val = blk.builder.tirValue(.UnionField, blk, payload_ty, loc, .{
                        .base = union_agg,
                        .field_index = tag_idx,
                    });

                    const pfields = a.pats.field_pool.slice(vs.fields);
                    for (pfields) |pfid| {
                        const pf = a.pats.StructField.get(pfid);
                        const struct_ty = ts.get(.Struct, payload_ty);
                        const sfields = ts.field_pool.slice(struct_ty.fields);
                        for (sfields, 0..) |sfid, i| {
                            const sf = ts.Field.get(sfid);
                            if (sf.name.eq(pf.name)) {
                                const field_val = blk.builder.extractField(blk, sf.ty, struct_val, @intCast(i), loc);
                                try self.bindValue(pf.pattern, field_val, sf.ty);
                                break;
                            }
                        }
                    }
                },
                else => {},
            }
        }

        fn destructureValue(
            self: *PatternBinder,
            pid: ast.PatternId,
            value: tir.ValueId,
            vty: types.TypeId,
            to_slots: bool,
        ) !void {
            const ts = self.lower.context.type_store;
            const a = self.ast;
            const env = self.env;
            const f = self.func;
            const blk = self.block;
            const loc = self.lower.patternOptLoc(a, pid);
            switch (a.pats.index.kinds.items[pid.toRaw()]) {
                .Binding => {
                    const nm = a.pats.get(.Binding, pid).name;
                    if (to_slots) {
                        const slot = self.allocateSlot(vty, loc);
                        _ = f.builder.tirValue(.Store, blk, vty, loc, .{ .ptr = slot, .value = value, .@"align" = 0 });
                        try env.bind(nm, .{ .value = slot, .ty = vty, .is_slot = true });
                    } else {
                        try env.bind(nm, .{ .value = value, .ty = vty, .is_slot = false });
                    }
                },
                .Tuple => {
                    const row = a.pats.get(.Tuple, pid);
                    const elems = a.pats.pat_pool.slice(row.elems);
                    var elem_tys: []const types.TypeId = &[_]types.TypeId{};
                    if (ts.index.kinds.items[vty.toRaw()] == .Tuple) {
                        const tr = ts.get(.Tuple, vty);
                        elem_tys = ts.type_pool.slice(tr.elems);
                    }
                    var i: usize = 0;
                    while (i < elems.len) : (i += 1) {
                        const ety = if (i < elem_tys.len) elem_tys[i] else ts.tAny();
                        const ev = blk.builder.extractElem(blk, ety, value, @intCast(i), loc);
                        try self.destructureValue(elems[i], ev, ety, to_slots);
                    }
                },
                .Struct => {
                    const row = a.pats.get(.Struct, pid);
                    const fields = a.pats.field_pool.slice(row.fields);
                    var type_fields: ?[]const types.FieldId = null;
                    if (ts.getKind(vty) == .Struct) {
                        const srow = ts.get(.Struct, vty);
                        type_fields = ts.field_pool.slice(srow.fields);
                    }
                    for (fields) |fid| {
                        const pf = a.pats.StructField.get(fid);
                        var field_ty = ts.tAny();
                        var extracted: tir.ValueId = undefined;
                        if (type_fields) |list| {
                            var matched = false;
                            var j: usize = 0;
                            while (j < list.len) : (j += 1) {
                                const stf = ts.Field.get(list[j]);
                                if (stf.name.toRaw() == pf.name.toRaw()) {
                                    field_ty = stf.ty;
                                    extracted = blk.builder.extractField(blk, field_ty, value, @intCast(j), loc);
                                    matched = true;
                                    break;
                                }
                            }
                            if (!matched) {
                                extracted = self.lower.emitUndefValue(blk, field_ty, loc, true);
                            }
                        } else {
                            extracted = blk.builder.extractFieldNamed(blk, field_ty, value, pf.name, loc);
                        }
                        try self.destructureValue(pf.pattern, extracted, field_ty, to_slots);
                    }
                },
                else => {},
            }
        }

        fn allocateSlot(self: *PatternBinder, ty: types.TypeId, loc: tir.OptLocId) tir.ValueId {
            const ptr_ty = self.lower.context.type_store.mkPtr(ty, false);
            return self.func.builder.tirValue(.Alloca, self.block, ptr_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });
        }
    };
    fn bindPattern(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        pid: ast.PatternId,
        value: tir.ValueId,
        vty: types.TypeId,
    ) !void {
        var binder = PatternBinder.init(self, a, env, f, blk);
        try binder.bindValue(pid, value, vty);
    }


    // Destructure a declaration pattern and bind its sub-bindings either as values (const) or slots (mutable).
    fn destructureDeclPattern(self: *LowerTir, a: *ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, value: tir.ValueId, vty: types.TypeId, to_slots: bool) !void {
        var binder = PatternBinder.init(self, a, env, f, blk);
        try binder.destructureValue(pid, value, vty, to_slots);
    }


    // Prefer destructuring directly from the source expression when available (avoids building temp tuples).
    fn destructureDeclFromTupleLit(self: *LowerTir, a: *ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, src_expr: ast.ExprId, vty: types.TypeId, to_slots: bool) anyerror!void {
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
            const uv = self.emitUndefValue(blk, ety, elem_loc, true);
            try self.destructureDeclPattern(a, env, f, blk, elems_pat[i], uv, ety, to_slots);
        }
    }



    fn destructureDeclFromStructLit(self: *LowerTir, a: *ast.Ast, env: *Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, src_expr: ast.ExprId, vty: types.TypeId, to_slots: bool) !void {
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
                const uv = self.emitUndefValue(blk, fty, field_loc, true);
                try self.destructureDeclPattern(a, env, f, blk, pf.pattern, uv, fty, to_slots);
            }
        }
    }

    fn destructureDeclFromExpr(
        self: *LowerTir,
        a: *ast.Ast,
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
        const src_ty_opt = self.getExprType(a, src_expr);
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
            const placeholder = self.emitUndefValue(blk, type_ty, expr_loc, false);
            try self.destructureDeclPattern(a, env, f, blk, pid, placeholder, type_ty, to_slots);
            return;
        }

        switch (pk) {
            .Binding => {
                const guess_ty = src_ty_opt orelse target_ty;
                const expect_ty = if (target_kind == .Any) guess_ty else target_ty;
                var raw = try self.lowerExpr(a, env, f, blk, src_expr, expect_ty, .rvalue);

                const refined = try self.refineExprType(a, env, src_expr, self.getExprType(a, src_expr));
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
                            const uv = self.emitUndefValue(blk, ety, elem_loc, true);
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
                    const uv = self.emitUndefValue(blk, ety, elem_loc, true);
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
                                    const uv = self.emitUndefValue(blk, fty, field_loc, true);
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
                    const uv = self.emitUndefValue(blk, self.context.type_store.tAny(), field_loc, true);
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

    fn variantCacheKey(ty: types.TypeId, name: StrId) u64 {
        return (@as(u64, ty.toRaw()) << 32) | @as(u64, name.toRaw());
    }

    fn tagIndexForCase(self: *LowerTir, case_ty: types.TypeId, name: StrId) ?u32 {
        const key = variantCacheKey(case_ty, name);
        if (self.variant_tag_cache.get(key)) |cached| return cached;

        const view = VariantView.init(self.context.type_store, case_ty);
        if (view.tagIndex(name)) |idx| {
            self.variant_tag_cache.put(key, idx) catch {};
            return idx;
        }
        return null;
    }

    fn enumMemberValue(self: *LowerTir, enum_ty: types.TypeId, name: StrId) ?u64 {
        const key = variantCacheKey(enum_ty, name);
        if (self.enum_value_cache.get(key)) |cached| return cached;

        const view = VariantView.init(self.context.type_store, enum_ty);
        if (view.enumValue(name)) |value| {
            self.enum_value_cache.put(key, value) catch {};
            return value;
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
        return VariantView.init(self.context.type_store, ty).isVariantLike();
    }

    /// If `expr` is a tag literal like `MyErr.NotFound` (i.e. a field access on a
    /// TypeType whose `.of` is Variant or Error) return the variant/error type and
    /// the resolved tag index. Only returns for void-payload cases (constructorless).
    fn tagConstFromTypePath(
        self: *const LowerTir,
        a: *ast.Ast,
        expr: ast.ExprId,
    ) ?struct { of_ty: types.TypeId, tag_idx: u32 } {
        if (a.exprs.index.kinds.items[expr.toRaw()] != .FieldAccess) return null;
        const fr = a.exprs.get(.FieldAccess, expr);
        const pty = self.getExprType(a, fr.parent) orelse return null;
        if (self.context.type_store.getKind(pty) != .TypeType) return null;

        const of_ty = self.context.type_store.get(.TypeType, pty).of;
        const view = VariantView.init(self.context.type_store, of_ty);
        if (!view.isVariantLike()) return null;

        const idx = a.type_info.getFieldIndex(expr) orelse return null;
        const pos: usize = @intCast(idx);
        if (pos >= view.caseCount()) return null;
        const payload_ty = view.payloadTypeAt(pos);
        if (self.context.type_store.getKind(payload_ty) != .Void) return null;

        return .{ .of_ty = of_ty, .tag_idx = idx };
    }

    const PatternMatcher = struct {
        lower: *LowerTir,
        ast: *ast.Ast,
        env: *Env,
        func: *Builder.FunctionFrame,
        block: *Builder.BlockFrame,
        scrut: tir.ValueId,
        scrut_ty: types.TypeId,
        loc: tir.OptLocId,

        fn init(
            lower: *LowerTir,
            ast: *ast.Ast,
            env: *Env,
            func: *Builder.FunctionFrame,
            block: *Builder.BlockFrame,
            scrut: tir.ValueId,
            scrut_ty: types.TypeId,
            loc: tir.OptLocId,
        ) PatternMatcher {
            return .{
                .lower = lower,
                .ast = ast,
                .env = env,
                .func = func,
                .block = block,
                .scrut = scrut,
                .scrut_ty = scrut_ty,
                .loc = loc,
            };
        }

        fn boolType(self: *PatternMatcher) types.TypeId {
            return self.lower.context.type_store.tBool();
        }

        fn boolConst(self: *PatternMatcher, value: bool) tir.ValueId {
            return self.block.builder.tirValue(.ConstBool, self.block, self.boolType(), self.loc, .{ .value = value });
        }

        fn boolAnd(self: *PatternMatcher, lhs: tir.ValueId, rhs: tir.ValueId) tir.ValueId {
            return self.block.builder.binBool(self.block, .LogicalAnd, lhs, rhs, self.loc);
        }

        fn boolOr(self: *PatternMatcher, lhs: tir.ValueId, rhs: tir.ValueId) tir.ValueId {
            return self.block.builder.binBool(self.block, .LogicalOr, lhs, rhs, self.loc);
        }

        fn lastPathName(self: *PatternMatcher, range: anytype) ?StrId {
            const segs = self.ast.pats.seg_pool.slice(range);
            if (segs.len == 0) return null;
            return self.ast.pats.PathSeg.get(segs[segs.len - 1]).name;
        }

        fn compareTag(self: *PatternMatcher, idx: u32) tir.ValueId {
            const tag_ty = self.lower.context.type_store.tI32();
            const tag = self.block.builder.extractField(self.block, tag_ty, self.scrut, 0, self.loc);
            const want = self.block.builder.tirValue(.ConstInt, self.block, tag_ty, self.loc, .{ .value = @as(u64, @intCast(idx)) });
            return self.block.builder.binBool(self.block, .CmpEq, tag, want, self.loc);
        }

        fn matchVariantByName(self: *PatternMatcher, case_name: StrId) tir.ValueId {
            if (self.lower.tagIndexForCase(self.scrut_ty, case_name)) |idx| {
                return self.compareTag(idx);
            }
            return self.boolConst(false);
        }

        fn matchLiteral(self: *PatternMatcher, pid: ast.PatternId) !tir.ValueId {
            const pr = self.ast.pats.get(.Literal, pid);
            const expr_kind = self.ast.exprs.index.kinds.items[pr.expr.toRaw()];
            if (expr_kind == .Range) {
                const range = self.ast.exprs.get(.Range, pr.expr);
                return self.matchRangeBounds(range.start, range.end, range.inclusive_right);
            }

            const litv = try self.lower.lowerExpr(self.ast, self.env, self.func, self.block, pr.expr, null, .rvalue);
            return self.block.builder.binBool(self.block, .CmpEq, self.scrut, litv, self.loc);
        }

        fn matchVariantTuple(self: *PatternMatcher, pid: ast.PatternId) tir.ValueId {
            const vt = self.ast.pats.get(.VariantTuple, pid);
            const case_name = self.lastPathName(vt.path) orelse return self.boolConst(false);
            return self.matchVariantByName(case_name);
        }

        fn matchVariantStruct(self: *PatternMatcher, pid: ast.PatternId) tir.ValueId {
            const ts = self.lower.context.type_store;
            if (ts.getKind(self.scrut_ty) == .Struct) {
                return self.boolConst(true);
            }

            const vs = self.ast.pats.get(.VariantStruct, pid);
            const case_name = self.lastPathName(vs.path) orelse return self.boolConst(false);
            return self.matchVariantByName(case_name);
        }

        fn matchPath(self: *PatternMatcher, pid: ast.PatternId) tir.ValueId {
            const pp = self.ast.pats.get(.Path, pid);
            const case_name = self.lastPathName(pp.segments) orelse return self.boolConst(false);

            if (self.lower.enumMemberValue(self.scrut_ty, case_name)) |val| {
                const want = self.block.builder.tirValue(.ConstInt, self.block, self.scrut_ty, self.loc, .{ .value = val });
                return self.block.builder.binBool(self.block, .CmpEq, self.scrut, want, self.loc);
            }

            return self.matchVariantByName(case_name);
        }

        fn matchSlice(self: *PatternMatcher, pid: ast.PatternId) !tir.ValueId {
            const ts = self.lower.context.type_store;
            const sl = self.ast.pats.get(.Slice, pid);
            const elems = self.ast.pats.pat_pool.slice(sl.elems);
            const required_len = elems.len;

            const usize_ty = ts.tUsize();
            var len_val: tir.ValueId = undefined;
            const scrut_kind = ts.getKind(self.scrut_ty);
            if (scrut_kind == .Array) {
                const arr_ty = ts.get(.Array, self.scrut_ty);
                const len = switch (arr_ty.len) {
                    .Concrete => |l| l,
                    .Unresolved => |expr_id| try self.lower.resolveArrayLen(self.ast, expr_id, self.loc),
                };
                len_val = self.block.builder.tirValue(.ConstInt, self.block, usize_ty, self.loc, .{ .value = len });
            } else {
                len_val = self.block.builder.extractFieldNamed(self.block, usize_ty, self.scrut, self.func.builder.intern("len"), self.loc);
            }

            const required_val = self.block.builder.tirValue(.ConstInt, self.block, usize_ty, self.loc, .{ .value = required_len });
            const len_ok = if (sl.has_rest)
                self.block.builder.binBool(self.block, .CmpGe, len_val, required_val, self.loc)
            else
                self.block.builder.binBool(self.block, .CmpEq, len_val, required_val, self.loc);

            const elem_ty = switch (ts.getKind(self.scrut_ty)) {
                .Array => ts.get(.Array, self.scrut_ty).elem,
                .Slice => ts.get(.Slice, self.scrut_ty).elem,
                else => ts.tAny(),
            };

            var result = len_ok;
            var i: usize = 0;
            while (i < required_len) : (i += 1) {
                const index_val = self.block.builder.tirValue(.ConstInt, self.block, usize_ty, self.loc, .{ .value = i });
                const elem_val = self.block.builder.indexOp(self.block, elem_ty, self.scrut, index_val, self.loc);
                const elem_match = try self.lower.matchPattern(self.ast, self.env, self.func, self.block, elems[i], elem_val, elem_ty, self.loc);
                result = self.boolAnd(result, elem_match);
            }

            return result;
        }

        fn matchOr(self: *PatternMatcher, pid: ast.PatternId) !tir.ValueId {
            const or_pat = self.ast.pats.get(.Or, pid);
            const alts = self.ast.pats.pat_pool.slice(or_pat.alts);
            if (alts.len == 0) return self.boolConst(false);

            var result = try self.lower.matchPattern(self.ast, self.env, self.func, self.block, alts[0], self.scrut, self.scrut_ty, self.loc);
            var i: usize = 1;
            while (i < alts.len) : (i += 1) {
                const next_ok = try self.lower.matchPattern(self.ast, self.env, self.func, self.block, alts[i], self.scrut, self.scrut_ty, self.loc);
                result = self.boolOr(result, next_ok);
            }
            return result;
        }

        fn matchRangePattern(self: *PatternMatcher, pid: ast.PatternId) !tir.ValueId {
            const range_pat = self.ast.pats.get(.Range, pid);
            return self.matchRangeBounds(range_pat.start, range_pat.end, range_pat.inclusive_right);
        }

        fn matchRangeBounds(
            self: *PatternMatcher,
            start: ast.OptExprId,
            end: ast.OptExprId,
            inclusive_right: bool,
        ) !tir.ValueId {
            var result = self.boolConst(true);

            if (!start.isNone()) {
                const start_expr = start.unwrap();
                const start_val = try self.lower.lowerExpr(self.ast, self.env, self.func, self.block, start_expr, self.scrut_ty, .rvalue);
                const cmp = self.block.builder.binBool(self.block, .CmpGe, self.scrut, start_val, self.loc);
                result = self.boolAnd(result, cmp);
            }

            if (!end.isNone()) {
                const end_expr = end.unwrap();
                const end_val = try self.lower.lowerExpr(self.ast, self.env, self.func, self.block, end_expr, self.scrut_ty, .rvalue);
                const cmp = if (inclusive_right)
                    self.block.builder.binBool(self.block, .CmpLe, self.scrut, end_val, self.loc)
                else
                    self.block.builder.binBool(self.block, .CmpLt, self.scrut, end_val, self.loc);
                result = self.boolAnd(result, cmp);
            }

            return result;
        }

        fn run(self: *PatternMatcher, pid: ast.PatternId) !tir.ValueId {
            const kind = self.ast.pats.index.kinds.items[pid.toRaw()];
            return switch (kind) {
                .Wildcard => self.boolConst(true),
                .Literal => self.matchLiteral(pid),
                .VariantTuple => self.matchVariantTuple(pid),
                .At => blk: {
                    const node = self.ast.pats.get(.At, pid);
                    break :blk self.lower.matchPattern(self.ast, self.env, self.func, self.block, node.pattern, self.scrut, self.scrut_ty, self.loc);
                },
                .VariantStruct => self.matchVariantStruct(pid),
                .Path => self.matchPath(pid),
                .Slice => self.matchSlice(pid),
                .Or => self.matchOr(pid),
                .Range => self.matchRangePattern(pid),
                .Binding, .Tuple, .Struct => self.boolConst(true),
                else => self.boolConst(false),
            };
        }
    };

    fn matchPattern(
        self: *LowerTir,
        a: *ast.Ast,
        env: *Env,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        pid: ast.PatternId,
        scrut: tir.ValueId,
        scrut_ty: types.TypeId,
        loc: tir.OptLocId,
    ) !tir.ValueId {
        var matcher = PatternMatcher.init(self, a, env, f, blk, scrut, scrut_ty, loc);
        return matcher.run(pid);
    }

    fn restoreBindings(self: *LowerTir, env: *Env, saved: []const BindingSnapshot) !void {
        var i: usize = saved.len;
        while (i > 0) : (i -= 1) {
            const entry = saved[i - 1];
            _ = try env.restoreBinding(entry.name, entry.prev);
        }
    }
};

pub fn evalComptimeExpr(
    gpa: std.mem.Allocator,
    context: *Context,
    pipeline: *Pipeline,
    chk: *checker.Checker,
    ast_unit: *ast.Ast,
    expr: ast.ExprId,
    result_ty: types.TypeId,
    bindings: []const Pipeline.ComptimeBinding,
) !comp.ComptimeValue {
    return LowerTir.ComptimeRuntime.run(gpa, context, pipeline, chk, ast_unit, expr, result_ty, bindings);
}

// ============================
// Context structs
// ============================

const DeferEntry = struct { expr: ast.ExprId, is_err: bool };

const DeferMark = struct { index: u32, err_count: u32 };

const DeferStack = struct {
    entries: std.ArrayListUnmanaged(DeferEntry) = .{},
    scope_marks: std.ArrayListUnmanaged(DeferMark) = .{},
    err_count: u32 = 0,

    fn deinit(self: *DeferStack, gpa: std.mem.Allocator) void {
        self.entries.deinit(gpa);
        self.scope_marks.deinit(gpa);
    }

    fn push(self: *DeferStack, gpa: std.mem.Allocator, entry: DeferEntry) !void {
        try self.entries.append(gpa, entry);
        if (entry.is_err) self.err_count += 1;
    }

    fn mark(self: *DeferStack) DeferMark {
        return .{ .index = @intCast(self.entries.items.len), .err_count = self.err_count };
    }

    fn beginScope(self: *DeferStack, gpa: std.mem.Allocator) !void {
        try self.scope_marks.append(gpa, self.mark());
    }

    fn endScope(self: *DeferStack) DeferMark {
        if (self.scope_marks.items.len == 0) return self.mark();
        const idx = self.scope_marks.items.len - 1;
        const mark = self.scope_marks.items[idx];
        self.scope_marks.items.len = idx;
        self.restore(mark);
        return mark;
    }

    fn restore(self: *DeferStack, mark: DeferMark) void {
        while (self.entries.items.len > mark.index) {
            const idx = self.entries.items.len - 1;
            const entry = self.entries.items[idx];
            if (entry.is_err and self.err_count > 0) self.err_count -= 1;
            self.entries.items.len = idx;
        }
    }

    fn hasErrSince(self: *DeferStack, mark: DeferMark) bool {
        return self.err_count > mark.err_count;
    }

    fn sliceSince(self: *DeferStack, mark: DeferMark) []const DeferEntry {
        return self.entries.items[mark.index..];
    }
};

const ContinueInfo = union(enum) {
    none,
    range: struct { update_block: tir.BlockId, idx_value: tir.ValueId },
};

const LoopCtx = struct {
    label: ast.OptStrId,
    break_block: tir.BlockId,
    continue_block: tir.BlockId,
    join_block: tir.BlockId,
    res_ty: ?types.TypeId,
    has_result: bool,
    res_param: tir.OptValueId,
    continue_info: ContinueInfo,
    defer_mark: DeferMark,
};

const LoopStack = struct {
    list: std.ArrayListUnmanaged(LoopCtx) = .{},
    labels: std.AutoHashMapUnmanaged(u32, usize) = .{},

    fn deinit(self: *LoopStack, gpa: std.mem.Allocator) void {
        self.list.deinit(gpa);
        self.labels.deinit(gpa);
    }

    fn push(self: *LoopStack, gpa: std.mem.Allocator, ctx: LoopCtx) !*LoopCtx {
        try self.list.append(gpa, ctx);
        const idx = self.list.items.len - 1;
        if (!ctx.label.isNone()) {
            try self.labels.put(gpa, ctx.label.unwrap().toRaw(), idx);
        }
        return &self.list.items[idx];
    }

    fn pop(self: *LoopStack, gpa: std.mem.Allocator) void {
        if (self.list.items.len == 0) return;
        const idx = self.list.items.len - 1;
        const ctx = self.list.items[idx];
        self.list.items.len = idx;
        if (ctx.label.isNone()) return;
        const key = ctx.label.unwrap().toRaw();
        _ = self.labels.remove(key);
        var i: isize = @as(isize, @intCast(self.list.items.len)) - 1;
        while (i >= 0) : (i -= 1) {
            const other = self.list.items[@intCast(i)];
            if (!other.label.isNone() and other.label.unwrap().toRaw() == key) {
                self.labels.put(gpa, key, @intCast(i)) catch unreachable;
                break;
            }
        }
    }

    fn peek(self: *LoopStack) ?*LoopCtx {
        if (self.list.items.len == 0) return null;
        return &self.list.items[self.list.items.len - 1];
    }

    fn find(self: *LoopStack, opt_label: ast.OptStrId) ?*LoopCtx {
        if (opt_label.isNone()) {
            return self.peek();
        }
        const key = opt_label.unwrap().toRaw();
        if (self.labels.get(key)) |idx| {
            return &self.list.items[idx];
        }
        return null;
    }
};

const Env = struct {
    allocator: std.mem.Allocator,
    map: std.AutoArrayHashMapUnmanaged(ast.StrId, ValueBinding) = .{},
    defers: DeferStack = .{},

    const Scope = struct {
        env: *Env,
        active: bool = true,

        pub fn end(self: *Scope) void {
            if (!self.active) return;
            _ = self.env.defers.endScope();
            self.active = false;
        }

        pub fn deinit(self: *Scope) void {
            self.end();
        }
    };

    fn init(allocator: std.mem.Allocator) Env {
        return .{ .allocator = allocator, .map = .{} };
    }

    fn deinit(self: *Env) void {
        self.map.deinit(self.allocator);
        self.defers.deinit(self.allocator);
    }

    fn bind(self: *Env, name: StrId, vb: ValueBinding) !void {
        _ = try self.install(name, vb);
    }

    fn lookup(self: *Env, s: ast.StrId) ?ValueBinding {
        return self.map.get(s);
    }

    fn restoreBinding(self: *Env, name: StrId, prev: ?ValueBinding) !?ValueBinding {
        if (prev) |val| {
            return try self.install(name, val);
        }
        if (self.map.get(name)) |current| {
            const saved = current;
            _ = self.map.remove(name);
            return saved;
        }
        return null;
    }

    fn pushScope(self: *Env) !Scope {
        try self.defers.beginScope(self.allocator);
        return .{ .env = self };
    }

    fn deferMark(self: *Env) DeferMark {
        return self.defers.mark();
    }

    fn truncateDefers(self: *Env, mark: DeferMark) void {
        self.defers.restore(mark);
    }

    fn pendingDefers(self: *Env, mark: DeferMark) []const DeferEntry {
        return self.defers.sliceSince(mark);
    }

    fn hasErrDefersSince(self: *Env, mark: DeferMark) bool {
        return self.defers.hasErrSince(mark);
    }

    fn addDefer(self: *Env, expr: ast.ExprId, is_err: bool) !void {
        try self.defers.push(self.allocator, .{ .expr = expr, .is_err = is_err });
    }

    fn rootDeferMark(_: *Env) DeferMark {
        return .{ .index = 0, .err_count = 0 };
    }

    fn install(self: *Env, name: StrId, vb: ValueBinding) !?ValueBinding {
        if (self.map.getPtr(name)) |slot| {
            const prev = slot.*;
            slot.* = vb;
            return prev;
        }
        try self.map.put(self.allocator, name, vb);
        return null;
    }
};

const ValueBinding = struct { value: tir.ValueId, ty: types.TypeId, is_slot: bool };
