const std = @import("std");
const ast = @import("ast.zig");
const comp = @import("comptime.zig");
const types = @import("types.zig");
const tir = @import("tir.zig");
const LowerTir = @import("lower_tir.zig");
const mlir = @import("mlir_bindings.zig");

pub const BindingValue = struct {
    ty: types.TypeId,
    value: comp.ComptimeValue,

    pub fn init(gpa: std.mem.Allocator, ty: types.TypeId, value: comp.ComptimeValue) !BindingValue {
        return .{ .ty = ty, .value = try comp.cloneComptimeValue(gpa, value) };
    }

    fn clone(self: BindingValue, gpa: std.mem.Allocator) !BindingValue {
        return .{ .ty = self.ty, .value = try comp.cloneComptimeValue(gpa, self.value) };
    }

    fn deinit(self: *BindingValue, gpa: std.mem.Allocator) void {
        destroyComptimeValue(gpa, &self.value);
        self.* = .{ .ty = types.TypeId.fromRaw(0), .value = .Void };
    }
};

pub const BindingInfo = struct {
    name: ast.StrId,
    kind: Kind,

    pub const Kind = union(enum) {
        type_param: types.TypeId,
        value_param: BindingValue,
        runtime_param: types.TypeId,
    };

    pub fn typeParam(name: ast.StrId, ty: types.TypeId) BindingInfo {
        return .{ .name = name, .kind = .{ .type_param = ty } };
    }

    pub fn valueParam(gpa: std.mem.Allocator, name: ast.StrId, ty: types.TypeId, value: comp.ComptimeValue) !BindingInfo {
        return .{ .name = name, .kind = .{ .value_param = try BindingValue.init(gpa, ty, value) } };
    }

    pub fn runtimeParam(name: ast.StrId, ty: types.TypeId) BindingInfo {
        return .{ .name = name, .kind = .{ .runtime_param = ty } };
    }

    pub fn deinit(self: *BindingInfo, gpa: std.mem.Allocator) void {
        switch (self.kind) {
            .value_param => |*vp| vp.deinit(gpa),
            else => {},
        }
        self.* = .{ .name = ast.StrId.fromRaw(0), .kind = .{ .type_param = types.TypeId.fromRaw(0) } };
    }

    fn clone(self: BindingInfo, gpa: std.mem.Allocator) !BindingInfo {
        return switch (self.kind) {
            .type_param => |ty| BindingInfo.typeParam(self.name, ty),
            .value_param => |vp| blk: {
                const cloned = try vp.clone(gpa);
                break :blk .{ .name = self.name, .kind = .{ .value_param = cloned } };
            },
            .runtime_param => |ty| BindingInfo.runtimeParam(self.name, ty),
        };
    }
};

pub const Binding = struct {
    name: ast.StrId,
    kind: Kind,

    pub const Kind = union(enum) {
        type_param: types.TypeId,
        value_param: BindingValue,
        runtime_param: types.TypeId,
    };

    fn fromInfo(info: BindingInfo, gpa: std.mem.Allocator) !Binding {
        return switch (info.kind) {
            .type_param => |ty| .{ .name = info.name, .kind = .{ .type_param = ty } },
            .value_param => |vp| blk: {
                const cloned = try vp.clone(gpa);
                break :blk .{ .name = info.name, .kind = .{ .value_param = cloned } };
            },
            .runtime_param => |ty| .{ .name = info.name, .kind = .{ .runtime_param = ty } },
        };
    }

    fn deinit(self: *Binding, gpa: std.mem.Allocator) void {
        switch (self.kind) {
            .value_param => |*vp| vp.deinit(gpa),
            else => {},
        }
        self.* = .{ .name = ast.StrId.fromRaw(0), .kind = .{ .type_param = types.TypeId.fromRaw(0) } };
    }
};

fn destroyComptimeValue(gpa: std.mem.Allocator, value: *comp.ComptimeValue) void {
    value.destroy(gpa);
}

pub const MonomorphizationContext = struct {
    bindings: []Binding,
    skip_params: usize,
    specialized_ty: types.TypeId,

    pub fn init(
        gpa: std.mem.Allocator,
        infos: []const BindingInfo,
        skip_params: usize,
        specialized_ty: types.TypeId,
    ) !MonomorphizationContext {
        var bindings = try gpa.alloc(Binding, infos.len);
        var initialized: usize = 0;
        errdefer {
            var j: usize = 0;
            while (j < initialized) : (j += 1) bindings[j].deinit(gpa);
            gpa.free(bindings);
        }
        for (infos, 0..) |info, i| {
            bindings[i] = try Binding.fromInfo(info, gpa);
            initialized = i + 1;
        }
        return .{
            .bindings = bindings,
            .skip_params = skip_params,
            .specialized_ty = specialized_ty,
        };
    }

    pub fn deinit(self: *MonomorphizationContext, gpa: std.mem.Allocator) void {
        for (self.bindings) |*binding| binding.deinit(gpa);
        gpa.free(self.bindings);
        self.bindings = &[_]Binding{};
    }

    pub fn lookupType(self: *const MonomorphizationContext, name: ast.StrId) ?types.TypeId {
        for (self.bindings) |b| {
            if (!b.name.eq(name)) continue;
            return switch (b.kind) {
                .type_param => |ty| ty,
                .value_param => |_| null,
                .runtime_param => |_| null,
            };
        }
        return null;
    }

    pub fn lookupValue(self: *const MonomorphizationContext, name: ast.StrId) ?*const BindingValue {
        for (self.bindings) |b| {
            if (!b.name.eq(name)) continue;
            return switch (b.kind) {
                .type_param => |_| null,
                .value_param => |*vp| vp,
                .runtime_param => |_| null,
            };
        }
        return null;
    }

    pub fn lookupRuntimeParamType(self: *const MonomorphizationContext, name: ast.StrId) ?types.TypeId {
        for (self.bindings) |b| {
            if (!b.name.eq(name)) continue;
            return switch (b.kind) {
                .runtime_param => |ty| ty,
                else => null,
            };
        }
        return null;
    }
};

pub const MonomorphizationRequest = struct {
    ast: *ast.Ast,
    base_name: ast.StrId,
    decl_id: ast.DeclId,
    mangled_name: ast.StrId,
    specialized_ty: types.TypeId,
    bindings: []BindingInfo,
    skip_params: usize,
};

pub const RequestResult = struct {
    mangled_name: ast.StrId,
    specialized_ty: types.TypeId,
};

pub const LowerCallback = *const fn (
    ctx: ?*anyopaque,
    lower_ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    b: *tir.Builder,
    req: *const MonomorphizationRequest,
) anyerror!void;

const CacheEntry = struct {
    name: ast.StrId,
    specialized_ty: types.TypeId,
};

pub const Monomorphizer = struct {
    gpa: std.mem.Allocator,
    cache: std.AutoHashMap(u64, CacheEntry),
    requests: std.ArrayListUnmanaged(MonomorphizationRequest) = .{},

    pub fn init(gpa: std.mem.Allocator) Monomorphizer {
        return .{
            .gpa = gpa,
            .cache = std.AutoHashMap(u64, CacheEntry).init(gpa),
        };
    }

    pub fn deinit(self: *Monomorphizer) void {
        var i: usize = 0;
        while (i < self.requests.items.len) : (i += 1) {
            self.freeRequest(&self.requests.items[i]);
        }
        self.requests.deinit(self.gpa);
        self.cache.deinit();
    }

    fn hashComptimeValue(hasher: *std.hash.Wyhash, value: comp.ComptimeValue) void {
        switch (value) {
            .Void => {},
            .Int => |v| hasher.update(std.mem.asBytes(&v)),
            .Float => |v| hasher.update(std.mem.asBytes(&v)),
            .Bool => |v| {
                const byte: u8 = if (v) 1 else 0;
                hasher.update(std.mem.asBytes(&byte));
            },
            .String => |s| hasher.update(s),
            .Type => |ty| {
                const raw: u32 = ty.toRaw();
                hasher.update(std.mem.asBytes(&raw));
            },
            .MlirType => |ty| {
                const ptr_val: usize = if (ty.handle.ptr) |p| @intFromPtr(p) else 0;
                hasher.update(std.mem.asBytes(&ptr_val));
            },
            .MlirAttribute => |attr| {
                const ptr_val: usize = if (attr.handle.ptr) |p| @intFromPtr(p) else 0;
                hasher.update(std.mem.asBytes(&ptr_val));
            },
            .MlirModule => |mod| {
                const ptr_val: usize = if (mod.handle.ptr) |p| @intFromPtr(p) else 0;
                hasher.update(std.mem.asBytes(&ptr_val));
            },
            .Function => |func| {
                const raw: u32 = func.expr.toRaw();
                hasher.update(std.mem.asBytes(&raw));
            },
            .Sequence => |seq| {
                hasher.update(std.mem.asBytes(&seq.values.items.len));
                var idx: usize = 0;
                while (idx < seq.values.items.len) : (idx += 1) {
                    hashComptimeValue(hasher, seq.values.items[idx]);
                }
            },
            .Struct => |sv| {
                hasher.update(std.mem.asBytes(&sv.fields.items.len));
                var idx: usize = 0;
                while (idx < sv.fields.items.len) : (idx += 1) {
                    hasher.update(std.mem.asBytes(&sv.fields.items[idx].name));
                    hashComptimeValue(hasher, sv.fields.items[idx].value);
                }
                if (sv.owner) |owner| hasher.update(std.mem.asBytes(&owner));
            },
            .Range => |rng| {
                hasher.update(std.mem.asBytes(&rng.start));
                hasher.update(std.mem.asBytes(&rng.end));
                const flag: u8 = if (rng.inclusive) 1 else 0;
                hasher.update(std.mem.asBytes(&flag));
            },
        }
    }

    fn hashKey(base: ast.StrId, bindings: []const BindingInfo) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const base_raw: u32 = base.toRaw();
        hasher.update(std.mem.asBytes(&base_raw));
        for (bindings) |info| {
            const name_raw: u32 = info.name.toRaw();
            hasher.update(std.mem.asBytes(&name_raw));
            switch (info.kind) {
                .type_param => |ty| {
                    const raw: u32 = ty.toRaw();
                    hasher.update(std.mem.asBytes(&raw));
                },
                .value_param => |vp| {
                    const ty_raw: u32 = vp.ty.toRaw();
                    hasher.update(std.mem.asBytes(&ty_raw));
                    hashComptimeValue(&hasher, vp.value);
                },
                .runtime_param => |ty| {
                    const raw: u32 = ty.toRaw();
                    hasher.update(std.mem.asBytes(&raw));
                },
            }
        }
        return hasher.final();
    }

    fn dupBindings(self: *Monomorphizer, slice: []const BindingInfo) ![]BindingInfo {
        var out = try self.gpa.alloc(BindingInfo, slice.len);
        var initialized: usize = 0;
        errdefer {
            var j: usize = 0;
            while (j < initialized) : (j += 1) out[j].deinit(self.gpa);
            self.gpa.free(out);
        }
        for (slice, 0..) |info, i| {
            out[i] = try info.clone(self.gpa);
            initialized = i + 1;
        }
        return out;
    }

    fn freeRequest(self: *Monomorphizer, req: *MonomorphizationRequest) void {
        for (req.bindings) |*info| info.deinit(self.gpa);
        self.gpa.free(req.bindings);
        req.bindings = &[_]BindingInfo{};
    }

    pub fn request(
        self: *Monomorphizer,
        ast_unit: *ast.Ast,
        ts: *types.TypeStore,
        base_name: ast.StrId,
        decl_id: ast.DeclId,
        fn_ty: types.TypeId,
        bindings: []const BindingInfo,
        skip_params: usize,
        mangled_name: ast.StrId,
        specialized_result_override: ?types.TypeId,
    ) !RequestResult {
        const key = hashKey(base_name, bindings);
        if (self.cache.get(key)) |cached| {
            return .{ .mangled_name = cached.name, .specialized_ty = cached.specialized_ty };
        }

        const fn_kind = ts.get(.Function, fn_ty);
        const base_params = ts.type_pool.slice(fn_kind.params);
        std.debug.assert(skip_params <= base_params.len);

        const runtime_count = base_params.len - skip_params;
        var runtime_params = try self.gpa.alloc(types.TypeId, runtime_count);
        defer self.gpa.free(runtime_params);

        var idx: usize = 0;
        var i: usize = skip_params;
        const decl = ast_unit.exprs.Decl.get(decl_id);
        const fn_lit = ast_unit.exprs.get(.FunctionLit, decl.value);
        const params = ast_unit.exprs.param_pool.slice(fn_lit.params);

        while (i < base_params.len) : (i += 1) {
            const base_ty = base_params[i];
            const param_index = i;
            const param = ast_unit.exprs.Param.get(params[param_index]);
            var specialized_ty = base_ty;
            if (!param.ty.isNone()) {
                specialized_ty = resolveSpecializedType(ts, bindings, ast_unit, param.ty.unwrap()) orelse base_ty;
            }
            if (!param.pat.isNone()) {
                if (bindingNameOfPattern(ast_unit, param.pat.unwrap())) |pname| {
                    if (lookupRuntimeOverride(bindings, pname)) |override_ty|
                        specialized_ty = override_ty;
                }
            }
            const k = ts.getKind(specialized_ty);
            runtime_params[idx] = if (k == .TypeType)
                ts.get(.TypeType, specialized_ty).of
            else
                specialized_ty;
            idx += 1;
        }

        var result_ty = if (specialized_result_override) |override|
            override
        else blk: {
            if (!fn_lit.result_ty.isNone()) {
                if (resolveSpecializedType(ts, bindings, ast_unit, fn_lit.result_ty.unwrap())) |resolved|
                    break :blk resolved;
            }
            break :blk fn_kind.result;
        };

        if (specialized_result_override == null and ts.getKind(result_ty) == .Any) {
            if (runtimeResultType(bindings)) |override| {
                result_ty = override;
            }
        }

        if (ts.getKind(result_ty) == .TypeType) {
            result_ty = ts.get(.TypeType, result_ty).of;
        }

        const specialized_ty = ts.mkFunction(runtime_params, result_ty, fn_kind.is_variadic, fn_kind.is_pure, fn_kind.is_extern);

        const owned_bindings = try self.dupBindings(bindings);
        errdefer {
            for (owned_bindings) |*info| info.deinit(self.gpa);
            self.gpa.free(owned_bindings);
        }

        try self.requests.append(self.gpa, .{
            .ast = ast_unit,
            .base_name = base_name,
            .decl_id = decl_id,
            .mangled_name = mangled_name,
            .specialized_ty = specialized_ty,
            .bindings = owned_bindings,
            .skip_params = skip_params,
        });

        try self.cache.put(key, .{ .name = mangled_name, .specialized_ty = specialized_ty });

        return .{ .mangled_name = mangled_name, .specialized_ty = specialized_ty };
    }

    pub fn run(self: *Monomorphizer, ctx: ?*anyopaque, lower_ctx: *LowerTir.LowerContext, b: *tir.Builder, cb: LowerCallback) !void {
        while (self.requests.items.len > 0) {
            var req = self.requests.pop().?;
            defer self.freeRequest(&req);
            try cb(ctx, lower_ctx, req.ast, b, &req);
        }
    }
};

fn resolveSpecializedType(
    ts: *types.TypeStore,
    bindings: []const BindingInfo,
    a: *const ast.Ast,
    expr: ast.ExprId,
) ?types.TypeId {
    _ = ts;
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

fn lookupRuntimeOverride(bindings: []const BindingInfo, name: ast.StrId) ?types.TypeId {
    for (bindings) |info| {
        if (!info.name.eq(name)) continue;
        switch (info.kind) {
            .runtime_param => |ty| return ty,
            else => {},
        }
    }
    return null;
}

fn bindingNameOfPattern(a: *const ast.Ast, pid: ast.PatternId) ?ast.StrId {
    const k = a.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Binding => a.pats.get(.Binding, pid).name,
        else => null,
    };
}

fn runtimeResultType(bindings: []const BindingInfo) ?types.TypeId {
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
