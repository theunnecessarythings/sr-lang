const std = @import("std");
const ast = @import("ast.zig");
const types = @import("types.zig");
const tir = @import("tir.zig");

pub const BindingInfo = struct {
    name: ast.StrId,
};

pub const Binding = struct {
    name: ast.StrId,
    ty: types.TypeId,
};

pub const MonomorphizationContext = struct {
    bindings: []Binding,
    skip_params: usize,
    specialized_ty: types.TypeId,

    pub fn init(
        gpa: std.mem.Allocator,
        infos: []const BindingInfo,
        type_args: []const types.TypeId,
        skip_params: usize,
        specialized_ty: types.TypeId,
    ) !MonomorphizationContext {
        std.debug.assert(infos.len == type_args.len);
        var bindings = try gpa.alloc(Binding, infos.len);
        for (infos, 0..) |info, i| {
            bindings[i] = .{ .name = info.name, .ty = type_args[i] };
        }
        return .{
            .bindings = bindings,
            .skip_params = skip_params,
            .specialized_ty = specialized_ty,
        };
    }

    pub fn deinit(self: *MonomorphizationContext, gpa: std.mem.Allocator) void {
        gpa.free(self.bindings);
        self.bindings = &[_]Binding{};
    }
};

pub const MonomorphizationRequest = struct {
    base_name: ast.StrId,
    decl_id: ast.DeclId,
    mangled_name: ast.StrId,
    specialized_ty: types.TypeId,
    type_args: []types.TypeId,
    bindings: []BindingInfo,
    skip_params: usize,
};

pub const RequestResult = struct {
    mangled_name: ast.StrId,
    specialized_ty: types.TypeId,
};

pub const LowerCallback = *const fn (
    ctx: ?*anyopaque,
    a: *const ast.Ast,
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

    fn hashKey(base: ast.StrId, type_args: []const types.TypeId) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const base_raw: u32 = base.toRaw();
        hasher.update(std.mem.asBytes(&base_raw));
        for (type_args) |ty| {
            const raw: u32 = ty.toRaw();
            hasher.update(std.mem.asBytes(&raw));
        }
        return hasher.final();
    }

    fn dupTypes(self: *Monomorphizer, slice: []const types.TypeId) ![]types.TypeId {
        return try self.gpa.dupe(types.TypeId, slice);
    }

    fn dupBindings(self: *Monomorphizer, slice: []const BindingInfo) ![]BindingInfo {
        return try self.gpa.dupe(BindingInfo, slice);
    }

    fn freeRequest(self: *Monomorphizer, req: *MonomorphizationRequest) void {
        self.gpa.free(req.type_args);
        self.gpa.free(req.bindings);
        req.type_args = &[_]types.TypeId{};
        req.bindings = &[_]BindingInfo{};
    }

    pub fn request(
        self: *Monomorphizer,
        ts: *types.TypeStore,
        base_name: ast.StrId,
        decl_id: ast.DeclId,
        fn_ty: types.TypeId,
        type_args: []const types.TypeId,
        bindings: []const BindingInfo,
        skip_params: usize,
        mangled_name: ast.StrId,
    ) !RequestResult {
        const key = hashKey(base_name, type_args);
        if (self.cache.get(key)) |cached| {
            return .{ .mangled_name = cached.name, .specialized_ty = cached.specialized_ty };
        }

        std.debug.assert(type_args.len == skip_params);
        std.debug.assert(bindings.len == type_args.len);

        const fn_kind = ts.get(.Function, fn_ty);
        const base_params = ts.type_pool.slice(fn_kind.params);
        std.debug.assert(skip_params <= base_params.len);

        const runtime_count = base_params.len - skip_params;
        var runtime_params = try self.gpa.alloc(types.TypeId, runtime_count);
        defer self.gpa.free(runtime_params);

        var idx: usize = 0;
        var i: usize = skip_params;
        while (i < base_params.len) : (i += 1) {
            const param_ty = base_params[i];
            const k = ts.getKind(param_ty);
            runtime_params[idx] = if (k == .TypeType)
                ts.get(.TypeType, param_ty).of
            else
                param_ty;
            idx += 1;
        }

        var result_ty = fn_kind.result;
        if (ts.getKind(result_ty) == .TypeType) {
            result_ty = ts.get(.TypeType, result_ty).of;
        }

        const specialized_ty = ts.mkFunction(runtime_params, result_ty, fn_kind.is_variadic, fn_kind.is_pure);

        const owned_types = try self.dupTypes(type_args);
        errdefer self.gpa.free(owned_types);

        const owned_bindings = try self.dupBindings(bindings);
        errdefer self.gpa.free(owned_bindings);

        try self.requests.append(self.gpa, .{
            .base_name = base_name,
            .decl_id = decl_id,
            .mangled_name = mangled_name,
            .specialized_ty = specialized_ty,
            .type_args = owned_types,
            .bindings = owned_bindings,
            .skip_params = skip_params,
        });

        try self.cache.put(key, .{ .name = mangled_name, .specialized_ty = specialized_ty });

        return .{ .mangled_name = mangled_name, .specialized_ty = specialized_ty };
    }

    pub fn run(
        self: *Monomorphizer,
        ctx: ?*anyopaque,
        a: *const ast.Ast,
        b: *tir.Builder,
        cb: LowerCallback,
    ) !void {
        while (self.requests.items.len > 0) {
            var req = self.requests.pop().?;
            defer self.freeRequest(&req);
            try cb(ctx, a, b, &req);
        }
    }
};
