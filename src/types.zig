const std = @import("std");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const comp = @import("comptime.zig");
const call_resolution = @import("call_resolution.zig");

// DOD Type Store
pub const TypeTag = struct {};

pub const max_tensor_rank: usize = 4;

pub const TypeId = cst.Index(TypeTag);
pub const FieldId = cst.Index(Rows.Field);
pub const EnumMemberId = cst.Index(Rows.EnumMember);
pub const RangeEnumMember = cst.RangeOf(EnumMemberId);
pub const RangeType = cst.RangeOf(TypeId);
pub const RangeField = cst.RangeOf(FieldId);

pub const StringInterner = cst.StringInterner;
pub const Table = cst.Table;
pub const Pool = cst.Pool;
pub const StoreIndex = cst.StoreIndex;
pub const StrId = cst.StrId;

/// MlirSpliceInfo union definition used by the compiler.
pub const MlirSpliceInfo = union(enum) {
    decl: struct { decl_id: ast.DeclId, name: ast.StrId },
    value_param: struct { param_id: ast.ParamId, name: ast.StrId, ty: TypeId },
    type_param: struct { param_id: ast.ParamId, name: ast.StrId, ty: TypeId },
};

pub const MethodReceiverKind = enum { none, value, pointer, pointer_const };
pub const BuiltinMethod = enum { dynarray_append };

pub const MethodEntry = struct {
    owner_type: TypeId,
    method_name: ast.StrId,
    decl_id: ast.DeclId,
    decl_ast: *ast.Ast,
    func_expr: ast.ExprId,
    func_type: TypeId,
    self_param_type: ?TypeId,
    receiver_kind: MethodReceiverKind,
    builtin: ?BuiltinMethod = null,
};

pub const MethodBinding = struct {
    owner_type: TypeId,
    method_name: ast.StrId,
    decl_id: ast.DeclId,
    decl_ast: *ast.Ast,
    func_type: TypeId,
    self_param_type: ?TypeId,
    receiver_kind: MethodReceiverKind,
    requires_implicit_receiver: bool,
    needs_addr_of: bool,
    builtin: ?BuiltinMethod = null,
};

pub const MethodKey = struct {
    owner: usize,
    name: usize,
};

pub const CallSpecialization = struct {
    target_decl: u32,
    target_file_id: u32 = std.math.maxInt(u32),
    pack_args: bool = false,
    pack_start_index: usize = 0,
    is_spread: bool = false,
};

pub fn hashSpecialization(original_decl_id: u32, param_types: []const TypeId, comptime_hashes: []const u64) u64 {
    var hasher: std.hash.Fnv1a_64 = .init();
    hasher.update(std.mem.asBytes(&original_decl_id));
    for (param_types) |pt| hasher.update(std.mem.asBytes(&pt.toRaw()));
    for (comptime_hashes) |h| hasher.update(std.mem.asBytes(&h));
    return hasher.final();
}

pub const SpecializationKey = struct {
    digest: u64,
    original_decl_id: u32,
    param_types: []const TypeId,
    comptime_hashes: []const u64,

    pub fn hash(self: SpecializationKey) u64 {
        return self.digest;
    }
    pub fn eql(self: SpecializationKey, other: SpecializationKey) bool {
        if (self.digest != other.digest) return false;
        if (self.original_decl_id != other.original_decl_id) return false;
        if (self.param_types.len != other.param_types.len) return false;
        if (self.comptime_hashes.len != other.comptime_hashes.len) return false;
        for (self.param_types, other.param_types) |a, b| if (!a.eq(b)) return false;
        return std.mem.eql(u64, self.comptime_hashes, other.comptime_hashes);
    }
};

pub const SpecializationKeyContext = struct {
    pub fn hash(_: @This(), key: SpecializationKey) u64 {
        return key.hash();
    }
    pub fn eql(_: @This(), a: SpecializationKey, b: SpecializationKey) bool {
        return a.eql(b);
    }
};

fn makeMethodKey(owner: TypeId, name: ast.StrId) MethodKey {
    return .{ .owner = owner.toRaw(), .name = name.toRaw() };
}

const StoredComptimeBinding = struct { ty: TypeId, value: comp.ComptimeValue };
pub const ComptimeBindingVisitor = fn (?*anyopaque, ast.StrId, comp.ComptimeValue, TypeId) anyerror!void;

pub const TypeInfo = struct {
    arena: *std.heap.ArenaAllocator,
    backing_gpa: std.mem.Allocator,
    gpa: std.mem.Allocator,
    store: *TypeStore,

    expr_types: std.ArrayListUnmanaged(?TypeId) = .{},
    decl_types: std.ArrayListUnmanaged(?TypeId) = .{},
    field_index_for_expr: std.AutoArrayHashMapUnmanaged(u32, u32) = .{},
    comptime_values: std.AutoArrayHashMapUnmanaged(ast.ExprId, comp.ComptimeValue) = .{},
    comptime_bindings: std.AutoArrayHashMapUnmanaged(ast.StrId, StoredComptimeBinding) = .{},

    method_bindings: std.AutoArrayHashMapUnmanaged(u32, MethodBinding) = .{},
    method_expr_snapshots: std.AutoArrayHashMapUnmanaged(MethodKey, MethodExprSnapshot) = .{},

    specialization_expr_snapshots: std.AutoArrayHashMapUnmanaged(u32, MethodExprSnapshot) = .{},
    specialization_call_snapshots: std.AutoArrayHashMapUnmanaged(u32, CallSpecSnapshot) = .{},
    specialization_comptime_expr_snapshots: std.AutoArrayHashMapUnmanaged(u32, ComptimeExprSnapshot) = .{},

    mlir_splice_info: std.AutoArrayHashMapUnmanaged(u32, MlirSpliceInfo) = .{},
    mlir_splice_values: std.AutoArrayHashMapUnmanaged(u32, comp.ComptimeValue) = .{},
    exports: std.AutoArrayHashMapUnmanaged(ast.StrId, ExportEntry) = .{},
    specialized_calls: std.AutoArrayHashMapUnmanaged(u32, call_resolution.FunctionDeclContext) = .{},
    spread_ranges: std.AutoArrayHashMapUnmanaged(u32, void) = .{},
    call_specializations: std.AutoArrayHashMapUnmanaged(u32, CallSpecialization) = .{},
    synthetic_decls: std.ArrayListUnmanaged(u32) = .{},

    pub const ExportEntry = struct { ty: TypeId, decl_id: ast.DeclId };
    const MethodExprSnapshot = struct { expr_ids: []u32, expr_types: []TypeId };
    const CallSpecSnapshot = struct { expr_ids: []u32, specs: []CallSpecialization, comptime_snapshot: ?ComptimeBindingSnapshot = null };
    const ComptimeBindingSnapshot = struct { names: []ast.StrId, types: []TypeId, values: []comp.ComptimeValue };
    const ComptimeExprSnapshot = struct { expr_ids: []u32, values: []comp.ComptimeValue };

    pub fn init(gpa: std.mem.Allocator, store: *TypeStore) TypeInfo {
        const arena = gpa.create(std.heap.ArenaAllocator) catch @panic("OOM");
        arena.* = std.heap.ArenaAllocator.init(gpa);
        return .{
            .arena = arena,
            .backing_gpa = gpa,
            .gpa = arena.allocator(),
            .store = store,
        };
    }

    pub fn deinit(self: *TypeInfo) void {
        self.arena.deinit();
        self.backing_gpa.destroy(self.arena);
    }

    pub fn print(self: *TypeInfo) void {
        std.debug.print("TypeInfo:\n Expr types:\n", .{});
        var buffer: [1024]u8 = undefined;
        var writer = std.fs.File.stdout().writer(&buffer);
        for (self.expr_types.items, 0..) |value, i| {
            writer.interface.print("  {}: ", .{i}) catch {};
            if (value) |ty| self.store.fmt(ty, &writer.interface) catch {} else writer.interface.print("null", .{}) catch {};
            writer.interface.print("\n", .{}) catch {};
        }
        writer.interface.flush() catch {};

        std.debug.print("\n Decl types:\n", .{});
        for (self.decl_types.items, 0..) |value, i| {
            writer.interface.print("  {}: ", .{i}) catch {};
            if (value) |ty| self.store.fmt(ty, &writer.interface) catch {} else writer.interface.print("null", .{}) catch {};
            writer.interface.print("\n", .{}) catch {};
        }
        writer.interface.flush() catch {};
    }

    pub fn ensureExpr(self: *TypeInfo, _: std.mem.Allocator, expr_id: ast.ExprId) !void {
        const need = expr_id.toRaw() + 1;
        if (self.expr_types.items.len < need) {
            try self.expr_types.ensureTotalCapacity(self.arena.allocator(), need);
            while (self.expr_types.items.len < need) self.expr_types.appendAssumeCapacity(null);
        }
        if (self.field_index_for_expr.count() < need) {
            try self.field_index_for_expr.ensureTotalCapacity(self.arena.allocator(), need);
            var i = self.field_index_for_expr.count();
            while (i < need) : (i += 1) try self.field_index_for_expr.put(self.arena.allocator(), @intCast(i), 0xFFFF_FFFF);
        }
    }

    pub fn setExprType(self: *TypeInfo, expr_id: ast.ExprId, ty: TypeId) void {
        self.expr_types.items[expr_id.toRaw()] = ty;
    }

    pub fn setFieldIndex(self: *TypeInfo, expr_id: ast.ExprId, idx: u32) !void {
        try self.field_index_for_expr.put(self.arena.allocator(), expr_id.toRaw(), idx);
    }

    pub fn getFieldIndex(self: *const TypeInfo, expr_id: ast.ExprId) ?u32 {
        const v = self.field_index_for_expr.get(expr_id.toRaw()) orelse 0xFFFF_FFFF;
        return if (v == 0xFFFF_FFFF) null else v;
    }

    pub fn clearFieldIndex(self: *TypeInfo, expr_id: ast.ExprId) !void {
        try self.field_index_for_expr.put(self.arena.allocator(), expr_id.toRaw(), 0xFFFF_FFFF);
    }

    pub fn getMethodBinding(self: *const TypeInfo, expr_id: ast.ExprId) ?MethodBinding {
        return self.method_bindings.get(expr_id.toRaw());
    }

    pub fn setMethodBinding(self: *TypeInfo, expr_id: ast.ExprId, binding: MethodBinding) !void {
        try self.method_bindings.put(self.arena.allocator(), expr_id.toRaw(), binding);
    }

    fn updateSnapshot(self: *TypeInfo, map: anytype, key: anytype, val: anytype) !void {
        const gop = try map.getOrPut(self.arena.allocator(), key);
        gop.value_ptr.* = val;
    }

    fn cloneSlice(self: *TypeInfo, comptime T: type, slice: []const T) ![]T {
        const copy = try self.arena.allocator().alloc(T, slice.len);
        @memcpy(copy, slice);
        return copy;
    }

    pub fn storeMethodExprSnapshot(self: *TypeInfo, owner: TypeId, method_name: ast.StrId, expr_ids: []const u32, expr_types: []const TypeId) !void {
        const val = MethodExprSnapshot{
            .expr_ids = try self.cloneSlice(u32, expr_ids),
            .expr_types = try self.cloneSlice(TypeId, expr_types),
        };
        try self.updateSnapshot(&self.method_expr_snapshots, makeMethodKey(owner, method_name), val);
    }

    pub fn applyMethodExprSnapshot(self: *TypeInfo, owner: TypeId, method_name: ast.StrId) bool {
        const snapshot = self.method_expr_snapshots.get(makeMethodKey(owner, method_name)) orelse return false;
        for (snapshot.expr_ids, snapshot.expr_types) |raw, ty| {
            if (raw < self.expr_types.items.len) self.expr_types.items[raw] = ty;
        }
        return true;
    }

    pub fn storeSpecializationExprSnapshot(self: *TypeInfo, decl_id: ast.DeclId, expr_ids: []const u32, expr_types: []const TypeId) !void {
        const val = MethodExprSnapshot{
            .expr_ids = try self.cloneSlice(u32, expr_ids),
            .expr_types = try self.cloneSlice(TypeId, expr_types),
        };
        try self.updateSnapshot(&self.specialization_expr_snapshots, decl_id.toRaw(), val);
    }

    pub fn storeSpecializationComptimeExprSnapshot(self: *TypeInfo, decl_id: ast.DeclId, expr_ids: []const u32, values: []const comp.ComptimeValue) !void {
        const ids = try self.cloneSlice(u32, expr_ids);
        const val_copy = try self.arena.allocator().alloc(comp.ComptimeValue, values.len);
        for (values, 0..) |v, i| val_copy[i] = try comp.cloneComptimeValue(self.arena.allocator(), v);
        try self.updateSnapshot(&self.specialization_comptime_expr_snapshots, decl_id.toRaw(), ComptimeExprSnapshot{ .expr_ids = ids, .values = val_copy });
    }

    pub fn storeSpecializationCallSnapshot(self: *TypeInfo, decl_id: ast.DeclId, expr_ids: []const u32, specs: []const CallSpecialization) !void {
        const gop = try self.specialization_call_snapshots.getOrPut(self.arena.allocator(), decl_id.toRaw());
        const existing_comptime = if (gop.found_existing) gop.value_ptr.comptime_snapshot else null;

        gop.value_ptr.* = .{ .expr_ids = try self.cloneSlice(u32, expr_ids), .specs = try self.cloneSlice(CallSpecialization, specs), .comptime_snapshot = existing_comptime };
    }

    pub fn getSpecializationExprSnapshot(self: *const TypeInfo, decl_id: ast.DeclId) ?MethodExprSnapshot {
        return self.specialization_expr_snapshots.get(decl_id.toRaw());
    }

    pub fn getSpecializationComptimeExprSnapshot(self: *const TypeInfo, decl_id: ast.DeclId) ?ComptimeExprSnapshot {
        return self.specialization_comptime_expr_snapshots.get(decl_id.toRaw());
    }

    pub fn getSpecializationCallSnapshot(self: *const TypeInfo, decl_id: ast.DeclId) ?CallSpecSnapshot {
        return self.specialization_call_snapshots.get(decl_id.toRaw());
    }

    pub fn storeSpecializationComptimeSnapshot(self: *TypeInfo, _: std.mem.Allocator, decl_id: ast.DeclId, names: []const ast.StrId, types: []const TypeId, values: []const comp.ComptimeValue) !void {
        const gop = try self.specialization_call_snapshots.getOrPut(self.arena.allocator(), decl_id.toRaw());
        if (!gop.found_existing) {
            gop.value_ptr.* = .{ .expr_ids = &.{}, .specs = &.{}, .comptime_snapshot = null };
        }

        const val_copy = try self.arena.allocator().alloc(comp.ComptimeValue, values.len);
        for (values, 0..) |v, i| val_copy[i] = try comp.cloneComptimeValue(self.arena.allocator(), v);

        gop.value_ptr.comptime_snapshot = .{
            .names = try self.cloneSlice(ast.StrId, names),
            .types = try self.cloneSlice(TypeId, types),
            .values = val_copy,
        };
    }

    pub fn getSpecializationComptimeSnapshot(self: *const TypeInfo, decl_id: ast.DeclId) ?ComptimeBindingSnapshot {
        return if (self.specialization_call_snapshots.get(decl_id.toRaw())) |snap| snap.comptime_snapshot else null;
    }

    pub fn addExport(self: *TypeInfo, name: ast.StrId, ty: TypeId, decl_id: ast.DeclId) !void {
        try self.exports.put(self.arena.allocator(), name, .{ .ty = ty, .decl_id = decl_id });
    }
    pub fn getExport(self: *const TypeInfo, name: ast.StrId) ?ExportEntry {
        return self.exports.get(name);
    }

    pub fn markSpecializedCall(self: *TypeInfo, _: std.mem.Allocator, expr_id: ast.ExprId, ctx: call_resolution.FunctionDeclContext) !void {
        try self.specialized_calls.put(self.arena.allocator(), expr_id.toRaw(), ctx);
    }

    pub fn setCallSpecialization(self: *TypeInfo, _: std.mem.Allocator, expr_id: ast.ExprId, spec: CallSpecialization) !void {
        try self.call_specializations.put(self.arena.allocator(), expr_id.toRaw(), spec);
    }

    pub fn markRangeSpread(self: *TypeInfo, _: std.mem.Allocator, expr_id: ast.ExprId) !void {
        try self.spread_ranges.put(self.arena.allocator(), expr_id.toRaw(), {});
    }
    pub fn isRangeSpread(self: *const TypeInfo, expr_id: ast.ExprId) bool {
        return self.spread_ranges.contains(expr_id.toRaw());
    }
    pub fn getSpecializedCall(self: *const TypeInfo, expr_id: ast.ExprId) ?call_resolution.FunctionDeclContext {
        return self.specialized_calls.get(expr_id.toRaw());
    }

    pub fn hasComptimeValue(self: *const TypeInfo, expr_id: ast.ExprId) bool {
        return self.comptime_values.contains(expr_id);
    }
    pub fn getComptimeValue(self: *const TypeInfo, expr_id: ast.ExprId) ?*comp.ComptimeValue {
        return self.comptime_values.getPtr(expr_id);
    }

    pub fn setComptimeValue(self: *TypeInfo, expr_id: ast.ExprId, value: comp.ComptimeValue) !void {
        try self.comptime_values.put(self.arena.allocator(), expr_id, value);
    }

    pub fn setComptimeBinding(self: *TypeInfo, name: ast.StrId, ty: TypeId, value: comp.ComptimeValue) !void {
        try self.comptime_bindings.put(self.arena.allocator(), name, .{ .ty = ty, .value = value });
    }

    pub fn lookupComptimeBindingType(self: *const TypeInfo, name: ast.StrId) ?TypeId {
        return if (self.comptime_bindings.get(name)) |e| e.ty else null;
    }

    pub fn cloneComptimeBindingValue(self: *const TypeInfo, gpa: std.mem.Allocator, name: ast.StrId) anyerror!?comp.ComptimeValue {
        return if (self.comptime_bindings.get(name)) |e| try comp.cloneComptimeValue(gpa, e.value) else null;
    }

    pub fn removeComptimeBinding(self: *TypeInfo, name: ast.StrId) void {
        _ = self.comptime_bindings.fetchSwapRemove(name);
    }

    pub fn forEachComptimeBinding(self: *TypeInfo, gpa: std.mem.Allocator, ctx: ?*anyopaque, visitor: ComptimeBindingVisitor) anyerror!void {
        var iter = self.comptime_bindings.iterator();
        while (iter.next()) |entry| {
            var val = try comp.cloneComptimeValue(gpa, entry.value_ptr.value);
            defer if (val != .Void) val.destroy(gpa);
            try visitor(ctx, entry.key_ptr.*, val, entry.value_ptr.ty);
        }
    }

    pub fn setMlirSpliceInfo(self: *TypeInfo, piece_id: ast.MlirPieceId, info: MlirSpliceInfo) !void {
        try self.mlir_splice_info.put(self.arena.allocator(), piece_id.toRaw(), info);
    }
    pub fn getMlirSpliceInfo(self: *const TypeInfo, piece_id: ast.MlirPieceId) ?MlirSpliceInfo {
        return self.mlir_splice_info.get(piece_id.toRaw());
    }

    pub fn getMlirSpliceValue(self: *const TypeInfo, piece_id: ast.MlirPieceId) ?*comp.ComptimeValue {
        return self.mlir_splice_values.getPtr(piece_id.toRaw());
    }
    pub fn setMlirSpliceValue(self: *TypeInfo, piece_id: ast.MlirPieceId, value: comp.ComptimeValue) !void {
        try self.mlir_splice_values.put(self.arena.allocator(), piece_id.toRaw(), value);
    }
};

pub const TypeKind = enum(u8) { Void, Bool, I8, I16, I32, I64, U8, U16, U32, U64, F32, F64, Usize, Complex, Tensor, Simd, String, Any, Code, Undef, Ptr, Slice, Array, DynArray, Map, Optional, Tuple, Function, Struct, Union, Enum, Variant, Error, ErrorSet, MlirModule, MlirAttribute, MlirType, TypeType, Future, Noreturn, Ast, TypeError };

pub const Rows = struct {
    pub const Void = struct {};
    pub const Bool = struct {};
    pub const I8 = struct {};
    pub const I16 = struct {};
    pub const I32 = struct {};
    pub const I64 = struct {};
    pub const U8 = struct {};
    pub const U16 = struct {};
    pub const U32 = struct {};
    pub const U64 = struct {};
    pub const F32 = struct {};
    pub const F64 = struct {};
    pub const Usize = struct {};
    pub const String = struct {};
    pub const Any = struct {};
    pub const Code = struct {};
    pub const Undef = struct {};
    pub const Noreturn = struct {};

    pub const Complex = struct { elem: TypeId };
    pub const Tensor = struct { elem: TypeId, rank: u8, dims: [4]usize };
    pub const Simd = struct { elem: TypeId, lanes: u16 };

    pub const Ptr = struct { elem: TypeId, is_const: bool };
    pub const Slice = struct { elem: TypeId, is_const: bool };
    pub const Array = struct { elem: TypeId, len: usize };
    pub const DynArray = struct { elem: TypeId };
    pub const Map = struct { key: TypeId, value: TypeId };
    pub const Optional = struct { elem: TypeId };
    pub const Future = struct { elem: TypeId };
    pub const Tuple = struct { elems: RangeType };
    pub const Function = struct { params: RangeType, result: TypeId, is_variadic: bool, is_pure: bool, is_extern: bool };
    pub const Field = struct { name: StrId, ty: TypeId };
    pub const EnumMember = struct { name: StrId, value: i64 };
    pub const Struct = struct { fields: RangeField, provenance: u64 };
    pub const Union = struct { fields: RangeField };
    pub const Enum = struct { members: RangeEnumMember, tag_type: TypeId };
    pub const Variant = struct { variants: RangeField };
    pub const Error = struct { variants: RangeField };
    pub const ErrorSet = struct { value_ty: TypeId, error_ty: TypeId };
    pub const MlirModule = struct {};
    pub const MlirAttribute = struct { src: StrId };
    pub const MlirType = struct { src: StrId };
    pub const TypeType = struct { of: TypeId };
    pub const Ast = struct { pkg_name: ast.StrId, filepath: ast.StrId };
    pub const TypeError = struct {};
};

pub const FormatOptions = struct {
    max_depth: u8 = 2,
    max_params: u8 = 5,
    max_fields: u8 = 3,
    show_module_path: bool = true,
    prefer_names: bool = true,
    show_const: bool = true,
};

inline fn RowT(comptime K: TypeKind) type {
    return @field(Rows, @tagName(K));
}

pub const TypeStore = struct {
    arena: *std.heap.ArenaAllocator,
    backing_gpa: std.mem.Allocator,
    gpa: std.mem.Allocator,
    index: StoreIndex(TypeKind) = .{},
    method_table: std.AutoArrayHashMapUnmanaged(MethodKey, MethodEntry) = .{},

    // Table storage
    Void: Table(Rows.Void) = .{},
    Bool: Table(Rows.Bool) = .{},
    I8: Table(Rows.I8) = .{},
    I16: Table(Rows.I16) = .{},
    I32: Table(Rows.I32) = .{},
    I64: Table(Rows.I64) = .{},
    U8: Table(Rows.U8) = .{},
    U16: Table(Rows.U16) = .{},
    U32: Table(Rows.U32) = .{},
    U64: Table(Rows.U64) = .{},
    F32: Table(Rows.F32) = .{},
    F64: Table(Rows.F64) = .{},
    Usize: Table(Rows.Usize) = .{},
    String: Table(Rows.String) = .{},
    Any: Table(Rows.Any) = .{},
    Code: Table(Rows.Code) = .{},
    Undef: Table(Rows.Undef) = .{},
    Noreturn: Table(Rows.Noreturn) = .{},
    MlirModule: Table(Rows.MlirModule) = .{},
    MlirAttribute: Table(Rows.MlirAttribute) = .{},
    MlirType: Table(Rows.MlirType) = .{},

    Complex: Table(Rows.Complex) = .{},
    Tensor: Table(Rows.Tensor) = .{},
    Simd: Table(Rows.Simd) = .{},

    Ptr: Table(Rows.Ptr) = .{},
    Slice: Table(Rows.Slice) = .{},
    Array: Table(Rows.Array) = .{},
    DynArray: Table(Rows.DynArray) = .{},
    Map: Table(Rows.Map) = .{},
    Optional: Table(Rows.Optional) = .{},
    Future: Table(Rows.Future) = .{},
    Tuple: Table(Rows.Tuple) = .{},
    Function: Table(Rows.Function) = .{},
    Field: Table(Rows.Field) = .{},
    Struct: Table(Rows.Struct) = .{},
    Union: Table(Rows.Union) = .{},
    Enum: Table(Rows.Enum) = .{},
    EnumMember: Table(Rows.EnumMember) = .{},
    Variant: Table(Rows.Variant) = .{},
    Error: Table(Rows.Error) = .{},
    ErrorSet: Table(Rows.ErrorSet) = .{},
    TypeType: Table(Rows.TypeType) = .{},
    TypeError: Table(Rows.TypeError) = .{},
    Ast: Table(Rows.Ast) = .{},

    type_pool: Pool(TypeId) = .{},
    field_pool: Pool(FieldId) = .{},
    enum_member_pool: Pool(EnumMemberId) = .{},
    strs: *StringInterner,
    type_names: std.AutoArrayHashMapUnmanaged(TypeId, StrId) = .{},

    // Cached primitive IDs
    t_void: ?TypeId = null,
    t_bool: ?TypeId = null,
    t_i32: ?TypeId = null,
    t_i8: ?TypeId = null,
    t_i16: ?TypeId = null,
    t_i64: ?TypeId = null,
    t_u8: ?TypeId = null,
    t_u16: ?TypeId = null,
    t_u32: ?TypeId = null,
    t_u64: ?TypeId = null,
    t_f32: ?TypeId = null,
    t_f64: ?TypeId = null,
    t_usize: ?TypeId = null,
    t_string: ?TypeId = null,
    t_any: ?TypeId = null,
    t_code: ?TypeId = null,
    t_undef: ?TypeId = null,
    t_type: ?TypeId = null,
    t_noreturn: ?TypeId = null,
    t_mlir_module: ?TypeId = null,
    t_type_error: ?TypeId = null,
    t_test_error: ?TypeId = null,

    pub const TypeInfoKeys = struct {
        name: StrId,
        ty: StrId,
        value: StrId,
        elem: StrId,
        is_const: StrId,
        len: StrId,
        params: StrId,
        result: StrId,
        fields: StrId,
        cases: StrId,
        members: StrId,
        tag: StrId,
        provenance: StrId,
        key: StrId,
        of: StrId,
        err: StrId,
        rank: StrId,
        dims: StrId,
        lanes: StrId,
        src: StrId,
        pkg: StrId,
        filepath: StrId,
        is_variadic: StrId,
        is_pure: StrId,
        is_extern: StrId,
        elems: StrId,
    };

    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner) TypeStore {
        const arena = gpa.create(std.heap.ArenaAllocator) catch @panic("OOM");
        arena.* = std.heap.ArenaAllocator.init(gpa);
        return .{
            .arena = arena,
            .backing_gpa = gpa,
            .gpa = arena.allocator(),
            .strs = strs,
        };
    }

    pub fn deinit(self: *TypeStore) void {
        self.arena.deinit();
        self.backing_gpa.destroy(self.arena);
    }

    pub fn typeInfoKeys(self: *TypeStore) TypeInfoKeys {
        return .{
            .name = self.strs.intern("name"),
            .ty = self.strs.intern("ty"),
            .value = self.strs.intern("value"),
            .elem = self.strs.intern("elem"),
            .is_const = self.strs.intern("is_const"),
            .len = self.strs.intern("len"),
            .params = self.strs.intern("params"),
            .result = self.strs.intern("result"),
            .fields = self.strs.intern("fields"),
            .cases = self.strs.intern("cases"),
            .members = self.strs.intern("members"),
            .tag = self.strs.intern("tag"),
            .provenance = self.strs.intern("provenance"),
            .key = self.strs.intern("key"),
            .of = self.strs.intern("of"),
            .err = self.strs.intern("err"),
            .rank = self.strs.intern("rank"),
            .dims = self.strs.intern("dims"),
            .lanes = self.strs.intern("lanes"),
            .src = self.strs.intern("src"),
            .pkg = self.strs.intern("pkg"),
            .filepath = self.strs.intern("filepath"),
            .is_variadic = self.strs.intern("is_variadic"),
            .is_pure = self.strs.intern("is_pure"),
            .is_extern = self.strs.intern("is_extern"),
            .elems = self.strs.intern("elems"),
        };
    }

    pub fn getKind(self: *const TypeStore, id: TypeId) TypeKind {
        return self.index.kinds.items[id.toRaw()];
    }

    pub fn get(self: *TypeStore, comptime K: TypeKind, id: TypeId) RowT(K) {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = self.index.rows.items[id.toRaw()] });
    }

    pub fn setQualifiedName(self: *TypeStore, id: TypeId, name: StrId) !void {
        const gop = try self.type_names.getOrPut(self.arena.allocator(), id);
        if (!gop.found_existing) gop.value_ptr.* = name;
    }
    pub fn getQualifiedName(self: *const TypeStore, id: TypeId) ?StrId {
        return self.type_names.get(id);
    }

    pub fn addMethod(self: *TypeStore, entry: MethodEntry) !bool {
        const key = makeMethodKey(entry.owner_type, entry.method_name);
        const gop = try self.method_table.getOrPut(self.arena.allocator(), key);
        if (gop.found_existing) return false;
        gop.value_ptr.* = entry;
        return true;
    }

    pub fn putMethod(self: *TypeStore, entry: MethodEntry) !void {
        try self.method_table.put(self.arena.allocator(), makeMethodKey(entry.owner_type, entry.method_name), entry);
    }

    pub fn getMethod(self: *TypeStore, owner: TypeId, name: ast.StrId) ?MethodEntry {
        return self.method_table.get(makeMethodKey(owner, name));
    }

    fn addLocked(self: *TypeStore, comptime K: TypeKind, row: RowT(K)) TypeId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        return self.index.newId(self.arena.allocator(), K, tbl.add(self.arena.allocator(), row).toRaw(), TypeId);
    }

    pub fn add(self: *TypeStore, comptime K: TypeKind, row: RowT(K)) TypeId {
        return self.addLocked(K, row);
    }
    pub fn addField(self: *TypeStore, row: Rows.Field) FieldId {
        return self.Field.add(self.arena.allocator(), row);
    }
    pub fn addEnumMember(self: *TypeStore, row: Rows.EnumMember) EnumMemberId {
        return self.EnumMember.add(self.arena.allocator(), row);
    }

    // Primitive Constructors
    fn mkPrim(self: *TypeStore, comptime K: TypeKind, cache: *?TypeId) TypeId {
        if (cache.*) |id| return id;
        const id = self.addLocked(K, .{});
        cache.* = id;
        return id;
    }

    pub fn tVoid(self: *TypeStore) TypeId {
        return self.mkPrim(.Void, &self.t_void);
    }
    pub fn tBool(self: *TypeStore) TypeId {
        return self.mkPrim(.Bool, &self.t_bool);
    }
    pub fn tI8(self: *TypeStore) TypeId {
        return self.mkPrim(.I8, &self.t_i8);
    }
    pub fn tI16(self: *TypeStore) TypeId {
        return self.mkPrim(.I16, &self.t_i16);
    }
    pub fn tI32(self: *TypeStore) TypeId {
        return self.mkPrim(.I32, &self.t_i32);
    }
    pub fn tI64(self: *TypeStore) TypeId {
        return self.mkPrim(.I64, &self.t_i64);
    }
    pub fn tU8(self: *TypeStore) TypeId {
        return self.mkPrim(.U8, &self.t_u8);
    }
    pub fn tU16(self: *TypeStore) TypeId {
        return self.mkPrim(.U16, &self.t_u16);
    }
    pub fn tU32(self: *TypeStore) TypeId {
        return self.mkPrim(.U32, &self.t_u32);
    }
    pub fn tU64(self: *TypeStore) TypeId {
        return self.mkPrim(.U64, &self.t_u64);
    }
    pub fn tF32(self: *TypeStore) TypeId {
        return self.mkPrim(.F32, &self.t_f32);
    }
    pub fn tF64(self: *TypeStore) TypeId {
        return self.mkPrim(.F64, &self.t_f64);
    }
    pub fn tUsize(self: *TypeStore) TypeId {
        return self.mkPrim(.Usize, &self.t_usize);
    }
    pub fn tString(self: *TypeStore) TypeId {
        return self.mkPrim(.String, &self.t_string);
    }
    pub fn tAny(self: *TypeStore) TypeId {
        return self.mkPrim(.Any, &self.t_any);
    }
    pub fn tCode(self: *TypeStore) TypeId {
        return self.mkPrim(.Code, &self.t_code);
    }
    pub fn tUndef(self: *TypeStore) TypeId {
        return self.mkPrim(.Undef, &self.t_undef);
    }
    pub fn tNoreturn(self: *TypeStore) TypeId {
        return self.mkPrim(.Noreturn, &self.t_noreturn);
    }
    pub fn tNoReturn(self: *TypeStore) TypeId {
        return self.tNoreturn();
    }
    pub fn tMlirModule(self: *TypeStore) TypeId {
        return self.mkPrim(.MlirModule, &self.t_mlir_module);
    }
    pub fn tTypeError(self: *TypeStore) TypeId {
        return self.mkPrim(.TypeError, &self.t_type_error);
    }

    pub fn tType(self: *TypeStore) TypeId {
        if (self.t_type) |id| return id;
        const id = self.addLocked(.TypeType, .{ .of = self.tAny() });
        self.t_type = id;
        self.TypeType.col("of")[self.index.rows.items[id.toRaw()]] = id;
        return id;
    }

    pub fn tTestError(self: *TypeStore) TypeId {
        if (self.t_test_error) |id| return id;
        const fail_name = self.strs.intern("Fail");
        const id = self.mkError(&[_]StructFieldArg{.{ .name = fail_name, .ty = self.tVoid() }});
        self.t_test_error = id;
        return id;
    }

    // Interned Constructors
    pub fn mkPtr(self: *TypeStore, elem: TypeId, is_const: bool) TypeId {
        return self.mkInterned(.Ptr, .{ .elem = elem, .is_const = is_const }, struct {
            fn eq(_: *const TypeStore, r: Rows.Ptr, k: anytype) bool {
                return r.elem.eq(k.elem) and r.is_const == k.is_const;
            }
        });
    }

    pub fn mkSlice(self: *TypeStore, elem: TypeId, is_const: bool) TypeId {
        return self.mkInterned(.Slice, .{ .elem = elem, .is_const = is_const }, struct {
            fn eq(_: *const TypeStore, r: Rows.Slice, k: anytype) bool {
                return r.elem.eq(k.elem) and r.is_const == k.is_const;
            }
        });
    }

    pub fn mkArray(self: *TypeStore, elem: TypeId, len: usize) TypeId {
        return self.mkInterned(.Array, .{ .elem = elem, .len = len }, struct {
            fn eq(_: *const TypeStore, r: Rows.Array, k: anytype) bool {
                return r.elem.eq(k.elem) and r.len == k.len;
            }
        });
    }

    pub fn mkDynArray(self: *TypeStore, elem: TypeId) TypeId {
        return self.mkInterned(.DynArray, .{ .elem = elem }, struct {
            fn eq(_: *const TypeStore, r: Rows.DynArray, k: anytype) bool {
                return r.elem.eq(k.elem);
            }
        });
    }

    pub fn mkMap(self: *TypeStore, key: TypeId, value: TypeId) TypeId {
        return self.mkInterned(.Map, .{ .key = key, .value = value }, struct {
            fn eq(_: *const TypeStore, r: Rows.Map, k: anytype) bool {
                return r.key.eq(k.key) and r.value.eq(k.value);
            }
        });
    }

    pub fn mkAst(self: *TypeStore, pkg_name: ast.StrId, filepath: StrId) TypeId {
        return self.mkInterned(.Ast, .{ .pkg_name = pkg_name, .filepath = filepath }, struct {
            fn eq(_: *const TypeStore, r: Rows.Ast, k: anytype) bool {
                return r.filepath.eq(k.filepath) and r.pkg_name.eq(k.pkg_name);
            }
        });
    }

    pub fn mkSimd(self: *TypeStore, elem: TypeId, lanes: u16) TypeId {
        return self.mkInterned(.Simd, .{ .elem = elem, .lanes = lanes }, struct {
            fn eq(_: *const TypeStore, r: Rows.Simd, k: anytype) bool {
                return r.elem.eq(k.elem) and r.lanes == k.lanes;
            }
        });
    }

    pub fn mkComplex(self: *TypeStore, elem: TypeId) TypeId {
        return self.mkInterned(.Complex, .{ .elem = elem }, struct {
            fn eq(_: *const TypeStore, r: Rows.Complex, k: anytype) bool {
                return r.elem.eq(k.elem);
            }
        });
    }

    pub fn mkOptional(self: *TypeStore, elem: TypeId) TypeId {
        return self.mkInterned(.Optional, .{ .elem = elem }, struct {
            fn eq(_: *const TypeStore, r: Rows.Optional, k: anytype) bool {
                return r.elem.eq(k.elem);
            }
        });
    }

    pub fn mkFuture(self: *TypeStore, elem: TypeId) TypeId {
        return self.mkInterned(.Future, .{ .elem = elem }, struct {
            fn eq(_: *const TypeStore, r: Rows.Future, k: anytype) bool {
                return r.elem.eq(k.elem);
            }
        });
    }

    pub fn mkTypeType(self: *TypeStore, of: TypeId) TypeId {
        return self.mkInterned(.TypeType, .{ .of = of }, struct {
            fn eq(_: *const TypeStore, r: Rows.TypeType, k: anytype) bool {
                return r.of.eq(k.of);
            }
        });
    }

    pub fn mkMlirType(self: *TypeStore, src: StrId) TypeId {
        return self.mkInterned(.MlirType, .{ .src = src }, struct {
            fn eq(_: *const TypeStore, r: Rows.MlirType, k: anytype) bool {
                return r.src.eq(k.src);
            }
        });
    }

    pub fn mkMlirAttribute(self: *TypeStore, src: StrId) TypeId {
        return self.mkInterned(.MlirAttribute, .{ .src = src }, struct {
            fn eq(_: *const TypeStore, r: Rows.MlirAttribute, k: anytype) bool {
                return r.src.eq(k.src);
            }
        });
    }

    pub fn mkErrorSet(self: *TypeStore, value_ty: TypeId, error_ty: TypeId) TypeId {
        return self.mkInterned(.ErrorSet, .{ .value_ty = value_ty, .error_ty = error_ty }, struct {
            fn eq(_: *const TypeStore, r: Rows.ErrorSet, k: anytype) bool {
                return r.value_ty.eq(k.value_ty) and r.error_ty.eq(k.error_ty);
            }
        });
    }

    pub fn mkTensor(self: *TypeStore, elem: TypeId, dims: []const usize) TypeId {
        var row_dims = [_]usize{0} ** max_tensor_rank;
        for (dims, 0..) |d, i| row_dims[i] = d;
        const key = Rows.Tensor{ .elem = elem, .rank = @as(u8, @intCast(dims.len)), .dims = row_dims };

        return self.mkInterned(.Tensor, key, struct {
            fn eq(_: *const TypeStore, r: Rows.Tensor, k: anytype) bool {
                if (!r.elem.eq(k.elem) or r.rank != k.rank) return false;
                for (r.dims[0..r.rank], k.dims[0..k.rank]) |a, b| if (a != b) return false;
                return true;
            }
        });
    }

    pub fn isOptionalPointer(self: *TypeStore, ty: TypeId) bool {
        if (self.getKind(ty) != .Optional) return false;
        return self.getKind(self.get(.Optional, ty).elem) == .Ptr;
    }

    pub fn mkTuple(self: *TypeStore, elems: []const TypeId) TypeId {
        return self.findMatch(.Tuple, elems, struct {
            fn eq(s: *const TypeStore, r: Rows.Tuple, k: []const TypeId) bool {
                const ids = s.type_pool.slice(r.elems);
                if (ids.len != k.len) return false;
                for (ids, k) |a, b| if (!a.eq(b)) return false;
                return true;
            }
        }) orelse self.addLocked(.Tuple, .{ .elems = self.type_pool.pushMany(self.arena.allocator(), elems) });
    }

    pub fn mkFunction(self: *TypeStore, params: []const TypeId, result: TypeId, is_variadic: bool, is_pure: bool, is_extern: bool) TypeId {
        const key = .{ .p = params, .r = result, .v = is_variadic, .pure = is_pure, .ext = is_extern };
        return self.findMatch(.Function, key, struct {
            fn eq(s: *const TypeStore, r: Rows.Function, k: anytype) bool {
                if (!r.result.eq(k.r) or r.is_variadic != k.v or r.is_pure != k.pure or r.is_extern != k.ext) return false;
                const ids = s.type_pool.slice(r.params);
                if (ids.len != k.p.len) return false;
                for (ids, k.p) |a, b| if (!a.eq(b)) return false;
                return true;
            }
        }) orelse blk: {
            const copy = self.arena.allocator().alloc(TypeId, params.len) catch @panic("OOM");
            @memcpy(copy, params);
            break :blk self.addLocked(.Function, .{ .params = self.type_pool.pushMany(self.arena.allocator(), copy), .result = result, .is_variadic = is_variadic, .is_pure = is_pure, .is_extern = is_extern });
        };
    }

    pub const StructFieldArg = struct { name: StrId, ty: TypeId };
    pub const EnumMemberArg = struct { name: StrId, value: i64 };

    pub fn mkEnum(self: *TypeStore, members: []const EnumMemberArg, tag_type: TypeId) TypeId {
        const ids = self.arena.allocator().alloc(EnumMemberId, members.len) catch @panic("OOM");
        for (members, 0..) |m, i| ids[i] = self.addEnumMember(.{ .name = m.name, .value = m.value });
        return self.addLocked(.Enum, .{ .members = self.enum_member_pool.pushMany(self.arena.allocator(), ids), .tag_type = tag_type });
    }

    fn mkFields(self: *TypeStore, fields: []const StructFieldArg) ![]FieldId {
        const ids = try self.arena.allocator().alloc(FieldId, fields.len);
        for (fields, 0..) |f, i| ids[i] = self.addField(.{ .name = f.name, .ty = f.ty });
        return ids;
    }

    // Generic match logic for fields (struct/union/variant/error)
    fn findFields(self: *TypeStore, pool_range: anytype, fields: []const StructFieldArg) bool {
        const ids = self.field_pool.slice(pool_range);
        if (ids.len != fields.len) return false;
        for (ids, 0..) |fid, i| {
            const f = self.Field.get(fid);
            if (!f.name.eq(fields[i].name) or !f.ty.eq(fields[i].ty)) return false;
        }
        return true;
    }

    pub fn mkStruct(self: *TypeStore, fields: []const StructFieldArg, provenance: u64) TypeId {
        const key = .{ .fields = fields, .prov = provenance };
        return self.findMatch(.Struct, key, struct {
            fn eq(s: *TypeStore, r: Rows.Struct, k: anytype) bool {
                return r.provenance == k.prov and s.findFields(r.fields, k.fields);
            }
        }) orelse self.addLocked(.Struct, .{ .fields = self.field_pool.pushMany(self.arena.allocator(), self.mkFields(fields) catch @panic("OOM")), .provenance = provenance });
    }

    pub fn mkUnion(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        return self.findMatch(.Union, fields, struct {
            fn eq(s: *TypeStore, r: Rows.Union, k: anytype) bool {
                return s.findFields(r.fields, k);
            }
        }) orelse self.addLocked(.Union, .{ .fields = self.field_pool.pushMany(self.arena.allocator(), self.mkFields(fields) catch @panic("OOM")) });
    }

    pub fn mkError(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        return self.findMatch(.Error, fields, struct {
            fn eq(s: *TypeStore, r: Rows.Error, k: anytype) bool {
                return s.findFields(r.variants, k);
            }
        }) orelse self.addLocked(.Error, .{ .variants = self.field_pool.pushMany(self.arena.allocator(), self.mkFields(fields) catch @panic("OOM")) });
    }

    pub fn mkVariant(self: *TypeStore, variants: []const StructFieldArg) TypeId {
        return self.findMatch(.Variant, variants, struct {
            fn eq(s: *TypeStore, r: Rows.Variant, k: anytype) bool {
                return s.findFields(r.variants, k);
            }
        }) orelse self.addLocked(.Variant, .{ .variants = self.field_pool.pushMany(self.arena.allocator(), self.mkFields(variants) catch @panic("OOM")) });
    }

    fn findMatch(self: *TypeStore, comptime K: TypeKind, key: anytype, comptime Helper: type) ?TypeId {
        const kinds = self.index.kinds.items;
        const rows = self.index.rows.items;
        for (kinds, 0..) |k, i| {
            if (k != K) continue;
            const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
            if (Helper.eq(self, tbl.get(.{ .index = rows[i] }), key)) return TypeId.fromRaw(@intCast(i));
        }
        return null;
    }

    fn mkInterned(self: *TypeStore, comptime K: TypeKind, key: RowT(K), comptime Comparator: type) TypeId {
        return self.findMatch(K, key, Comparator) orelse self.addLocked(K, key);
    }

    pub fn fmt(self: *TypeStore, id: TypeId, w: anytype) !void {
        const k = self.getKind(id);
        switch (k) {
            .Void => try w.print("void", .{}),
            .Bool => try w.print("bool", .{}),
            .I8 => try w.print("i8", .{}),
            .I16 => try w.print("i16", .{}),
            .I32 => try w.print("i32", .{}),
            .I64 => try w.print("i64", .{}),
            .U8 => try w.print("u8", .{}),
            .U16 => try w.print("u16", .{}),
            .U32 => try w.print("u32", .{}),
            .U64 => try w.print("u64", .{}),
            .F32 => try w.print("f32", .{}),
            .F64 => try w.print("f64", .{}),
            .Usize => try w.print("usize", .{}),
            .String => try w.print("string", .{}),
            .Any => try w.print("any", .{}),
            .Code => try w.print("Code", .{}),
            .Noreturn => try w.print("noreturn", .{}),
            .Undef => try w.print("undef", .{}),
            .MlirModule => try w.print("mlir.module", .{}),
            .MlirAttribute => try w.print("mlir.attribute", .{}),
            .MlirType => try w.print("mlir.type", .{}),
            .TypeError => try w.print("<type error>", .{}),
            .Complex => {
                try w.print("complex@", .{});
                try self.fmt(self.get(.Complex, id).elem, w);
            },
            .Tensor => {
                const r = self.get(.Tensor, id);
                try w.print("tensor{}@", .{r.rank});
                try self.fmt(r.elem, w);
                try w.print("[", .{});
                for (r.dims[0..r.rank], 0..) |d, i| {
                    if (i != 0) try w.print(" x ", .{});
                    try w.print("{}", .{d});
                }
                try w.print("]", .{});
            },
            .Simd => {
                const r = self.get(.Simd, id);
                try w.print("simd{}@", .{r.lanes});
                try self.fmt(r.elem, w);
            },
            .Ptr => {
                try w.print("*", .{});
                try self.fmt(self.get(.Ptr, id).elem, w);
            },
            .Slice => {
                try w.print("[]", .{});
                try self.fmt(self.get(.Slice, id).elem, w);
            },
            .Array => {
                const r = self.get(.Array, id);
                try w.print("[{}]", .{r.len});
                try self.fmt(r.elem, w);
            },
            .DynArray => {
                try w.print("dyn[]", .{});
                try self.fmt(self.get(.DynArray, id).elem, w);
            },
            .Optional => {
                try w.print("?", .{});
                try self.fmt(self.get(.Optional, id).elem, w);
            },
            .Future => {
                try w.print("future<", .{});
                try self.fmt(self.get(.Future, id).elem, w);
                try w.print(">", .{});
            },
            .Tuple => {
                try w.print("(", .{});
                const ids = self.type_pool.slice(self.get(.Tuple, id).elems);
                for (ids, 0..) |e, i| {
                    if (i != 0) try w.print(", ", .{});
                    try self.fmt(e, w);
                }
                try w.print(")", .{});
            },
            .Map => {
                const r = self.get(.Map, id);
                try w.print("map[", .{});
                try self.fmt(r.key, w);
                try w.print("] ", .{});
                try self.fmt(r.value, w);
            },
            .Function => {
                const r = self.get(.Function, id);
                try w.print("{s}(", .{if (r.is_pure) "fn" else "proc"});
                const ids = self.type_pool.slice(r.params);
                for (ids, 0..) |p, i| {
                    if (i != 0) try w.print(", ", .{});
                    try self.fmt(p, w);
                }
                try w.print(") ", .{});
                try self.fmt(r.result, w);
                if (r.is_variadic) try w.print(" variadic", .{});
            },
            .Struct => {
                try w.print("struct {{ ", .{});
                const ids = self.field_pool.slice(self.get(.Struct, id).fields);
                for (ids, 0..) |fid, i| {
                    if (i != 0) try w.print(", ", .{});
                    const f = self.Field.get(fid);
                    try w.print("{s}: ", .{self.strs.get(f.name)});
                    try self.fmt(f.ty, w);
                }
                try w.print(" }}", .{});
            },
            .Enum => {
                const r = self.get(.Enum, id);
                try w.print("enum(", .{});
                try self.fmt(r.tag_type, w);
                try w.print(") {{ ", .{});
                const ids = self.enum_member_pool.slice(r.members);
                for (ids, 0..) |mid, i| {
                    if (i != 0) try w.print(", ", .{});
                    const m = self.EnumMember.get(mid);
                    try w.print("{s} = {}", .{ self.strs.get(m.name), m.value });
                }
                try w.print(" }}", .{});
            },
            .Variant, .Error, .Union => |kk| {
                try w.print("{s} {{ ", .{switch (kk) {
                    .Union => "union",
                    .Error => "error",
                    .Variant => "variant",
                    else => unreachable,
                }});
                const r = switch (kk) {
                    .Variant => self.get(.Variant, id).variants,
                    .Error => self.get(.Error, id).variants,
                    else => self.get(.Union, id).fields,
                };
                const ids = self.field_pool.slice(r);
                for (ids, 0..) |fid, i| {
                    if (i != 0) try w.print(", ", .{});
                    const f = self.Field.get(fid);
                    try w.print("{s}: ", .{self.strs.get(f.name)});
                    try self.fmt(f.ty, w);
                }
                try w.print(" }}", .{});
            },
            .ErrorSet => {
                const r = self.get(.ErrorSet, id);
                try w.print("error(", .{});
                try self.fmt(r.error_ty, w);
                try w.print(", ", .{});
                try self.fmt(r.value_ty, w);
                try w.print(")", .{});
            },
            .TypeType => {
                const of = self.get(.TypeType, id).of;
                if (of.eq(id)) {
                    try w.print("type", .{});
                } else {
                    try w.print("type(", .{});
                    try self.fmt(of, w);
                    try w.print(")", .{});
                }
            },
            .Ast => {
                const r = self.get(.Ast, id);
                try w.print("ast({s}#{s})", .{ self.strs.get(r.pkg_name), self.strs.get(r.filepath) });
            },
        }
    }

    pub fn formatTypeForDiagnostic(self: *TypeStore, type_id: TypeId, options: FormatOptions, writer: anytype) !void {
        try self.fmtDiagnostic(type_id, writer, options, 0);
    }

    fn fmtDiagnostic(self: *TypeStore, type_id: TypeId, writer: anytype, options: FormatOptions, depth: u8) !void {
        if (depth >= options.max_depth) return writer.print("...", .{});
        if (options.prefer_names) if (self.getQualifiedName(type_id)) |name| return writer.print("{s}", .{self.strs.get(name)});

        const kind = self.getKind(type_id);
        switch (kind) {
            .Void, .Bool, .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize, .String, .Any, .Code, .Noreturn, .Undef, .MlirModule, .MlirAttribute, .MlirType, .TypeType, .TypeError, .Ast => try self.fmt(type_id, writer),
            .Ptr => {
                const r = self.get(.Ptr, type_id);
                try writer.print("{s}", .{if (options.show_const and r.is_const) "*const " else "*"});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },
            .Slice => {
                const r = self.get(.Slice, type_id);
                try writer.print("{s}", .{if (options.show_const and r.is_const) "[]const " else "[]"});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },
            .Array => {
                const r = self.get(.Array, type_id);
                try writer.print("[{}]", .{r.len});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },
            .DynArray => {
                const r = self.get(.DynArray, type_id);
                try writer.print("dyn[]", .{});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },
            .Optional => {
                const r = self.get(.Optional, type_id);
                try writer.print("?", .{});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },
            .Future => {
                const r = self.get(.Future, type_id);
                try writer.print("future<", .{});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
                try writer.print(">", .{});
            },
            .Complex => {
                const r = self.get(.Complex, type_id);
                try writer.print("complex@", .{});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },
            .Simd => {
                const r = self.get(.Simd, type_id);
                try writer.print("simd{}@", .{r.lanes});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },
            .Tensor => {
                const r = self.get(.Tensor, type_id);
                try writer.print("tensor<", .{});
                for (r.dims[0..r.rank]) |d| try writer.print("{}x", .{d});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
                try writer.print(">", .{});
            },
            .Tuple => {
                try writer.print("(", .{});
                const ids = self.type_pool.slice(self.get(.Tuple, type_id).elems);
                const limit = @min(ids.len, options.max_fields);
                for (ids[0..limit], 0..) |e, i| {
                    if (i > 0) try writer.print(", ", .{});
                    try self.fmtDiagnostic(e, writer, options, depth + 1);
                }
                if (ids.len > limit) try writer.print(", ... ({d} more)", .{ids.len - limit});
                try writer.print(")", .{});
            },
            .Map => {
                const r = self.get(.Map, type_id);
                try writer.print("map[", .{});
                try self.fmtDiagnostic(r.key, writer, options, depth + 1);
                try writer.print("] ", .{});
                try self.fmtDiagnostic(r.value, writer, options, depth + 1);
            },
            .Function => {
                const r = self.get(.Function, type_id);
                try writer.print("{s}(", .{if (r.is_pure) "fn" else "proc"});
                const params = self.type_pool.slice(r.params);
                const limit = @min(params.len, options.max_params);
                for (params[0..limit], 0..) |p, i| {
                    if (i > 0) try writer.print(", ", .{});
                    try self.fmtDiagnostic(p, writer, options, depth + 1);
                }
                if (params.len > limit) try writer.print(", ... ({d} more)", .{params.len - limit});
                try writer.print(") ", .{});
                try self.fmtDiagnostic(r.result, writer, options, depth + 1);
                if (r.is_variadic) try writer.print(" variadic", .{});
            },
            .Struct => {
                try writer.print("struct {{ ", .{});
                const fields = self.field_pool.slice(self.get(.Struct, type_id).fields);
                const limit = @min(fields.len, options.max_fields);
                for (fields[0..limit], 0..) |fid, i| {
                    if (i > 0) try writer.print(", ", .{});
                    const f = self.Field.get(fid);
                    try writer.print("{s}: ", .{self.strs.get(f.name)});
                    try self.fmtDiagnostic(f.ty, writer, options, depth + 1);
                }
                if (fields.len > limit) try writer.print(", ... ({d} more)", .{fields.len - limit});
                try writer.print(" }}", .{});
            },
            .Enum => {
                const r = self.get(.Enum, type_id);
                try writer.print("enum(", .{});
                try self.fmtDiagnostic(r.tag_type, writer, options, depth + 1);
                try writer.print(") {{ ", .{});
                const members = self.enum_member_pool.slice(r.members);
                const limit = @min(members.len, options.max_fields);
                for (members[0..limit], 0..) |mid, i| {
                    if (i > 0) try writer.print(", ", .{});
                    try writer.print("{s}", .{self.strs.get(self.EnumMember.get(mid).name)});
                }
                if (members.len > limit) try writer.print(", ... ({d} more)", .{members.len - limit});
                try writer.print(" }}", .{});
            },
            .Variant, .Error, .Union => |kk| {
                try writer.print("{s} {{ ", .{switch (kk) {
                    .Union => "union",
                    .Error => "error",
                    .Variant => "variant",
                    else => unreachable,
                }});
                const range = switch (kk) {
                    .Variant => self.get(.Variant, type_id).variants,
                    .Error => self.get(.Error, type_id).variants,
                    else => self.get(.Union, type_id).fields,
                };
                const fields = self.field_pool.slice(range);
                const limit = @min(fields.len, options.max_fields);
                for (fields[0..limit], 0..) |fid, i| {
                    if (i > 0) try writer.print(", ", .{});
                    try writer.print("{s}", .{self.strs.get(self.Field.get(fid).name)});
                }
                if (fields.len > limit) try writer.print(", ... ({d} more)", .{fields.len - limit});
                try writer.print(" }}", .{});
            },
            .ErrorSet => {
                const r = self.get(.ErrorSet, type_id);
                try writer.print("!", .{});
                try self.fmtDiagnostic(r.value_ty, writer, options, depth + 1);
            },
        }
    }
};
