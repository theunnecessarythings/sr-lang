const std = @import("std");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const comp = @import("comptime.zig");
const call_resolution = @import("call_resolution.zig");

// DOD Type Store
/// TypeTag struct definition used by the compiler.
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
    decl: struct {
        decl_id: ast.DeclId,
        name: ast.StrId,
    },
    value_param: struct {
        param_id: ast.ParamId,
        name: ast.StrId,
        ty: TypeId,
    },
    type_param: struct {
        param_id: ast.ParamId,
        name: ast.StrId,
        ty: TypeId,
    },
};

/// MethodReceiverKind enum definition used by the compiler.
pub const MethodReceiverKind = enum {
    none,
    value,
    pointer,
    pointer_const,
};

/// BuiltinMethod enum definition used by the compiler.
pub const BuiltinMethod = enum {
    dynarray_append,
};

/// MethodEntry struct definition used by the compiler.
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

/// MethodBinding struct definition used by the compiler.
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

/// MethodKey struct definition used by the compiler.
pub const MethodKey = struct {
    owner: usize,
    name: usize,
};

/// Instructions for `lower_tir` on how to handle a specific function call.
pub const CallSpecialization = struct {
    /// The concrete function ID to call instead of the one in the AST.
    target_decl: u32, // represents ast.DeclId
    /// File id of the AST that owns `target_decl`.
    target_file_id: u32 = std.math.maxInt(u32),
    /// If true, the backend must create a tuple from the tail arguments before calling.
    pack_args: bool = false,
    /// The index in the argument list where packing begins.
    pack_start_index: usize = 0,
    /// If true, this call uses the spread `..` operator on a tuple,
    /// requiring the backend to explode the tuple onto the stack/registers.
    is_spread: bool = false,
};

/// Key used to cache specializations so we don't generate the same function twice.
pub const SpecializationKey = struct {
    original_decl_id: u32,
    /// The concrete types mapped to the function's parameters for this specific call.
    param_types: []const TypeId,
    // (Future: Add comptime_values hash here)

    pub fn hash(self: SpecializationKey) u64 {
        var hasher: std.hash.Fnv1a_64 = .init();
        hasher.update(std.mem.asBytes(&self.original_decl_id));
        for (self.param_types) |pt| {
            const raw = pt.toRaw();
            hasher.update(std.mem.asBytes(&raw));
        }
        return hasher.final();
    }
    pub fn eql(self: SpecializationKey, other: SpecializationKey) bool {
        if (self.original_decl_id != other.original_decl_id) return false;
        if (self.param_types.len != other.param_types.len) return false;
        for (self.param_types, other.param_types) |a, b| {
            if (!a.eq(b)) return false;
        }
        return true;
    }
};

/// Hash/equality context for `SpecializationKey` that hashes parameter contents.
pub const SpecializationKeyContext = struct {
    pub fn hash(_: @This(), key: SpecializationKey) u64 {
        return key.hash();
    }
    pub fn eql(_: @This(), a: SpecializationKey, b: SpecializationKey) bool {
        return a.eql(b);
    }
};

/// makeMethodKey type system helper.
fn makeMethodKey(owner: TypeId, name: ast.StrId) MethodKey {
    return .{ .owner = owner.toRaw(), .name = name.toRaw() };
}

/// StoredComptimeBinding struct definition used by the compiler.
const StoredComptimeBinding = struct {
    ty: TypeId,
    value: comp.ComptimeValue,
};

pub const ComptimeBindingVisitor = fn (?*anyopaque, ast.StrId, comp.ComptimeValue, TypeId) anyerror!void;

/// TypeInfo struct definition used by the compiler.
pub const TypeInfo = struct {
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
    mlir_splice_info: std.AutoArrayHashMapUnmanaged(u32, MlirSpliceInfo) = .{},
    mlir_splice_values: std.AutoArrayHashMapUnmanaged(u32, comp.ComptimeValue) = .{},
    exports: std.AutoArrayHashMapUnmanaged(ast.StrId, ExportEntry) = .{},
    specialized_calls: std.AutoArrayHashMapUnmanaged(u32, call_resolution.FunctionDeclContext) = .{},
    spread_ranges: std.AutoArrayHashMapUnmanaged(u32, void) = .{},
    call_specializations: std.AutoArrayHashMapUnmanaged(u32, CallSpecialization) = .{},
    synthetic_decls: std.ArrayListUnmanaged(u32) = .{},

    /// ExportEntry struct definition used by the compiler.
    pub const ExportEntry = struct {
        ty: TypeId,
        decl_id: ast.DeclId,
    };

    /// MethodExprSnapshot struct definition used by the compiler.
    const MethodExprSnapshot = struct {
        expr_ids: []u32,
        expr_types: []TypeId,
    };

    const CallSpecSnapshot = struct {
        expr_ids: []u32,
        specs: []CallSpecialization,
    };

    /// init type system helper.
    pub fn init(gpa: std.mem.Allocator, store: *TypeStore) TypeInfo {
        return .{
            .gpa = gpa,
            .store = store,
            .comptime_values = .{},
            .comptime_bindings = .{},
            .mlir_splice_info = .{},
            .mlir_splice_values = .{},
        };
    }
    /// deinit type system helper.
    pub fn deinit(self: *TypeInfo) void {
        self.expr_types.deinit(self.gpa);
        self.decl_types.deinit(self.gpa);
        self.field_index_for_expr.deinit(self.gpa);
        var cv_it = self.comptime_values.iterator();
        while (cv_it.next()) |value_ptr| {
            self.destroyComptimeValue(value_ptr.value_ptr);
        }
        self.comptime_values.deinit(self.gpa);
        var cb_it = self.comptime_bindings.iterator();
        while (cb_it.next()) |entry| {
            self.destroyStoredComptimeBinding(entry.value_ptr);
        }
        self.comptime_bindings.deinit(self.gpa);
        self.method_bindings.deinit(self.gpa);
        var snapshot_it = self.method_expr_snapshots.iterator();
        while (snapshot_it.next()) |entry| {
            self.gpa.free(entry.value_ptr.expr_ids);
            self.gpa.free(entry.value_ptr.expr_types);
        }
        self.method_expr_snapshots.deinit(self.gpa);
        var spec_snapshot_it = self.specialization_expr_snapshots.iterator();
        while (spec_snapshot_it.next()) |entry| {
            self.gpa.free(entry.value_ptr.expr_ids);
            self.gpa.free(entry.value_ptr.expr_types);
        }
        self.specialization_expr_snapshots.deinit(self.gpa);
        var call_snapshot_it = self.specialization_call_snapshots.iterator();
        while (call_snapshot_it.next()) |entry| {
            self.gpa.free(entry.value_ptr.expr_ids);
            self.gpa.free(entry.value_ptr.specs);
        }
        self.specialization_call_snapshots.deinit(self.gpa);
        self.mlir_splice_info.deinit(self.gpa);
        var splice_values_it = self.mlir_splice_values.iterator();
        while (splice_values_it.next()) |entry| {
            self.destroyComptimeValue(entry.value_ptr);
        }
        self.mlir_splice_values.deinit(self.gpa);
        self.exports.deinit(self.gpa);
        self.specialized_calls.deinit(self.gpa);
        self.spread_ranges.deinit(self.gpa);
        self.call_specializations.deinit(self.gpa);
        self.synthetic_decls.deinit(self.gpa);
    }

    /// print type system helper.
    pub fn print(self: *TypeInfo) void {
        std.debug.print("TypeInfo:\n", .{});
        std.debug.print(" Expr types:\n", .{});
        var buffer: [1024]u8 = undefined;
        var writer = std.fs.File.stdout().writer(&buffer);
        for (self.expr_types.items, 0..) |value, i| {
            writer.interface.print("  {}: ", .{i}) catch {};
            if (value) |ty| {
                self.store.fmt(ty, &writer.interface) catch {};
            } else {
                writer.interface.print("null", .{}) catch {};
            }
            writer.interface.print("\n", .{}) catch {};
        }
        writer.interface.flush() catch {};

        std.debug.print("\n Decl types:\n", .{});
        for (self.decl_types.items, 0..) |value, i| {
            writer.interface.print("  {}: ", .{i}) catch {};
            if (value) |ty| {
                self.store.fmt(ty, &writer.interface) catch {};
            } else {
                writer.interface.print("null", .{}) catch {};
            }
            writer.interface.print("\n", .{}) catch {};
        }
        writer.interface.flush() catch {};
    }

    /// Ensure we have room up to (and including) `expr_id.toRaw()`
    pub fn ensureExpr(self: *TypeInfo, gpa: std.mem.Allocator, expr_id: ast.ExprId) !void {
        const need = expr_id.toRaw() + 1;

        if (self.expr_types.items.len < need) {
            try self.expr_types.ensureTotalCapacity(gpa, need);
            while (self.expr_types.items.len < need) self.expr_types.appendAssumeCapacity(null);
        }
        if (self.field_index_for_expr.count() < need) {
            try self.field_index_for_expr.ensureTotalCapacity(gpa, need);
            var i = self.field_index_for_expr.count();
            while (i < need) : (i += 1) {
                try self.field_index_for_expr.put(gpa, @intCast(i), 0xFFFF_FFFF);
            }
        }
    }

    /// setExprType type system helper.
    pub fn setExprType(self: *TypeInfo, expr_id: ast.ExprId, ty: TypeId) void {
        self.expr_types.items[expr_id.toRaw()] = ty;
    }

    /// setFieldIndex type system helper.
    pub fn setFieldIndex(self: *TypeInfo, expr_id: ast.ExprId, idx: u32) !void {
        try self.field_index_for_expr.put(self.gpa, expr_id.toRaw(), idx);
    }

    /// getFieldIndex type system helper.
    pub fn getFieldIndex(self: *const TypeInfo, expr_id: ast.ExprId) ?u32 {
        const v = self.field_index_for_expr.get(expr_id.toRaw()) orelse 0xFFFF_FFFF;
        return if (v == 0xFFFF_FFFF) null else v;
    }

    /// clearFieldIndex type system helper.
    pub fn clearFieldIndex(self: *TypeInfo, expr_id: ast.ExprId) !void {
        try self.field_index_for_expr.put(self.gpa, expr_id.toRaw(), 0xFFFF_FFFF);
    }

    /// getMethodBinding type system helper.
    pub fn getMethodBinding(self: *const TypeInfo, expr_id: ast.ExprId) ?MethodBinding {
        return self.method_bindings.get(expr_id.toRaw());
    }

    /// setMethodBinding type system helper.
    pub fn setMethodBinding(self: *TypeInfo, expr_id: ast.ExprId, binding: MethodBinding) !void {
        const gop = try self.method_bindings.getOrPut(self.gpa, expr_id.toRaw());
        gop.value_ptr.* = binding;
    }

    /// storeMethodExprSnapshot type system helper.
    pub fn storeMethodExprSnapshot(
        self: *TypeInfo,
        owner: TypeId,
        method_name: ast.StrId,
        expr_ids: []const u32,
        expr_types: []const TypeId,
    ) !void {
        std.debug.assert(expr_ids.len == expr_types.len);
        const key = makeMethodKey(owner, method_name);
        const gop = try self.method_expr_snapshots.getOrPut(self.gpa, key);
        if (gop.found_existing) {
            self.gpa.free(gop.value_ptr.expr_ids);
            self.gpa.free(gop.value_ptr.expr_types);
        }
        const ids_copy = try self.gpa.alloc(u32, expr_ids.len);
        const tys_copy = try self.gpa.alloc(TypeId, expr_types.len);
        std.mem.copyForwards(u32, ids_copy, expr_ids);
        std.mem.copyForwards(TypeId, tys_copy, expr_types);
        gop.value_ptr.* = .{ .expr_ids = ids_copy, .expr_types = tys_copy };
    }

    /// applyMethodExprSnapshot type system helper.
    pub fn applyMethodExprSnapshot(
        self: *TypeInfo,
        owner: TypeId,
        method_name: ast.StrId,
    ) bool {
        const key = makeMethodKey(owner, method_name);
        const snapshot = self.method_expr_snapshots.get(key) orelse return false;
        var i: usize = 0;
        while (i < snapshot.expr_ids.len) : (i += 1) {
            const raw = snapshot.expr_ids[i];
            if (raw >= self.expr_types.items.len) continue;
            self.expr_types.items[raw] = snapshot.expr_types[i];
        }
        return true;
    }

    /// storeSpecializationExprSnapshot type system helper.
    pub fn storeSpecializationExprSnapshot(
        self: *TypeInfo,
        decl_id: ast.DeclId,
        expr_ids: []const u32,
        expr_types: []const TypeId,
    ) !void {
        std.debug.assert(expr_ids.len == expr_types.len);
        const gop = try self.specialization_expr_snapshots.getOrPut(self.gpa, decl_id.toRaw());
        if (gop.found_existing) {
            self.gpa.free(gop.value_ptr.expr_ids);
            self.gpa.free(gop.value_ptr.expr_types);
        }
        const ids_copy = try self.gpa.alloc(u32, expr_ids.len);
        const tys_copy = try self.gpa.alloc(TypeId, expr_types.len);
        std.mem.copyForwards(u32, ids_copy, expr_ids);
        std.mem.copyForwards(TypeId, tys_copy, expr_types);
        gop.value_ptr.* = .{ .expr_ids = ids_copy, .expr_types = tys_copy };
    }

    pub fn storeSpecializationCallSnapshot(
        self: *TypeInfo,
        decl_id: ast.DeclId,
        expr_ids: []const u32,
        specs: []const CallSpecialization,
    ) !void {
        std.debug.assert(expr_ids.len == specs.len);
        const gop = try self.specialization_call_snapshots.getOrPut(self.gpa, decl_id.toRaw());
        if (gop.found_existing) {
            self.gpa.free(gop.value_ptr.expr_ids);
            self.gpa.free(gop.value_ptr.specs);
        }
        const ids_copy = try self.gpa.alloc(u32, expr_ids.len);
        const specs_copy = try self.gpa.alloc(CallSpecialization, specs.len);
        std.mem.copyForwards(u32, ids_copy, expr_ids);
        std.mem.copyForwards(CallSpecialization, specs_copy, specs);
        gop.value_ptr.* = .{ .expr_ids = ids_copy, .specs = specs_copy };
    }

    /// getSpecializationExprSnapshot type system helper.
    pub fn getSpecializationExprSnapshot(self: *const TypeInfo, decl_id: ast.DeclId) ?MethodExprSnapshot {
        return self.specialization_expr_snapshots.get(decl_id.toRaw());
    }

    pub fn getSpecializationCallSnapshot(self: *const TypeInfo, decl_id: ast.DeclId) ?CallSpecSnapshot {
        return self.specialization_call_snapshots.get(decl_id.toRaw());
    }

    /// addExport type system helper.
    pub fn addExport(self: *TypeInfo, name: ast.StrId, ty: TypeId, decl_id: ast.DeclId) !void {
        const gop = try self.exports.getOrPut(self.gpa, name);
        gop.value_ptr.* = .{ .ty = ty, .decl_id = decl_id };
    }

    /// getExport type system helper.
    pub fn getExport(self: *const TypeInfo, name: ast.StrId) ?ExportEntry {
        return self.exports.get(name);
    }

    /// markSpecializedCall type system helper.
    pub fn markSpecializedCall(self: *TypeInfo, gpa: std.mem.Allocator, expr_id: ast.ExprId, ctx: call_resolution.FunctionDeclContext) !void {
        const key = expr_id.toRaw();
        const gop = try self.specialized_calls.getOrPut(gpa, key);
        gop.value_ptr.* = ctx;
    }

    /// Maps a Call ExprId to its specialization details for lowering.
    pub fn setCallSpecialization(self: *TypeInfo, gpa: std.mem.Allocator, expr_id: ast.ExprId, spec: CallSpecialization) !void {
        try self.call_specializations.put(gpa, expr_id.toRaw(), spec);
    }

    /// markRangeSpread type system helper.
    pub fn markRangeSpread(self: *TypeInfo, gpa: std.mem.Allocator, expr_id: ast.ExprId) !void {
        try self.spread_ranges.put(gpa, expr_id.toRaw(), {});
    }

    /// isRangeSpread type system helper.
    pub fn isRangeSpread(self: *const TypeInfo, expr_id: ast.ExprId) bool {
        return self.spread_ranges.contains(expr_id.toRaw());
    }

    /// getSpecializedCall type system helper.
    pub fn getSpecializedCall(self: *const TypeInfo, expr_id: ast.ExprId) ?call_resolution.FunctionDeclContext {
        return self.specialized_calls.get(expr_id.toRaw());
    }

    /// hasComptimeValue type system helper.
    pub fn hasComptimeValue(self: *const TypeInfo, expr_id: ast.ExprId) bool {
        return self.comptime_values.get(expr_id) != null;
    }

    /// getComptimeValue type system helper.
    pub fn getComptimeValue(self: *const TypeInfo, expr_id: ast.ExprId) ?*comp.ComptimeValue {
        return if (self.comptime_values.getEntry(expr_id)) |entry| entry.value_ptr else null;
    }

    /// setComptimeValue type system helper.
    pub fn setComptimeValue(self: *TypeInfo, expr_id: ast.ExprId, value: comp.ComptimeValue) !void {
        const gop = try self.comptime_values.getOrPut(self.gpa, expr_id);
        if (gop.found_existing) {
            self.destroyComptimeValue(gop.value_ptr);
        }
        gop.value_ptr.* = value;
    }

    /// setComptimeBinding type system helper.
    pub fn setComptimeBinding(self: *TypeInfo, name: ast.StrId, ty: TypeId, value: comp.ComptimeValue) !void {
        const gop = try self.comptime_bindings.getOrPut(self.gpa, name);
        if (gop.found_existing) {
            self.destroyStoredComptimeBinding(gop.value_ptr);
        }
        gop.value_ptr.* = StoredComptimeBinding{ .ty = ty, .value = value };
    }

    /// lookupComptimeBindingType returns a stored type alias or `null`.
    pub fn lookupComptimeBindingType(self: *const TypeInfo, name: ast.StrId) ?TypeId {
        if (self.comptime_bindings.get(name)) |entry| {
            return entry.ty;
        }
        return null;
    }

    /// cloneComptimeBindingValue duplicates a stored value alias so callers can own it.
    pub fn cloneComptimeBindingValue(
        self: *const TypeInfo,
        gpa: std.mem.Allocator,
        name: ast.StrId,
    ) anyerror!?comp.ComptimeValue {
        if (self.comptime_bindings.get(name)) |entry| {
            return try comp.cloneComptimeValue(gpa, entry.value);
        }
        return null;
    }

    /// forEachComptimeBinding type system helper.
    pub fn forEachComptimeBinding(
        self: *TypeInfo,
        gpa: std.mem.Allocator,
        ctx: ?*anyopaque,
        visitor: ComptimeBindingVisitor,
    ) anyerror!void {
        var iter = self.comptime_bindings.iterator();
        while (iter.next()) |entry| {
            const ty = entry.value_ptr.ty;
            var value = try comp.cloneComptimeValue(gpa, entry.value_ptr.value);
            defer if (value != .Void) value.destroy(gpa);
            try visitor(ctx, entry.key_ptr.*, value, ty);
            value = .Void;
        }
    }

    /// destroyStoredComptimeBinding type system helper.
    fn destroyStoredComptimeBinding(self: *TypeInfo, binding: *StoredComptimeBinding) void {
        binding.value.destroy(self.gpa);
    }

    /// destroyComptimeValue type system helper.
    fn destroyComptimeValue(self: *TypeInfo, value_ptr: *comp.ComptimeValue) void {
        value_ptr.destroy(self.gpa);
    }

    /// setMlirSpliceInfo type system helper.
    pub fn setMlirSpliceInfo(self: *TypeInfo, piece_id: ast.MlirPieceId, info: MlirSpliceInfo) !void {
        const gop = try self.mlir_splice_info.getOrPut(self.gpa, piece_id.toRaw());
        gop.value_ptr.* = info;
    }

    /// getMlirSpliceInfo type system helper.
    pub fn getMlirSpliceInfo(self: *const TypeInfo, piece_id: ast.MlirPieceId) ?MlirSpliceInfo {
        if (self.mlir_splice_info.get(piece_id.toRaw())) |info_ptr|
            return info_ptr;
        return null;
    }

    /// getMlirSpliceValue type system helper.
    pub fn getMlirSpliceValue(self: *const TypeInfo, piece_id: ast.MlirPieceId) ?*comp.ComptimeValue {
        if (self.mlir_splice_values.getPtr(piece_id.toRaw())) |entry| return entry;
        return null;
    }

    /// setMlirSpliceValue type system helper.
    pub fn setMlirSpliceValue(self: *TypeInfo, piece_id: ast.MlirPieceId, value: comp.ComptimeValue) !void {
        const gop = try self.mlir_splice_values.getOrPut(self.gpa, piece_id.toRaw());
        if (gop.found_existing) {
            self.destroyComptimeValue(gop.value_ptr);
        }
        gop.value_ptr.* = value;
    }
};

/// TypeKind enum definition used by the compiler.
pub const TypeKind = enum(u8) {
    Void,
    Bool,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Usize,
    Complex,
    Tensor,
    Simd,
    String,
    Any,
    Undef,
    Ptr,
    Slice,
    Array,
    DynArray,
    Map,
    Optional,
    Tuple,
    Function,
    Struct,
    Union,
    Enum,
    Variant,
    Error,
    ErrorSet,
    MlirModule,
    MlirAttribute,
    MlirType,
    TypeType,
    Noreturn,
    Ast,
    TypeError,
};

/// Rows struct definition used by the compiler.
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
    pub const MlirAttribute = struct {};
    pub const MlirType = struct {};
    pub const TypeType = struct { of: TypeId };
    pub const Ast = struct { pkg_name: ast.StrId, filepath: ast.StrId };
    pub const TypeError = struct {};
};

/// Options for formatting types in diagnostic messages
pub const FormatOptions = struct {
    /// Maximum depth for nested types (default: 2)
    max_depth: u8 = 2,

    /// Maximum parameters to show in function (default: 5)
    max_params: u8 = 5,

    /// Maximum fields to show in struct/enum (default: 3)
    max_fields: u8 = 3,

    /// Show module path for named types (default: true)
    show_module_path: bool = true,

    /// Use type names instead of structure (default: true)
    prefer_names: bool = true,

    /// Show constness for pointers (default: true)
    show_const: bool = true,
};

/// RowT type system helper.
inline fn RowT(comptime K: TypeKind) type {
    return @field(Rows, @tagName(K));
}

/// TypeStore struct definition used by the compiler.
pub const TypeStore = struct {
    gpa: std.mem.Allocator,
    index: StoreIndex(TypeKind) = .{},

    method_table: std.AutoArrayHashMapUnmanaged(MethodKey, MethodEntry) = .{},

    // basic kinds
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

    // cached builtins
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
    t_undef: ?TypeId = null,
    t_type: ?TypeId = null,
    t_noreturn: ?TypeId = null,
    t_mlir_module: ?TypeId = null,
    t_mlir_attribute: ?TypeId = null,
    t_mlir_type: ?TypeId = null,
    t_type_error: ?TypeId = null,

    /// init type system helper.
    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner) TypeStore {
        return .{ .gpa = gpa, .strs = strs };
    }
    /// deinit type system helper.
    pub fn deinit(self: *TypeStore) void {
        const gpa = self.gpa;
        self.index.deinit(gpa);
        self.method_table.deinit(gpa);
        inline for (@typeInfo(TypeKind).@"enum".fields) |f| @field(self, f.name).deinit(gpa);
        self.Field.deinit(gpa);
        self.EnumMember.deinit(gpa);
        self.type_pool.deinit(gpa);
        self.field_pool.deinit(gpa);
        self.enum_member_pool.deinit(gpa);
    }

    /// getKind type system helper.
    pub fn getKind(self: *const TypeStore, id: TypeId) TypeKind {
        return self.index.kinds.items[id.toRaw()];
    }

    /// get type system helper.
    pub fn get(self: *TypeStore, comptime K: TypeKind, id: TypeId) RowT(K) {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = self.index.rows.items[id.toRaw()] });
    }

    /// addMethod type system helper.
    pub fn addMethod(self: *TypeStore, entry: MethodEntry) !bool {
        const key = makeMethodKey(entry.owner_type, entry.method_name);
        const gop = try self.method_table.getOrPut(self.gpa, key);
        if (gop.found_existing) return false;
        gop.value_ptr.* = entry;
        return true;
    }

    /// putMethod type system helper.
    pub fn putMethod(self: *TypeStore, entry: MethodEntry) !void {
        const key = makeMethodKey(entry.owner_type, entry.method_name);
        try self.method_table.put(self.gpa, key, entry);
    }

    /// getMethod type system helper.
    pub fn getMethod(self: *TypeStore, owner: TypeId, name: ast.StrId) ?MethodEntry {
        const key = makeMethodKey(owner, name);
        return self.method_table.get(key);
    }

    /// addLocked type system helper.
    fn addLocked(self: *TypeStore, comptime K: TypeKind, row: RowT(K)) TypeId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), TypeId);
    }

    /// add type system helper.
    pub fn add(self: *TypeStore, comptime K: TypeKind, row: RowT(K)) TypeId {
        return self.addLocked(K, row);
    }

    /// addFieldLocked type system helper.
    fn addFieldLocked(self: *TypeStore, row: Rows.Field) FieldId {
        return self.Field.add(self.gpa, row);
    }

    /// addField type system helper.
    pub fn addField(self: *TypeStore, row: Rows.Field) FieldId {
        return self.addFieldLocked(row);
    }

    /// addEnumMemberLocked type system helper.
    fn addEnumMemberLocked(self: *TypeStore, row: Rows.EnumMember) EnumMemberId {
        return self.EnumMember.add(self.gpa, row);
    }

    /// addEnumMember type system helper.
    pub fn addEnumMember(self: *TypeStore, row: Rows.EnumMember) EnumMemberId {
        return self.addEnumMemberLocked(row);
    }

    // ---- builtin constructors (interned once) ----
    /// tVoidLocked type system helper.
    fn tVoidLocked(self: *TypeStore) TypeId {
        if (self.t_void) |id| return id;
        const id = self.addLocked(.Void, .{});
        self.t_void = id;
        return id;
    }
    /// tVoid type system helper.
    pub fn tVoid(self: *TypeStore) TypeId {
        return self.tVoidLocked();
    }
    /// tBoolLocked type system helper.
    fn tBoolLocked(self: *TypeStore) TypeId {
        if (self.t_bool) |id| return id;
        const id = self.addLocked(.Bool, .{});
        self.t_bool = id;
        return id;
    }
    /// tBool type system helper.
    pub fn tBool(self: *TypeStore) TypeId {
        return self.tBoolLocked();
    }
    /// tI8Locked type system helper.
    fn tI8Locked(self: *TypeStore) TypeId {
        if (self.t_i8) |id| return id;
        const id = self.addLocked(.I8, .{});
        self.t_i8 = id;
        return id;
    }
    /// tI8 type system helper.
    pub fn tI8(self: *TypeStore) TypeId {
        return self.tI8Locked();
    }
    /// tI16Locked type system helper.
    fn tI16Locked(self: *TypeStore) TypeId {
        if (self.t_i16) |id| return id;
        const id = self.addLocked(.I16, .{});
        self.t_i16 = id;
        return id;
    }
    /// tI16 type system helper.
    pub fn tI16(self: *TypeStore) TypeId {
        return self.tI16Locked();
    }
    /// tI32Locked type system helper.
    fn tI32Locked(self: *TypeStore) TypeId {
        if (self.t_i32) |id| return id;
        const id = self.addLocked(.I32, .{});
        self.t_i32 = id;
        return id;
    }
    /// tI32 type system helper.
    pub fn tI32(self: *TypeStore) TypeId {
        return self.tI32Locked();
    }
    /// tI64Locked type system helper.
    fn tI64Locked(self: *TypeStore) TypeId {
        if (self.t_i64) |id| return id;
        const id = self.addLocked(.I64, .{});
        self.t_i64 = id;
        return id;
    }
    /// tI64 type system helper.
    pub fn tI64(self: *TypeStore) TypeId {
        return self.tI64Locked();
    }
    /// tU8Locked type system helper.
    fn tU8Locked(self: *TypeStore) TypeId {
        if (self.t_u8) |id| return id;
        const id = self.addLocked(.U8, .{});
        self.t_u8 = id;
        return id;
    }
    /// tU8 type system helper.
    pub fn tU8(self: *TypeStore) TypeId {
        return self.tU8Locked();
    }
    /// tU16Locked type system helper.
    fn tU16Locked(self: *TypeStore) TypeId {
        if (self.t_u16) |id| return id;
        const id = self.addLocked(.U16, .{});
        self.t_u16 = id;
        return id;
    }
    /// tU16 type system helper.
    pub fn tU16(self: *TypeStore) TypeId {
        return self.tU16Locked();
    }
    /// tU32Locked type system helper.
    fn tU32Locked(self: *TypeStore) TypeId {
        if (self.t_u32) |id| return id;
        const id = self.addLocked(.U32, .{});
        self.t_u32 = id;
        return id;
    }

    pub fn tU64(self: *TypeStore) TypeId {
        return self.tU64Locked();
    }

    fn tU64Locked(self: *TypeStore) TypeId {
        if (self.t_u64) |id| return id;
        const id = self.addLocked(.U64, .{});
        self.t_u64 = id;
        return id;
    }

    /// tU32 type system helper.
    pub fn tU32(self: *TypeStore) TypeId {
        return self.tU32Locked();
    }
    /// tF32Locked type system helper.
    fn tF32Locked(self: *TypeStore) TypeId {
        if (self.t_f32) |id| return id;
        const id = self.addLocked(.F32, .{});
        self.t_f32 = id;
        return id;
    }
    /// tF32 type system helper.
    pub fn tF32(self: *TypeStore) TypeId {
        return self.tF32Locked();
    }
    /// tF64Locked type system helper.
    fn tF64Locked(self: *TypeStore) TypeId {
        if (self.t_f64) |id| return id;
        const id = self.addLocked(.F64, .{});
        self.t_f64 = id;
        return id;
    }
    /// tF64 type system helper.
    pub fn tF64(self: *TypeStore) TypeId {
        return self.tF64Locked();
    }
    /// tUsizeLocked type system helper.
    fn tUsizeLocked(self: *TypeStore) TypeId {
        if (self.t_usize) |id| return id;
        const id = self.addLocked(.Usize, .{});
        self.t_usize = id;
        return id;
    }
    /// tUsize type system helper.
    pub fn tUsize(self: *TypeStore) TypeId {
        return self.tUsizeLocked();
    }
    /// tStringLocked type system helper.
    fn tStringLocked(self: *TypeStore) TypeId {
        if (self.t_string) |id| return id;
        const id = self.addLocked(.String, .{});
        self.t_string = id;
        return id;
    }
    /// tString type system helper.
    pub fn tString(self: *TypeStore) TypeId {
        return self.tStringLocked();
    }
    /// tAnyLocked type system helper.
    fn tAnyLocked(self: *TypeStore) TypeId {
        if (self.t_any) |id| return id;
        const id = self.addLocked(.Any, .{});
        self.t_any = id;
        return id;
    }
    /// tAny type system helper.
    pub fn tAny(self: *TypeStore) TypeId {
        return self.tAnyLocked();
    }
    /// tUndefLocked type system helper.
    fn tUndefLocked(self: *TypeStore) TypeId {
        if (self.t_undef) |id| return id;
        const id = self.addLocked(.Undef, .{});
        self.t_undef = id;
        return id;
    }
    /// tUndef type system helper.
    pub fn tUndef(self: *TypeStore) TypeId {
        return self.tUndefLocked();
    }
    /// tTypeLocked type system helper.
    fn tTypeLocked(self: *TypeStore) TypeId {
        if (self.t_type) |id| return id;
        const id = self.addLocked(.TypeType, .{ .of = self.tAnyLocked() });
        self.t_type = id;
        return id;
    }
    /// tType type system helper.
    pub fn tType(self: *TypeStore) TypeId {
        return self.tTypeLocked();
    }
    /// tNoreturnLocked type system helper.
    fn tNoreturnLocked(self: *TypeStore) TypeId {
        if (self.t_noreturn) |id| return id;
        const id = self.addLocked(.Noreturn, .{});
        self.t_noreturn = id;
        return id;
    }
    /// tNoreturn type system helper.
    pub fn tNoreturn(self: *TypeStore) TypeId {
        return self.tNoreturnLocked();
    }
    /// tNoReturn type system helper.
    pub fn tNoReturn(self: *TypeStore) TypeId {
        return self.tNoreturnLocked();
    }

    /// tMlirModuleLocked type system helper.
    fn tMlirModuleLocked(self: *TypeStore) TypeId {
        if (self.t_mlir_module) |id| return id;
        const id = self.addLocked(.MlirModule, .{});
        self.t_mlir_module = id;
        return id;
    }
    /// tMlirModule type system helper.
    pub fn tMlirModule(self: *TypeStore) TypeId {
        return self.tMlirModuleLocked();
    }

    /// tMlirAttributeLocked type system helper.
    fn tMlirAttributeLocked(self: *TypeStore) TypeId {
        if (self.t_mlir_attribute) |id| return id;
        const id = self.addLocked(.MlirAttribute, .{});
        self.t_mlir_attribute = id;
        return id;
    }
    /// tMlirAttribute type system helper.
    pub fn tMlirAttribute(self: *TypeStore) TypeId {
        return self.tMlirAttributeLocked();
    }

    /// tMlirTypeLocked type system helper.
    fn tMlirTypeLocked(self: *TypeStore) TypeId {
        if (self.t_mlir_type) |id| return id;
        const id = self.addLocked(.MlirType, .{});
        self.t_mlir_type = id;
        return id;
    }
    /// tMlirType type system helper.
    pub fn tMlirType(self: *TypeStore) TypeId {
        return self.tMlirTypeLocked();
    }

    /// tTypeErrorLocked type system helper.
    fn tTypeErrorLocked(self: *TypeStore) TypeId {
        if (self.t_type_error) |id| return id;
        const id = self.addLocked(.TypeError, .{});
        self.t_type_error = id;
        return id;
    }
    /// tTypeError type system helper.
    pub fn tTypeError(self: *TypeStore) TypeId {
        return self.tTypeErrorLocked();
    }

    // ---- constructors with interning (linear dedup) ----
    /// mkPtr type system helper.
    pub fn mkPtr(self: *TypeStore, elem: TypeId, is_const: bool) TypeId {
        if (self.findPtr(elem, is_const)) |id| return id;
        return self.addLocked(.Ptr, .{ .elem = elem, .is_const = is_const });
    }
    /// mkSlice type system helper.
    pub fn mkSlice(self: *TypeStore, elem: TypeId, is_const: bool) TypeId {
        if (self.findSlice(elem, is_const)) |id| return id;
        return self.addLocked(.Slice, .{ .elem = elem, .is_const = is_const });
    }
    /// mkArray type system helper.
    pub fn mkArray(self: *TypeStore, elem: TypeId, len: usize) TypeId {
        if (self.findArray(elem, len)) |id| return id;
        return self.addLocked(.Array, .{ .elem = elem, .len = len });
    }
    /// mkDynArray type system helper.
    pub fn mkDynArray(self: *TypeStore, elem: TypeId) TypeId {
        if (self.findDynArray(elem)) |id| return id;
        return self.addLocked(.DynArray, .{ .elem = elem });
    }
    /// mkMap type system helper.
    pub fn mkMap(self: *TypeStore, key: TypeId, value: TypeId) TypeId {
        if (self.findMap(key, value)) |id| return id;
        return self.addLocked(.Map, .{ .key = key, .value = value });
    }
    /// mkAst type system helper.
    pub fn mkAst(self: *TypeStore, pkg_name: ast.StrId, filepath: StrId) TypeId {
        if (self.findAst(pkg_name, filepath)) |id| return id;
        return self.addLocked(.Ast, .{
            .pkg_name = pkg_name,
            .filepath = filepath,
        });
    }
    /// mkSimd type system helper.
    pub fn mkSimd(self: *TypeStore, elem: TypeId, lanes: u16) TypeId {
        if (self.findSimd(elem, lanes)) |id| return id;
        return self.addLocked(.Simd, .{ .elem = elem, .lanes = lanes });
    }
    /// mkTensor type system helper.
    pub fn mkTensor(self: *TypeStore, elem: TypeId, dims: []const usize) TypeId {
        std.debug.assert(dims.len <= max_tensor_rank);
        if (self.findTensor(elem, dims)) |id| return id;
        var row_dims = [_]usize{0} ** max_tensor_rank;
        var i: usize = 0;
        while (i < dims.len) : (i += 1) row_dims[i] = dims[i];
        return self.addLocked(.Tensor, .{
            .elem = elem,
            .rank = @intCast(dims.len),
            .dims = row_dims,
        });
    }
    /// mkOptional type system helper.
    pub fn mkOptional(self: *TypeStore, elem: TypeId) TypeId {
        if (self.findOptional(elem)) |id| return id;
        return self.addLocked(.Optional, .{ .elem = elem });
    }
    /// isOptionalPointer type system helper.
    pub fn isOptionalPointer(self: *TypeStore, ty: TypeId) bool {
        if (self.index.kinds.items[ty.toRaw()] != .Optional) return false;
        const elem = self.get(.Optional, ty).elem;
        return self.index.kinds.items[elem.toRaw()] == .Ptr;
    }
    /// mkTuple type system helper.
    pub fn mkTuple(self: *TypeStore, elems: []const TypeId) TypeId {
        if (self.findTuple(elems)) |id| return id;
        const r = self.type_pool.pushMany(self.gpa, elems);
        return self.addLocked(.Tuple, .{ .elems = r });
    }
    /// mkFunction type system helper.
    pub fn mkFunction(self: *TypeStore, params: []const TypeId, result: TypeId, is_variadic: bool, is_pure: bool, is_extern: bool) TypeId {
        if (self.findFunction(params, result, is_variadic, is_pure, is_extern)) |id| return id;

        // Copy params to a temporary buffer to avoid use-after-free if params is a slice of self.type_pool
        const params_copy = self.gpa.alloc(TypeId, params.len) catch @panic("OOM");
        defer self.gpa.free(params_copy);
        @memcpy(params_copy, params);

        const r = self.type_pool.pushMany(self.gpa, params_copy);
        return self.addLocked(.Function, .{ .params = r, .result = result, .is_variadic = is_variadic, .is_pure = is_pure, .is_extern = is_extern });
    }
    /// EnumMemberArg struct definition used by the compiler.
    pub const EnumMemberArg = struct { name: StrId, value: i64 };
    /// mkEnum type system helper.
    pub fn mkEnum(self: *TypeStore, members: []const EnumMemberArg, tag_type: TypeId) TypeId {
        var ids = self.gpa.alloc(EnumMemberId, members.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < members.len) : (i += 1) {
            const mid = self.addEnumMemberLocked(.{ .name = members[i].name, .value = members[i].value });
            ids[i] = mid;
        }
        const r = self.enum_member_pool.pushMany(self.gpa, ids);
        return self.addLocked(.Enum, .{ .members = r, .tag_type = tag_type });
    }
    /// mkVariant type system helper.
    pub fn mkVariant(self: *TypeStore, variants: []const StructFieldArg) TypeId {
        if (self.findVariant(variants)) |id| return id;
        var ids = self.gpa.alloc(FieldId, variants.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < variants.len) : (i += 1) {
            const fid = self.addFieldLocked(.{ .name = variants[i].name, .ty = variants[i].ty });
            ids[i] = fid;
        }
        const r = self.field_pool.pushMany(self.gpa, ids);
        return self.addLocked(.Variant, .{ .variants = r });
    }
    /// mkErrorSet type system helper.
    pub fn mkErrorSet(self: *TypeStore, value_ty: TypeId, error_ty: TypeId) TypeId {
        if (self.findErrorSet(value_ty, error_ty)) |id| return id;
        return self.addLocked(.ErrorSet, .{ .value_ty = value_ty, .error_ty = error_ty });
    }
    /// mkTypeType type system helper.
    pub fn mkTypeType(self: *TypeStore, of: TypeId) TypeId {
        if (self.findTypeType(of)) |id| return id;
        return self.addLocked(.TypeType, .{ .of = of });
    }
    /// StructFieldArg struct definition used by the compiler.
    pub const StructFieldArg = struct { name: StrId, ty: TypeId };
    /// mkStruct type system helper.
    pub fn mkStruct(self: *TypeStore, fields: []const StructFieldArg, provenance: u64) TypeId {
        // Build interning key arrays
        if (self.findStruct(fields, provenance)) |id| return id;
        var ids = self.gpa.alloc(FieldId, fields.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const fid = self.addFieldLocked(.{ .name = fields[i].name, .ty = fields[i].ty });
            ids[i] = fid;
        }
        const r = self.field_pool.pushMany(self.gpa, ids);
        return self.addLocked(.Struct, .{ .fields = r, .provenance = provenance });
    }
    /// mkUnion type system helper.
    pub fn mkUnion(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        var ids = self.gpa.alloc(FieldId, fields.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const fid = self.addFieldLocked(.{ .name = fields[i].name, .ty = fields[i].ty });
            ids[i] = fid;
        }
        const r = self.field_pool.pushMany(self.gpa, ids);
        return self.addLocked(.Union, .{ .fields = r });
    }
    /// mkError type system helper.
    pub fn mkError(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        var ids = self.gpa.alloc(FieldId, fields.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const fid = self.addFieldLocked(.{ .name = fields[i].name, .ty = fields[i].ty });
            ids[i] = fid;
        }
        const r = self.field_pool.pushMany(self.gpa, ids);
        return self.addLocked(.Error, .{ .variants = r });
    }

    // ---- finders ----
    /// findPtr type system helper.
    fn findPtr(self: *TypeStore, elem: TypeId, is_const: bool) ?TypeId {
        return self.findMatch(.Ptr, struct { e: TypeId, c: bool }{ .e = elem, .c = is_const }, struct {
            /// eq type system helper.
            fn eq(s: *const TypeStore, row: Rows.Ptr, key: anytype) bool {
                _ = s;
                return row.elem.eq(key.e) and row.is_const == key.c;
            }
        });
    }
    /// findSlice type system helper.
    fn findSlice(self: *TypeStore, elem: TypeId, is_const: bool) ?TypeId {
        return self.findMatch(.Slice, struct { e: TypeId, c: bool }{ .e = elem, .c = is_const }, struct {
            /// eq type system helper.
            fn eq(s: *const TypeStore, row: Rows.Slice, key: anytype) bool {
                _ = s;
                return row.elem.eq(key.e) and row.is_const == key.c;
            }
        });
    }
    /// findDynArray type system helper.
    fn findDynArray(self: *TypeStore, elem: TypeId) ?TypeId {
        return self.findMatch(.DynArray, elem, struct {
            /// eq type system helper.
            fn eq(s: *const TypeStore, row: Rows.DynArray, key: TypeId) bool {
                _ = s;
                return row.elem.eq(key);
            }
        });
    }
    /// findArray type system helper.
    fn findArray(self: *TypeStore, elem: TypeId, len: usize) ?TypeId {
        return self.findMatch(.Array, struct { e: TypeId, l: usize }{ .e = elem, .l = len }, struct {
            /// eq type system helper.
            fn eq(s: *const TypeStore, row: Rows.Array, key: anytype) bool {
                _ = s;
                return row.elem.eq(key.e) and row.len == key.l;
            }
        });
    }
    /// findTensor type system helper.
    fn findTensor(self: *TypeStore, elem: TypeId, dims: []const usize) ?TypeId {
        return self.findMatch(.Tensor, struct { e: TypeId, d: []const usize }{ .e = elem, .d = dims }, struct {
            /// eq type system helper.
            fn eq(_: *const TypeStore, row: Rows.Tensor, key: anytype) bool {
                if (!row.elem.eq(key.e)) return false;
                if (row.rank != key.d.len) return false;
                var i: usize = 0;
                while (i < row.rank) : (i += 1) {
                    if (row.dims[i] != key.d[i]) return false;
                }
                return true;
            }
        });
    }
    /// findMap type system helper.
    fn findMap(self: *TypeStore, key: TypeId, value: TypeId) ?TypeId {
        return self.findMatch(.Map, struct { k: TypeId, v: TypeId }{ .k = key, .v = value }, struct {
            /// eq type system helper.
            fn eq(s: *const TypeStore, row: Rows.Map, k: anytype) bool {
                _ = s;
                return row.key.eq(k.k) and row.value.eq(k.v);
            }
        });
    }
    /// findAst type system helper.
    fn findAst(self: *TypeStore, pkg_name: ast.StrId, filepath: StrId) ?TypeId {
        return self.findMatch(.Ast, struct { pkg: ast.StrId, filepath: StrId }{
            .pkg = pkg_name,
            .filepath = filepath,
        }, struct {
            /// eq type system helper.
            fn eq(_: *const TypeStore, row: Rows.Ast, key: anytype) bool {
                return row.filepath.eq(key.filepath) and row.pkg_name.eq(key.pkg);
            }
        });
    }
    /// findSimd type system helper.
    fn findSimd(self: *TypeStore, elem: TypeId, lanes: u16) ?TypeId {
        return self.findMatch(.Simd, struct { e: TypeId, l: u16 }{ .e = elem, .l = lanes }, struct {
            /// eq type system helper.
            fn eq(_: *const TypeStore, row: Rows.Simd, key: anytype) bool {
                return row.elem.eq(key.e) and row.lanes == key.l;
            }
        });
    }
    /// findOptional type system helper.
    fn findOptional(self: *TypeStore, elem: TypeId) ?TypeId {
        return self.findMatch(.Optional, elem, struct {
            /// eq type system helper.
            fn eq(s: *const TypeStore, row: Rows.Optional, key: TypeId) bool {
                _ = s;
                return row.elem.eq(key);
            }
        });
    }
    /// findTuple type system helper.
    fn findTuple(self: *TypeStore, elems: []const TypeId) ?TypeId {
        return self.findMatch(.Tuple, elems, struct {
            /// eq type system helper.
            fn eq(s: *const TypeStore, row: Rows.Tuple, key: []const TypeId) bool {
                const ids = s.type_pool.slice(row.elems);
                if (ids.len != key.len) return false;
                var i: usize = 0;
                while (i < ids.len) : (i += 1) if (!ids[i].eq(key[i])) return false;
                return true;
            }
        });
    }
    /// findFunction type system helper.
    fn findFunction(self: *TypeStore, params: []const TypeId, result: TypeId, is_variadic: bool, is_pure: bool, is_extern: bool) ?TypeId {
        return self.findMatch(.Function, struct { p: []const TypeId, r: TypeId, v: bool, pure: bool, ext: bool }{ .p = params, .r = result, .v = is_variadic, .pure = is_pure, .ext = is_extern }, struct {
            /// eq type system helper.
            fn eq(s: *const TypeStore, row: Rows.Function, key: anytype) bool {
                if (!row.result.eq(key.r) or row.is_variadic != key.v or row.is_pure != key.pure or row.is_extern != key.ext) return false;
                const ids = s.type_pool.slice(row.params);
                if (ids.len != key.p.len) return false;
                var i: usize = 0;
                while (i < ids.len) : (i += 1) if (!ids[i].eq(key.p[i])) return false;
                return true;
            }
        });
    }

    /// findVariant type system helper.
    fn findVariant(self: *TypeStore, variants: []const StructFieldArg) ?TypeId {
        // Compare by name + type sequence
        // Key that pairs variant field names with their types for equality checks.
        const key_names_and_tys = struct { names: []const StrId, tys: []const TypeId };
        var names = self.gpa.alloc(StrId, variants.len) catch @panic("OOM");
        defer self.gpa.free(names);
        var tys = self.gpa.alloc(TypeId, variants.len) catch @panic("OOM");
        defer self.gpa.free(tys);
        var i: usize = 0;
        while (i < variants.len) : (i += 1) {
            names[i] = variants[i].name;
            tys[i] = variants[i].ty;
        }
        const key_val = key_names_and_tys{ .names = names, .tys = tys };
        return self.findMatch(.Variant, key_val, struct {
            /// eq type system helper.
            fn eq(s: *TypeStore, row: Rows.Variant, k: anytype) bool {
                const ids = s.field_pool.slice(row.variants);
                if (ids.len != k.names.len) return false;
                var j: usize = 0;
                while (j < ids.len) : (j += 1) {
                    const f = s.Field.get(ids[j]);
                    if (!f.name.eq(k.names[j])) return false;
                    if (!f.ty.eq(k.tys[j])) return false;
                }
                return true;
            }
        });
    }
    /// findErrorSet type system helper.
    fn findErrorSet(self: *TypeStore, value_ty: TypeId, error_ty: TypeId) ?TypeId {
        return self.findMatch(.ErrorSet, struct { v: TypeId, e: TypeId }{ .v = value_ty, .e = error_ty }, struct {
            /// eq type system helper.
            fn eq(s: *const TypeStore, row: Rows.ErrorSet, k: anytype) bool {
                _ = s;
                return row.value_ty.eq(k.v) and row.error_ty.eq(k.e);
            }
        });
    }

    /// findTypeType type system helper.
    fn findTypeType(self: *TypeStore, of: TypeId) ?TypeId {
        return self.findMatch(.TypeType, of, struct {
            /// eq type system helper.
            fn eq(_: *const TypeStore, row: Rows.TypeType, key: TypeId) bool {
                return row.of.eq(key);
            }
        });
    }
    /// findStruct type system helper.
    fn findStruct(self: *TypeStore, fields: []const StructFieldArg, provenance: u64) ?TypeId {
        // Compare by name + type sequence
        // Key that pairs struct field names with their types for equality checks.
        const key_names_and_tys = struct { names: []const StrId, tys: []const TypeId, prov: u64 };
        var names = self.gpa.alloc(StrId, fields.len) catch @panic("OOM");
        defer self.gpa.free(names);
        var tys = self.gpa.alloc(TypeId, fields.len) catch @panic("OOM");
        defer self.gpa.free(tys);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            names[i] = fields[i].name;
            tys[i] = fields[i].ty;
        }
        const key_val = key_names_and_tys{ .names = names, .tys = tys, .prov = provenance };
        return self.findMatch(.Struct, key_val, struct {
            /// eq type system helper.
            fn eq(s: *TypeStore, row: Rows.Struct, k: anytype) bool {
                if (row.provenance != k.prov) return false;
                const ids = s.field_pool.slice(row.fields);
                if (ids.len != k.names.len) return false;
                var j: usize = 0;
                while (j < ids.len) : (j += 1) {
                    const f = s.Field.get(ids[j]);
                    if (!f.name.eq(k.names[j])) return false;
                    if (!f.ty.eq(k.tys[j])) return false;
                }
                return true;
            }
        });
    }

    /// findMatch type system helper.
    fn findMatch(self: *TypeStore, comptime K: TypeKind, key: anytype, comptime Helper: type) ?TypeId {
        // Scan all types and find first matching row of kind K
        const kinds = self.index.kinds.items;
        const rows = self.index.rows.items;
        var i: usize = 0;
        while (i < kinds.len) : (i += 1) {
            if (kinds[i] != K) continue;
            const row_idx = rows[i];
            const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
            const row = tbl.get(.{ .index = row_idx });
            if (Helper.eq(self, row, key)) return TypeId.fromRaw(@intCast(i));
        }
        return null;
    }

    // ---- formatting ----
    /// fmt type system helper.
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
            .Noreturn => try w.print("noreturn", .{}),
            .Undef => try w.print("undef", .{}),
            .MlirModule => try w.print("mlir.module", .{}),
            .MlirAttribute => try w.print("mlir.attribute", .{}),
            .MlirType => try w.print("mlir.type", .{}),
            .Complex => {
                const r = self.get(.Complex, id);
                try w.print("complex@", .{});
                try self.fmt(r.elem, w);
            },
            .Tensor => {
                const r = self.get(.Tensor, id);
                try w.print("tensor{}@", .{r.rank});
                try self.fmt(r.elem, w);
                try w.print("[", .{});
                var i: u8 = 0;
                while (i < r.rank) : (i += 1) {
                    if (i != 0) try w.print(" x ", .{});
                    try w.print("{}", .{r.dims[i]});
                }
                try w.print("]", .{});
            },
            .Simd => {
                const r = self.get(.Simd, id);
                try w.print("simd{}@", .{r.lanes});
                try self.fmt(r.elem, w);
            },
            .Ptr => {
                const r = self.get(.Ptr, id);
                try w.print("*", .{});
                try self.fmt(r.elem, w);
            },
            .Slice => {
                const r = self.get(.Slice, id);
                try w.print("[]", .{});
                try self.fmt(r.elem, w);
            },
            .Array => {
                const r = self.get(.Array, id);
                try w.print("[{}]", .{r.len});
                try self.fmt(r.elem, w);
            },
            .DynArray => {
                const r = self.get(.DynArray, id);
                try w.print("dyn[]", .{});
                try self.fmt(r.elem, w);
            },
            .Optional => {
                const r = self.get(.Optional, id);
                try w.print("?", .{});
                try self.fmt(r.elem, w);
            },
            .Tuple => {
                const r = self.get(.Tuple, id);
                try w.print("(", .{});
                const ids = self.type_pool.slice(r.elems);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    try self.fmt(ids[i], w);
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
                // print kind as 'fn' for pure, 'proc' otherwise
                if (r.is_pure) {
                    try w.print("fn(", .{});
                } else {
                    try w.print("proc(", .{});
                }
                const ids = self.type_pool.slice(r.params);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    try self.fmt(ids[i], w);
                }
                try w.print(") ", .{});
                try self.fmt(r.result, w);
                if (r.is_variadic) try w.print(" variadic", .{});
            },
            .Struct => {
                const r = self.get(.Struct, id);
                try w.print("struct {{ ", .{});
                const ids = self.field_pool.slice(r.fields);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    const f = self.Field.get(ids[i]);
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
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    const member = self.EnumMember.get(ids[i]);
                    try w.print("{s} = {}", .{ self.strs.get(member.name), member.value });
                }
                try w.print(" }}", .{});
            },
            .Variant => {
                const r = self.get(.Variant, id);
                try w.print("variant {{ ", .{});
                const ids = self.field_pool.slice(r.variants);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    const f = self.Field.get(ids[i]);
                    try w.print("{s}: ", .{self.strs.get(f.name)});
                    try self.fmt(f.ty, w);
                }
                try w.print(" }}", .{});
            },
            .Error => {
                const r = self.get(.Error, id);
                try w.print("error {{ ", .{});
                const ids = self.field_pool.slice(r.variants);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    const f = self.Field.get(ids[i]);
                    try w.print("{s}: ", .{self.strs.get(f.name)});
                    try self.fmt(f.ty, w);
                }
                try w.print(" }}", .{});
            },
            .Union => {
                const r = self.get(.Union, id);
                try w.print("union {{ ", .{});
                const ids = self.field_pool.slice(r.fields);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    const f = self.Field.get(ids[i]);
                    try w.print("{s}: ", .{self.strs.get(f.name)});
                    try self.fmt(f.ty, w);
                }
                try w.print(" }}", .{});
            },
            .ErrorSet => {
                const r = self.get(.ErrorSet, id);
                try w.print("error", .{});
                try w.print("(", .{});
                try self.fmt(r.error_ty, w);
                try w.print(", ", .{});
                try self.fmt(r.value_ty, w);
                try w.print(")", .{});
            },
            .TypeType => {
                const r = self.get(.TypeType, id);
                try w.print("type(", .{});
                try self.fmt(r.of, w);
                try w.print(")", .{});
            },
            .Ast => {
                const r = self.get(.Ast, id);
                try w.print("ast(", .{});
                const name = self.strs.get(r.pkg_name);
                try w.print("{s}", .{name});
                const filepath = self.strs.get(r.filepath);
                try w.print("#{s}", .{filepath});
                try w.print(")", .{});
            },
            .TypeError => try w.print("<type error>", .{}),
        }
    }

    /// Format a type for use in diagnostic messages.
    /// Returns a concise, human-readable string representation.
    /// Caller owns returned memory.
    pub fn formatTypeForDiagnostic(
        self: *TypeStore,
        type_id: TypeId,
        options: FormatOptions,
        writer: anytype,
    ) !void {
        try self.fmtDiagnostic(type_id, writer, options, 0);
    }

    /// Internal function for diagnostic-friendly type formatting
    fn fmtDiagnostic(
        self: *TypeStore,
        type_id: TypeId,
        writer: anytype,
        options: FormatOptions,
        depth: u8,
    ) !void {
        // Prevent infinite recursion
        if (depth >= options.max_depth) {
            try writer.print("...", .{});
            return;
        }

        const kind = self.getKind(type_id);

        switch (kind) {
            // Primitives: use existing lowercase format
            .Void, .Bool, .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize, .String, .Any, .Noreturn, .Undef, .MlirModule, .MlirAttribute, .MlirType, .TypeType, .TypeError, .Ast => try self.fmt(type_id, writer),

            // Pointers: add const support
            .Ptr => {
                const r = self.get(.Ptr, type_id);
                if (options.show_const and r.is_const) {
                    try writer.print("*const ", .{});
                } else {
                    try writer.print("*", .{});
                }
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },

            // Slices, Arrays, DynArrays, Optional: delegate with depth tracking
            .Slice => {
                const r = self.get(.Slice, type_id);
                if (options.show_const and r.is_const) {
                    try writer.print("[]const ", .{});
                } else {
                    try writer.print("[]", .{});
                }
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

            // Complex types
            .Complex => {
                const r = self.get(.Complex, type_id);
                try writer.print("complex@", .{});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },
            .Tensor => {
                const r = self.get(.Tensor, type_id);
                try writer.print("tensor{}@", .{r.rank});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
                try writer.print("[", .{});
                var i: u8 = 0;
                while (i < r.rank) : (i += 1) {
                    if (i != 0) try writer.print(" x ", .{});
                    try writer.print("{}", .{r.dims[i]});
                }
                try writer.print("]", .{});
            },
            .Simd => {
                const r = self.get(.Simd, type_id);
                try writer.print("simd{}@", .{r.lanes});
                try self.fmtDiagnostic(r.elem, writer, options, depth + 1);
            },

            // Tuples: with truncation
            .Tuple => {
                const r = self.get(.Tuple, type_id);
                try writer.print("(", .{});
                const ids = self.type_pool.slice(r.elems);
                const show_count = @min(ids.len, options.max_fields);

                for (ids[0..show_count], 0..) |elem_id, idx| {
                    if (idx > 0) try writer.print(", ", .{});
                    try self.fmtDiagnostic(elem_id, writer, options, depth + 1);
                }

                if (ids.len > show_count) {
                    try writer.print(", ... ({d} more)", .{ids.len - show_count});
                }

                try writer.print(")", .{});
            },

            // Maps
            .Map => {
                const r = self.get(.Map, type_id);
                try writer.print("map[", .{});
                try self.fmtDiagnostic(r.key, writer, options, depth + 1);
                try writer.print("] ", .{});
                try self.fmtDiagnostic(r.value, writer, options, depth + 1);
            },

            // Functions: with parameter truncation
            .Function => {
                const r = self.get(.Function, type_id);
                const kind_str = if (r.is_pure) "fn" else "proc";
                try writer.print("{s}(", .{kind_str});

                const params = self.type_pool.slice(r.params);
                const show_count = @min(params.len, options.max_params);

                for (params[0..show_count], 0..) |param, idx| {
                    if (idx > 0) try writer.print(", ", .{});
                    try self.fmtDiagnostic(param, writer, options, depth + 1);
                }

                if (params.len > show_count) {
                    try writer.print(", ... ({d} more)", .{params.len - show_count});
                }

                try writer.print(") ", .{});
                try self.fmtDiagnostic(r.result, writer, options, depth + 1);

                if (r.is_variadic) try writer.print(" variadic", .{});
            },

            // Structs: with field truncation (type names will be added in Phase 3)
            .Struct => {
                const r = self.get(.Struct, type_id);
                try writer.print("struct {{ ", .{});
                const fields = self.field_pool.slice(r.fields);
                const show_count = @min(fields.len, options.max_fields);

                for (fields[0..show_count], 0..) |field_id, idx| {
                    if (idx > 0) try writer.print(", ", .{});
                    const f = self.Field.get(field_id);
                    try writer.print("{s}: ", .{self.strs.get(f.name)});
                    try self.fmtDiagnostic(f.ty, writer, options, depth + 1);
                }

                if (fields.len > show_count) {
                    try writer.print(", ... ({d} more)", .{fields.len - show_count});
                }

                try writer.print(" }}", .{});
            },

            // Enums: with member truncation
            .Enum => {
                const r = self.get(.Enum, type_id);
                try writer.print("enum(", .{});
                try self.fmtDiagnostic(r.tag_type, writer, options, depth + 1);
                try writer.print(") {{ ", .{});
                const members = self.enum_member_pool.slice(r.members);
                const show_count = @min(members.len, options.max_fields);

                for (members[0..show_count], 0..) |member_id, idx| {
                    if (idx > 0) try writer.print(", ", .{});
                    const member = self.EnumMember.get(member_id);
                    try writer.print("{s}", .{self.strs.get(member.name)});
                }

                if (members.len > show_count) {
                    try writer.print(", ... ({d} more)", .{members.len - show_count});
                }

                try writer.print(" }}", .{});
            },

            // Variants: with truncation
            .Variant => {
                const r = self.get(.Variant, type_id);
                try writer.print("variant {{ ", .{});
                const variants = self.field_pool.slice(r.variants);
                const show_count = @min(variants.len, options.max_fields);

                for (variants[0..show_count], 0..) |variant_id, idx| {
                    if (idx > 0) try writer.print(", ", .{});
                    const v = self.Field.get(variant_id);
                    try writer.print("{s}", .{self.strs.get(v.name)});
                }

                if (variants.len > show_count) {
                    try writer.print(", ... ({d} more)", .{variants.len - show_count});
                }

                try writer.print(" }}", .{});
            },

            // Errors: with truncation
            .Error => {
                const r = self.get(.Error, type_id);
                try writer.print("error {{ ", .{});
                const errors = self.field_pool.slice(r.variants);
                const show_count = @min(errors.len, options.max_fields);

                for (errors[0..show_count], 0..) |error_id, idx| {
                    if (idx > 0) try writer.print(", ", .{});
                    const e = self.Field.get(error_id);
                    try writer.print("{s}", .{self.strs.get(e.name)});
                }

                if (errors.len > show_count) {
                    try writer.print(", ... ({d} more)", .{errors.len - show_count});
                }

                try writer.print(" }}", .{});
            },

            // ErrorSet
            .ErrorSet => {
                const r = self.get(.ErrorSet, type_id);
                try writer.print("!", .{});
                try self.fmtDiagnostic(r.value_ty, writer, options, depth + 1);
            },

            // Union
            .Union => {
                const r = self.get(.Union, type_id);
                try writer.print("union {{ ", .{});
                const fields = self.field_pool.slice(r.fields);
                const show_count = @min(fields.len, options.max_fields);

                for (fields[0..show_count], 0..) |field_id, idx| {
                    if (idx > 0) try writer.print(", ", .{});
                    const f = self.Field.get(field_id);
                    try writer.print("{s}", .{self.strs.get(f.name)});
                }

                if (fields.len > show_count) {
                    try writer.print(", ... ({d} more)", .{fields.len - show_count});
                }

                try writer.print(" }}", .{});
            },
        }
    }
};
