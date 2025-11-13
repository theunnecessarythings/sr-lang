const std = @import("std");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const comp = @import("comptime.zig");

// DOD Type Store
pub const TypeTag = struct {};

pub const ArraySize = union(enum) {
    Concrete: usize,
    Unresolved: ast.ExprId,
};

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

pub const MethodReceiverKind = enum {
    none,
    value,
    pointer,
    pointer_const,
};

pub const BuiltinMethod = enum {
    dynarray_append,
};

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

const MethodKey = struct {
    owner: usize,
    name: usize,
};

fn makeMethodKey(owner: TypeId, name: ast.StrId) MethodKey {
    return .{ .owner = owner.toRaw(), .name = name.toRaw() };
}

pub const TypeInfo = struct {
    gpa: std.mem.Allocator,
    store: *TypeStore,
    mutex: std.Thread.Mutex = .{},
    expr_types: std.ArrayListUnmanaged(?TypeId) = .{},
    decl_types: std.ArrayListUnmanaged(?TypeId) = .{},
    field_index_for_expr: std.AutoArrayHashMapUnmanaged(u32, u32) = .{},
    comptime_values: std.AutoArrayHashMapUnmanaged(ast.ExprId, comp.ComptimeValue) = .{},
    method_bindings: std.AutoArrayHashMapUnmanaged(u32, MethodBinding) = .{},
    mlir_splice_info: std.AutoArrayHashMapUnmanaged(u32, MlirSpliceInfo) = .{},
    exports: std.AutoArrayHashMapUnmanaged(ast.StrId, ExportEntry) = .{},

    pub const ExportEntry = struct {
        ty: TypeId,
        decl_id: ast.DeclId,
    };

    pub fn init(gpa: std.mem.Allocator, store: *TypeStore) TypeInfo {
        return .{
            .gpa = gpa,
            .store = store,
            .comptime_values = .{},
        };
    }
    pub fn deinit(self: *TypeInfo) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        self.expr_types.deinit(self.gpa);
        self.decl_types.deinit(self.gpa);
        self.field_index_for_expr.deinit(self.gpa);
        var cv_it = self.comptime_values.iterator();
        while (cv_it.next()) |value_ptr| {
            self.destroyComptimeValue(value_ptr.value_ptr);
        }
        self.comptime_values.deinit(self.gpa);
        self.method_bindings.deinit(self.gpa);
        self.mlir_splice_info.deinit(self.gpa);
        self.exports.deinit(self.gpa);
    }

    pub fn print(self: *TypeInfo) void {
        self.mutex.lock();
        defer self.mutex.unlock();
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
        self.mutex.lock();
        defer self.mutex.unlock();
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

    pub fn setExprType(self: *TypeInfo, expr_id: ast.ExprId, ty: TypeId) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        self.expr_types.items[expr_id.toRaw()] = ty;
    }

    pub fn setFieldIndex(self: *TypeInfo, expr_id: ast.ExprId, idx: u32) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        try self.field_index_for_expr.put(self.gpa, expr_id.toRaw(), idx);
    }

    pub fn getFieldIndex(self: *const TypeInfo, expr_id: ast.ExprId) ?u32 {
        const v = self.field_index_for_expr.get(expr_id.toRaw()) orelse 0xFFFF_FFFF;
        return if (v == 0xFFFF_FFFF) null else v;
    }

    pub fn clearFieldIndex(self: *TypeInfo, expr_id: ast.ExprId) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        try self.field_index_for_expr.put(self.gpa, expr_id.toRaw(), 0xFFFF_FFFF);
    }

    pub fn getMethodBinding(self: *const TypeInfo, expr_id: ast.ExprId) ?MethodBinding {
        return self.method_bindings.get(expr_id.toRaw());
    }

    pub fn setMethodBinding(self: *TypeInfo, expr_id: ast.ExprId, binding: MethodBinding) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        const gop = try self.method_bindings.getOrPut(self.gpa, expr_id.toRaw());
        gop.value_ptr.* = binding;
    }

    pub fn addExport(self: *TypeInfo, name: ast.StrId, ty: TypeId, decl_id: ast.DeclId) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        const gop = try self.exports.getOrPut(self.gpa, name);
        gop.value_ptr.* = .{ .ty = ty, .decl_id = decl_id };
    }

    pub fn getExport(self: *const TypeInfo, name: ast.StrId) ?ExportEntry {
        return self.exports.get(name);
    }

    pub fn hasComptimeValue(self: *const TypeInfo, expr_id: ast.ExprId) bool {
        return self.comptime_values.get(expr_id) != null;
    }

    pub fn getComptimeValue(self: *const TypeInfo, expr_id: ast.ExprId) ?*comp.ComptimeValue {
        return if (self.comptime_values.getEntry(expr_id)) |entry| entry.value_ptr else null;
    }

    pub fn setComptimeValue(self: *TypeInfo, expr_id: ast.ExprId, value: comp.ComptimeValue) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        const gop = try self.comptime_values.getOrPut(self.gpa, expr_id);
        if (gop.found_existing) {
            self.destroyComptimeValue(gop.value_ptr);
        }
        gop.value_ptr.* = value;
    }

    fn destroyComptimeValue(self: *TypeInfo, value_ptr: *comp.ComptimeValue) void {
        switch (value_ptr.*) {
            .String => |s| {
                const mut: []u8 = @constCast(s);
                self.gpa.free(mut);
            },
            .MlirModule => |*mod| {
                mod.destroy();
            },
            else => {},
        }
        value_ptr.* = .Void;
    }

    pub fn setMlirSpliceInfo(self: *TypeInfo, piece_id: ast.MlirPieceId, info: MlirSpliceInfo) !void {
        self.mutex.lock();
        defer self.mutex.unlock();
        const gop = try self.mlir_splice_info.getOrPut(self.gpa, piece_id.toRaw());
        gop.value_ptr.* = info;
    }

    pub fn getMlirSpliceInfo(self: *const TypeInfo, piece_id: ast.MlirPieceId) ?MlirSpliceInfo {
        if (self.mlir_splice_info.get(piece_id.toRaw())) |info_ptr|
            return info_ptr;
        return null;
    }
};

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
    pub const Slice = struct { elem: TypeId };
    pub const Array = struct { elem: TypeId, len: ArraySize };
    pub const DynArray = struct { elem: TypeId };
    pub const Map = struct { key: TypeId, value: TypeId };
    pub const Optional = struct { elem: TypeId };
    pub const Tuple = struct { elems: RangeType };
    pub const Function = struct { params: RangeType, result: TypeId, is_variadic: bool, is_pure: bool, is_extern: bool };
    pub const Field = struct { name: StrId, ty: TypeId };
    pub const EnumMember = struct { name: StrId, value: u64 };
    pub const Struct = struct { fields: RangeField };
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

inline fn RowT(comptime K: TypeKind) type {
    return @field(Rows, @tagName(K));
}

pub const TypeStore = struct {
    gpa: std.mem.Allocator,
    index: StoreIndex(TypeKind) = .{},
    mutex: std.Thread.Mutex = .{},

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

    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner) TypeStore {
        return .{ .gpa = gpa, .strs = strs };
    }
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

    pub fn getKind(self: *const TypeStore, id: TypeId) TypeKind {
        return self.index.kinds.items[id.toRaw()];
    }

    pub fn get(self: *const TypeStore, comptime K: TypeKind, id: TypeId) RowT(K) {
        const tbl: *const Table(RowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = self.index.rows.items[id.toRaw()] });
    }

    pub fn addMethod(self: *TypeStore, entry: MethodEntry) !bool {
        self.mutex.lock();
        defer self.mutex.unlock();
        const key = makeMethodKey(entry.owner_type, entry.method_name);
        const gop = try self.method_table.getOrPut(self.gpa, key);
        if (gop.found_existing) return false;
        gop.value_ptr.* = entry;
        return true;
    }

    pub fn getMethod(self: *TypeStore, owner: TypeId, name: ast.StrId) ?MethodEntry {
        self.mutex.lock();
        defer self.mutex.unlock();
        const key = makeMethodKey(owner, name);
        return self.method_table.get(key);
    }

    fn addLocked(self: *TypeStore, comptime K: TypeKind, row: RowT(K)) TypeId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), TypeId);
    }

    pub fn add(self: *TypeStore, comptime K: TypeKind, row: RowT(K)) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.addLocked(K, row);
    }

    fn addFieldLocked(self: *TypeStore, row: Rows.Field) FieldId {
        return self.Field.add(self.gpa, row);
    }

    pub fn addField(self: *TypeStore, row: Rows.Field) FieldId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.addFieldLocked(row);
    }

    fn addEnumMemberLocked(self: *TypeStore, row: Rows.EnumMember) EnumMemberId {
        return self.EnumMember.add(self.gpa, row);
    }

    pub fn addEnumMember(self: *TypeStore, row: Rows.EnumMember) EnumMemberId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.addEnumMemberLocked(row);
    }

    // ---- builtin constructors (interned once) ----
    fn tVoidLocked(self: *TypeStore) TypeId {
        if (self.t_void) |id| return id;
        const id = self.addLocked(.Void, .{});
        self.t_void = id;
        return id;
    }
    pub fn tVoid(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tVoidLocked();
    }
    fn tBoolLocked(self: *TypeStore) TypeId {
        if (self.t_bool) |id| return id;
        const id = self.addLocked(.Bool, .{});
        self.t_bool = id;
        return id;
    }
    pub fn tBool(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tBoolLocked();
    }
    fn tI8Locked(self: *TypeStore) TypeId {
        if (self.t_i8) |id| return id;
        const id = self.addLocked(.I8, .{});
        self.t_i8 = id;
        return id;
    }
    pub fn tI8(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tI8Locked();
    }
    fn tI16Locked(self: *TypeStore) TypeId {
        if (self.t_i16) |id| return id;
        const id = self.addLocked(.I16, .{});
        self.t_i16 = id;
        return id;
    }
    pub fn tI16(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tI16Locked();
    }
    fn tI32Locked(self: *TypeStore) TypeId {
        if (self.t_i32) |id| return id;
        const id = self.addLocked(.I32, .{});
        self.t_i32 = id;
        return id;
    }
    pub fn tI32(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tI32Locked();
    }
    fn tI64Locked(self: *TypeStore) TypeId {
        if (self.t_i64) |id| return id;
        const id = self.addLocked(.I64, .{});
        self.t_i64 = id;
        return id;
    }
    pub fn tI64(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tI64Locked();
    }
    fn tU8Locked(self: *TypeStore) TypeId {
        if (self.t_u8) |id| return id;
        const id = self.addLocked(.U8, .{});
        self.t_u8 = id;
        return id;
    }
    pub fn tU8(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tU8Locked();
    }
    fn tU16Locked(self: *TypeStore) TypeId {
        if (self.t_u16) |id| return id;
        const id = self.addLocked(.U16, .{});
        self.t_u16 = id;
        return id;
    }
    pub fn tU16(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tU16Locked();
    }
    fn tU32Locked(self: *TypeStore) TypeId {
        if (self.t_u32) |id| return id;
        const id = self.addLocked(.U32, .{});
        self.t_u32 = id;
        return id;
    }
    pub fn tU32(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tU32Locked();
    }
    fn tU64Locked(self: *TypeStore) TypeId {
        if (self.t_u64) |id| return id;
        const id = self.addLocked(.U64, .{});
        self.t_u64 = id;
        return id;
    }
    pub fn tU64(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tU64Locked();
    }
    fn tF32Locked(self: *TypeStore) TypeId {
        if (self.t_f32) |id| return id;
        const id = self.addLocked(.F32, .{});
        self.t_f32 = id;
        return id;
    }
    pub fn tF32(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tF32Locked();
    }
    fn tF64Locked(self: *TypeStore) TypeId {
        if (self.t_f64) |id| return id;
        const id = self.addLocked(.F64, .{});
        self.t_f64 = id;
        return id;
    }
    pub fn tF64(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tF64Locked();
    }
    fn tUsizeLocked(self: *TypeStore) TypeId {
        if (self.t_usize) |id| return id;
        const id = self.addLocked(.Usize, .{});
        self.t_usize = id;
        return id;
    }
    pub fn tUsize(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tUsizeLocked();
    }
    fn tStringLocked(self: *TypeStore) TypeId {
        if (self.t_string) |id| return id;
        const id = self.addLocked(.String, .{});
        self.t_string = id;
        return id;
    }
    pub fn tString(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tStringLocked();
    }
    fn tAnyLocked(self: *TypeStore) TypeId {
        if (self.t_any) |id| return id;
        const id = self.addLocked(.Any, .{});
        self.t_any = id;
        return id;
    }
    pub fn tAny(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tAnyLocked();
    }
    fn tUndefLocked(self: *TypeStore) TypeId {
        if (self.t_undef) |id| return id;
        const id = self.addLocked(.Undef, .{});
        self.t_undef = id;
        return id;
    }
    pub fn tUndef(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tUndefLocked();
    }
    fn tTypeLocked(self: *TypeStore) TypeId {
        if (self.t_type) |id| return id;
        const id = self.addLocked(.TypeType, .{ .of = self.tAnyLocked() });
        self.t_type = id;
        return id;
    }
    pub fn tType(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tTypeLocked();
    }
    fn tNoreturnLocked(self: *TypeStore) TypeId {
        if (self.t_noreturn) |id| return id;
        const id = self.addLocked(.Noreturn, .{});
        self.t_noreturn = id;
        return id;
    }
    pub fn tNoreturn(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tNoreturnLocked();
    }
    pub fn tNoReturn(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tNoreturnLocked();
    }

    fn tMlirModuleLocked(self: *TypeStore) TypeId {
        if (self.t_mlir_module) |id| return id;
        const id = self.addLocked(.MlirModule, .{});
        self.t_mlir_module = id;
        return id;
    }
    pub fn tMlirModule(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tMlirModuleLocked();
    }

    fn tMlirAttributeLocked(self: *TypeStore) TypeId {
        if (self.t_mlir_attribute) |id| return id;
        const id = self.addLocked(.MlirAttribute, .{});
        self.t_mlir_attribute = id;
        return id;
    }
    pub fn tMlirAttribute(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tMlirAttributeLocked();
    }

    fn tMlirTypeLocked(self: *TypeStore) TypeId {
        if (self.t_mlir_type) |id| return id;
        const id = self.addLocked(.MlirType, .{});
        self.t_mlir_type = id;
        return id;
    }
    pub fn tMlirType(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tMlirTypeLocked();
    }

    fn tTypeErrorLocked(self: *TypeStore) TypeId {
        if (self.t_type_error) |id| return id;
        const id = self.addLocked(.TypeError, .{});
        self.t_type_error = id;
        return id;
    }
    pub fn tTypeError(self: *TypeStore) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        return self.tTypeErrorLocked();
    }

    // ---- constructors with interning (linear dedup) ----
    pub fn mkPtr(self: *TypeStore, elem: TypeId, is_const: bool) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findPtr(elem, is_const)) |id| return id;
        return self.addLocked(.Ptr, .{ .elem = elem, .is_const = is_const });
    }
    pub fn mkSlice(self: *TypeStore, elem: TypeId) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findSlice(elem)) |id| return id;
        return self.addLocked(.Slice, .{ .elem = elem });
    }
    pub fn mkArray(self: *TypeStore, elem: TypeId, len: ArraySize) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findArray(elem, len)) |id| return id;
        return self.addLocked(.Array, .{ .elem = elem, .len = len });
    }
    pub fn mkDynArray(self: *TypeStore, elem: TypeId) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findDynArray(elem)) |id| return id;
        return self.addLocked(.DynArray, .{ .elem = elem });
    }
    pub fn mkMap(self: *TypeStore, key: TypeId, value: TypeId) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findMap(key, value)) |id| return id;
        return self.addLocked(.Map, .{ .key = key, .value = value });
    }
    pub fn mkAst(self: *TypeStore, pkg_name: ast.StrId, filepath: StrId) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findAst(pkg_name, filepath)) |id| return id;
        return self.addLocked(.Ast, .{
            .pkg_name = pkg_name,
            .filepath = filepath,
        });
    }
    pub fn mkSimd(self: *TypeStore, elem: TypeId, lanes: u16) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findSimd(elem, lanes)) |id| return id;
        return self.addLocked(.Simd, .{ .elem = elem, .lanes = lanes });
    }
    pub fn mkTensor(self: *TypeStore, elem: TypeId, dims: []const usize) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
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
    pub fn mkOptional(self: *TypeStore, elem: TypeId) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findOptional(elem)) |id| return id;
        return self.addLocked(.Optional, .{ .elem = elem });
    }
    pub fn mkTuple(self: *TypeStore, elems: []const TypeId) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findTuple(elems)) |id| return id;
        const r = self.type_pool.pushMany(self.gpa, elems);
        return self.addLocked(.Tuple, .{ .elems = r });
    }
    pub fn mkFunction(self: *TypeStore, params: []const TypeId, result: TypeId, is_variadic: bool, is_pure: bool, is_extern: bool) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findFunction(params, result, is_variadic, is_pure, is_extern)) |id| return id;

        // Copy params to a temporary buffer to avoid use-after-free if params is a slice of self.type_pool
        const params_copy = self.gpa.alloc(TypeId, params.len) catch @panic("OOM");
        defer self.gpa.free(params_copy);
        @memcpy(params_copy, params);

        const r = self.type_pool.pushMany(self.gpa, params_copy);
        return self.addLocked(.Function, .{ .params = r, .result = result, .is_variadic = is_variadic, .is_pure = is_pure, .is_extern = is_extern });
    }
    pub const EnumMemberArg = struct { name: StrId, value: u64 };
    pub fn mkEnum(self: *TypeStore, members: []const EnumMemberArg, tag_type: TypeId) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
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
    pub fn mkVariant(self: *TypeStore, variants: []const StructFieldArg) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
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
    pub fn mkErrorSet(self: *TypeStore, value_ty: TypeId, error_ty: TypeId) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findErrorSet(value_ty, error_ty)) |id| return id;
        return self.addLocked(.ErrorSet, .{ .value_ty = value_ty, .error_ty = error_ty });
    }
    pub fn mkTypeType(self: *TypeStore, of: TypeId) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.findTypeType(of)) |id| return id;
        return self.addLocked(.TypeType, .{ .of = of });
    }
    pub const StructFieldArg = struct { name: StrId, ty: TypeId };
    pub fn mkStruct(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
        // Build interning key arrays
        if (self.findStruct(fields)) |id| return id;
        var ids = self.gpa.alloc(FieldId, fields.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const fid = self.addFieldLocked(.{ .name = fields[i].name, .ty = fields[i].ty });
            ids[i] = fid;
        }
        const r = self.field_pool.pushMany(self.gpa, ids);
        return self.addLocked(.Struct, .{ .fields = r });
    }
    pub fn mkUnion(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
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
    pub fn mkError(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        self.mutex.lock();
        defer self.mutex.unlock();
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
    fn findPtr(self: *const TypeStore, elem: TypeId, is_const: bool) ?TypeId {
        return self.findMatch(.Ptr, struct { e: TypeId, c: bool }{ .e = elem, .c = is_const }, struct {
            fn eq(s: *const TypeStore, row: Rows.Ptr, key: anytype) bool {
                _ = s;
                return row.elem.toRaw() == key.e.toRaw() and row.is_const == key.c;
            }
        });
    }
    fn findSlice(self: *const TypeStore, elem: TypeId) ?TypeId {
        return self.findMatch(.Slice, elem, struct {
            fn eq(s: *const TypeStore, row: Rows.Slice, key: TypeId) bool {
                _ = s;
                return row.elem.eq(key);
            }
        });
    }
    fn findDynArray(self: *const TypeStore, elem: TypeId) ?TypeId {
        return self.findMatch(.DynArray, elem, struct {
            fn eq(s: *const TypeStore, row: Rows.DynArray, key: TypeId) bool {
                _ = s;
                return row.elem.eq(key);
            }
        });
    }
    fn findArray(self: *const TypeStore, elem: TypeId, len: ArraySize) ?TypeId {
        return self.findMatch(.Array, struct { e: TypeId, l: ArraySize }{ .e = elem, .l = len }, struct {
            fn eq(s: *const TypeStore, row: Rows.Array, key: anytype) bool {
                _ = s;
                if (row.elem.toRaw() != key.e.toRaw()) return false;
                return switch (row.len) {
                    .Concrete => |l1| switch (key.l) {
                        .Concrete => |l2| l1 == l2,
                        else => false,
                    },
                    .Unresolved => |e1| switch (key.l) {
                        .Unresolved => |e2| e1.toRaw() == e2.toRaw(),
                        else => false,
                    },
                };
            }
        });
    }
    fn findTensor(self: *const TypeStore, elem: TypeId, dims: []const usize) ?TypeId {
        return self.findMatch(.Tensor, struct { e: TypeId, d: []const usize }{ .e = elem, .d = dims }, struct {
            fn eq(_: *const TypeStore, row: Rows.Tensor, key: anytype) bool {
                if (row.elem.toRaw() != key.e.toRaw()) return false;
                if (row.rank != key.d.len) return false;
                var i: usize = 0;
                while (i < row.rank) : (i += 1) {
                    if (row.dims[i] != key.d[i]) return false;
                }
                return true;
            }
        });
    }
    fn findMap(self: *const TypeStore, key: TypeId, value: TypeId) ?TypeId {
        return self.findMatch(.Map, struct { k: TypeId, v: TypeId }{ .k = key, .v = value }, struct {
            fn eq(s: *const TypeStore, row: Rows.Map, k: anytype) bool {
                _ = s;
                return row.key.toRaw() == k.k.toRaw() and row.value.toRaw() == k.v.toRaw();
            }
        });
    }
    fn findAst(self: *const TypeStore, pkg_name: ast.StrId, filepath: StrId) ?TypeId {
        return self.findMatch(.Ast, struct { pkg: ast.StrId, filepath: StrId }{
            .pkg = pkg_name,
            .filepath = filepath,
        }, struct {
            fn eq(_: *const TypeStore, row: Rows.Ast, key: anytype) bool {
                return row.filepath.toRaw() == key.filepath.toRaw() and row.pkg_name.toRaw() == key.pkg.toRaw();
            }
        });
    }
    fn findSimd(self: *const TypeStore, elem: TypeId, lanes: u16) ?TypeId {
        return self.findMatch(.Simd, struct { e: TypeId, l: u16 }{ .e = elem, .l = lanes }, struct {
            fn eq(_: *const TypeStore, row: Rows.Simd, key: anytype) bool {
                return row.elem.toRaw() == key.e.toRaw() and row.lanes == key.l;
            }
        });
    }
    fn findOptional(self: *const TypeStore, elem: TypeId) ?TypeId {
        return self.findMatch(.Optional, elem, struct {
            fn eq(s: *const TypeStore, row: Rows.Optional, key: TypeId) bool {
                _ = s;
                return row.elem.eq(key);
            }
        });
    }
    fn findTuple(self: *const TypeStore, elems: []const TypeId) ?TypeId {
        return self.findMatch(.Tuple, elems, struct {
            fn eq(s: *const TypeStore, row: Rows.Tuple, key: []const TypeId) bool {
                const ids = s.type_pool.slice(row.elems);
                if (ids.len != key.len) return false;
                var i: usize = 0;
                while (i < ids.len) : (i += 1) if (ids[i].toRaw() != key[i].toRaw()) return false;
                return true;
            }
        });
    }
    fn findFunction(self: *const TypeStore, params: []const TypeId, result: TypeId, is_variadic: bool, is_pure: bool, is_extern: bool) ?TypeId {
        return self.findMatch(.Function, struct { p: []const TypeId, r: TypeId, v: bool, pure: bool, ext: bool }{ .p = params, .r = result, .v = is_variadic, .pure = is_pure, .ext = is_extern }, struct {
            fn eq(s: *const TypeStore, row: Rows.Function, key: anytype) bool {
                if (row.result.toRaw() != key.r.toRaw() or row.is_variadic != key.v or row.is_pure != key.pure or row.is_extern != key.ext) return false;
                const ids = s.type_pool.slice(row.params);
                if (ids.len != key.p.len) return false;
                var i: usize = 0;
                while (i < ids.len) : (i += 1) if (ids[i].toRaw() != key.p[i].toRaw()) return false;
                return true;
            }
        });
    }

    fn findVariant(self: *const TypeStore, variants: []const StructFieldArg) ?TypeId {
        // Compare by name + type sequence
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
            fn eq(s: *const TypeStore, row: Rows.Variant, k: anytype) bool {
                const ids = s.field_pool.slice(row.variants);
                if (ids.len != k.names.len) return false;
                var j: usize = 0;
                while (j < ids.len) : (j += 1) {
                    const f = s.Field.get(ids[j]);
                    if (f.name.toRaw() != k.names[j].toRaw()) return false;
                    if (f.ty.toRaw() != k.tys[j].toRaw()) return false;
                }
                return true;
            }
        });
    }
    fn findErrorSet(self: *const TypeStore, value_ty: TypeId, error_ty: TypeId) ?TypeId {
        return self.findMatch(.ErrorSet, struct { v: TypeId, e: TypeId }{ .v = value_ty, .e = error_ty }, struct {
            fn eq(s: *const TypeStore, row: Rows.ErrorSet, k: anytype) bool {
                _ = s;
                return row.value_ty.toRaw() == k.v.toRaw() and row.error_ty.toRaw() == k.e.toRaw();
            }
        });
    }

    fn findTypeType(self: *const TypeStore, of: TypeId) ?TypeId {
        return self.findMatch(.TypeType, of, struct {
            fn eq(_: *const TypeStore, row: Rows.TypeType, key: TypeId) bool {
                return row.of.eq(key);
            }
        });
    }
    fn findStruct(self: *const TypeStore, fields: []const StructFieldArg) ?TypeId {
        // Compare by name + type sequence
        const key_names_and_tys = struct { names: []const StrId, tys: []const TypeId };
        var names = self.gpa.alloc(StrId, fields.len) catch @panic("OOM");
        defer self.gpa.free(names);
        var tys = self.gpa.alloc(TypeId, fields.len) catch @panic("OOM");
        defer self.gpa.free(tys);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            names[i] = fields[i].name;
            tys[i] = fields[i].ty;
        }
        const key_val = key_names_and_tys{ .names = names, .tys = tys };
        return self.findMatch(.Struct, key_val, struct {
            fn eq(s: *const TypeStore, row: Rows.Struct, k: anytype) bool {
                const ids = s.field_pool.slice(row.fields);
                if (ids.len != k.names.len) return false;
                var j: usize = 0;
                while (j < ids.len) : (j += 1) {
                    const f = s.Field.get(ids[j]);
                    if (f.name.toRaw() != k.names[j].toRaw()) return false;
                    if (f.ty.toRaw() != k.tys[j].toRaw()) return false;
                }
                return true;
            }
        });
    }

    fn findMatch(self: *const TypeStore, comptime K: TypeKind, key: anytype, comptime Helper: type) ?TypeId {
        // Scan all types and find first matching row of kind K
        const kinds = self.index.kinds.items;
        const rows = self.index.rows.items;
        var i: usize = 0;
        while (i < kinds.len) : (i += 1) {
            if (kinds[i] != K) continue;
            const row_idx = rows[i];
            const tbl: *const Table(RowT(K)) = &@field(self, @tagName(K));
            const row = tbl.get(.{ .index = row_idx });
            if (Helper.eq(self, row, key)) return TypeId.fromRaw(@intCast(i));
        }
        return null;
    }

    // ---- formatting ----
    pub fn fmt(self: *const TypeStore, id: TypeId, w: anytype) !void {
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
                switch (r.len) {
                    .Concrete => |l| try w.print("[{}]", .{l}),
                    .Unresolved => try w.print("[]", .{}),
                }
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
};
