const std = @import("std");
const cst = @import("cst_v2.zig");

// DOD Type Store
pub const TypeTag = struct {};
pub const FieldTag = struct {};

pub const TypeId = cst.Index(TypeTag);
pub const FieldId = cst.Index(FieldTag);
pub const EnumMemberTag = struct {};
pub const EnumMemberId = cst.Index(EnumMemberTag);
pub const RangeEnumMember = cst.RangeOf(EnumMemberId);
pub const RangeType = cst.RangeOf(TypeId);
pub const RangeField = cst.RangeOf(FieldId);

pub const StringInterner = cst.StringInterner;
pub const Table = cst.Table;
pub const Pool = cst.Pool;
pub const StoreIndex = cst.StoreIndex;
pub const StrId = cst.StrId;

pub const TypeInfoV2 = struct {
    gpa: std.mem.Allocator,
    store: TypeStore,
    expr_types: std.ArrayListUnmanaged(?TypeId) = .{},
    decl_types: std.ArrayListUnmanaged(?TypeId) = .{},

    pub fn init(gpa: std.mem.Allocator, interner: *StringInterner) TypeInfoV2 {
        return .{ .gpa = gpa, .store = TypeStore.init(gpa, interner) };
    }
    pub fn deinit(self: *TypeInfoV2) void {
        self.expr_types.deinit(self.gpa);
        self.decl_types.deinit(self.gpa);
        self.store.deinit();
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
    TypeType,
    Noreturn,
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
    pub const Noreturn = struct {};

    pub const Complex = struct { elem: TypeId };
    pub const Tensor = struct { elem: TypeId, rank: u8, dims: [4]usize };
    pub const Simd = struct { elem: TypeId, lanes: u16 };

    pub const Ptr = struct { elem: TypeId, is_const: bool };
    pub const Slice = struct { elem: TypeId };
    pub const Array = struct { elem: TypeId, len: usize };
    pub const DynArray = struct { elem: TypeId };
    pub const Map = struct { key: TypeId, value: TypeId };
    pub const Optional = struct { elem: TypeId };
    pub const Tuple = struct { elems: RangeType };
    pub const Function = struct { params: RangeType, result: TypeId, is_variadic: bool };
    pub const Field = struct { name: StrId, ty: TypeId };
    pub const EnumMember = struct { name: StrId, value: u64 };
    pub const Struct = struct { fields: RangeField };
    pub const Union = struct { fields: RangeField };
    pub const Enum = struct { members: RangeEnumMember, tag_type: TypeId };
    pub const Variant = struct { variants: RangeField };
    pub const Error = struct { variants: RangeField };
    pub const ErrorSet = struct { payload: ?TypeId };
    pub const TypeType = struct { of: TypeId };
};

inline fn RowT(comptime K: TypeKind) type {
    return @field(Rows, @tagName(K));
}

pub const TypeStore = struct {
    gpa: std.mem.Allocator,
    index: StoreIndex(TypeKind) = .{},

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
    Noreturn: Table(Rows.Noreturn) = .{},

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
    t_type: ?TypeId = null,
    t_noreturn: ?TypeId = null,

    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner) TypeStore {
        return .{ .gpa = gpa, .strs = strs };
    }
    pub fn deinit(self: *TypeStore) void {
        const gpa = self.gpa;
        self.index.deinit(gpa);
        inline for (@typeInfo(TypeKind).@"enum".fields) |f| @field(self, f.name).deinit(gpa);
        self.Field.deinit(gpa);
        self.EnumMember.deinit(gpa);
        self.type_pool.deinit(gpa);
        self.field_pool.deinit(gpa);
        self.enum_member_pool.deinit(gpa);
    }

    pub fn add(self: *TypeStore, comptime K: TypeKind, row: RowT(K)) TypeId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx, TypeId);
    }

    pub fn addField(self: *TypeStore, row: Rows.Field) FieldId {
        const idx = self.Field.add(self.gpa, row);
        return FieldId.fromRaw(idx);
    }

    pub fn addEnumMember(self: *TypeStore, row: Rows.EnumMember) EnumMemberId {
        const idx = self.EnumMember.add(self.gpa, row);
        return EnumMemberId.fromRaw(idx);
    }

    // ---- builtin constructors (interned once) ----
    pub fn tVoid(self: *TypeStore) TypeId {
        if (self.t_void) |id| return id;
        const id = self.add(.Void, .{});
        self.t_void = id;
        return id;
    }
    pub fn tBool(self: *TypeStore) TypeId {
        if (self.t_bool) |id| return id;
        const id = self.add(.Bool, .{});
        self.t_bool = id;
        return id;
    }
    pub fn tI8(self: *TypeStore) TypeId {
        if (self.t_i8) |id| return id;
        const id = self.add(.I8, .{});
        self.t_i8 = id;
        return id;
    }
    pub fn tI16(self: *TypeStore) TypeId {
        if (self.t_i16) |id| return id;
        const id = self.add(.I16, .{});
        self.t_i16 = id;
        return id;
    }
    pub fn tI32(self: *TypeStore) TypeId {
        if (self.t_i32) |id| return id;
        const id = self.add(.I32, .{});
        self.t_i32 = id;
        return id;
    }
    pub fn tI64(self: *TypeStore) TypeId {
        if (self.t_i64) |id| return id;
        const id = self.add(.I64, .{});
        self.t_i64 = id;
        return id;
    }
    pub fn tU8(self: *TypeStore) TypeId {
        if (self.t_u8) |id| return id;
        const id = self.add(.U8, .{});
        self.t_u8 = id;
        return id;
    }
    pub fn tU16(self: *TypeStore) TypeId {
        if (self.t_u16) |id| return id;
        const id = self.add(.U16, .{});
        self.t_u16 = id;
        return id;
    }
    pub fn tU32(self: *TypeStore) TypeId {
        if (self.t_u32) |id| return id;
        const id = self.add(.U32, .{});
        self.t_u32 = id;
        return id;
    }
    pub fn tU64(self: *TypeStore) TypeId {
        if (self.t_u64) |id| return id;
        const id = self.add(.U64, .{});
        self.t_u64 = id;
        return id;
    }
    pub fn tF32(self: *TypeStore) TypeId {
        if (self.t_f32) |id| return id;
        const id = self.add(.F32, .{});
        self.t_f32 = id;
        return id;
    }
    pub fn tF64(self: *TypeStore) TypeId {
        if (self.t_f64) |id| return id;
        const id = self.add(.F64, .{});
        self.t_f64 = id;
        return id;
    }
    pub fn tUsize(self: *TypeStore) TypeId {
        if (self.t_usize) |id| return id;
        const id = self.add(.Usize, .{});
        self.t_usize = id;
        return id;
    }
    pub fn tString(self: *TypeStore) TypeId {
        if (self.t_string) |id| return id;
        const id = self.add(.String, .{});
        self.t_string = id;
        return id;
    }
    pub fn tAny(self: *TypeStore) TypeId {
        if (self.t_any) |id| return id;
        const id = self.add(.Any, .{});
        self.t_any = id;
        return id;
    }
    pub fn tType(self: *TypeStore) TypeId {
        if (self.t_type) |id| return id;
        const id = self.add(.TypeType, .{ .of = self.tAny() });
        self.t_type = id;
        return id;
    }
    pub fn tNoReturn(self: *TypeStore) TypeId {
        if (self.t_noreturn) |id| return id;
        const id = self.add(.Noreturn, .{});
        self.t_noreturn = id;
        return id;
    }

    // ---- constructors with interning (linear dedup) ----
    pub fn mkPtr(self: *TypeStore, elem: TypeId, is_const: bool) TypeId {
        if (self.findPtr(elem, is_const)) |id| return id;
        return self.add(.Ptr, .{ .elem = elem, .is_const = is_const });
    }
    pub fn mkSlice(self: *TypeStore, elem: TypeId) TypeId {
        if (self.findSlice(elem)) |id| return id;
        return self.add(.Slice, .{ .elem = elem });
    }
    pub fn mkArray(self: *TypeStore, elem: TypeId, len: usize) TypeId {
        if (self.findArray(elem, len)) |id| return id;
        return self.add(.Array, .{ .elem = elem, .len = len });
    }
    pub fn mkDynArray(self: *TypeStore, elem: TypeId) TypeId {
        if (self.findDynArray(elem)) |id| return id;
        return self.add(.DynArray, .{ .elem = elem });
    }
    pub fn mkMap(self: *TypeStore, key: TypeId, value: TypeId) TypeId {
        if (self.findMap(key, value)) |id| return id;
        return self.add(.Map, .{ .key = key, .value = value });
    }
    pub fn mkOptional(self: *TypeStore, elem: TypeId) TypeId {
        if (self.findOptional(elem)) |id| return id;
        return self.add(.Optional, .{ .elem = elem });
    }
    pub fn mkTuple(self: *TypeStore, elems: []const TypeId) TypeId {
        if (self.findTuple(elems)) |id| return id;
        const r = self.type_pool.pushMany(self.gpa, elems);
        return self.add(.Tuple, .{ .elems = r });
    }
    pub fn mkFunction(self: *TypeStore, params: []const TypeId, result: TypeId, is_variadic: bool) TypeId {
        if (self.findFunction(params, result, is_variadic)) |id| return id;
        const r = self.type_pool.pushMany(self.gpa, params);
        return self.add(.Function, .{ .params = r, .result = result, .is_variadic = is_variadic });
    }
    pub const EnumMemberArg = struct { name: []const u8, value: u64 };
    pub fn mkEnum(self: *TypeStore, members: []const EnumMemberArg, tag_type: TypeId) TypeId {
        var ids = self.gpa.alloc(EnumMemberId, members.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < members.len) : (i += 1) {
            const mid = self.addEnumMember(.{ .name = self.strs.intern(members[i].name), .value = members[i].value });
            ids[i] = mid;
        }
        const r = self.enum_member_pool.pushMany(self.gpa, ids);
        return self.add(.Enum, .{ .members = r, .tag_type = tag_type });
    }
    pub fn mkVariant(self: *TypeStore, variants: []const StructFieldArg) TypeId {
        if (self.findVariant(variants)) |id| return id;
        var ids = self.gpa.alloc(FieldId, variants.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < variants.len) : (i += 1) {
            const fid = self.addField(.{ .name = variants[i].name, .ty = variants[i].ty });
            ids[i] = fid;
        }
        const r = self.field_pool.pushMany(self.gpa, ids);
        return self.add(.Variant, .{ .variants = r });
    }
    pub fn mkErrorSet(self: *TypeStore, payload: ?TypeId) TypeId {
        if (self.findErrorSet(payload)) |id| return id;
        return self.add(.ErrorSet, .{ .payload = payload });
    }

    pub fn mkTypeType(self: *TypeStore, of: TypeId) TypeId {
        if (self.findTypeType(of)) |id| return id;
        return self.add(.TypeType, .{ .of = of });
    }
    pub const StructFieldArg = struct { name: StrId, ty: TypeId };
    pub fn mkStruct(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        // Build interning key arrays
        if (self.findStruct(fields)) |id| return id;
        var ids = self.gpa.alloc(FieldId, fields.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const fid = self.addField(.{ .name = fields[i].name, .ty = fields[i].ty });
            ids[i] = fid;
        }
        const r = self.field_pool.pushMany(self.gpa, ids);
        return self.add(.Struct, .{ .fields = r });
    }
    pub fn mkUnion(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        var ids = self.gpa.alloc(FieldId, fields.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const fid = self.addField(.{ .name = fields[i].name, .ty = fields[i].ty });
            ids[i] = fid;
        }
        const r = self.field_pool.pushMany(self.gpa, ids);
        return self.add(.Union, .{ .fields = r });
    }
    pub fn mkError(self: *TypeStore, fields: []const StructFieldArg) TypeId {
        var ids = self.gpa.alloc(FieldId, fields.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            const fid = self.addField(.{ .name = fields[i].name, .ty = fields[i].ty });
            ids[i] = fid;
        }
        const r = self.field_pool.pushMany(self.gpa, ids);
        return self.add(.Error, .{ .variants = r });
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
                return row.elem.toRaw() == key.toRaw();
            }
        });
    }
    fn findDynArray(self: *const TypeStore, elem: TypeId) ?TypeId {
        return self.findMatch(.DynArray, elem, struct {
            fn eq(s: *const TypeStore, row: Rows.DynArray, key: TypeId) bool {
                _ = s;
                return row.elem.toRaw() == key.toRaw();
            }
        });
    }
    fn findArray(self: *const TypeStore, elem: TypeId, len: usize) ?TypeId {
        return self.findMatch(.Array, struct { e: TypeId, l: usize }{ .e = elem, .l = len }, struct {
            fn eq(s: *const TypeStore, row: Rows.Array, key: anytype) bool {
                _ = s;
                return row.elem.toRaw() == key.e.toRaw() and row.len == key.l;
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
    fn findOptional(self: *const TypeStore, elem: TypeId) ?TypeId {
        return self.findMatch(.Optional, elem, struct {
            fn eq(s: *const TypeStore, row: Rows.Optional, key: TypeId) bool {
                _ = s;
                return row.elem.toRaw() == key.toRaw();
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
    fn findFunction(self: *const TypeStore, params: []const TypeId, result: TypeId, is_variadic: bool) ?TypeId {
        return self.findMatch(.Function, struct { p: []const TypeId, r: TypeId, v: bool }{ .p = params, .r = result, .v = is_variadic }, struct {
            fn eq(s: *const TypeStore, row: Rows.Function, key: anytype) bool {
                if (row.result.toRaw() != key.r.toRaw() or row.is_variadic != key.v) return false;
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
                    const f = s.Field.get(ids[j].toRaw());
                    if (f.name.toRaw() != k.names[j].toRaw()) return false;
                    if (f.ty.toRaw() != k.tys[j].toRaw()) return false;
                }
                return true;
            }
        });
    }
    fn findErrorSet(self: *const TypeStore, payload: ?TypeId) ?TypeId {
        return self.findMatch(.ErrorSet, payload, struct {
            fn eq(_: *const TypeStore, row: Rows.ErrorSet, key: ?TypeId) bool {
                if (row.payload == null and key == null) return true;
                if (row.payload == null or key == null) return false;
                return row.payload.?.toRaw() == key.?.toRaw();
            }
        });
    }

    fn findTypeType(self: *const TypeStore, of: TypeId) ?TypeId {
        return self.findMatch(.TypeType, of, struct {
            fn eq(_: *const TypeStore, row: Rows.TypeType, key: TypeId) bool {
                return row.of.toRaw() == key.toRaw();
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
                    const f = s.Field.get(ids[j].toRaw());
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
            const row = tbl.get(row_idx);
            if (Helper.eq(self, row, key)) return TypeId.fromRaw(@intCast(i));
        }
        return null;
    }

    // ---- formatting ----
    pub fn fmt(self: *const TypeStore, id: TypeId, w: anytype) !void {
        const k = self.index.kinds.items[id.toRaw()];
        const row_idx = self.index.rows.items[id.toRaw()];
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
            .Complex => {
                const r = self.Complex.get(row_idx);
                try w.print("complex@", .{});
                try self.fmt(r.elem, w);
            },
            .Tensor => {
                const r = self.Tensor.get(row_idx);
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
                const r = self.Simd.get(row_idx);
                try w.print("simd{}@", .{r.lanes});
                try self.fmt(r.elem, w);
            },
            .Ptr => {
                const r = self.Ptr.get(row_idx);
                try w.print("*", .{});
                try self.fmt(r.elem, w);
            },
            .Slice => {
                const r = self.Slice.get(row_idx);
                try w.print("[]", .{});
                try self.fmt(r.elem, w);
            },
            .Array => {
                const r = self.Array.get(row_idx);
                try w.print("[{}]", .{r.len});
                try self.fmt(r.elem, w);
            },
            .DynArray => {
                const r = self.DynArray.get(row_idx);
                try w.print("dyn[]", .{});
                try self.fmt(r.elem, w);
            },
            .Optional => {
                const r = self.Optional.get(row_idx);
                try w.print("?", .{});
                try self.fmt(r.elem, w);
            },
            .Tuple => {
                const r = self.Tuple.get(row_idx);
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
                const r = self.Map.get(row_idx);
                try w.print("map[", .{});
                try self.fmt(r.key, w);
                try w.print("] ", .{});
                try self.fmt(r.value, w);
            },
            .Function => {
                const r = self.Function.get(row_idx);
                try w.print("fn(", .{});
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
                const r = self.Struct.get(row_idx);
                try w.print("struct { ", .{});
                const ids = self.field_pool.slice(r.fields);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    const f = self.Field.get(ids[i].toRaw());
                    try w.print("{s}: ", .{self.strs.get(f.name)});
                    try self.fmt(f.ty, w);
                }
                try w.print(" }", .{});
            },
            .Enum => {
                const r = self.Enum.get(row_idx);
                try w.print("enum(", .{});
                try self.fmt(r.tag_type, w);
                try w.print(") {{ ", .{});
                const ids = self.enum_member_pool.slice(r.members);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    const member = self.EnumMember.get(ids[i].toRaw());
                    try w.print("{s} = {}", .{ self.strs.get(member.name), member.value });
                }
                try w.print(" }}", .{});
            },
            .Variant => {
                const r = self.Variant.get(row_idx);
                try w.print("variant {{ ", .{});
                const ids = self.field_pool.slice(r.variants);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    if (i != 0) try w.print(", ", .{});
                    const f = self.Field.get(ids[i].toRaw());
                    try w.print("{s}: ", .{self.strs.get(f.name)});
                    try self.fmt(f.ty, w);
                }
                try w.print(" }}", .{});
            },
            .ErrorSet => {
                const r = self.ErrorSet.get(row_idx);
                try w.print("error", .{});
                if (r.payload) |p| {
                    try w.print("(", .{});
                    try self.fmt(p, w);
                    try w.print(")", .{});
                }
            },
            .TypeType => {
                const r = self.TypeType.get(row_idx);
                try w.print("type(", .{});
                try self.fmt(r.of, w);
                try w.print(")", .{});
            },
        }
    }
};
