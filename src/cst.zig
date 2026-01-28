const std = @import("std");
const ArrayList = std.array_list.Managed;

/// Core utilities for tracking indices, ranges, strings, and locations.
pub const FileId = u32;
const Loc = @import("lexer.zig").Token.Loc;

// centralized cold OOM handler to reduce binary bloat at call sites
fn oom() noreturn {
    @branchHint(.cold);
    @panic("OOM");
}

////////////////////////////////////////////////////////////////
//            Typed Indices, Optional Indices, Ranges
////////////////////////////////////////////////////////////////

pub fn Index(comptime T: type) type {
    return packed struct {
        index: u32,
        pub const Type = T;
        pub inline fn fromRaw(raw: u32) @This() {
            return .{ .index = raw };
        }
        pub inline fn toRaw(self: @This()) u32 {
            return self.index;
        }
        pub inline fn eq(self: @This(), other: @This()) bool {
            return self.index == other.index;
        }
    };
}

pub fn SentinelIndex(comptime T: type) type {
    return packed struct {
        raw: u32,
        pub const Type = T;
        pub const none_raw = NONE;
        const NONE: u32 = 0xFFFF_FFFF;

        pub inline fn none() @This() {
            return .{ .raw = NONE };
        }
        pub inline fn some(i: Index(T)) @This() {
            return .{ .raw = i.index };
        }
        pub inline fn isNone(self: @This()) bool {
            return self.raw == NONE;
        }
        pub inline fn unwrap(self: @This()) Index(T) {
            std.debug.assert(self.raw != NONE);
            return .{ .index = self.raw };
        }
        pub inline fn toRaw(self: @This()) u32 {
            return self.raw;
        }
        pub fn eq(self: @This(), other: anytype) bool {
            if (@TypeOf(other) == @This()) return self.raw == other.raw;
            return self.raw == other.index;
        }
    };
}

pub fn RangeOf(comptime IdT: type) type {
    return struct {
        start: u32,
        len: u32,
        pub const Type = IdT;
        pub inline fn empty() @This() {
            return .{ .start = 0, .len = 0 };
        }
    };
}

pub fn OptRangeOf(comptime IdT: type) type {
    return struct {
        start: u32,
        len: u32,
        pub inline fn none() @This() {
            return .{ .start = 0xFFFF_FFFF, .len = 0 };
        }
        pub inline fn isNone(self: @This()) bool {
            return self.start == 0xFFFF_FFFF;
        }
        pub inline fn some(r: RangeOf(IdT)) @This() {
            return .{ .start = r.start, .len = r.len };
        }
        pub inline fn asRange(self: @This()) RangeOf(IdT) {
            std.debug.assert(!self.isNone());
            return .{ .start = self.start, .len = self.len };
        }
    };
}

/// Backing storage for all Pools to reduce generic code bloat
const UnifiedPool = struct {
    data: std.ArrayListUnmanaged(u32) = .{},

    fn push(self: *@This(), gpa: std.mem.Allocator, raw: u32) u32 {
        const idx: u32 = @intCast(self.data.items.len);
        self.data.append(gpa, raw) catch oom();
        return idx;
    }

    fn pushMany(self: *@This(), gpa: std.mem.Allocator, raw_items: []const u32) u32 {
        const start: u32 = @intCast(self.data.items.len);
        self.data.appendSlice(gpa, raw_items) catch oom();
        return start;
    }

    fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
        self.data.deinit(gpa);
    }
};

pub fn Pool(comptime IdT: type) type {
    return struct {
        inner: UnifiedPool = .{},

        pub fn push(self: *@This(), gpa: std.mem.Allocator, id: IdT) u32 {
            // Safe bitcast as IdT is a packed struct(u32)
            return self.inner.push(gpa, @as(u32, @bitCast(id)));
        }
        pub fn pushMany(self: *@This(), gpa: std.mem.Allocator, items: []const IdT) RangeOf(IdT) {
            const raw_slice = std.mem.bytesAsSlice(u32, std.mem.sliceAsBytes(items));
            const start = self.inner.pushMany(gpa, raw_slice);
            return .{ .start = start, .len = @intCast(items.len) };
        }
        pub fn slice(self: *const @This(), r: RangeOf(IdT)) []const IdT {
            const start: usize = @intCast(r.start);
            const len: usize = @intCast(r.len);
            const end = start + len;
            std.debug.assert(end <= self.inner.data.items.len);
            const raw_sub = self.inner.data.items[start..end];
            // Safe ptr cast due to layout compatibility
            return @as([*]const IdT, @ptrCast(raw_sub.ptr))[0..len];
        }
        pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
            self.inner.deinit(gpa);
        }
    };
}

////////////////////////////////////////////////////////////////
//                 String Interner & Source Locations
////////////////////////////////////////////////////////////////

pub const StrTag = struct {};
pub const StrId = Index(StrTag);

pub const StringInterner = struct {
    gpa: std.mem.Allocator,
    map: std.StringHashMapUnmanaged(StrId) = .{},
    strings: std.ArrayListUnmanaged([]const u8) = .{},
    mutex: std.Thread.Mutex = .{},

    pub fn init(gpa: std.mem.Allocator) StringInterner {
        return .{ .gpa = gpa };
    }
    pub fn deinit(self: *StringInterner) void {
        var key_iter = self.map.keyIterator();
        while (key_iter.next()) |key| self.gpa.free(key.*);
        self.map.deinit(self.gpa);
        self.strings.deinit(self.gpa);
    }
    pub fn intern(self: *StringInterner, s: []const u8) StrId {
        self.mutex.lock();
        defer self.mutex.unlock();

        const gop = self.map.getOrPut(self.gpa, s) catch oom();
        if (gop.found_existing) return gop.value_ptr.*;

        // Not found: allocate now.
        const key_copy = self.gpa.dupe(u8, s) catch oom();
        // Update the key in the map to point to the owned copy
        gop.key_ptr.* = key_copy;

        const id = StrId.fromRaw(@intCast(self.strings.items.len));
        self.strings.append(self.gpa, key_copy) catch oom();
        gop.value_ptr.* = id;
        return id;
    }
    pub fn get(self: *const StringInterner, id: StrId) []const u8 {
        const self_mut: *StringInterner = @constCast(self);
        self_mut.mutex.lock();
        defer self_mut.mutex.unlock();
        return self_mut.strings.items[id.toRaw()];
    }
};

pub const LocTag = struct {};
pub const LocId = Index(LocTag);

pub const LocStore = struct {
    data: std.ArrayListUnmanaged(Loc) = .{},
    mutex: std.Thread.Mutex = .{},

    pub fn add(self: *LocStore, gpa: std.mem.Allocator, loc: Loc) LocId {
        self.mutex.lock();
        defer self.mutex.unlock();
        const id = LocId.fromRaw(@intCast(self.data.items.len));
        self.data.append(gpa, loc) catch oom();
        return id;
    }
    pub fn get(self: *const LocStore, id: LocId) Loc {
        return self.data.items[id.toRaw()];
    }
    pub fn deinit(self: *LocStore, gpa: std.mem.Allocator) void {
        self.data.deinit(gpa);
    }
};

////////////////////////////////////////////////////////////////
//         Column Store Wrapper over std.MultiArrayList
////////////////////////////////////////////////////////////////

pub fn Table(comptime T: type) type {
    if (std.meta.fields(T).len == 0) {
        return struct {
            len: u32 = 0,
            pub fn add(self: *@This(), _: std.mem.Allocator, _: T) Index(T) {
                const idx = self.len;
                self.len += 1;
                return .{ .index = idx };
            }
            pub fn get(_: *const @This(), _: Index(T)) T {
                return .{};
            }
            pub fn deinit(_: *@This(), _: std.mem.Allocator) void {}
            pub fn col(_: *@This(), comptime _: []const u8) void {
                @compileError("No cols");
            }
        };
    } else {
        return struct {
            list: std.MultiArrayList(T) = .{},
            mutex: std.Thread.Mutex = .{},

            pub fn add(self: *@This(), gpa: std.mem.Allocator, row: T) Index(T) {
                self.mutex.lock();
                defer self.mutex.unlock();
                const idx: u32 = @intCast(self.list.len);
                self.list.append(gpa, row) catch oom();
                return .{ .index = idx };
            }
            pub fn get(self: *@This(), idx: Index(T)) T {
                self.mutex.lock();
                defer self.mutex.unlock();
                return self.list.get(idx.toRaw());
            }
            fn ReturnType(comptime field: []const u8) type {
                inline for (std.meta.fields(T)) |f| {
                    if (std.mem.eql(u8, f.name, field)) return f.type;
                }
            }
            pub fn col(self: *@This(), comptime field_name: []const u8) []ReturnType(field_name) {
                const F = @TypeOf(self.list).Field;
                const idx = std.meta.fieldIndex(T, field_name) orelse @compileError("No field: " ++ field_name);
                return self.list.items(@as(F, @enumFromInt(idx)));
            }
            pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
                self.mutex.lock();
                defer self.mutex.unlock();
                self.list.deinit(gpa);
            }
        };
    }
}

////////////////////////////////////////////////////////////////
//                    Global Kinds & Small Enums
////////////////////////////////////////////////////////////////

pub const PrefixOp = enum(u16) { plus, minus, address_of, logical_not, range, range_inclusive };
pub const InfixOp = enum(u16) {
    add,
    sub,
    mul,
    div,
    mod,
    shl,
    shr,
    add_sat,
    add_wrap,
    sub_sat,
    sub_wrap,
    mul_sat,
    mul_wrap,
    shl_sat,
    b_and,
    b_or,
    b_xor,
    eq,
    neq,
    lt,
    lte,
    gt,
    gte,
    logical_and,
    logical_or,
    range,
    range_inclusive,
    assign,
    error_union,
    error_catch,
    unwrap_orelse,
    add_assign,
    sub_assign,
    mul_assign,
    div_assign,
    mod_assign,
    shl_assign,
    shr_assign,
    and_assign,
    or_assign,
    xor_assign,
    mul_wrap_assign,
    add_wrap_assign,
    sub_wrap_assign,
    mul_sat_assign,
    add_sat_assign,
    sub_sat_assign,
    shl_sat_assign,
    contains,
};
pub const MlirKind = enum(u8) { Module, Type, Attribute, Operation };
pub const MlirPieceKind = enum(u8) { literal, splice };
pub const CastKind = enum(u8) { normal, bitcast, saturate, wrap, checked };
pub const LiteralKind = enum { int, float, string, raw_string, char, imaginary, true, false };

////////////////////////////////////////////////////////////////
//                          IDs
////////////////////////////////////////////////////////////////

pub const ExprTag = struct {};
pub const PatTag = struct {};
pub const ExprId = Index(ExprTag);
pub const DeclId = Index(Rows.Decl);
pub const AttributeId = Index(Rows.Attribute);
pub const ParamId = Index(Rows.Param);
pub const StructFieldId = Index(Rows.StructField);
pub const EnumFieldId = Index(Rows.EnumField);
pub const VariantFieldId = Index(Rows.VariantField);
pub const KeyValueId = Index(Rows.KeyValue);
pub const MatchArmId = Index(Rows.MatchArm);
pub const StructFieldValueId = Index(Rows.StructFieldValue);
pub const MethodPathSegId = Index(Rows.MethodPathSeg);
pub const MlirPieceId = Index(Rows.MlirPiece);
pub const PathSegId = Index(PatRows.PathSeg);
pub const PatternId = Index(PatTag);
pub const PatFieldId = Index(PatRows.StructField);

pub const OptExprId = SentinelIndex(ExprTag);
pub const OptStrId = SentinelIndex(StrTag);
pub const OptLocId = SentinelIndex(LocTag);
pub const OptDeclId = SentinelIndex(Rows.Decl);
pub const OptParamId = SentinelIndex(Rows.Param);

pub const OptRangeExpr = OptRangeOf(ExprId);
pub const OptRangeDecl = OptRangeOf(DeclId);
pub const OptRangeAttr = OptRangeOf(AttributeId);
pub const OptRangeField = OptRangeOf(StructFieldId);
pub const OptRangePat = OptRangeOf(PatternId);
pub const OptRangeMethodPathSeg = OptRangeOf(MethodPathSegId);

pub const CommentTag = struct {};
pub const CommentId = Index(CommentTag);
pub const CommentKind = enum { line, block, doc, container_doc };

pub const CommentStore = struct {
    list: std.ArrayListUnmanaged(Comment) = .{},
    pub fn add(self: *@This(), gpa: std.mem.Allocator, comment: Comment) CommentId {
        const idx: u32 = @intCast(self.list.items.len);
        self.list.append(gpa, comment) catch oom();
        return .{ .index = idx };
    }
    pub fn slice(self: *const @This()) []const Comment {
        return self.list.items;
    }
    pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
        self.list.deinit(gpa);
    }
};

pub const Comment = struct { kind: CommentKind, loc: LocId };

////////////////////////////////////////////////////////////////
//                    Expression Kinds & Rows
////////////////////////////////////////////////////////////////

pub const ExprKind = enum(u16) {
    Literal,
    Ident,
    Splice,
    Prefix,
    Infix,
    Deref,
    ArrayLit,
    Tuple,
    Parenthesized,
    MapLit,
    Call,
    NamedArg,
    IndexAccess,
    FieldAccess,
    StructLit,
    Return,
    Block,
    If,
    While,
    For,
    Match,
    Break,
    Continue,
    Unreachable,
    Null,
    Undefined,
    Defer,
    ErrDefer,
    ErrUnwrap,
    OptionalUnwrap,
    Await,
    Closure,
    Async,
    Cast,
    Catch,
    Import,
    TypeOf,
    Comptime,
    Code,
    Insert,
    Mlir,
    Function,
    ArrayType,
    DynArrayType,
    MapType,
    SliceType,
    OptionalType,
    ErrorSetType,
    ErrorType,
    StructType,
    EnumType,
    VariantLikeType,
    UnionType,
    PointerType,
    SimdType,
    ComplexType,
    TensorType,
    TypeType,
    AnyType,
    NoreturnType,
};

pub const Rows = struct {
    pub const Literal = struct { value: StrId, tag_small: LiteralKind, loc: LocId };
    pub const Ident = struct { name: StrId, loc: LocId };
    pub const Splice = struct { name: StrId, loc: LocId };
    pub const Prefix = struct { right: ExprId, op: PrefixOp, loc: LocId };
    pub const Infix = struct { left: ExprId, right: ExprId, op: InfixOp, loc: LocId };
    pub const Deref = struct { expr: ExprId, loc: LocId };
    pub const ArrayLit = struct { elems: RangeOf(ExprId), trailing_comma: bool, loc: LocId };
    pub const Tuple = struct { elems: RangeOf(ExprId), is_type: bool, loc: LocId };
    pub const Parenthesized = struct { inner: ExprId, loc: LocId };
    pub const MapLit = struct { entries: RangeOf(KeyValueId), loc: LocId };
    pub const KeyValue = struct { key: ExprId, value: ExprId, loc: LocId };
    pub const Call = struct { callee: ExprId, args: RangeOf(ExprId), trailing_arg_comma: bool, loc: LocId };
    pub const NamedArg = struct { name: StrId, value: ExprId, loc: LocId };
    pub const IndexAccess = struct { collection: ExprId, index: ExprId, loc: LocId };
    pub const FieldAccess = struct { parent: ExprId, field: StrId, is_tuple: bool, loc: LocId };
    pub const StructFieldValue = struct { name: OptStrId, value: ExprId, loc: LocId };
    pub const StructLit = struct { fields: RangeOf(StructFieldValueId), ty: OptExprId, trailing_comma: bool, loc: LocId };
    pub const FnFlags = packed struct(u8) { is_proc: bool, is_async: bool, is_variadic: bool, is_extern: bool, is_test: bool, _pad: u3 = 0 };
    pub const Function = struct { params: RangeOf(ParamId), result_ty: OptExprId, body: OptExprId, raw_asm: OptStrId, attrs: OptRangeAttr, flags: FnFlags, trailing_param_comma: bool, loc: LocId };
    pub const Block = struct { items: RangeOf(DeclId), loc: LocId };
    pub const Comptime = struct { payload: ExprId, is_block: bool, loc: LocId };
    pub const Code = struct { block: ExprId, loc: LocId };
    pub const Insert = struct { expr: ExprId, loc: LocId };
    pub const MlirPiece = struct { kind: MlirPieceKind, text: StrId };
    pub const Mlir = struct { kind: MlirKind, text: StrId, pieces: RangeOf(MlirPieceId), args: OptRangeOf(ExprId), result_ty: OptExprId, loc: LocId };
    pub const Return = struct { value: OptExprId, loc: LocId };
    pub const If = struct { cond: ExprId, then_block: ExprId, else_block: OptExprId, loc: LocId };
    pub const While = struct { cond: OptExprId, pattern: SentinelIndex(PatTag), body: ExprId, is_pattern: bool, label: OptStrId, loc: LocId };
    pub const For = struct { pattern: Index(PatTag), iterable: ExprId, body: ExprId, label: OptStrId, loc: LocId };
    pub const Match = struct { expr: ExprId, arms: RangeOf(MatchArmId), loc: LocId };
    pub const MatchArm = struct { pattern: Index(PatTag), guard: OptExprId, body: ExprId, loc: LocId };
    pub const Break = struct { label: OptStrId, value: OptExprId, loc: LocId };
    pub const Continue = struct { label: OptStrId, loc: LocId };
    pub const Unreachable = struct { loc: LocId };
    pub const Null = struct { loc: LocId };
    pub const Undefined = struct { loc: LocId };
    pub const Defer = struct { expr: ExprId, loc: LocId };
    pub const ErrDefer = struct { expr: ExprId, loc: LocId };
    pub const ErrUnwrap = struct { expr: ExprId, loc: LocId };
    pub const OptionalUnwrap = struct { expr: ExprId, loc: LocId };
    pub const Await = struct { expr: ExprId, loc: LocId };
    pub const Closure = struct { params: RangeOf(ParamId), result_ty: OptExprId, body: ExprId, loc: LocId };
    pub const Async = struct { body: ExprId, loc: LocId };
    pub const Cast = struct { expr: ExprId, ty: ExprId, kind: CastKind, loc: LocId };
    pub const Catch = struct { expr: ExprId, binding_name: OptStrId, binding_loc: OptLocId, handler: ExprId, loc: LocId };
    pub const Import = struct { path: StrId, loc: LocId };
    pub const TypeOf = struct { expr: ExprId, loc: LocId };
    pub const Param = struct { pat: OptExprId, ty: OptExprId, value: OptExprId, attrs: OptRangeAttr, is_comptime: bool, loc: LocId };
    pub const Attribute = struct { name: StrId, value: OptExprId, loc: LocId };
    pub const MethodPathSeg = struct { name: StrId, loc: LocId };
    pub const DeclFlags = packed struct(u8) { is_const: bool, is_assign: bool, _pad: u6 = 0 };
    pub const Decl = struct { lhs: OptExprId, rhs: ExprId, ty: OptExprId, method_path: OptRangeMethodPathSeg, flags: DeclFlags, loc: LocId };
    pub const ArrayType = struct { elem: ExprId, size: ExprId, loc: LocId };
    pub const DynArrayType = struct { elem: ExprId, loc: LocId };
    pub const MapType = struct { key: ExprId, value: ExprId, loc: LocId };
    pub const SliceType = struct { elem: ExprId, is_const: bool, loc: LocId };
    pub const OptionalType = struct { elem: ExprId, loc: LocId };
    pub const ErrorSetType = struct { err: ExprId, value: ExprId, loc: LocId };
    pub const StructField = struct { name: StrId, ty: ExprId, value: OptExprId, attrs: OptRangeAttr, loc: LocId };
    pub const StructType = struct { fields: RangeOf(StructFieldId), is_extern: bool, attrs: OptRangeAttr, trailing_field_comma: bool, loc: LocId };
    pub const EnumField = struct { name: StrId, value: OptExprId, attrs: OptRangeAttr, loc: LocId };
    pub const EnumType = struct { fields: RangeOf(EnumFieldId), discriminant: OptExprId, is_extern: bool, attrs: OptRangeAttr, trailing_field_comma: bool, loc: LocId };
    pub const VariantFieldTyTag = enum(u8) { none, Tuple, Struct };
    pub const VariantField = struct { name: StrId, ty_tag: VariantFieldTyTag, tuple_elems: RangeOf(ExprId), struct_fields: RangeOf(StructFieldId), value: OptExprId, attrs: OptRangeAttr, tuple_trailing_comma: bool, struct_trailing_comma: bool, loc: LocId };
    pub const VariantLikeType = struct { fields: RangeOf(VariantFieldId), trailing_field_comma: bool, loc: LocId };
    pub const UnionType = struct { fields: RangeOf(StructFieldId), is_extern: bool, attrs: OptRangeAttr, trailing_field_comma: bool, loc: LocId };
    pub const PointerType = struct { elem: ExprId, is_const: bool, loc: LocId };
    pub const SimdType = struct { elem: ExprId, lanes: ExprId, loc: LocId };
    pub const ComplexType = struct { elem: ExprId, loc: LocId };
    pub const TensorType = struct { elem: ExprId, shape: RangeOf(ExprId), loc: LocId };
    pub const ErrorType = VariantLikeType;
    pub const TypeType = struct { loc: LocId };
    pub const AnyType = struct { loc: LocId };
    pub const NoreturnType = struct { loc: LocId };
};

////////////////////////////////////////////////////////////////
//                          Pattern Store
////////////////////////////////////////////////////////////////

pub const PatternKind = enum(u16) {
    Wildcard,
    Literal,
    Path,
    Binding,
    Parenthesized,
    Tuple,
    Slice,
    Struct,
    VariantTuple,
    VariantStruct,
    Range,
    Or,
    At,
};

pub const PatRows = struct {
    pub const Wildcard = struct { loc: LocId };
    pub const Literal = struct { expr: ExprId, loc: LocId };
    pub const PathSeg = struct { name: StrId, loc: LocId };
    pub const Path = struct { segments: RangeOf(PathSegId), loc: LocId };
    pub const Binding = struct { name: StrId, by_ref: bool, is_mut: bool, loc: LocId };
    pub const Parenthesized = struct { pattern: PatternId, loc: LocId };
    pub const Tuple = struct { elems: RangeOf(PatternId), loc: LocId };
    pub const Slice = struct { elems: RangeOf(PatternId), has_rest: bool, rest_index: u32, rest_binding: SentinelIndex(PatTag), loc: LocId };
    pub const StructField = struct { name: StrId, pattern: Index(PatTag), loc: LocId };
    pub const Struct = struct { path: RangeOf(PathSegId), fields: RangeOf(PatFieldId), has_rest: bool, loc: LocId };
    pub const VariantTuple = struct { path: RangeOf(PathSegId), elems: RangeOf(PatternId), loc: LocId };
    pub const VariantStruct = struct { path: RangeOf(PathSegId), fields: RangeOf(PatFieldId), has_rest: bool, loc: LocId };
    pub const Range = struct { start: OptExprId, end: OptExprId, inclusive_right: bool, loc: LocId };
    pub const Or = struct { alts: RangeOf(PatternId), loc: LocId };
    pub const At = struct { binder: StrId, pattern: Index(PatTag), loc: LocId };
};

pub inline fn RowT(comptime K: ExprKind) type {
    return @field(Rows, @tagName(K));
}
pub inline fn PatRowT(comptime K: PatternKind) type {
    return @field(PatRows, @tagName(K));
}

pub const ProgramDO = struct { top_decls: RangeOf(DeclId), package_name: OptStrId, package_loc: OptLocId };

pub fn StoreIndex(comptime KindT: type) type {
    return struct {
        kinds: std.ArrayListUnmanaged(KindT) = .{},
        rows: std.ArrayListUnmanaged(u32) = .{},
        pub fn newId(self: *@This(), gpa: std.mem.Allocator, k: KindT, row: u32, comptime IdT: type) IdT {
            const i_raw: u32 = @intCast(self.kinds.items.len);
            self.kinds.append(gpa, k) catch oom();
            self.rows.append(gpa, row) catch oom();
            return @field(IdT, "fromRaw")(i_raw);
        }
        pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
            self.kinds.deinit(gpa);
            self.rows.deinit(gpa);
        }
    };
}

pub const ExprStore = struct {
    gpa: std.mem.Allocator,
    index: StoreIndex(ExprKind) = .{},

    Literal: Table(Rows.Literal) = .{},
    Ident: Table(Rows.Ident) = .{},
    Splice: Table(Rows.Splice) = .{},
    Prefix: Table(Rows.Prefix) = .{},
    Infix: Table(Rows.Infix) = .{},
    Deref: Table(Rows.Deref) = .{},
    ArrayLit: Table(Rows.ArrayLit) = .{},
    Tuple: Table(Rows.Tuple) = .{},
    Parenthesized: Table(Rows.Parenthesized) = .{},
    MapLit: Table(Rows.MapLit) = .{},
    KeyValue: Table(Rows.KeyValue) = .{},
    Call: Table(Rows.Call) = .{},
    NamedArg: Table(Rows.NamedArg) = .{},
    IndexAccess: Table(Rows.IndexAccess) = .{},
    FieldAccess: Table(Rows.FieldAccess) = .{},
    StructFieldValue: Table(Rows.StructFieldValue) = .{},
    StructLit: Table(Rows.StructLit) = .{},
    Function: Table(Rows.Function) = .{},
    Block: Table(Rows.Block) = .{},
    Comptime: Table(Rows.Comptime) = .{},
    Code: Table(Rows.Code) = .{},
    Insert: Table(Rows.Insert) = .{},
    Mlir: Table(Rows.Mlir) = .{},
    MlirPiece: Table(Rows.MlirPiece) = .{},
    Return: Table(Rows.Return) = .{},
    If: Table(Rows.If) = .{},
    While: Table(Rows.While) = .{},
    For: Table(Rows.For) = .{},
    Match: Table(Rows.Match) = .{},
    MatchArm: Table(Rows.MatchArm) = .{},
    Break: Table(Rows.Break) = .{},
    Continue: Table(Rows.Continue) = .{},
    Unreachable: Table(Rows.Unreachable) = .{},
    Null: Table(Rows.Null) = .{},
    Undefined: Table(Rows.Undefined) = .{},
    Defer: Table(Rows.Defer) = .{},
    ErrDefer: Table(Rows.ErrDefer) = .{},
    ErrUnwrap: Table(Rows.ErrUnwrap) = .{},
    OptionalUnwrap: Table(Rows.OptionalUnwrap) = .{},
    Await: Table(Rows.Await) = .{},
    Closure: Table(Rows.Closure) = .{},
    Async: Table(Rows.Async) = .{},
    Cast: Table(Rows.Cast) = .{},
    Catch: Table(Rows.Catch) = .{},
    Import: Table(Rows.Import) = .{},
    TypeOf: Table(Rows.TypeOf) = .{},
    Param: Table(Rows.Param) = .{},
    Attribute: Table(Rows.Attribute) = .{},
    Decl: Table(Rows.Decl) = .{},
    MethodPathSeg: Table(Rows.MethodPathSeg) = .{},
    ArrayType: Table(Rows.ArrayType) = .{},
    DynArrayType: Table(Rows.DynArrayType) = .{},
    MapType: Table(Rows.MapType) = .{},
    SliceType: Table(Rows.SliceType) = .{},
    OptionalType: Table(Rows.OptionalType) = .{},
    ErrorSetType: Table(Rows.ErrorSetType) = .{},
    StructField: Table(Rows.StructField) = .{},
    StructType: Table(Rows.StructType) = .{},
    EnumField: Table(Rows.EnumField) = .{},
    EnumType: Table(Rows.EnumType) = .{},
    VariantField: Table(Rows.VariantField) = .{},
    VariantLikeType: Table(Rows.VariantLikeType) = .{},
    UnionType: Table(Rows.UnionType) = .{},
    PointerType: Table(Rows.PointerType) = .{},
    SimdType: Table(Rows.SimdType) = .{},
    ComplexType: Table(Rows.ComplexType) = .{},
    TensorType: Table(Rows.TensorType) = .{},
    ErrorType: Table(Rows.ErrorType) = .{},
    TypeType: Table(Rows.TypeType) = .{},
    AnyType: Table(Rows.AnyType) = .{},
    NoreturnType: Table(Rows.NoreturnType) = .{},

    expr_pool: Pool(ExprId) = .{},
    decl_pool: Pool(DeclId) = .{},
    param_pool: Pool(ParamId) = .{},
    attr_pool: Pool(AttributeId) = .{},
    sfv_pool: Pool(StructFieldValueId) = .{},
    kv_pool: Pool(KeyValueId) = .{},
    arm_pool: Pool(MatchArmId) = .{},
    sfield_pool: Pool(StructFieldId) = .{},
    efield_pool: Pool(EnumFieldId) = .{},
    vfield_pool: Pool(VariantFieldId) = .{},
    method_path_pool: Pool(MethodPathSegId) = .{},
    mlir_piece_pool: Pool(MlirPieceId) = .{},
    strs: *StringInterner,
    locs: *LocStore,

    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner, locs: *LocStore) ExprStore {
        return .{ .gpa = gpa, .strs = strs, .locs = locs };
    }
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;
        self.index.deinit(gpa);
        inline for (@typeInfo(ExprKind).@"enum".fields) |f| @field(self, f.name).deinit(gpa);
        inline for (.{ "MlirPiece", "Decl", "MethodPathSeg", "Param", "Attribute", "KeyValue", "StructFieldValue", "MatchArm", "StructField", "EnumField", "VariantField" }) |n| @field(self, n).deinit(gpa);
        inline for (.{ "expr_pool", "decl_pool", "param_pool", "attr_pool", "sfv_pool", "kv_pool", "arm_pool", "sfield_pool", "efield_pool", "vfield_pool", "method_path_pool", "mlir_piece_pool" }) |n| @field(self, n).deinit(gpa);
    }
    pub fn add(self: *@This(), comptime K: ExprKind, row: RowT(K)) ExprId {
        const r = @field(self, @tagName(K)).add(self.gpa, row);
        return self.index.newId(self.gpa, K, r.toRaw(), ExprId);
    }
    pub fn get(self: *@This(), comptime K: ExprKind, id: ExprId) RowT(K) {
        return @field(self, @tagName(K)).get(.{ .index = self.index.rows.items[id.toRaw()] });
    }
    pub fn kind(self: *ExprStore, id: ExprId) ExprKind {
        return self.index.kinds.items[id.toRaw()];
    }
    pub fn table(self: *@This(), comptime K: ExprKind) *std.MultiArrayList(RowT(K)) {
        return &@field(self, @tagName(K)).list;
    }

    pub fn addKeyValue(self: *@This(), row: Rows.KeyValue) KeyValueId {
        return self.KeyValue.add(self.gpa, row);
    }
    pub fn addStructFieldValue(self: *@This(), row: Rows.StructFieldValue) StructFieldValueId {
        return self.StructFieldValue.add(self.gpa, row);
    }
    pub fn addDeclRow(self: *@This(), row: Rows.Decl) DeclId {
        return self.Decl.add(self.gpa, row);
    }
    pub fn addMethodPathSegRow(self: *@This(), row: Rows.MethodPathSeg) MethodPathSegId {
        return self.MethodPathSeg.add(self.gpa, row);
    }
    pub fn addParamRow(self: *@This(), row: Rows.Param) ParamId {
        return self.Param.add(self.gpa, row);
    }
    pub fn addAttrRow(self: *@This(), row: Rows.Attribute) AttributeId {
        return self.Attribute.add(self.gpa, row);
    }
    pub fn addMlirPieceRow(self: *@This(), row: Rows.MlirPiece) MlirPieceId {
        return self.MlirPiece.add(self.gpa, row);
    }
    pub fn addStructFieldRow(self: *@This(), row: Rows.StructField) StructFieldId {
        return self.StructField.add(self.gpa, row);
    }
    pub fn addEnumFieldRow(self: *@This(), row: Rows.EnumField) EnumFieldId {
        return self.EnumField.add(self.gpa, row);
    }
    pub fn addVariantFieldRow(self: *@This(), row: Rows.VariantField) VariantFieldId {
        return self.VariantField.add(self.gpa, row);
    }
    pub fn addMatchArmRow(self: *@This(), row: Rows.MatchArm) MatchArmId {
        return self.MatchArm.add(self.gpa, row);
    }
};

pub const PatternStore = struct {
    gpa: std.mem.Allocator,
    index: StoreIndex(PatternKind) = .{},
    Wildcard: Table(PatRows.Wildcard) = .{},
    Literal: Table(PatRows.Literal) = .{},
    PathSeg: Table(PatRows.PathSeg) = .{},
    Path: Table(PatRows.Path) = .{},
    Binding: Table(PatRows.Binding) = .{},
    Parenthesized: Table(PatRows.Parenthesized) = .{},
    Tuple: Table(PatRows.Tuple) = .{},
    Slice: Table(PatRows.Slice) = .{},
    StructField: Table(PatRows.StructField) = .{},
    Struct: Table(PatRows.Struct) = .{},
    VariantTuple: Table(PatRows.VariantTuple) = .{},
    VariantStruct: Table(PatRows.VariantStruct) = .{},
    Range: Table(PatRows.Range) = .{},
    Or: Table(PatRows.Or) = .{},
    At: Table(PatRows.At) = .{},
    pat_pool: Pool(PatternId) = .{},
    seg_pool: Pool(PathSegId) = .{},
    field_pool: Pool(PatFieldId) = .{},
    strs: *StringInterner,

    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner) PatternStore {
        return .{ .gpa = gpa, .strs = strs };
    }
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;
        self.index.deinit(gpa);
        inline for (@typeInfo(PatternKind).@"enum".fields) |f| @field(self, f.name).deinit(gpa);
        inline for (.{ "PathSeg", "StructField" }) |n| @field(self, n).deinit(gpa);
        self.pat_pool.deinit(gpa);
        self.seg_pool.deinit(gpa);
        self.field_pool.deinit(gpa);
    }
    pub fn add(self: *@This(), comptime K: PatternKind, row: PatRowT(K)) PatternId {
        const r = @field(self, @tagName(K)).add(self.gpa, row);
        return self.index.newId(self.gpa, K, r.toRaw(), PatternId);
    }
    pub fn get(self: *@This(), comptime K: PatternKind, id: PatternId) PatRowT(K) {
        return @field(self, @tagName(K)).get(.{ .index = self.index.rows.items[id.toRaw()] });
    }
    pub fn kind(self: *PatternStore, id: PatternId) PatternKind {
        return self.index.kinds.items[id.toRaw()];
    }
    pub fn addPathSeg(self: *@This(), row: PatRows.PathSeg) PathSegId {
        return self.PathSeg.add(self.gpa, row);
    }
    pub fn addPatField(self: *@This(), row: PatRows.StructField) PatFieldId {
        return self.StructField.add(self.gpa, row);
    }
};

pub const CST = struct {
    gpa: std.mem.Allocator,
    exprs: ExprStore,
    pats: PatternStore,
    program: ProgramDO,
    interner: *StringInterner,
    comments: CommentStore = .{},
    pub fn init(gpa: std.mem.Allocator, interner: *StringInterner, locs: *LocStore) CST {
        return .{ .gpa = gpa, .exprs = .init(gpa, interner, locs), .pats = .init(gpa, interner), .program = .{ .top_decls = RangeOf(DeclId).empty(), .package_name = .none(), .package_loc = .none() }, .interner = interner };
    }
    pub fn deinit(self: *@This()) void {
        self.exprs.deinit();
        self.pats.deinit();
        self.comments.deinit(self.gpa);
    }
    pub fn kind(self: *CST, id: anytype) if (@TypeOf(id) == ExprId) ExprKind else PatternKind {
        if (@TypeOf(id) == ExprId) return self.exprs.kind(id);
        if (@TypeOf(id) == PatternId) return self.pats.kind(id);
        @compileError("Bad ID");
    }
};

comptime {
    std.debug.assert(@sizeOf(ExprId) == 4);
    std.debug.assert(@sizeOf(LocId) == 4);
    std.debug.assert(@sizeOf(StrId) == 4);
}

pub const DodPrinter = struct {
    writer: *std.io.Writer,
    indent: usize = 0,
    exprs: *ExprStore,
    pats: *PatternStore,

    pub fn init(writer: anytype, exprs: *ExprStore, pats: *PatternStore) DodPrinter {
        return .{ .writer = writer, .exprs = exprs, .pats = pats };
    }
    fn ws(self: *DodPrinter) !void {
        var i: usize = 0;
        while (i < self.indent) : (i += 1) try self.writer.writeByte(' ');
    }
    fn open(self: *DodPrinter, comptime head: []const u8, args: anytype) !void {
        try self.ws();
        try self.writer.print(head, args);
        try self.writer.writeAll("\n");
        self.indent += 2;
    }
    fn close(self: *DodPrinter) !void {
        self.indent = if (self.indent >= 2) self.indent - 2 else 0;
        try self.ws();
        try self.writer.writeAll(")\n");
    }
    fn leaf(self: *DodPrinter, comptime fmt: []const u8, args: anytype) !void {
        try self.ws();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
    }
    inline fn s(self: *const DodPrinter, id: StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    pub fn printProgram(self: *DodPrinter, prog: *const ProgramDO) !void {
        try self.open("(program", .{});
        if (!prog.package_name.isNone()) {
            try self.leaf("(package \"{s}\")", .{self.s(prog.package_name.unwrap())});
        } else try self.leaf("(package null)", .{});
        const decls = self.exprs.decl_pool.slice(prog.top_decls);
        for (decls) |did| try self.printDecl(did);
        try self.close();
    }
    pub fn printExpr(self: *DodPrinter, id: ExprId) anyerror!void {
        switch (self.exprs.kind(id)) {
            .Literal => {
                const n = self.exprs.get(.Literal, id);
                try self.leaf("(literal kind=#{d} \"{s}\")", .{ n.tag_small, self.s(n.value) });
            },
            .NamedArg => {
                const n = self.exprs.get(.NamedArg, id);
                try self.open("(named_arg \"{s}\"", .{self.s(n.name)});
                try self.printExpr(n.value);
                try self.close();
            },
            .Ident => {
                const n = self.exprs.get(.Ident, id);
                try self.leaf("(ident \"{s}\")", .{self.s(n.name)});
            },
            .Splice => {
                const n = self.exprs.get(.Splice, id);
                try self.leaf("(splice \"{s}\")", .{self.s(n.name)});
            },
            .Prefix => {
                const n = self.exprs.get(.Prefix, id);
                try self.open("(prefix op={s}", .{@tagName(n.op)});
                try self.printExpr(n.right);
                try self.close();
            },
            .Infix => {
                const n = self.exprs.get(.Infix, id);
                try self.open("(infix op={s}", .{@tagName(n.op)});
                try self.printExpr(n.left);
                try self.printExpr(n.right);
                try self.close();
            },
            .Deref => {
                const n = self.exprs.get(.Deref, id);
                try self.open("(deref", .{});
                try self.printExpr(n.expr);
                try self.close();
            },
            .ArrayLit => {
                const n = self.exprs.get(.ArrayLit, id);
                try self.open("(array", .{});
                try self.printExprRange("elems", n.elems);
                try self.close();
            },
            .Tuple => {
                const n = self.exprs.get(.Tuple, id);
                try self.open("(tuple is_type={})", .{n.is_type});
                try self.printExprRange("elems", n.elems);
                try self.close();
            },
            .Parenthesized => {
                const n = self.exprs.get(.Parenthesized, id);
                try self.open("(parenthesized", .{});
                try self.printExpr(n.inner);
                try self.close();
            },
            .MapLit => {
                const n = self.exprs.get(.MapLit, id);
                try self.open("(map", .{});
                const entries = self.exprs.kv_pool.slice(n.entries);
                for (entries) |e_id| {
                    const e = self.exprs.KeyValue.get(e_id);
                    try self.open("(entry", .{});
                    try self.open("(key", .{});
                    try self.printExpr(e.key);
                    try self.close();
                    try self.open("(value", .{});
                    try self.printExpr(e.value);
                    try self.close();
                    try self.close();
                }
                try self.close();
            },
            .Call => {
                const n = self.exprs.get(.Call, id);
                try self.open("(call", .{});
                try self.open("(callee", .{});
                try self.printExpr(n.callee);
                try self.close();
                try self.printExprRange("args", n.args);
                try self.close();
            },
            .IndexAccess => {
                const n = self.exprs.get(.IndexAccess, id);
                try self.open("(index", .{});
                try self.open("(collection", .{});
                try self.printExpr(n.collection);
                try self.close();
                try self.open("(expr", .{});
                try self.printExpr(n.index);
                try self.close();
                try self.close();
            },
            .FieldAccess => {
                const n = self.exprs.get(.FieldAccess, id);
                try self.open("(field name=\"{s}\" is_tuple={})", .{ self.s(n.field), n.is_tuple });
                try self.printExpr(n.parent);
                try self.close();
            },
            .StructLit => {
                const n = self.exprs.get(.StructLit, id);
                try self.open("(struct_literal", .{});
                const fields = self.exprs.sfv_pool.slice(n.fields);
                for (fields) |fid| {
                    const f = self.exprs.StructFieldValue.get(fid);
                    try self.open("(field", .{});
                    if (!f.name.isNone()) try self.leaf("name=\"{s}\"", .{self.s(f.name.unwrap())}) else try self.leaf("name=null", .{});
                    try self.open("(value", .{});
                    try self.printExpr(f.value);
                    try self.close();
                    try self.close();
                }
                try self.close();
            },
            .Function => {
                const n = self.exprs.get(.Function, id);
                try self.open("({s}", .{if (n.flags.is_proc) "procedure" else "function"});
                if (n.flags.is_async) try self.leaf("(async)", .{});
                if (n.flags.is_variadic) try self.leaf("(variadic)", .{});
                if (n.flags.is_extern) try self.leaf("(extern)", .{});
                if (!n.attrs.isNone()) try self.printAttrs(n.attrs);
                try self.printParams(n.params);
                if (!n.result_ty.isNone()) {
                    try self.open("(result", .{});
                    try self.printExpr(n.result_ty.unwrap());
                    try self.close();
                }
                if (!n.body.isNone()) {
                    try self.open("(body", .{});
                    try self.printExpr(n.body.unwrap());
                    try self.close();
                } else if (!n.raw_asm.isNone()) {
                    try self.leaf("(asm \"{s}\")", .{self.s(n.raw_asm.unwrap())});
                }
                try self.close();
            },
            .Block => {
                const n = self.exprs.get(.Block, id);
                try self.open("(block", .{});
                const decls = self.exprs.decl_pool.slice(n.items);
                for (decls) |did| try self.printDecl(did);
                try self.close();
            },
            .Comptime => {
                const n = self.exprs.get(.Comptime, id);
                try self.open("(comptime kind={s}", .{if (n.is_block) "block" else "expr"});
                try self.printExpr(n.payload);
                try self.close();
            },
            .Code => {
                const n = self.exprs.get(.Code, id);
                try self.open("(code", .{});
                try self.printExpr(n.block);
                try self.close();
            },
            .Insert => {
                const n = self.exprs.get(.Insert, id);
                try self.open("(insert", .{});
                try self.printExpr(n.expr);
                try self.close();
            },
            .Mlir => {
                const n = self.exprs.get(.Mlir, id);
                try self.open("(mlir kind={s}", .{@tagName(n.kind)});
                try self.leaf("(text \"{s}\")", .{self.s(n.text)});
                const pieces = self.exprs.mlir_piece_pool.slice(n.pieces);
                try self.open("(pieces", .{});
                for (pieces) |pid| {
                    const piece = self.exprs.MlirPiece.get(pid);
                    switch (piece.kind) {
                        .literal => try self.leaf("(literal \"{s}\")", .{self.s(piece.text)}),
                        .splice => try self.leaf("(splice {s})", .{self.s(piece.text)}),
                    }
                }
                try self.close();
                try self.close();
            },
            .Return => {
                const n = self.exprs.get(.Return, id);
                try self.open("(return", .{});
                if (!n.value.isNone()) {
                    try self.open("(value", .{});
                    try self.printExpr(n.value.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .If => {
                const n = self.exprs.get(.If, id);
                try self.open("(if", .{});
                try self.open("(cond", .{});
                try self.printExpr(n.cond);
                try self.close();
                try self.open("(then", .{});
                try self.printExpr(n.then_block);
                try self.close();
                if (!n.else_block.isNone()) {
                    try self.open("(else", .{});
                    try self.printExpr(n.else_block.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .While => {
                const n = self.exprs.get(.While, id);
                try self.open("(while is_pattern={})", .{n.is_pattern});
                if (!n.label.isNone()) try self.leaf("label=\"{s}\"", .{self.s(n.label.unwrap())});
                if (!n.pattern.isNone()) {
                    try self.open("(pattern", .{});
                    try self.printPattern(n.pattern.unwrap());
                    try self.close();
                }
                if (!n.cond.isNone()) {
                    try self.open("(cond", .{});
                    try self.printExpr(n.cond.unwrap());
                    try self.close();
                }
                try self.open("(body", .{});
                try self.printExpr(n.body);
                try self.close();
                try self.close();
            },
            .For => {
                const n = self.exprs.get(.For, id);
                try self.open("(for", .{});
                if (!n.label.isNone()) try self.leaf("label=\"{s}\"", .{self.s(n.label.unwrap())});
                try self.open("(pattern", .{});
                try self.printPattern(n.pattern);
                try self.close();
                try self.open("(iterable", .{});
                try self.printExpr(n.iterable);
                try self.close();
                try self.open("(body", .{});
                try self.printExpr(n.body);
                try self.close();
                try self.close();
            },
            .Match => {
                const n = self.exprs.get(.Match, id);
                try self.open("(match", .{});
                try self.open("(expr", .{});
                try self.printExpr(n.expr);
                try self.close();
                const arms = self.exprs.arm_pool.slice(n.arms);
                for (arms) |aid| {
                    const a = self.exprs.MatchArm.get(aid);
                    try self.open("(arm", .{});
                    try self.open("(pattern", .{});
                    try self.printPattern(a.pattern);
                    try self.close();
                    if (!a.guard.isNone()) {
                        try self.open("(guard", .{});
                        try self.printExpr(a.guard.unwrap());
                        try self.close();
                    }
                    try self.open("(body", .{});
                    try self.printExpr(a.body);
                    try self.close();
                    try self.close();
                }
                try self.close();
            },
            .Break => {
                const n = self.exprs.get(.Break, id);
                try self.open("(break", .{});
                if (!n.label.isNone()) try self.leaf("label=\"{s}\"", .{self.s(n.label.unwrap())});
                if (!n.value.isNone()) {
                    try self.open("(value", .{});
                    try self.printExpr(n.value.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .Continue => {
                const n = self.exprs.get(.Continue, id);
                if (n.label.isNone()) {
                    try self.leaf("(continue)", .{});
                } else {
                    try self.leaf("(continue label=\"{s}\")", .{self.s(n.label.unwrap())});
                }
            },
            .Unreachable => try self.leaf("(unreachable)", .{}),
            .Null => try self.leaf("(null)", .{}),
            .Undefined => try self.leaf("(undefined)", .{}),
            .Defer => {
                const n = self.exprs.get(.Defer, id);
                try self.open("(defer", .{});
                try self.printExpr(n.expr);
                try self.close();
            },
            .ErrDefer => {
                const n = self.exprs.get(.ErrDefer, id);
                try self.open("(err_defer", .{});
                try self.printExpr(n.expr);
                try self.close();
            },
            .ErrUnwrap => {
                const n = self.exprs.get(.ErrUnwrap, id);
                try self.open("(err_unwrap", .{});
                try self.printExpr(n.expr);
                try self.close();
            },
            .OptionalUnwrap => {
                const n = self.exprs.get(.OptionalUnwrap, id);
                try self.open("(opt_unwrap", .{});
                try self.printExpr(n.expr);
                try self.close();
            },
            .Await => {
                const n = self.exprs.get(.Await, id);
                try self.open("(await", .{});
                try self.printExpr(n.expr);
                try self.close();
            },
            .Closure => {
                const n = self.exprs.get(.Closure, id);
                try self.open("(closure", .{});
                try self.printParams(n.params);
                if (!n.result_ty.isNone()) {
                    try self.open("(result", .{});
                    try self.printExpr(n.result_ty.unwrap());
                    try self.close();
                }
                try self.open("(body", .{});
                try self.printExpr(n.body);
                try self.close();
                try self.close();
            },
            .Async => {
                const n = self.exprs.get(.Async, id);
                try self.open("(async", .{});
                try self.printExpr(n.body);
                try self.close();
            },
            .Cast => {
                const n = self.exprs.get(.Cast, id);
                try self.open("({s}", .{switch (n.kind) {
                    .normal => "cast",
                    .bitcast => "bitcast",
                    .saturate => "saturating_cast",
                    .wrap => "wrapping_cast",
                    .checked => "checked_cast",
                }});
                try self.open("(expr", .{});
                try self.printExpr(n.expr);
                try self.close();
                try self.open("(type", .{});
                try self.printExpr(n.ty);
                try self.close();
                try self.close();
            },
            .Catch => {
                const n = self.exprs.get(.Catch, id);
                try self.open("(catch", .{});
                try self.open("(expr", .{});
                try self.printExpr(n.expr);
                try self.close();
                if (!n.binding_name.isNone()) try self.leaf("(binding \"{s}\")", .{self.s(n.binding_name.unwrap())});
                try self.open("(handler", .{});
                try self.printExpr(n.handler);
                try self.close();
                try self.close();
            },
            .Import => {
                const n = self.exprs.get(.Import, id);
                try self.open("(import", .{});
                try self.leaf("(path \"{s}\")", .{self.s(n.path)});
                try self.close();
            },
            .TypeOf => {
                const n = self.exprs.get(.TypeOf, id);
                try self.open("(typeof", .{});
                try self.printExpr(n.expr);
                try self.close();
            },
            .ArrayType => {
                const n = self.exprs.get(.ArrayType, id);
                try self.open("(array_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(n.elem);
                try self.close();
                try self.open("(size", .{});
                try self.printExpr(n.size);
                try self.close();
                try self.close();
            },
            .DynArrayType => {
                const n = self.exprs.get(.DynArrayType, id);
                try self.open("(dyn_array_type", .{});
                try self.printExpr(n.elem);
                try self.close();
            },
            .MapType => {
                const n = self.exprs.get(.MapType, id);
                try self.open("(map_type", .{});
                try self.open("(key", .{});
                try self.printExpr(n.key);
                try self.close();
                try self.open("(value", .{});
                try self.printExpr(n.value);
                try self.close();
                try self.close();
            },
            .SliceType => {
                const n = self.exprs.get(.SliceType, id);
                try self.open("(slice_type is_const={})", .{n.is_const});
                try self.printExpr(n.elem);
                try self.close();
            },
            .OptionalType => {
                const n = self.exprs.get(.OptionalType, id);
                try self.open("(optional_type", .{});
                try self.printExpr(n.elem);
                try self.close();
            },
            .ErrorSetType => {
                const n = self.exprs.get(.ErrorSetType, id);
                try self.open("(error_set_type", .{});
                try self.open("(err", .{});
                try self.printExpr(n.err);
                try self.close();
                try self.open("(value", .{});
                try self.printExpr(n.value);
                try self.close();
                try self.close();
            },
            .StructType => {
                const n = self.exprs.get(.StructType, id);
                try self.open("(struct_type is_extern={})", .{n.is_extern});
                if (!n.attrs.isNone()) try self.printAttrs(n.attrs);
                const fields = self.exprs.sfield_pool.slice(n.fields);
                for (fields) |fid| try self.printStructField(fid);
                try self.close();
            },
            .EnumType => {
                const n = self.exprs.get(.EnumType, id);
                try self.open("(enum_type is_extern={})", .{n.is_extern});
                if (!n.attrs.isNone()) try self.printAttrs(n.attrs);
                if (!n.discriminant.isNone()) {
                    try self.open("(discriminant", .{});
                    try self.printExpr(n.discriminant.unwrap());
                    try self.close();
                }
                const fields = self.exprs.efield_pool.slice(n.fields);
                for (fields) |eid| {
                    const f = self.exprs.EnumField.get(eid);
                    try self.open("(field name=\"{s}\"", .{self.s(f.name)});
                    if (!f.attrs.isNone()) try self.printAttrs(f.attrs);
                    if (!f.value.isNone()) {
                        try self.open("(value", .{});
                        try self.printExpr(f.value.unwrap());
                        try self.close();
                    }
                    try self.close();
                }
                try self.close();
            },
            .VariantLikeType => {
                const n = self.exprs.get(.VariantLikeType, id);
                try self.open("(variant_type", .{});
                const fields = self.exprs.vfield_pool.slice(n.fields);
                for (fields) |vid| {
                    const f = self.exprs.VariantField.get(vid);
                    try self.open("(field name=\"{s}\"", .{self.s(f.name)});
                    if (!f.attrs.isNone()) try self.printAttrs(f.attrs);
                    switch (f.ty_tag) {
                        .none => {},
                        .Tuple => try self.printExprRange("tuple", f.tuple_elems),
                        .Struct => {
                            try self.open("(struct", .{});
                            const sfs = self.exprs.sfield_pool.slice(f.struct_fields);
                            for (sfs) |sfid| try self.printStructField(sfid);
                            try self.close();
                        },
                    }
                    if (!f.value.isNone()) {
                        try self.open("(value", .{});
                        try self.printExpr(f.value.unwrap());
                        try self.close();
                    }
                    try self.close();
                }
                try self.close();
            },
            .UnionType => {
                const n = self.exprs.get(.UnionType, id);
                try self.open("(union_type is_extern={})", .{n.is_extern});
                if (!n.attrs.isNone()) try self.printAttrs(n.attrs);
                const fields = self.exprs.sfield_pool.slice(n.fields);
                for (fields) |fid| try self.printStructField(fid);
                try self.close();
            },
            .PointerType => {
                const n = self.exprs.get(.PointerType, id);
                try self.open("(pointer_type is_const={})", .{n.is_const});
                try self.printExpr(n.elem);
                try self.close();
            },
            .SimdType => {
                const n = self.exprs.get(.SimdType, id);
                try self.open("(simd_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(n.elem);
                try self.close();
                try self.open("(lanes", .{});
                try self.printExpr(n.lanes);
                try self.close();
                try self.close();
            },
            .ComplexType => {
                const n = self.exprs.get(.ComplexType, id);
                try self.open("(complex_type", .{});
                try self.printExpr(n.elem);
                try self.close();
            },
            .TensorType => {
                const n = self.exprs.get(.TensorType, id);
                try self.open("(tensor_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(n.elem);
                try self.close();
                try self.printExprRange("shape", n.shape);
                try self.close();
            },
            .ErrorType => {
                const n = self.exprs.get(.ErrorType, id);
                try self.open("(error_type", .{});
                const fields = self.exprs.vfield_pool.slice(n.fields);
                for (fields) |vid| {
                    const f = self.exprs.VariantField.get(vid);
                    try self.open("(field name=\"{s}\"", .{self.s(f.name)});
                    if (!f.attrs.isNone()) try self.printAttrs(f.attrs);
                    switch (f.ty_tag) {
                        .none => {},
                        .Tuple => try self.printExprRange("tuple", f.tuple_elems),
                        .Struct => {
                            try self.open("(struct", .{});
                            const sfs = self.exprs.sfield_pool.slice(f.struct_fields);
                            for (sfs) |sfid| try self.printStructField(sfid);
                            try self.close();
                        },
                    }
                    try self.close();
                }
                try self.close();
            },
            .TypeType => try self.leaf("(type)", .{}),
            .AnyType => try self.leaf("(any)", .{}),
            .NoreturnType => try self.leaf("(noreturn)", .{}),
        }
    }
    pub fn printDecl(self: *DodPrinter, id: DeclId) !void {
        const d = self.exprs.Decl.get(id);
        try self.open("(decl is_const={} is_assign={})", .{ d.flags.is_const, d.flags.is_assign });
        if (!d.ty.isNone()) {
            try self.open("(type", .{});
            try self.printExpr(d.ty.unwrap());
            try self.close();
        }
        if (!d.lhs.isNone()) {
            try self.open("(lhs", .{});
            try self.printExpr(d.lhs.unwrap());
            try self.close();
        }
        if (!d.method_path.isNone()) {
            try self.open("(method_path", .{});
            const segs = self.exprs.method_path_pool.slice(d.method_path.asRange());
            for (segs) |sid| {
                const seg = self.exprs.MethodPathSeg.get(sid);
                try self.leaf("(seg \"{s}\")", .{self.s(seg.name)});
            }
            try self.close();
        }
        try self.open("(rhs", .{});
        try self.printExpr(d.rhs);
        try self.close();
        try self.close();
    }
    fn printExprRange(self: *DodPrinter, comptime name: []const u8, r: RangeOf(ExprId)) !void {
        try self.open("(" ++ name, .{});
        const xs = self.exprs.expr_pool.slice(r);
        for (xs) |eid| try self.printExpr(eid);
        try self.close();
    }
    fn printAttrs(self: *DodPrinter, opt_r: OptRangeAttr) !void {
        if (opt_r.isNone()) return;
        const xs = self.exprs.attr_pool.slice(opt_r.asRange());
        try self.open("(attributes", .{});
        for (xs) |aid| {
            const a = self.exprs.Attribute.get(aid);
            if (a.value.isNone()) {
                try self.leaf("(attr name=\"{s}\")", .{self.s(a.name)});
            } else {
                try self.open("(attr name=\"{s}\"", .{self.s(a.name)});
                try self.open("(value", .{});
                try self.printExpr(a.value.unwrap());
                try self.close();
                try self.close();
            }
        }
        try self.leaf(")", .{});
        self.indent = if (self.indent >= 2) self.indent - 2 else 0;
    }
    fn printParams(self: *DodPrinter, r: RangeOf(ParamId)) !void {
        const xs = self.exprs.param_pool.slice(r);
        for (xs) |pid| {
            const p = self.exprs.Param.get(pid);
            try self.open("(param", .{});
            if (!p.attrs.isNone()) try self.printAttrs(p.attrs);
            if (!p.pat.isNone()) {
                try self.open("(pat", .{});
                try self.printExpr(p.pat.unwrap());
                try self.close();
            }
            if (!p.ty.isNone()) {
                try self.open("(type", .{});
                try self.printExpr(p.ty.unwrap());
                try self.close();
            }
            if (!p.value.isNone()) {
                try self.open("(value", .{});
                try self.printExpr(p.value.unwrap());
                try self.close();
            }
            try self.close();
        }
    }
    fn printStructField(self: *DodPrinter, id: StructFieldId) !void {
        const f = self.exprs.StructField.get(id);
        try self.open("(field name=\"{s}\"", .{self.s(f.name)});
        if (!f.attrs.isNone()) try self.printAttrs(f.attrs);
        try self.open("(type", .{});
        try self.printExpr(f.ty);
        try self.close();
        if (!f.value.isNone()) {
            try self.open("(value", .{});
            try self.printExpr(f.value.unwrap());
            try self.close();
        }
        try self.close();
    }
    pub fn printPattern(self: *DodPrinter, id: PatternId) !void {
        switch (self.pats.kind(id)) {
            .Wildcard => try self.leaf("(wildcard)", .{}),
            .Literal => {
                const n = self.pats.get(.Literal, id);
                try self.open("(literal", .{});
                try self.printExpr(n.expr);
                try self.close();
            },
            .Path => {
                const n = self.pats.get(.Path, id);
                try self.open("(path", .{});
                const segs = self.pats.seg_pool.slice(n.segments);
                for (segs) |sid| {
                    const sseg = self.pats.PathSeg.get(sid);
                    try self.leaf("segment=\"{s}\"", .{self.s(sseg.name)});
                }
                try self.close();
            },
            .Binding => {
                const n = self.pats.get(.Binding, id);
                try self.leaf("(binding name=\"{s}\" by_ref={} is_mut={})", .{ self.s(n.name), n.by_ref, n.is_mut });
            },
            .Parenthesized => {
                const n = self.pats.get(.Parenthesized, id);
                try self.open("(parenthesized)", .{});
                try self.printPattern(n.pattern);
                try self.close();
            },
            .Tuple => {
                const n = self.pats.get(.Tuple, id);
                try self.open("(tuple_pattern", .{});
                const xs = self.pats.pat_pool.slice(n.elems);
                for (xs) |pid2| try self.printPattern(pid2);
                try self.close();
            },
            .Slice => {
                const n = self.pats.get(.Slice, id);
                try self.open("(slice_pattern has_rest={})", .{n.has_rest});
                const xs = self.pats.pat_pool.slice(n.elems);
                for (xs) |pid2| try self.printPattern(pid2);
                if (!n.rest_binding.isNone()) {
                    try self.open("(rest_binding", .{});
                    try self.printPattern(n.rest_binding.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .Struct => {
                const n = self.pats.get(.Struct, id);
                try self.open("(struct_pattern has_rest={})", .{n.has_rest});
                const path = self.pats.seg_pool.slice(n.path);
                for (path) |sid| {
                    const sseg = self.pats.PathSeg.get(sid);
                    try self.leaf("segment=\"{s}\"", .{self.s(sseg.name)});
                }
                const fields = self.pats.field_pool.slice(n.fields);
                for (fields) |fid| {
                    const f = self.pats.StructField.get(fid);
                    try self.open("(field name=\"{s}\"", .{self.s(f.name)});
                    try self.printPattern(f.pattern);
                    try self.close();
                }
                try self.close();
            },
            .VariantTuple => {
                const n = self.pats.get(.VariantTuple, id);
                try self.open("(variant_tuple_pattern", .{});
                const path = self.pats.seg_pool.slice(n.path);
                for (path) |sid| {
                    const sseg = self.pats.PathSeg.get(sid);
                    try self.leaf("segment=\"{s}\"", .{self.s(sseg.name)});
                }
                const elems = self.pats.pat_pool.slice(n.elems);
                for (elems) |pid2| try self.printPattern(pid2);
                try self.close();
            },
            .VariantStruct => {
                const n = self.pats.get(.VariantStruct, id);
                try self.open("(variant_struct_pattern has_rest={})", .{n.has_rest});
                const path = self.pats.seg_pool.slice(n.path);
                for (path) |sid| {
                    const sseg = self.pats.PathSeg.get(sid);
                    try self.leaf("segment=\"{s}\"", .{self.s(sseg.name)});
                }
                const fields = self.pats.field_pool.slice(n.fields);
                for (fields) |fid| {
                    const f = self.pats.StructField.get(fid);
                    try self.open("(field name=\"{s}\"", .{self.s(f.name)});
                    try self.printPattern(f.pattern);
                    try self.close();
                }
                try self.close();
            },
            .Range => {
                const n = self.pats.get(.Range, id);
                try self.open("(range_pattern inclusive_right={})", .{n.inclusive_right});
                if (!n.start.isNone()) {
                    try self.open("(start", .{});
                    try self.printExpr(n.start.unwrap());
                    try self.close();
                }
                if (!n.end.isNone()) {
                    try self.open("(end", .{});
                    try self.printExpr(n.end.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .Or => {
                const n = self.pats.get(.Or, id);
                try self.open("(or_pattern", .{});
                const alts = self.pats.pat_pool.slice(n.alts);
                for (alts) |pid2| try self.printPattern(pid2);
                try self.close();
            },
            .At => {
                const n = self.pats.get(.At, id);
                try self.open("(at_pattern binder=\"{s}\"", .{self.s(n.binder)});
                try self.printPattern(n.pattern);
                try self.close();
            },
        }
    }
};

fn mkLoc(es: *ExprStore, start: u32, end: u32) LocId {
    return es.locs.add(es.gpa, .{ .start = start, .end = end });
}

test "printer: simple const decl with lhs, rhs literal" {
    const gpa = std.testing.allocator;
    var locs = LocStore{};
    defer locs.deinit(gpa);
    var interner = StringInterner.init(gpa);
    defer interner.deinit();
    var cst = CST.init(gpa, &interner, &locs);
    defer cst.deinit();
    const s_pkg = cst.interner.intern("testpkg");
    const s_x = cst.interner.intern("x");
    const s_42 = cst.interner.intern("42");
    const loc = mkLoc(&cst.exprs, 1, 1);
    const id_x = cst.exprs.add(.Ident, .{ .name = s_x, .loc = loc });
    const id_42 = cst.exprs.add(.Literal, .{ .value = s_42, .tag_small = .int, .loc = loc });
    const did = cst.exprs.addDeclRow(.{ .lhs = .some(id_x), .rhs = id_42, .ty = .none(), .method_path = .none(), .flags = .{ .is_const = true, .is_assign = false }, .loc = loc });
    cst.program = .{ .top_decls = cst.exprs.decl_pool.pushMany(gpa, &[_]DeclId{did}), .package_name = .some(s_pkg), .package_loc = .none() };
    var buf = ArrayList(u8).init(gpa);
    defer buf.deinit();
    var pr = DodPrinter.init(buf.writer(), &cst.exprs, &cst.pats);
    try pr.printProgram(&cst.program);
    try std.testing.expectEqualStrings("(program\n  (package \"testpkg\")\n  (decl is_const=true is_assign=false)\n    (lhs\n      (ident \"x\")\n    )\n    (rhs\n      (literal kind=#0 \"42\")\n    )\n  )\n)\n", buf.items);
}

test "printer: function with attrs" {
    const gpa = std.testing.allocator;
    var locs = LocStore{};
    defer locs.deinit(gpa);
    var interner = StringInterner.init(gpa);
    defer interner.deinit();
    var cst = CST.init(gpa, &interner, &locs);
    defer cst.deinit();
    const loc = mkLoc(&cst.exprs, 1, 1);
    const s_i32 = cst.interner.intern("i32");
    const id_i32 = cst.exprs.add(.Ident, .{ .name = s_i32, .loc = loc });
    const pid = cst.exprs.addParamRow(.{ .pat = .none(), .ty = .some(id_i32), .value = .none(), .attrs = .none(), .is_comptime = false, .loc = loc });
    const aid = cst.exprs.addAttrRow(.{ .name = cst.interner.intern("inline"), .value = .none(), .loc = loc });
    const id_fun = cst.exprs.add(.Function, .{ .params = cst.exprs.param_pool.pushMany(gpa, &[_]ParamId{pid}), .result_ty = .some(id_i32), .body = .some(cst.exprs.add(.Block, .{ .items = RangeOf(DeclId).empty(), .loc = loc })), .raw_asm = .none(), .attrs = .some(cst.exprs.attr_pool.pushMany(gpa, &[_]AttributeId{aid})), .flags = .{ .is_proc = false, .is_async = false, .is_variadic = false, .is_extern = false, .is_test = false }, .trailing_param_comma = false, .loc = loc });
    const did = cst.exprs.addDeclRow(.{ .lhs = .some(cst.exprs.add(.Ident, .{ .name = cst.interner.intern("foo"), .loc = loc })), .rhs = id_fun, .ty = .none(), .method_path = .none(), .flags = .{ .is_const = true, .is_assign = false }, .loc = loc });
    cst.program = .{ .top_decls = cst.exprs.decl_pool.pushMany(gpa, &[_]DeclId{did}), .package_name = .some(cst.interner.intern("pkg")), .package_loc = .none() };
    var buf = ArrayList(u8).init(gpa);
    defer buf.deinit();
    var pr = DodPrinter.init(buf.writer(), &cst.exprs, &cst.pats);
    try pr.printProgram(&cst.program);
    try std.testing.expectEqualStrings("(program\n  (package \"pkg\")\n  (decl is_const=true is_assign=false)\n    (lhs\n      (ident \"foo\")\n    )\n    (rhs\n      (function\n        (attributes\n          (attr name=\"inline\")\n          )\n        (param\n          (type\n            (ident \"i32\")\n          )\n        )\n        (result\n          (ident \"i32\")\n        )\n        (body\n          (block\n          )\n        )\n      )\n    )\n  )\n)\n", buf.items);
}

test "printer: patterns" {
    const gpa = std.testing.allocator;
    var locs = LocStore{};
    defer locs.deinit(gpa);
    var interner = StringInterner.init(gpa);
    defer interner.deinit();
    var cst = CST.init(gpa, &interner, &locs);
    defer cst.deinit();
    const loc = mkLoc(&cst.exprs, 1, 1);
    const id_1 = cst.exprs.add(.Literal, .{ .value = cst.interner.intern("1"), .tag_small = .int, .loc = loc });
    const id_2 = cst.exprs.add(.Literal, .{ .value = cst.interner.intern("2"), .tag_small = .int, .loc = loc });
    const p1 = cst.pats.add(.Literal, .{ .expr = id_1, .loc = loc });
    const p2 = cst.pats.add(.Literal, .{ .expr = id_2, .loc = loc });
    const por = cst.pats.add(.Or, .{ .alts = cst.pats.pat_pool.pushMany(gpa, &[_]PatternId{ p1, p2 }), .loc = loc });
    var buf = ArrayList(u8).init(gpa);
    defer buf.deinit();
    var pr = DodPrinter.init(buf.writer(), &cst.exprs, &cst.pats);
    try pr.printPattern(por);
    try std.testing.expectEqualStrings("(or_pattern\n  (literal\n    (literal kind=#0 \"1\")\n  )\n  (literal\n    (literal kind=#0 \"2\")\n  )\n)\n", buf.items);
}
