const std = @import("std");
const ArrayList = std.array_list.Managed;

/// Core utilities for tracking indices, ranges, strings, and locations.
/// Unique identifier assigned to each source file in the compiler.
pub const FileId = u32;
const Loc = @import("lexer.zig").Token.Loc;

////////////////////////////////////////////////////////////////
//            Typed Indices, Optional Indices, Ranges
////////////////////////////////////////////////////////////////

/// Helper that wraps a `u32` but tracks which pool of IDs it belongs to.
pub fn Index(comptime T: type) type {
    return struct {
        index: u32,
        /// The element type indexed by this helper.
        pub const Type = T;

        /// Construct an index from a raw integer.
        pub fn fromRaw(raw: u32) @This() {
            return .{ .index = raw };
        }
        /// Return the underlying raw identifier.
        pub fn toRaw(self: @This()) u32 {
            return self.index;
        }
        /// Compare two indices for equality.
        pub fn eq(self: @This(), other: @This()) bool {
            return self.index == other.index;
        }
    };
}

/// Optional typed index that can represent absence via a sentinel value.
pub fn SentinelIndex(comptime T: type) type {
    return struct {
        raw: u32,
        /// Element type wrapped by this optional index.
        pub const Type = T;
        /// Raw sentinel value representing `none`.
        pub const none_raw = NONE;
        const NONE: u32 = 0xFFFF_FFFF;

        /// Construct the `none` sentinel.
        pub fn none() @This() {
            return .{ .raw = NONE };
        }
        /// Wrap a valid index value.
        pub fn some(i: Index(T)) @This() {
            return .{ .raw = i.index };
        }
        /// Return true when the sentinel represents `none`.
        pub fn isNone(self: @This()) bool {
            return self.raw == NONE;
        }
        /// Unwrap to a concrete index, asserting the sentinel is present.
        pub fn unwrap(self: @This()) Index(T) {
            std.debug.assert(self.raw != NONE);
            return .{ .index = self.raw };
        }
        /// Return the underlying raw identifier.
        pub fn toRaw(self: @This()) u32 {
            return self.raw;
        }

        pub fn eq(self: @This(), other: anytype) bool {
            if (@TypeOf(other) == @This()) return self.raw == other.raw;
            return self.raw == other.index;
        }
    };
}

/// Defines a contiguous range of `IdT` identifiers.
pub fn RangeOf(comptime IdT: type) type {
    return struct {
        start: u32,
        len: u32,
        /// Identifier type that the range covers.
        pub const Type = IdT;
        /// Construct an empty range.
        pub fn empty() @This() {
            return .{ .start = 0, .len = 0 };
        }
    };
}

/// Optional wrapper around `RangeOf` that can signal absence.
pub fn OptRangeOf(comptime IdT: type) type {
    return struct {
        start: u32,
        len: u32,
        /// Construct an `OptRangeOf` that contains no range.
        pub fn none() @This() {
            return .{ .start = 0xFFFF_FFFF, .len = 0 };
        }
        /// Return true when the option carries no range.
        pub fn isNone(self: @This()) bool {
            return self.start == 0xFFFF_FFFF;
        }
        /// Wrap a concrete range value.
        pub fn some(r: RangeOf(IdT)) @This() {
            return .{ .start = r.start, .len = r.len };
        }
        /// Convert back to a `RangeOf`, asserting the option is present.
        pub fn asRange(self: @This()) RangeOf(IdT) {
            std.debug.assert(!self.isNone());
            return .{ .start = self.start, .len = self.len };
        }
    };
}

/// Resizable pool that stores sequential identifiers for `IdT`.
pub fn Pool(comptime IdT: type) type {
    return struct {
        data: std.ArrayListUnmanaged(IdT) = .{},

        /// Append `id` to the pool and return its index.
        pub fn push(self: *@This(), gpa: std.mem.Allocator, id: IdT) u32 {
            const idx: u32 = @intCast(self.data.items.len);
            self.data.append(gpa, id) catch @panic("OOM");
            return idx;
        }
        /// Append multiple consecutive identifiers and return their range.
        pub fn pushMany(self: *@This(), gpa: std.mem.Allocator, items: []const IdT) RangeOf(IdT) {
            const start: u32 = @intCast(self.data.items.len);
            self.data.appendSlice(gpa, items) catch @panic("OOM");
            return .{ .start = start, .len = @intCast(items.len) };
        }
        /// Return a view over the identifiers stored in `r`.
        pub fn slice(self: *const @This(), r: RangeOf(IdT)) []const IdT {
            const start: usize = @intCast(r.start);
            const len: usize = @intCast(r.len);
            const end = start + len;
            if (end > self.data.items.len) {
                std.debug.panic("Pool.slice range out of bounds: {} + {} > {}", .{ start, len, self.data.items.len });
            }
            return self.data.items[start..end];
        }
        /// Release the underlying array list storage.
        pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
            self.data.deinit(gpa);
        }
    };
}

////////////////////////////////////////////////////////////////
//                 String Interner & Source Locations
////////////////////////////////////////////////////////////////

/// Tag used to differentiate string identifiers.
pub const StrTag = struct {};
/// Identifier type for interned strings.
pub const StrId = Index(StrTag);

/// Thread-safe interner that maps strings to `StrId`s and holds their bytes.
pub const StringInterner = struct {
    /// Allocator used for storing copies of strings.
    gpa: std.mem.Allocator,
    /// Map from string bytes to their `StrId`.
    map: std.StringHashMapUnmanaged(StrId) = .{},
    /// Owned string bytes indexed by `StrId`.
    strings: std.ArrayListUnmanaged([]const u8) = .{},
    /// Mutex guarding concurrent access.
    mutex: std.Thread.Mutex = .{},

    /// Initialize a `StringInterner` that owns allocations from `gpa`.
    pub fn init(gpa: std.mem.Allocator) StringInterner {
        return .{ .gpa = gpa };
    }

    /// Release every interned string and underlying map entries.
    pub fn deinit(self: *StringInterner) void {
        var key_iter = self.map.keyIterator();
        while (key_iter.next()) |key| {
            self.gpa.free(key.*);
        }

        self.map.deinit(self.gpa);
        self.strings.deinit(self.gpa);
    }

    /// Intern `s`, returning an existing `StrId` if available or allocating a new entry.
    pub fn intern(self: *StringInterner, s: []const u8) StrId {
        self.mutex.lock();
        defer self.mutex.unlock();
        if (self.map.get(s)) |existing| return existing;

        const key_copy = self.gpa.dupe(u8, s) catch @panic("OOM");

        const gop = self.map.getOrPut(self.gpa, key_copy) catch @panic("OOM");

        if (gop.found_existing) {
            self.gpa.free(key_copy);
            return gop.value_ptr.*;
        }

        const id = StrId.fromRaw(@intCast(self.strings.items.len));
        self.strings.append(self.gpa, key_copy) catch @panic("OOM");

        gop.value_ptr.* = id;
        return id;
    }

    /// Resolve `id` to its interned bytes.
    pub fn get(self: *const StringInterner, id: StrId) []const u8 {
        const self_mut: *StringInterner = @constCast(self);
        self_mut.mutex.lock();
        defer self_mut.mutex.unlock();
        std.debug.assert(id.toRaw() < self_mut.strings.items.len);
        return self_mut.strings.items[id.toRaw()];
    }
};

/// Tag type used by location identifiers.
pub const LocTag = struct {};
/// Identifier referring to a concrete `Loc`.
pub const LocId = Index(LocTag);

/// Storage for all source locations emitted by the lexer.
pub const LocStore = struct {
    /// Allocator-managed array holding location entries.
    data: std.ArrayListUnmanaged(Loc) = .{},
    /// Mutex guarding concurrent location inserts.
    mutex: std.Thread.Mutex = .{},

    /// Record `loc` and return a new `LocId`.
    pub fn add(self: *LocStore, gpa: std.mem.Allocator, loc: Loc) LocId {
        self.mutex.lock();
        defer self.mutex.unlock();
        const id = LocId.fromRaw(@intCast(self.data.items.len));
        self.data.append(gpa, loc) catch @panic("OOM");
        return id;
    }
    /// Fetch the stored location for `id`.
    pub fn get(self: *const LocStore, id: LocId) Loc {
        return self.data.items[id.toRaw()];
    }
    /// Release the stored locations.
    pub fn deinit(self: *LocStore, gpa: std.mem.Allocator) void {
        self.data.deinit(gpa);
    }
};

////////////////////////////////////////////////////////////////
//         Column Store Wrapper over std.MultiArrayList
////////////////////////////////////////////////////////////////

pub fn Table(comptime T: type) type {
    const is_empty_struct = std.meta.fields(T).len == 0;
    if (is_empty_struct) {
        return struct {
            len: u32 = 0,

            /// Add a new entry for empty rows (no-op placeholder).
            pub fn add(self: *@This(), gpa: std.mem.Allocator, row: T) Index(T) {
                _ = gpa;
                _ = row;
                const idx = self.len;
                self.len += 1;
                return .{ .index = idx };
            }
            /// Retrieve an entry from an empty row table (panic otherwise).
            pub fn get(self: *const @This(), idx: Index(T)) T {
                _ = self;
                _ = idx;
                return .{};
            }
            /// Deinitialize the empty row table (does nothing).
            pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
                _ = self;
                _ = gpa;
            }
            /// Determine the column type associated with `field`.
            fn ReturnType(comptime field: []const u8) type {
                _ = field;
                return void;
            }
            /// `col` access is unsupported for empty row tables and will panic.
            pub fn col(self: *@This(), comptime field_name: []const u8) []ReturnType(field_name) {
                _ = self;
                @compileError("col() not supported for empty row tables");
            }
        };
    } else {
        return struct {
            list: std.MultiArrayList(T) = .{},
            mutex: std.Thread.Mutex = .{},

            /// Add `row` to the table and return its index.
            pub fn add(self: *@This(), gpa: std.mem.Allocator, row: T) Index(T) {
                self.mutex.lock();
                defer self.mutex.unlock();
                const idx: u32 = @intCast(self.list.len);
                _ = self.list.addOne(gpa) catch @panic("OOM");
                self.list.set(idx, row);
                return .{ .index = idx };
            }
            /// Retrieve the stored row identified by `idx`.
            pub fn get(self: *@This(), idx: Index(T)) T {
                self.mutex.lock();
                defer self.mutex.unlock();
                return self.list.get(idx.toRaw());
            }

            /// Determine the return type used by `col`.
            fn ReturnType(comptime field: []const u8) type {
                inline for (std.meta.fields(T)) |f| {
                    if (std.mem.eql(u8, f.name, field))
                        return f.type;
                }
            }
            /// Get a slice of a specific column field across every row.
            pub fn col(self: *@This(), comptime field_name: []const u8) []ReturnType(field_name) {
                const F = @TypeOf(self.list).Field;
                const idx = std.meta.fieldIndex(T, field_name) orelse
                    @compileError("No such field: " ++ field_name);
                return self.list.items(@as(F, @enumFromInt(idx)));
            }
            /// Release all rows stored within this table.
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
/// Operators that take two operands within expressions.
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
/// Kinds of embedded MLIR constructs stored in the AST.
pub const MlirKind = enum(u8) { Module, Type, Attribute, Operation };
/// Distinguishes literal text from interpolated splices inside MLIR literals.
pub const MlirPieceKind = enum(u8) { literal, splice };
/// Classifies cast flavors recognized by the AST for lowering.
pub const CastKind = enum(u8) { normal, bitcast, saturate, wrap, checked };
/// Literal categories parsed from source code.
pub const LiteralKind = enum { int, float, string, raw_string, char, imaginary, true, false };

////////////////////////////////////////////////////////////////
//                          IDs
////////////////////////////////////////////////////////////////

pub const ExprTag = struct {};
pub const PatTag = struct {};

/// Identifier for expression rows.
pub const ExprId = Index(ExprTag);
/// Identifier for declaration rows.
pub const DeclId = Index(Rows.Decl);
/// Identifier for attribute rows.
pub const AttributeId = Index(Rows.Attribute);
/// Identifier for parameter rows.
pub const ParamId = Index(Rows.Param);
/// Identifier for struct field rows.
pub const StructFieldId = Index(Rows.StructField);
/// Identifier for enum field rows.
pub const EnumFieldId = Index(Rows.EnumField);
/// Identifier for variant field rows.
pub const VariantFieldId = Index(Rows.VariantField);
/// Identifier for key/value literal rows.
pub const KeyValueId = Index(Rows.KeyValue);
/// Identifier for match arms.
pub const MatchArmId = Index(Rows.MatchArm);
/// Identifier for struct literal field values.
pub const StructFieldValueId = Index(Rows.StructFieldValue);
/// Identifier for method path segments.
pub const MethodPathSegId = Index(Rows.MethodPathSeg);
/// Identifier for MLIR snippet pieces.
pub const MlirPieceId = Index(Rows.MlirPiece);

/// Identifier for pattern path segments.
pub const PathSegId = Index(PatRows.PathSeg);
/// Identifier for general pattern rows.
pub const PatternId = Index(PatTag);
/// Identifier for struct pattern field entries.
pub const PatFieldId = Index(PatRows.StructField);

// Optional (sentinel) versions where optionals are expected
/// Optional expression identifier.
pub const OptExprId = SentinelIndex(ExprTag);
/// Optional string identifier.
pub const OptStrId = SentinelIndex(StrTag);
/// Optional location identifier.
pub const OptLocId = SentinelIndex(LocTag);
/// Optional declaration identifier.
pub const OptDeclId = SentinelIndex(Rows.Decl);
/// Optional parameter identifier.
pub const OptParamId = SentinelIndex(Rows.Param);

/// Optional range over expression IDs.
pub const OptRangeExpr = OptRangeOf(ExprId);
/// Optional range over declaration IDs.
pub const OptRangeDecl = OptRangeOf(DeclId);
/// Optional range over attribute IDs.
pub const OptRangeAttr = OptRangeOf(AttributeId);
/// Optional range over struct field IDs.
pub const OptRangeField = OptRangeOf(StructFieldId);
/// Optional range over pattern IDs.
pub const OptRangePat = OptRangeOf(PatternId);
/// Optional range over method path segment IDs.
pub const OptRangeMethodPathSeg = OptRangeOf(MethodPathSegId);

/// Tag used to capture AST comments.
pub const CommentTag = struct {};
/// Identifier for each comment entry.
pub const CommentId = Index(CommentTag);
/// Classification of comment text stored in the AST.
pub const CommentKind = enum { line, block, doc, container_doc };

/// Container that holds every parsed comment encountered by the parser.
pub const CommentStore = struct {
    /// Backing array storing comment metadata.
    list: std.ArrayListUnmanaged(Comment) = .{},

    /// Append `comment` and return the assigned `CommentId`.
    pub fn add(self: *@This(), gpa: std.mem.Allocator, comment: Comment) CommentId {
        const idx: u32 = @intCast(self.list.items.len);
        self.list.append(gpa, comment) catch @panic("OOM");
        return .{ .index = idx };
    }

    /// View all stored `Comment` entries.
    pub fn slice(self: *const @This()) []const Comment {
        return self.list.items;
    }

    /// Release the comment list memory.
    pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
        self.list.deinit(gpa);
    }
};

/// Representation of a comment attached to source code.
pub const Comment = struct {
    /// Kind of the comment (line, block, doc, etc.)
    kind: CommentKind,
    /// Source location for the comment token.
    loc: LocId,
};

////////////////////////////////////////////////////////////////
//                    Expression Kinds & Rows
////////////////////////////////////////////////////////////////

/// Enumerator for every expression kind recorded in the AST.
pub const ExprKind = enum(u16) {
    // basic
    Literal,
    Ident,
    Prefix,
    Infix,
    Deref,
    ArrayLit,
    Tuple,
    Parenthesized,
    MapLit,
    Call,
    IndexAccess,
    FieldAccess,
    StructLit,
    Return,
    Block,
    // control / flow
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
    // meta / mlir
    Comptime,
    Code,
    Insert,
    Mlir,
    // function
    Function,

    // ==== Types (flattened BuiltinType) ====
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

/// Columnar store describing every expression row by kind.
pub const Rows = struct {
    // ---------- literals / identifiers ----------
    /// Row describing literal expressions.
    pub const Literal = struct {
        /// Interned literal text stored in the interner.
        value: StrId,
        /// Literal kind discriminator.
        tag_small: LiteralKind,
        /// Location in source where the literal was parsed.
        loc: LocId,
    };
    /// Row representing identifier expressions.
    pub const Ident = struct {
        /// Interned identifier name.
        name: StrId,
        /// Location of the identifier.
        loc: LocId,
    };

    // ---------- operators ----------
    /// Row storing unary prefix operators.
    pub const Prefix = struct {
        /// Operand expression the operator acts on.
        right: ExprId,
        /// Operator kind being applied.
        op: PrefixOp,
        /// Location covering the operator token.
        loc: LocId,
    };
    /// Row storing binary/infix operations.
    pub const Infix = struct {
        /// Left operand.
        left: ExprId,
        /// Right operand.
        right: ExprId,
        /// Operator kind.
        op: InfixOp,
        /// Source location for the entire expression.
        loc: LocId,
    };
    /// Row representing dereference expressions (`.*` or `.*`).
    pub const Deref = struct {
        /// Expression being dereferenced.
        expr: ExprId,
        /// Location of the dereference token.
        loc: LocId,
    };

    // ---------- collections / literals ----------
    /// Row for array literal expressions.
    pub const ArrayLit = struct {
        /// Element expressions forming the array.
        elems: RangeOf(ExprId),
        /// Whether a trailing comma was present.
        trailing_comma: bool,
        /// Location of the array literal.
        loc: LocId,
    };
    /// Row for tuple literal expressions.
    pub const Tuple = struct {
        /// Element expressions within the tuple literal.
        elems: RangeOf(ExprId),
        /// Indicates the literal represents a type tuple.
        is_type: bool,
        /// Location covering the tuple literal.
        loc: LocId,
    };
    /// Row for parenthesized expressions.
    pub const Parenthesized = struct {
        /// Underlying expression wrapped in parentheses.
        inner: ExprId,
        /// Location of the parentheses.
        loc: LocId,
    };
    /// Row for map literal constructors.
    pub const MapLit = struct {
        /// Key/value entries stored in the literal.
        entries: RangeOf(KeyValueId),
        /// Location of the literal braces.
        loc: LocId,
    };
    /// Row representing a single key/value pair in a literal.
    pub const KeyValue = struct {
        /// Expression used as the key.
        key: ExprId,
        /// Expression used as the value.
        value: ExprId,
        /// Location of the key/value pair.
        loc: LocId,
    };

    // ---------- calls / selectors ----------
    /// Row for call expressions.
    pub const Call = struct {
        /// Expression being invoked.
        callee: ExprId,
        /// Arguments supplied to the call.
        args: RangeOf(ExprId),
        /// Whether a trailing comma ended the argument list.
        trailing_arg_comma: bool,
        /// Location of the call expression.
        loc: LocId,
    };
    /// Row for index access expressions (`collection[index]`).
    pub const IndexAccess = struct {
        /// Collection being indexed.
        collection: ExprId,
        /// Index expression.
        index: ExprId,
        /// Location of the access.
        loc: LocId,
    };
    /// Row for field or tuple slot access.
    pub const FieldAccess = struct {
        /// Expression providing the parent value.
        parent: ExprId,
        /// Field name or tuple identifier.
        field: StrId,
        /// True when accessing tuple positions.
        is_tuple: bool,
        /// Location of the field access.
        loc: LocId,
    };

    // ---------- struct literal ----------
    /// Row representing a struct literal field initializer.
    pub const StructFieldValue = struct {
        /// Optional named field being initialized.
        name: OptStrId,
        /// Expression providing the field value.
        value: ExprId,
        /// Location of the initializer.
        loc: LocId,
    };
    /// Row for struct literal constructions.
    pub const StructLit = struct {
        /// Field value entries.
        fields: RangeOf(StructFieldValueId),
        /// Optional structural type annotation.
        ty: OptExprId,
        /// Whether a trailing comma was present.
        trailing_comma: bool,
        /// Location of the struct literal braces.
        loc: LocId,
    };

    // ---------- function / block ----------
    /// Flags describing qualifiers on function literals.
    pub const FnFlags = packed struct(u8) {
        /// True when literal uses `proc`.
        is_proc: bool,
        /// True when literal is asynchronous.
        is_async: bool,
        /// True when literal accepts variadic arguments.
        is_variadic: bool,
        /// True when literal is marked `extern`.
        is_extern: bool,
        /// True when literal originated from a `test` declaration.
        is_test: bool,
        _pad: u3 = 0,
    };
    /// Row representing a function literal or declaration block.
    pub const Function = struct {
        params: RangeOf(ParamId),
        result_ty: OptExprId,
        body: OptExprId, // Block or raw asm (null)
        raw_asm: OptStrId,
        attrs: OptRangeAttr,
        flags: FnFlags,
        trailing_param_comma: bool,
        loc: LocId,
    };
    /// Row storing block statements along with their location.
    pub const Block = struct { items: RangeOf(DeclId), loc: LocId };

    // ---------- meta / mlir ----------
    /// Row capturing `comptime` expression payloads.
    pub const Comptime = struct { payload: ExprId, is_block: bool, loc: LocId };
    /// Row for raw `code` blocks emitted in MLIR fragments.
    pub const Code = struct { block: ExprId, loc: LocId };
    /// Row for `insert` MLIR expressions.
    pub const Insert = struct { expr: ExprId, loc: LocId };
    /// Row representing a chunk within an MLIR splice.
    pub const MlirPiece = struct { kind: MlirPieceKind, text: StrId };
    /// Row for top-level MLIR expressions/splices.
    pub const Mlir = struct {
        kind: MlirKind,
        text: StrId,
        pieces: RangeOf(MlirPieceId),
        args: OptRangeOf(ExprId),
        loc: LocId,
    };

    // ---------- flow ----------
    /// Row emitting a return statement and its optional value.
    pub const Return = struct { value: OptExprId, loc: LocId };
    /// Row for `if` expressions including guards and alternatives.
    pub const If = struct { cond: ExprId, then_block: ExprId, else_block: OptExprId, loc: LocId };
    /// Row describing `while` loops and optional pattern matches.
    pub const While = struct {
        cond: OptExprId,
        pattern: SentinelIndex(PatTag),
        body: ExprId, // Block
        is_pattern: bool,
        label: OptStrId,
        loc: LocId,
    };
    /// Row capturing `for` loops with their iterable and body.
    pub const For = struct {
        pattern: Index(PatTag),
        iterable: ExprId,
        body: ExprId, // Block
        label: OptStrId,
        loc: LocId,
    };
    /// Row for match expressions mapping to pattern arms.
    pub const Match = struct { expr: ExprId, arms: RangeOf(MatchArmId), loc: LocId };
    /// Row describing each arm inside a match expression.
    pub const MatchArm = struct { pattern: Index(PatTag), guard: OptExprId, body: ExprId, loc: LocId };
    /// Row representing `break` statements optionally carrying a value.
    pub const Break = struct { label: OptStrId, value: OptExprId, loc: LocId };
    /// Row for `continue` statements targeting optional labels.
    pub const Continue = struct { label: OptStrId, loc: LocId };
    /// Row for unreachable markers.
    pub const Unreachable = struct { loc: LocId };
    /// Row representing the `null` literal.
    pub const Null = struct { loc: LocId };
    /// Row representing the `undefined` literal.
    pub const Undefined = struct { loc: LocId };
    /// Row storing deferred expressions.
    pub const Defer = struct { expr: ExprId, loc: LocId };
    /// Row for error-only `errdefer` statements.
    pub const ErrDefer = struct { expr: ExprId, loc: LocId };
    /// Row describing `err.unwrap` expressions.
    pub const ErrUnwrap = struct { expr: ExprId, loc: LocId };
    /// Row describing optional unwrap expressions.
    pub const OptionalUnwrap = struct { expr: ExprId, loc: LocId };
    /// Row for `await` expressions.
    pub const Await = struct { expr: ExprId, loc: LocId };
    /// Row representing closure literals.
    pub const Closure = struct { params: RangeOf(ParamId), result_ty: OptExprId, body: ExprId, loc: LocId };
    /// Row wrapping asynchronous expressions.
    pub const Async = struct { body: ExprId, loc: LocId };
    /// Row describing explicit cast expressions.
    pub const Cast = struct { expr: ExprId, ty: ExprId, kind: CastKind, loc: LocId };
    /// Row for `catch` blocks with optional binding info.
    pub const Catch = struct { expr: ExprId, binding_name: OptStrId, binding_loc: OptLocId, handler: ExprId, loc: LocId };
    /// Row capturing `import` statements and their path.
    pub const Import = struct { path: StrId, loc: LocId };
    /// Row for `typeof` expressions.
    pub const TypeOf = struct { expr: ExprId, loc: LocId };

    // ---------- params & attributes ----------
    /// Row describing function parameters generated from patterns.
    pub const Param = struct {
        pat: OptExprId,
        ty: OptExprId,
        value: OptExprId,
        attrs: OptRangeAttr,
        is_comptime: bool,
        loc: LocId,
    };
    /// Row storing attributes attached to declarations or expressions.
    pub const Attribute = struct { name: StrId, value: OptExprId, loc: LocId };

    // ---------- decls ----------
    /// Row for segments inside a method access path.
    pub const MethodPathSeg = struct { name: StrId, loc: LocId };
    /// Packed flags representing declaration modifiers.
    pub const DeclFlags = packed struct(u8) { is_const: bool, is_assign: bool, _pad: u6 = 0 };
    /// Row representing a declaration with lhs/rhs metadata.
    pub const Decl = struct {
        lhs: OptExprId,
        rhs: ExprId,
        ty: OptExprId,
        method_path: OptRangeMethodPathSeg,
        flags: DeclFlags,
        loc: LocId,
    };

    // ---------- builtin types (flattened) ----------
    /// Row describing fixed-length array type annotations.
    pub const ArrayType = struct { elem: ExprId, size: ExprId, loc: LocId };
    /// Row for dynamic array type annotations.
    pub const DynArrayType = struct { elem: ExprId, loc: LocId };
    /// Row for map type annotations.
    pub const MapType = struct { key: ExprId, value: ExprId, loc: LocId };
    /// Row for slice type annotations.
    pub const SliceType = struct { elem: ExprId, is_const: bool, loc: LocId };
    /// Row representing optional type wrappers.
    pub const OptionalType = struct { elem: ExprId, loc: LocId };
    /// Row for error set type definitions.
    pub const ErrorSetType = struct { err: ExprId, value: ExprId, loc: LocId };

    /// Row describing struct field declarations.
    pub const StructField = struct { name: StrId, ty: ExprId, value: OptExprId, attrs: OptRangeAttr, loc: LocId };
    /// Row for struct type definitions.
    pub const StructType = struct { fields: RangeOf(StructFieldId), is_extern: bool, attrs: OptRangeAttr, trailing_field_comma: bool, loc: LocId };

    /// Row describing enum members.
    pub const EnumField = struct { name: StrId, value: OptExprId, attrs: OptRangeAttr, loc: LocId };
    /// Row for enum type definitions.
    pub const EnumType = struct { fields: RangeOf(EnumFieldId), discriminant: OptExprId, is_extern: bool, attrs: OptRangeAttr, trailing_field_comma: bool, loc: LocId };

    /// Kinds of payload shapes for variant fields.
    pub const VariantFieldTyTag = enum(u8) { none, Tuple, Struct };
    /// Row representing a variant payload field.
    pub const VariantField = struct {
        name: StrId,
        ty_tag: VariantFieldTyTag, // none/tuple/struct
        tuple_elems: RangeOf(ExprId), // valid if Tuple
        struct_fields: RangeOf(StructFieldId), // valid if Struct
        value: OptExprId,
        attrs: OptRangeAttr,
        tuple_trailing_comma: bool,
        struct_trailing_comma: bool,
        loc: LocId,
    };
    /// Row for variants/unions that share payload layouts.
    pub const VariantLikeType = struct { fields: RangeOf(VariantFieldId), trailing_field_comma: bool, loc: LocId };

    /// Row for union type declarations.
    pub const UnionType = struct { fields: RangeOf(StructFieldId), is_extern: bool, attrs: OptRangeAttr, trailing_field_comma: bool, loc: LocId };
    /// Row describing pointer type annotations.
    pub const PointerType = struct { elem: ExprId, is_const: bool, loc: LocId };
    /// Row for SIMD vector type specifications.
    pub const SimdType = struct { elem: ExprId, lanes: ExprId, loc: LocId };
    /// Row describing complex number type annotations.
    pub const ComplexType = struct { elem: ExprId, loc: LocId };
    /// Row for tensor type descriptors.
    pub const TensorType = struct { elem: ExprId, shape: RangeOf(ExprId), loc: LocId };
    /// `Error` types reuse the variant-like layout.
    pub const ErrorType = VariantLikeType;
    /// Row for `type` meta-annotations.
    pub const TypeType = struct { loc: LocId };
    /// Row representing the `any` placeholder type.
    pub const AnyType = struct { loc: LocId };
    /// Row for the `noreturn` builtin type.
    pub const NoreturnType = struct { loc: LocId };
};

////////////////////////////////////////////////////////////////
//                       Pattern Store
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

/// Columnar store describing every pattern row.
pub const PatRows = struct {
    /// Row for wildcard patterns (`_`).
    pub const Wildcard = struct { loc: LocId };
    /// Row for literal patterns (numbers, strings).
    pub const Literal = struct { expr: ExprId, loc: LocId };

    /// Row for segments within pattern paths.
    pub const PathSeg = struct { name: StrId, loc: LocId };
    /// Row for path patterns (e.g., qualified names).
    pub const Path = struct { segments: RangeOf(PathSegId), loc: LocId };

    /// Row describing binding pattern forms.
    pub const Binding = struct { name: StrId, by_ref: bool, is_mut: bool, loc: LocId };

    /// Row for parenthesized patterns.
    pub const Parenthesized = struct {
        pattern: PatternId,
        loc: LocId,
    };

    /// Row describing tuple patterns.
    pub const Tuple = struct { elems: RangeOf(PatternId), loc: LocId };

    /// Row for slice/array patterns with optional rest.
    pub const Slice = struct {
        elems: RangeOf(PatternId),
        has_rest: bool,
        rest_index: u32,
        rest_binding: SentinelIndex(PatTag),
        loc: LocId,
    };

    /// Row linking struct field names to nested patterns.
    pub const StructField = struct { name: StrId, pattern: Index(PatTag), loc: LocId };

    /// Row for struct patterns listing field binds.
    pub const Struct = struct {
        path: RangeOf(PathSegId),
        fields: RangeOf(PatFieldId),
        has_rest: bool,
        loc: LocId,
    };

    /// Row for tuple-like variant patterns.
    pub const VariantTuple = struct {
        path: RangeOf(PathSegId),
        elems: RangeOf(PatternId),
        loc: LocId,
    };

    /// Row for struct-like variant patterns.
    pub const VariantStruct = struct {
        path: RangeOf(PathSegId),
        fields: RangeOf(PatFieldId),
        has_rest: bool,
        loc: LocId,
    };

    /// Row for range patterns (`start..end`).
    pub const Range = struct { start: OptExprId, end: OptExprId, inclusive_right: bool, loc: LocId };
    /// Row representing `|` alternatives inside patterns.
    pub const Or = struct { alts: RangeOf(PatternId), loc: LocId };
    /// Row for `@` binder patterns.
    pub const At = struct { binder: StrId, pattern: Index(PatTag), loc: LocId };
};

// Resolve the concrete row type for an ExprKind or PatternKind at comptime.
/// Resolve the concrete row type for an `ExprKind`.
pub inline fn RowT(comptime K: ExprKind) type {
    return @field(Rows, @tagName(K));
}
/// Resolve the concrete row type for a `PatternKind`.
pub inline fn PatRowT(comptime K: PatternKind) type {
    return @field(PatRows, @tagName(K));
}

////////////////////////////////////////////////////////////////
//                    Program / Package (top-level)
////////////////////////////////////////////////////////////////

pub const ProgramDO = struct {
    top_decls: RangeOf(DeclId),
    package_name: OptStrId,
    package_loc: OptLocId,
};

////////////////////////////////////////////////////////////////
//                    Store Index
////////////////////////////////////////////////////////////////

pub fn StoreIndex(comptime KindT: type) type {
    return struct {
        kinds: std.ArrayListUnmanaged(KindT) = .{},
        rows: std.ArrayListUnmanaged(u32) = .{},

        /// Create a new ID of `IdT` for the provided `KindT`/row pair.
        pub fn newId(self: *@This(), gpa: std.mem.Allocator, k: KindT, row: u32, comptime IdT: type) IdT {
            const i_raw: u32 = @intCast(self.kinds.items.len);
            self.kinds.append(gpa, k) catch @panic("OOM");
            self.rows.append(gpa, row) catch @panic("OOM");
            return @field(IdT, "fromRaw")(i_raw);
        }

        /// Release the stored kind/row arrays.
        pub fn deinit(self: *@This(), gpa: std.mem.Allocator) void {
            self.kinds.deinit(gpa);
            self.rows.deinit(gpa);
        }
    };
}

////////////////////////////////////////////////////////////////
//                        Expr Store
////////////////////////////////////////////////////////////////

pub const ExprStore = struct {
    gpa: std.mem.Allocator,
    index: StoreIndex(ExprKind) = .{},

    // Tables (one per kind)
    Literal: Table(Rows.Literal) = .{},
    Ident: Table(Rows.Ident) = .{},
    Prefix: Table(Rows.Prefix) = .{},
    Infix: Table(Rows.Infix) = .{},
    Deref: Table(Rows.Deref) = .{},

    ArrayLit: Table(Rows.ArrayLit) = .{},
    Tuple: Table(Rows.Tuple) = .{},
    Parenthesized: Table(Rows.Parenthesized) = .{},
    MapLit: Table(Rows.MapLit) = .{},
    KeyValue: Table(Rows.KeyValue) = .{},

    Call: Table(Rows.Call) = .{},
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

    // Pools
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

    // Infra
    strs: *StringInterner,
    locs: *LocStore,

    // ----- lifecycle -----
    /// Create an `ExprStore` backed by `strs` and `locs`.
    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner, locs: *LocStore) ExprStore {
        return .{ .gpa = gpa, .strs = strs, .locs = locs };
    }
    /// Tear down every table and pool within the expression store.
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;

        // index + all ExprKind tables
        self.index.deinit(gpa);
        inline for (@typeInfo(ExprKind).@"enum".fields) |f| {
            @field(self, f.name).deinit(gpa);
        }

        self.MlirPiece.deinit(gpa);
        self.Decl.deinit(gpa);
        self.MethodPathSeg.deinit(gpa);
        self.Param.deinit(gpa);
        self.Attribute.deinit(gpa);
        self.KeyValue.deinit(gpa);
        self.StructFieldValue.deinit(gpa);
        self.MatchArm.deinit(gpa);
        self.StructField.deinit(gpa);
        self.EnumField.deinit(gpa);
        self.VariantField.deinit(gpa);

        // pools
        self.expr_pool.deinit(gpa);
        self.decl_pool.deinit(gpa);
        self.param_pool.deinit(gpa);
        self.attr_pool.deinit(gpa);
        self.sfv_pool.deinit(gpa);
        self.kv_pool.deinit(gpa);
        self.arm_pool.deinit(gpa);
        self.sfield_pool.deinit(gpa);
        self.efield_pool.deinit(gpa);
        self.vfield_pool.deinit(gpa);
        self.method_path_pool.deinit(gpa);
        self.mlir_piece_pool.deinit(gpa);
    }

    /// Add an expression row of kind `K`, returning its `ExprId`.
    pub fn add(self: *@This(), comptime K: ExprKind, row: RowT(K)) ExprId {
        const TblT = Table(RowT(K));
        const p: *TblT = &@field(self, @tagName(K));
        const r = p.add(self.gpa, row);
        return self.index.newId(self.gpa, K, r.toRaw(), ExprId);
    }

    /// Lookup the row stored under `id` when its kind is `K`.
    pub fn get(self: *@This(), comptime K: ExprKind, id: ExprId) RowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row = self.index.rows.items[id.toRaw()];
        const TblT = Table(RowT(K));
        const p: *TblT = &@field(self, @tagName(K));
        return p.get(.{ .index = row });
    }

    pub fn kind(self: *ExprStore, id: ExprId) ExprKind {
        return self.index.kinds.items[id.toRaw()];
    }

    /// Access the underlying MultiArrayList for kind `K`.
    pub fn table(self: *@This(), comptime K: ExprKind) *std.MultiArrayList(RowT(K)) {
        const TblT = Table(RowT(K));
        const p: *TblT = &@field(self, @tagName(K));
        return &p.list;
    }

    // ----- non-expr tables (constructors return typed ids) -----
    /// Append a literal key/value entry.
    pub fn addKeyValue(self: *@This(), row: Rows.KeyValue) KeyValueId {
        return self.KeyValue.add(self.gpa, row);
    }
    /// Append a struct field value row.
    pub fn addStructFieldValue(self: *@This(), row: Rows.StructFieldValue) StructFieldValueId {
        return self.StructFieldValue.add(self.gpa, row);
    }
    /// Append a declaration row.
    pub fn addDeclRow(self: *@This(), row: Rows.Decl) DeclId {
        return self.Decl.add(self.gpa, row);
    }
    /// Append a method path segment.
    pub fn addMethodPathSegRow(self: *@This(), row: Rows.MethodPathSeg) MethodPathSegId {
        return self.MethodPathSeg.add(self.gpa, row);
    }
    /// Append a parameter declaration row.
    pub fn addParamRow(self: *@This(), row: Rows.Param) ParamId {
        return self.Param.add(self.gpa, row);
    }
    /// Append an attribute row.
    pub fn addAttrRow(self: *@This(), row: Rows.Attribute) AttributeId {
        return self.Attribute.add(self.gpa, row);
    }
    /// Append an MLIR piece row for `MlirBlock`.
    pub fn addMlirPieceRow(self: *@This(), row: Rows.MlirPiece) MlirPieceId {
        return self.MlirPiece.add(self.gpa, row);
    }
    /// Append a struct field definition row.
    pub fn addStructFieldRow(self: *@This(), row: Rows.StructField) StructFieldId {
        return self.StructField.add(self.gpa, row);
    }
    /// Append an enum field row.
    pub fn addEnumFieldRow(self: *@This(), row: Rows.EnumField) EnumFieldId {
        return self.EnumField.add(self.gpa, row);
    }
    /// Append a variant field row.
    pub fn addVariantFieldRow(self: *@This(), row: Rows.VariantField) VariantFieldId {
        return self.VariantField.add(self.gpa, row);
    }
    /// Append a match arm row.
    pub fn addMatchArmRow(self: *@This(), row: Rows.MatchArm) MatchArmId {
        return self.MatchArm.add(self.gpa, row);
    }
};

////////////////////////////////////////////////////////////////
//                       Pattern Store
////////////////////////////////////////////////////////////////

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

    // Pools
    pat_pool: Pool(PatternId) = .{},
    seg_pool: Pool(PathSegId) = .{},
    field_pool: Pool(PatFieldId) = .{},

    strs: *StringInterner,

    /// Initialize a pattern store backed by `strs`.
    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner) PatternStore {
        return .{ .gpa = gpa, .strs = strs };
    }
    /// Release the pattern tables and pools.
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;

        self.index.deinit(gpa);
        inline for (@typeInfo(PatternKind).@"enum".fields) |f| {
            @field(self, f.name).deinit(gpa);
        }

        self.PathSeg.deinit(gpa);
        self.StructField.deinit(gpa);

        self.pat_pool.deinit(gpa);
        self.seg_pool.deinit(gpa);
        self.field_pool.deinit(gpa);
    }

    /// Add a pattern row of kind `K` and return its `PatternId`.
    pub fn add(self: *@This(), comptime K: PatternKind, row: PatRowT(K)) PatternId {
        const TblT = Table(PatRowT(K));
        const p: *TblT = &@field(self, @tagName(K));
        const r = p.add(self.gpa, row);
        return self.index.newId(self.gpa, K, r.toRaw(), PatternId);
    }

    /// Lookup the row for pattern `id` of kind `K`.
    pub fn get(self: *@This(), comptime K: PatternKind, id: PatternId) PatRowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row = self.index.rows.items[id.toRaw()];
        const TblT = Table(PatRowT(K));
        const p: *TblT = &@field(self, @tagName(K));
        return p.get(.{ .index = row });
    }

    pub fn kind(self: *PatternStore, id: PatternId) PatternKind {
        return self.index.kinds.items[id.toRaw()];
    }

    // non-kind tables adders
    /// Store a pattern path segment.
    pub fn addPathSeg(self: *@This(), row: PatRows.PathSeg) PathSegId {
        return self.PathSeg.add(self.gpa, row);
    }
    /// Store a pattern struct field entry.
    pub fn addPatField(self: *@This(), row: PatRows.StructField) PatFieldId {
        return self.StructField.add(self.gpa, row);
    }
};

////////////////////////////////////////////////////////////////
//                 Top-level Aggregation (optional)
////////////////////////////////////////////////////////////////

pub const CST = struct {
    gpa: std.mem.Allocator,
    exprs: ExprStore,
    pats: PatternStore,
    program: ProgramDO,
    interner: *StringInterner,
    comments: CommentStore = .{},

    /// Construct the CST with fresh expr/pattern stores.
    pub fn init(gpa: std.mem.Allocator, interner: *StringInterner, locs: *LocStore) CST {
        return .{
            .gpa = gpa,
            .exprs = .init(gpa, interner, locs),
            .pats = .init(gpa, interner),
            .program = .{ .top_decls = RangeOf(DeclId).empty(), .package_name = .none(), .package_loc = .none() },
            .interner = interner,
        };
    }
    /// Release all embedded stores.
    pub fn deinit(self: *@This()) void {
        self.exprs.deinit();
        self.pats.deinit();
        self.comments.deinit(self.gpa);
    }

    fn KindType(T: type) type {
        if (T == ExprId) return ExprKind;
        if (T == PatternId) return PatternKind;
        @compileError("Unsupported id type: " ++ @typeName(T));
    }

    pub fn kind(self: *CST, id: anytype) KindType(@TypeOf(id)) {
        if (@TypeOf(id) == ExprId)
            return self.exprs.kind(id);
        if (@TypeOf(id) == PatternId)
            return self.pats.kind(id);
        @compileError("Unsupported id type: " ++ @typeName(@TypeOf(id)));
    }
};

////////////////////////////////////////////////////////////////
//                    Compile-time sanity checks
////////////////////////////////////////////////////////////////

comptime {
    for (@typeInfo(ExprKind).@"enum".fields) |f| {
        _ = @field(Rows, f.name);
    }
    for (@typeInfo(PatternKind).@"enum".fields) |f| {
        _ = @field(PatRows, f.name);
    }
    std.debug.assert(@sizeOf(ExprId) == 4);
    std.debug.assert(@sizeOf(LocId) == 4);
    std.debug.assert(@sizeOf(StrId) == 4);
}

//========================================================================
//                    Pretty-printing (debugging)
//========================================================================

/// LISP-style pretty printer for the DOD AST / IR.
pub const DodPrinter = struct {
    writer: *std.io.Writer,
    indent: usize = 0,

    exprs: *ExprStore,
    pats: *PatternStore,

    /// Create a `DodPrinter` that writes to `writer`.
    pub fn init(writer: anytype, exprs: *ExprStore, pats: *PatternStore) DodPrinter {
        return .{ .writer = writer, .exprs = exprs, .pats = pats };
    }

    // ------------------------------------------------------------
    // Basics
    // ------------------------------------------------------------
    /// Emit whitespace matching the current indent level.
    fn ws(self: *DodPrinter) anyerror!void {
        var i: usize = 0;
        while (i < self.indent) : (i += 1) try self.writer.writeByte(' ');
    }
    /// Begin a new grouped block labeled `head`.
    fn open(self: *DodPrinter, comptime head: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(head, args);
        try self.writer.writeAll("\n");
        self.indent += 2;
    }
    /// Close the current block and write a newline.
    fn close(self: *DodPrinter) anyerror!void {
        self.indent = if (self.indent >= 2) self.indent - 2 else 0;
        try self.ws();
        try self.writer.writeAll(")\n");
    }
    /// Emit a single-line leaf entry using `fmt`.
    fn leaf(self: *DodPrinter, comptime fmt: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
    }
    /// Resolve string identifier `id`.
    inline fn s(self: *const DodPrinter, id: StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    // ------------------------------------------------------------
    // Public entrypoints
    // ------------------------------------------------------------
    /// Print the top-level program and its package metadata.
    pub fn printProgram(self: *DodPrinter, prog: *const ProgramDO) anyerror!void {
        try self.open("(program", .{});
        if (!prog.package_name.isNone()) {
            try self.leaf("(package \"{s}\")", .{self.s(prog.package_name.unwrap())});
        } else {
            try self.leaf("(package null)", .{});
        }
        const r = prog.top_decls;
        const decls = self.exprs.decl_pool.slice(r);
        for (decls) |did| try self.printDecl(did);
        try self.close();
    }

    /// Recursively print expression `id`.
    pub fn printExpr(self: *DodPrinter, id: ExprId) anyerror!void {
        const kind = self.exprs.kind(id);
        switch (kind) {
            .Literal => {
                const n = self.exprs.get(.Literal, id);
                try self.leaf("(literal kind=#{d} \"{s}\")", .{ n.tag_small, self.s(n.value) });
            },
            .Ident => {
                const n = self.exprs.get(.Ident, id);
                try self.leaf("(ident \"{s}\")", .{self.s(n.name)});
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
                    try self.printExpr(n.body.unwrap()); // Block expr id
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
            .Unreachable => {
                _ = self.exprs.get(.Unreachable, id);
                try self.leaf("(unreachable)", .{});
            },
            .Null => {
                _ = self.exprs.get(.Null, id);
                try self.leaf("(null)", .{});
            },
            .Undefined => {
                _ = self.exprs.get(.Undefined, id);
                try self.leaf("(undefined)", .{});
            },
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

            // ---- Types ----
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
            .TypeType => {
                _ = self.exprs.get(.TypeType, id);
                try self.leaf("(type)", .{});
            },
            .AnyType => {
                _ = self.exprs.get(.AnyType, id);
                try self.leaf("(any)", .{});
            },
            .NoreturnType => {
                _ = self.exprs.get(.NoreturnType, id);
                try self.leaf("(noreturn)", .{});
            },
        }
    }

    /// Print declaration `id`, including its rhs/lhs.
    pub fn printDecl(self: *DodPrinter, id: DeclId) anyerror!void {
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

    // ------------------------------------------------------------
    // Helpers: lists, attributes, params, fields, patterns
    // ------------------------------------------------------------
    /// Print every expression within `r` under the heading `name`.
    fn printExprRange(self: *DodPrinter, comptime name: []const u8, r: RangeOf(ExprId)) anyerror!void {
        try self.open("(" ++ name, .{});
        const xs = self.exprs.expr_pool.slice(r);
        for (xs) |eid| try self.printExpr(eid);
        try self.close();
    }
    /// Print optional attributes described by `opt_r`.
    fn printAttrs(self: *DodPrinter, opt_r: OptRangeAttr) !void {
        if (opt_r.isNone()) return;
        const r = opt_r.asRange();
        const xs = self.exprs.attr_pool.slice(r);

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

    /// Print the parameter list referenced by `r`.
    fn printParams(self: *DodPrinter, r: RangeOf(ParamId)) anyerror!void {
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
    /// Print the struct field metadata for `id`.
    fn printStructField(self: *DodPrinter, id: StructFieldId) anyerror!void {
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

    // ------------------------------------------------------------
    // Patterns
    // ------------------------------------------------------------
    /// Print pattern `id` and its nested branches.
    pub fn printPattern(self: *DodPrinter, id: PatternId) anyerror!void {
        const kind = self.pats.kind(id);
        switch (kind) {
            .Wildcard => {
                _ = self.pats.get(.Wildcard, id);
                try self.leaf("(wildcard)", .{});
            },
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

/// Print `program` into an owned buffer and return the bytes.
fn printToString(
    gpa: std.mem.Allocator,
    printer: *DodPrinter,
    program: *const ProgramDO,
) ![]u8 {
    var buf: ArrayList(u8) = .init(gpa);
    errdefer buf.deinit();
    const w = buf.writer();
    // Re-bind the writer for this call
    var local: DodPrinter = .init(w, printer.exprs, printer.pats);
    try local.printProgram(program);
    return buf.toOwnedSlice();
}

/// Record a new location spanning `[start, end)` via `es`.
fn mkLoc(es: *ExprStore, start: u32, end: u32) LocId {
    return es.locs.add(es.gpa, .{ .start = start, .end = end });
}

test "printer: simple const decl with lhs, rhs literal" {
    const gpa = std.testing.allocator;

    var exprs: ExprStore = .init(gpa);
    defer exprs.deinit();

    var pats: PatternStore = .init(gpa);
    defer pats.deinit();

    // strings & loc
    const s_pkg = exprs.strs.intern(gpa, "testpkg");
    const s_x = exprs.strs.intern(gpa, "x");
    const s_42 = exprs.strs.intern(gpa, "42");
    const loc = mkLoc(&exprs, 1, 1);

    // lhs: ident "x"
    const id_x = exprs.add(.Ident, .{ .name = s_x, .loc = loc });

    // rhs: literal "42"
    const id_42 = exprs.add(.Literal, .{ .value = s_42, .tag_small = 0, .loc = loc });

    // decl
    const drow: Rows.Decl = .{
        .lhs = .some(id_x),
        .rhs = id_42,
        .ty = .none(),
        .method_path = .none(),
        .flags = .{ .is_const = true, .is_assign = false },
        .loc = loc,
    };
    const did = exprs.addDeclRow(drow);

    // program
    var prog: ProgramDO = .{
        .top_decls = exprs.decl_pool.pushMany(gpa, &[_]DeclId{did}),
        .package_name = .some(s_pkg),
        .package_loc = .none(),
    };
    var buf: ArrayList(u8) = .init(gpa);
    defer buf.deinit();
    const w = buf.writer();
    var local: DodPrinter = .init(w, &exprs, &pats);
    try local.printProgram(&prog);
    const out = buf.items;

    const expected =
        \\(program
        \\  (package "testpkg")
        \\  (decl is_const=true is_assign=false)
        \\    (lhs
        \\      (ident "x")
        \\    )
        \\    (rhs
        \\      (literal kind=#0 "42")
        \\    )
        \\  )
        \\)
        \\
    ;

    try std.testing.expectEqualStrings(expected, out);
}

test "printer: function with attrs, one param, result type, empty body" {
    const gpa = std.testing.allocator;

    var exprs: ExprStore = .init(gpa);
    defer exprs.deinit();

    var pats: PatternStore = .init(gpa);
    defer pats.deinit();

    // strings & loc
    const s_pkg = exprs.strs.intern(gpa, "pkg");
    const s_fn = exprs.strs.intern(gpa, "foo");
    const s_i32 = exprs.strs.intern(gpa, "i32");
    const s_inline = exprs.strs.intern(gpa, "inline");
    const loc = mkLoc(&exprs, 1, 1);

    // type ident "i32"
    const id_i32 = exprs.add(.Ident, .{ .name = s_i32, .loc = loc });

    // param: (type i32)
    const pid = exprs.addParamRow(.{
        .pat = .none(),
        .ty = .some(id_i32),
        .value = .none(),
        .attrs = .none(),
        .is_comptime = false,
        .loc = loc,
    });
    const params_r = exprs.param_pool.pushMany(gpa, &[_]ParamId{pid});

    // attributes: (attr name="inline")
    const aid = exprs.addAttrRow(.{ .name = s_inline, .value = .none(), .loc = loc });
    const attrs_r = exprs.attr_pool.pushMany(gpa, &[_]AttributeId{aid});

    // body: empty block
    const id_blk = exprs.add(.Block, .{ .items = RangeOf(DeclId).empty(), .loc = loc });

    // function expr
    const id_fun = exprs.add(.Function, .{
        .params = params_r,
        .result_ty = .some(id_i32),
        .body = .some(id_blk),
        .raw_asm = .none(),
        .attrs = .some(attrs_r),
        .flags = .{ .is_proc = false, .is_async = false, .is_variadic = false, .is_extern = false, .is_test = false },
        .loc = loc,
    });

    // lhs: ident "foo"
    const id_lhs = exprs.add(.Ident, .{ .name = s_fn, .loc = loc });

    // decl
    const did = exprs.addDeclRow(.{
        .lhs = .some(id_lhs),
        .rhs = id_fun,
        .ty = .none(),
        .flags = .{ .is_const = true, .is_assign = false },
        .loc = loc,
    });

    var prog: ProgramDO = .{
        .top_decls = exprs.decl_pool.pushMany(gpa, &[_]DeclId{did}),
        .package_name = .some(s_pkg),
        .package_loc = .none(),
    };

    var buf: ArrayList(u8) = .init(gpa);
    defer buf.deinit();
    const w = buf.writer();
    var local: DodPrinter = .init(w, &exprs, &pats);
    try local.printProgram(&prog);
    const out = buf.items;

    const expected =
        \\(program
        \\  (package "pkg")
        \\  (decl is_const=true is_assign=false)
        \\    (lhs
        \\      (ident "foo")
        \\    )
        \\    (rhs
        \\      (function
        \\        (attributes
        \\          (attr name="inline")
        \\          )
        \\        (param
        \\          (type
        \\            (ident "i32")
        \\          )
        \\        )
        \\        (result
        \\          (ident "i32")
        \\        )
        \\        (body
        \\          (block
        \\          )
        \\        )
        \\      )
        \\    )
        \\  )
        \\)
        \\
    ;

    try std.testing.expectEqualStrings(expected, out);
}

test "printer: patterns — Or(literal 1 | literal 2)" {
    var gpa = std.testing.allocator;

    var exprs: ExprStore = .init(gpa);
    defer exprs.deinit();

    var pats: PatternStore = .init(gpa);
    defer pats.deinit();

    // strings & loc
    const s_1 = exprs.strs.intern(gpa, "1");
    const s_2 = exprs.strs.intern(gpa, "2");
    const loc = mkLoc(&exprs, 1, 1);

    // expr literals "1", "2"
    const id_1 = exprs.add(.Literal, .{ .value = s_1, .tag_small = 0, .loc = loc });
    const id_2 = exprs.add(.Literal, .{ .value = s_2, .tag_small = 0, .loc = loc });

    // patterns: Literal(1), Literal(2)
    const p1 = pats.add(.Literal, .{ .expr = id_1, .loc = loc });
    const p2 = pats.add(.Literal, .{ .expr = id_2, .loc = loc });

    // Or(p1 | p2)
    const alts = pats.pat_pool.pushMany(gpa, &[_]PatternId{ p1, p2 });
    const por = pats.add(.Or, .{ .alts = alts, .loc = loc });

    // Make a tiny "program" with no decls (printer entry needs one),
    // but we won't print program in this test; we'll print pattern directly.
    const dummy_prog: ProgramDO = .{
        .top_decls = RangeOf(DeclId).empty(),
        .package_name = .none(),
        .package_loc = .none(),
    };
    _ = dummy_prog;

    // Print just the pattern by calling the printer's pattern entry.
    var buf: ArrayList(u8) = .init(gpa);
    defer buf.deinit();
    const w = buf.writer();
    var printer: DodPrinter = .init(w, &exprs, &pats);
    try printer.printPattern(por);
    const out = try buf.toOwnedSlice();
    defer gpa.free(out);

    const expected =
        \\(or_pattern
        \\  (literal
        \\    (literal kind=#0 "1")
        \\  )
        \\  (literal
        \\    (literal kind=#0 "2")
        \\  )
        \\)
        \\
    ;

    try std.testing.expectEqualStrings(expected, out);
}
