const std = @import("std");
const dod = @import("cst.zig");
const TypeInfo = @import("types.zig").TypeInfo;
const TypeStore = @import("types.zig").TypeStore;
const ArrayList = std.array_list.Managed;

pub const Index = dod.Index;
pub const SentinelIndex = dod.SentinelIndex;
pub const RangeOf = dod.RangeOf;
pub const OptRangeOf = dod.OptRangeOf;
pub const Pool = dod.Pool;
pub const Table = dod.Table;
pub const StoreIndex = dod.StoreIndex;
pub const StringInterner = dod.StringInterner;
pub const LocStore = dod.LocStore;
pub const StrId = dod.StrId;
pub const LocId = dod.LocId;
pub const OptStrId = dod.OptStrId;
pub const OptLocId = dod.OptLocId;
pub const MlirKind = dod.MlirKind;
pub const CastKind = dod.CastKind;
pub const MlirPieceKind = dod.MlirPieceKind;

pub const ExprTag = struct {};
pub const StmtTag = struct {};
pub const PatternTag = struct {};

pub const ExprId = Index(ExprTag);
pub const DeclId = Index(Rows.Decl);
pub const StmtId = Index(StmtTag);
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
pub const PatternId = Index(PatternTag);
pub const PatFieldId = Index(PatRows.StructField);

pub const OptExprId = SentinelIndex(ExprTag);
pub const OptStmtId = SentinelIndex(StmtTag);
pub const OptDeclId = SentinelIndex(Rows.Decl);
pub const OptParamId = SentinelIndex(Rows.Param);
pub const OptPatternId = SentinelIndex(PatternTag);

pub const RangeExpr = RangeOf(ExprId);
pub const RangeStmt = RangeOf(StmtId);
pub const RangeDecl = RangeOf(DeclId);
pub const RangeParam = RangeOf(ParamId);
pub const RangeAttr = RangeOf(AttributeId);
pub const RangeField = RangeOf(StructFieldId);
pub const RangeEnumField = RangeOf(EnumFieldId);
pub const RangeVariantField = RangeOf(VariantFieldId);
pub const RangeKeyValue = RangeOf(KeyValueId);
pub const RangeStructFieldValue = RangeOf(StructFieldValueId);
pub const RangeMatchArm = RangeOf(MatchArmId);
pub const RangeMethodPathSeg = RangeOf(MethodPathSegId);
pub const RangeMlirPiece = RangeOf(MlirPieceId);
pub const RangePat = RangeOf(PatternId);
pub const RangePathSeg = RangeOf(PathSegId);
pub const RangePatField = RangeOf(PatFieldId);

pub const OptRangeExpr = OptRangeOf(ExprId);
pub const OptRangeStmt = OptRangeOf(StmtId);
pub const OptRangeDecl = OptRangeOf(DeclId);
pub const OptRangeAttr = OptRangeOf(AttributeId);
pub const OptRangeField = OptRangeOf(StructFieldId);
pub const OptRangePat = OptRangeOf(PatternId);
pub const OptRangeMethodPathSeg = OptRangeOf(MethodPathSegId);

pub const LiteralKind = enum(u8) { int, float, bool, string, char, imaginary };
pub const UnaryOp = enum(u8) { pos, neg, address_of, logical_not };
pub const BinaryOp = enum(u8) {
    add,
    sub,
    mul,
    div,
    mod,
    shl,
    shr,
    bit_and,
    bit_or,
    bit_xor,
    eq,
    neq,
    lt,
    lte,
    gt,
    gte,
    logical_and,
    logical_or,
    @"orelse",
};
pub const VariantPayloadKind = enum(u2) { none, tuple, @"struct" };

pub const Unit = struct {
    decls: RangeDecl,
    package_name: OptStrId,
    package_loc: OptLocId,

    pub fn empty() Unit {
        return .{
            .decls = RangeDecl.empty(),
            .package_name = OptStrId.none(),
            .package_loc = OptLocId.none(),
        };
    }
};

pub const ExprKind = enum(u16) {
    Literal,
    Ident,
    Unary,
    Binary,
    Range,
    Deref,
    ArrayLit,
    TupleLit,
    MapLit,
    Call,
    IndexAccess,
    FieldAccess,
    StructLit,
    FunctionLit,
    Block,
    ComptimeBlock,
    CodeBlock,
    AsyncBlock,
    MlirBlock,
    Insert,
    Return,
    If,
    While,
    For,
    Match,
    Break,
    Continue,
    Unreachable,
    NullLit,
    UndefLit,
    Defer,
    ErrDefer,
    ErrUnwrap,
    OptionalUnwrap,
    Await,
    Closure,
    Cast,
    Catch,
    Import,
    TypeOf,
    TupleType,
    ArrayType,
    DynArrayType,
    MapType,
    SliceType,
    OptionalType,
    ErrorSetType,
    ErrorType,
    StructType,
    EnumType,
    VariantType,
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
    pub const Literal = struct {
        kind: LiteralKind,
        data: LiteralValue,
        loc: LocId,
    };
    pub const Ident = struct { name: StrId, loc: LocId };
    pub const Unary = struct { expr: ExprId, op: UnaryOp, loc: LocId };
    pub const Binary = struct { left: ExprId, right: ExprId, op: BinaryOp, wrap: bool, saturate: bool, loc: LocId };
    pub const Range = struct { start: OptExprId, end: OptExprId, inclusive_right: bool, loc: LocId };
    pub const Deref = struct { expr: ExprId, loc: LocId };
    pub const ArrayLit = struct { elems: RangeExpr, loc: LocId };
    pub const TupleLit = struct { elems: RangeExpr, loc: LocId };
    pub const MapLit = struct { entries: RangeKeyValue, loc: LocId };
    pub const KeyValue = struct { key: ExprId, value: ExprId, loc: LocId };
    pub const Call = struct { callee: ExprId, args: RangeExpr, loc: LocId };
    pub const IndexAccess = struct { collection: ExprId, index: ExprId, loc: LocId };
    pub const FieldAccess = struct { parent: ExprId, field: StrId, is_tuple: bool, loc: LocId };
    pub const StructFieldValue = struct { name: OptStrId, value: ExprId, loc: LocId };
    pub const StructLit = struct { fields: RangeStructFieldValue, ty: OptExprId, loc: LocId };

    pub const FnFlags = packed struct(u8) { is_proc: bool, is_async: bool, is_variadic: bool, is_extern: bool, _pad: u4 = 0 };

    pub const FunctionLit = struct {
        params: RangeParam,
        result_ty: OptExprId,
        body: OptExprId,
        raw_asm: OptStrId,
        attrs: OptRangeAttr,
        flags: FnFlags,
        loc: LocId,
    };

    pub const Block = struct { items: RangeStmt, loc: LocId };
    pub const ComptimeBlock = struct { block: ExprId, loc: LocId };
    pub const CodeBlock = struct { block: ExprId, loc: LocId };
    pub const AsyncBlock = struct { body: ExprId, loc: LocId };
    pub const MlirPiece = struct { kind: MlirPieceKind, text: StrId };
    pub const MlirBlock = struct { kind: MlirKind, text: StrId, pieces: RangeMlirPiece, args: RangeExpr, loc: LocId };
    pub const Insert = struct { expr: ExprId, loc: LocId };

    pub const Return = struct { value: OptExprId, loc: LocId };
    pub const If = struct { cond: ExprId, then_block: ExprId, else_block: OptExprId, loc: LocId };
    pub const While = struct {
        cond: OptExprId,
        pattern: OptPatternId,
        body: ExprId,
        is_pattern: bool,
        label: OptStrId,
        loc: LocId,
    };
    pub const For = struct { pattern: PatternId, iterable: ExprId, body: ExprId, label: OptStrId, loc: LocId };
    pub const Match = struct { expr: ExprId, arms: RangeMatchArm, loc: LocId };
    pub const MatchArm = struct { pattern: PatternId, guard: OptExprId, body: ExprId, loc: LocId };

    pub const Break = struct { label: OptStrId, value: OptExprId, loc: LocId };
    pub const Continue = struct { label: OptStrId, loc: LocId };
    pub const Unreachable = struct { loc: LocId };
    pub const NullLit = struct { loc: LocId };
    pub const UndefLit = struct { loc: LocId };
    pub const Defer = struct { expr: ExprId, loc: LocId };
    pub const ErrDefer = struct { expr: ExprId, loc: LocId };
    pub const ErrUnwrap = struct { expr: ExprId, loc: LocId };
    pub const OptionalUnwrap = struct { expr: ExprId, loc: LocId };
    pub const Await = struct { expr: ExprId, loc: LocId };
    pub const Closure = struct { params: RangeParam, result_ty: OptExprId, body: ExprId, loc: LocId };
    pub const Cast = struct { expr: ExprId, ty: ExprId, kind: CastKind, loc: LocId };
    pub const Catch = struct { expr: ExprId, binding_name: OptStrId, binding_loc: OptLocId, handler: ExprId, loc: LocId };
    pub const Import = struct { path: StrId, loc: LocId };
    pub const TypeOf = struct { expr: ExprId, loc: LocId };

    pub const Param = struct {
        pat: OptPatternId,
        ty: OptExprId,
        value: OptExprId,
        attrs: OptRangeAttr,
        is_comptime: bool,
        loc: LocId,
    };
    pub const Attribute = struct { name: StrId, value: OptExprId, loc: LocId };

    pub const MethodPathSeg = struct { name: StrId, loc: LocId };
    pub const DeclFlags = packed struct(u8) { is_const: bool, _pad: u7 = 0 };
    pub const Decl = struct {
        pattern: OptPatternId,
        value: ExprId,
        ty: OptExprId,
        method_path: OptRangeMethodPathSeg,
        flags: DeclFlags,
        loc: LocId,
    };

    pub const TupleType = struct { elems: RangeExpr, loc: LocId };
    pub const ArrayType = struct { elem: ExprId, size: ExprId, loc: LocId };
    pub const DynArrayType = struct { elem: ExprId, loc: LocId };
    pub const MapType = struct { key: ExprId, value: ExprId, loc: LocId };
    pub const SliceType = struct { elem: ExprId, loc: LocId };
    pub const OptionalType = struct { elem: ExprId, loc: LocId };
    pub const ErrorSetType = struct { err: ExprId, value: ExprId, loc: LocId };

    pub const StructField = struct { name: StrId, ty: ExprId, value: OptExprId, attrs: OptRangeAttr, loc: LocId };
    pub const StructType = struct { fields: RangeField, is_extern: bool, attrs: OptRangeAttr, loc: LocId };

    pub const EnumField = struct { name: StrId, value: OptExprId, attrs: OptRangeAttr, loc: LocId };
    pub const EnumType = struct { fields: RangeEnumField, discriminant: OptExprId, is_extern: bool, attrs: OptRangeAttr, loc: LocId };

    pub const VariantField = struct {
        name: StrId,
        payload_kind: VariantPayloadKind,
        payload_elems: OptRangeExpr,
        payload_fields: OptRangeField,
        value: OptExprId,
        attrs: OptRangeAttr,
        loc: LocId,
    };
    pub const VariantType = struct { fields: RangeVariantField, loc: LocId };
    pub const ErrorType = VariantType;

    pub const UnionType = struct { fields: RangeField, is_extern: bool, attrs: OptRangeAttr, loc: LocId };

    pub const PointerType = struct { elem: ExprId, is_const: bool, loc: LocId };
    pub const SimdType = struct { elem: ExprId, lanes: ExprId, loc: LocId };
    pub const ComplexType = struct { elem: ExprId, loc: LocId };
    pub const TensorType = struct { elem: ExprId, shape: RangeExpr, loc: LocId };
    pub const TypeType = struct { loc: LocId };
    pub const AnyType = struct { loc: LocId };
    pub const NoreturnType = struct { loc: LocId };
};

pub inline fn RowT(comptime K: ExprKind) type {
    return @field(Rows, @tagName(K));
}

pub const StmtKind = enum(u8) {
    Expr,
    Decl,
    Assign,
    Insert,
    Return,
    Break,
    Continue,
    Unreachable,
    Defer,
    ErrDefer,
};

pub const StmtRows = struct {
    pub const Expr = struct { expr: ExprId };
    pub const Decl = struct { decl: DeclId };
    pub const Assign = struct { left: ExprId, right: ExprId, loc: LocId };
    pub const Insert = Rows.Insert;
    pub const Return = Rows.Return;
    pub const Break = Rows.Break;
    pub const Continue = Rows.Continue;
    pub const Unreachable = Rows.Unreachable;
    pub const Defer = Rows.Defer;
    pub const ErrDefer = Rows.ErrDefer;
};

pub inline fn StmtRowT(comptime K: StmtKind) type {
    return @field(StmtRows, @tagName(K));
}

pub const PatternKind = enum(u16) {
    Wildcard,
    Literal,
    Path,
    Binding,
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

    pub const PathSeg = struct { name: StrId, by_ref: bool, is_mut: bool, loc: LocId };
    pub const Path = struct { segments: RangePathSeg, loc: LocId };

    pub const Binding = struct { name: StrId, by_ref: bool, is_mut: bool, loc: LocId };

    pub const Tuple = struct { elems: RangePat, loc: LocId };

    pub const Slice = struct {
        elems: RangePat,
        has_rest: bool,
        rest_index: u32,
        rest_binding: OptPatternId,
        loc: LocId,
    };

    pub const StructField = struct { name: StrId, pattern: PatternId, loc: LocId };

    pub const Struct = struct {
        path: RangePathSeg,
        fields: RangePatField,
        has_rest: bool,
        loc: LocId,
    };

    pub const VariantTuple = struct {
        path: RangePathSeg,
        elems: RangePat,
        loc: LocId,
    };

    pub const VariantStruct = struct {
        path: RangePathSeg,
        fields: RangePatField,
        has_rest: bool,
        loc: LocId,
    };

    pub const Range = struct { start: OptExprId, end: OptExprId, inclusive_right: bool, loc: LocId };
    pub const Or = struct { alts: RangePat, loc: LocId };
    pub const At = struct { binder: StrId, pattern: PatternId, loc: LocId };
};

inline fn PatRowT(comptime K: PatternKind) type {
    return @field(PatRows, @tagName(K));
}

pub const LiteralInt = struct {
    text: StrId,
    value: u128,
    base: u8,
    valid: bool,
};

pub const LiteralFloat = struct {
    text: StrId,
    value: f64,
    valid: bool,
};

pub const LiteralValue = union(enum) {
    none,
    bool: bool,
    char: u32,
    string: StrId,
    int: LiteralInt,
    float: LiteralFloat,
    imaginary: LiteralFloat,
};

pub const ExprStore = struct {
    gpa: std.mem.Allocator,
    index: StoreIndex(ExprKind) = .{},

    Literal: Table(Rows.Literal) = .{},
    Ident: Table(Rows.Ident) = .{},
    Unary: Table(Rows.Unary) = .{},
    Binary: Table(Rows.Binary) = .{},
    Range: Table(Rows.Range) = .{},
    Deref: Table(Rows.Deref) = .{},

    ArrayLit: Table(Rows.ArrayLit) = .{},
    TupleLit: Table(Rows.TupleLit) = .{},
    MapLit: Table(Rows.MapLit) = .{},
    KeyValue: Table(Rows.KeyValue) = .{},

    Call: Table(Rows.Call) = .{},
    IndexAccess: Table(Rows.IndexAccess) = .{},
    FieldAccess: Table(Rows.FieldAccess) = .{},

    StructFieldValue: Table(Rows.StructFieldValue) = .{},
    StructLit: Table(Rows.StructLit) = .{},

    FunctionLit: Table(Rows.FunctionLit) = .{},
    Block: Table(Rows.Block) = .{},
    ComptimeBlock: Table(Rows.ComptimeBlock) = .{},
    CodeBlock: Table(Rows.CodeBlock) = .{},
    AsyncBlock: Table(Rows.AsyncBlock) = .{},
    MlirBlock: Table(Rows.MlirBlock) = .{},
    MlirPiece: Table(Rows.MlirPiece) = .{},
    Insert: Table(Rows.Insert) = .{},

    Return: Table(Rows.Return) = .{},
    If: Table(Rows.If) = .{},
    While: Table(Rows.While) = .{},
    For: Table(Rows.For) = .{},
    Match: Table(Rows.Match) = .{},
    MatchArm: Table(Rows.MatchArm) = .{},

    Break: Table(Rows.Break) = .{},
    Continue: Table(Rows.Continue) = .{},
    Unreachable: Table(Rows.Unreachable) = .{},
    NullLit: Table(Rows.NullLit) = .{},
    UndefLit: Table(Rows.UndefLit) = .{},
    Defer: Table(Rows.Defer) = .{},
    ErrDefer: Table(Rows.ErrDefer) = .{},
    ErrUnwrap: Table(Rows.ErrUnwrap) = .{},
    OptionalUnwrap: Table(Rows.OptionalUnwrap) = .{},
    Await: Table(Rows.Await) = .{},
    Closure: Table(Rows.Closure) = .{},
    Cast: Table(Rows.Cast) = .{},
    Catch: Table(Rows.Catch) = .{},
    Import: Table(Rows.Import) = .{},
    TypeOf: Table(Rows.TypeOf) = .{},

    TupleType: Table(Rows.TupleType) = .{},
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
    VariantType: Table(Rows.VariantType) = .{},
    ErrorType: Table(Rows.ErrorType) = .{},
    UnionType: Table(Rows.UnionType) = .{},
    PointerType: Table(Rows.PointerType) = .{},
    SimdType: Table(Rows.SimdType) = .{},
    ComplexType: Table(Rows.ComplexType) = .{},
    TensorType: Table(Rows.TensorType) = .{},
    TypeType: Table(Rows.TypeType) = .{},
    AnyType: Table(Rows.AnyType) = .{},
    NoreturnType: Table(Rows.NoreturnType) = .{},

    Param: Table(Rows.Param) = .{},
    Attribute: Table(Rows.Attribute) = .{},
    Decl: Table(Rows.Decl) = .{},
    MethodPathSeg: Table(Rows.MethodPathSeg) = .{},

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
    locs: *const LocStore,

    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner, locs: *const LocStore) ExprStore {
        return .{ .gpa = gpa, .strs = strs, .locs = locs };
    }

    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;

        self.index.deinit(gpa);

        inline for (@typeInfo(ExprKind).@"enum".fields) |f| {
            @field(self, f.name).deinit(gpa);
        }

        self.StructFieldValue.deinit(gpa);
        self.KeyValue.deinit(gpa);
        self.MlirPiece.deinit(gpa);
        self.MatchArm.deinit(gpa);
        self.Param.deinit(gpa);
        self.Attribute.deinit(gpa);
        self.Decl.deinit(gpa);
        self.MethodPathSeg.deinit(gpa);
        self.StructField.deinit(gpa);
        self.EnumField.deinit(gpa);
        self.VariantField.deinit(gpa);

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

    pub fn add(self: *@This(), comptime K: ExprKind, row: RowT(K)) ExprId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), ExprId);
    }

    pub fn get(self: *const @This(), comptime K: ExprKind, id: ExprId) RowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *const Table(RowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
    }

    pub fn addKeyValue(self: *@This(), row: Rows.KeyValue) KeyValueId {
        return self.KeyValue.add(self.gpa, row);
    }

    pub fn addStructFieldValue(self: *@This(), row: Rows.StructFieldValue) StructFieldValueId {
        return self.StructFieldValue.add(self.gpa, row);
    }

    pub fn addMatchArm(self: *@This(), row: Rows.MatchArm) MatchArmId {
        return self.MatchArm.add(self.gpa, row);
    }

    pub fn addParam(self: *@This(), row: Rows.Param) ParamId {
        return self.Param.add(self.gpa, row);
    }

    pub fn addAttribute(self: *@This(), row: Rows.Attribute) AttributeId {
        return self.Attribute.add(self.gpa, row);
    }

    pub fn addDecl(self: *@This(), row: Rows.Decl) DeclId {
        return self.Decl.add(self.gpa, row);
    }

    pub fn addMethodPathSeg(self: *@This(), row: Rows.MethodPathSeg) MethodPathSegId {
        return self.MethodPathSeg.add(self.gpa, row);
    }

    pub fn addStructField(self: *@This(), row: Rows.StructField) StructFieldId {
        return self.StructField.add(self.gpa, row);
    }

    pub fn addEnumField(self: *@This(), row: Rows.EnumField) EnumFieldId {
        return self.EnumField.add(self.gpa, row);
    }

    pub fn addVariantField(self: *@This(), row: Rows.VariantField) VariantFieldId {
        return self.VariantField.add(self.gpa, row);
    }
    pub fn addMlirPiece(self: *@This(), row: Rows.MlirPiece) MlirPieceId {
        return self.MlirPiece.add(self.gpa, row);
    }
};

pub const StmtStore = struct {
    gpa: std.mem.Allocator,
    index: StoreIndex(StmtKind) = .{},

    Expr: Table(StmtRows.Expr) = .{},
    Decl: Table(StmtRows.Decl) = .{},
    Assign: Table(StmtRows.Assign) = .{},
    Insert: Table(StmtRows.Insert) = .{},
    Return: Table(StmtRows.Return) = .{},
    Break: Table(StmtRows.Break) = .{},
    Continue: Table(StmtRows.Continue) = .{},
    Unreachable: Table(StmtRows.Unreachable) = .{},
    Defer: Table(StmtRows.Defer) = .{},
    ErrDefer: Table(StmtRows.ErrDefer) = .{},

    stmt_pool: Pool(StmtId) = .{},

    pub fn init(gpa: std.mem.Allocator) StmtStore {
        return .{ .gpa = gpa };
    }

    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;

        self.index.deinit(gpa);
        inline for (@typeInfo(StmtKind).@"enum".fields) |f| {
            @field(self, f.name).deinit(gpa);
        }
        self.stmt_pool.deinit(gpa);
    }

    pub fn add(self: *@This(), comptime K: StmtKind, row: StmtRowT(K)) StmtId {
        const tbl: *Table(StmtRowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), StmtId);
    }

    pub fn get(self: *const @This(), comptime K: StmtKind, id: StmtId) StmtRowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *const Table(StmtRowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
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
        inline for (@typeInfo(PatternKind).@"enum".fields) |f| {
            @field(self, f.name).deinit(gpa);
        }

        self.PathSeg.deinit(gpa);
        self.StructField.deinit(gpa);

        self.pat_pool.deinit(gpa);
        self.seg_pool.deinit(gpa);
        self.field_pool.deinit(gpa);
    }

    pub fn add(self: *@This(), comptime K: PatternKind, row: PatRowT(K)) PatternId {
        const tbl: *Table(PatRowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), PatternId);
    }

    pub fn get(self: *const @This(), comptime K: PatternKind, id: PatternId) PatRowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *const Table(PatRowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
    }

    pub fn addPathSeg(self: *@This(), row: PatRows.PathSeg) PathSegId {
        const idx = self.PathSeg.add(self.gpa, row);
        return PathSegId.fromRaw(idx);
    }

    pub fn addPatField(self: *@This(), row: PatRows.StructField) PatFieldId {
        const idx = self.StructField.add(self.gpa, row);
        return PatFieldId.fromRaw(idx);
    }
};

pub const Ast = struct {
    gpa: std.mem.Allocator,
    file_id: usize,
    unit: Unit,
    exprs: ExprStore,
    stmts: StmtStore,
    pats: PatternStore,
    type_info: TypeInfo,

    pub fn init(
        gpa: std.mem.Allocator,
        interner: *StringInterner,
        locs: *const LocStore,
        type_store: *TypeStore,
        file_id: usize,
    ) Ast {
        return .{
            .gpa = gpa,
            .file_id = file_id,
            .unit = Unit.empty(),
            .exprs = ExprStore.init(gpa, interner, locs),
            .stmts = StmtStore.init(gpa),
            .pats = PatternStore.init(gpa, interner),
            .type_info = TypeInfo.init(gpa, type_store),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.type_info.deinit();
        self.exprs.deinit();
        self.stmts.deinit();
        self.pats.deinit();
    }
};

pub const AstPrinter = struct {
    writer: *std.io.Writer,
    indent: usize = 0,

    exprs: *const ExprStore,
    stmts: *const StmtStore,
    pats: *const PatternStore,

    pub fn init(writer: anytype, exprs: *const ExprStore, stmts: *const StmtStore, pats: *const PatternStore) AstPrinter {
        return .{ .writer = writer, .exprs = exprs, .stmts = stmts, .pats = pats };
    }

    fn ws(self: *AstPrinter) anyerror!void {
        var i: usize = 0;
        while (i < self.indent) : (i += 1) try self.writer.writeByte(' ');
    }

    fn open(self: *AstPrinter, comptime head: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(head, args);
        try self.writer.writeAll("\n");
        self.indent += 2;
    }

    fn close(self: *AstPrinter) anyerror!void {
        self.indent = if (self.indent >= 2) self.indent - 2 else 0;
        try self.ws();
        try self.writer.writeAll(")\n");
    }

    fn leaf(self: *AstPrinter, comptime fmt: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
    }

    inline fn s(self: *const AstPrinter, id: StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    pub fn printUnit(self: *AstPrinter, unit: *const Unit) anyerror!void {
        try self.open("(unit", .{});
        if (!unit.package_name.isNone()) {
            try self.leaf("(package \"{s}\")", .{self.s(unit.package_name.unwrap())});
        } else {
            try self.leaf("(package null)", .{});
        }

        const decl_ids = self.exprs.decl_pool.slice(unit.decls);
        for (decl_ids) |did| try self.printDecl(did);
        try self.close();
        try self.writer.flush();
    }

    fn printDecl(self: *AstPrinter, id: DeclId) anyerror!void {
        const row = self.exprs.Decl.get(id);
        try self.open("(decl is_const={})", .{row.flags.is_const});

        if (!row.pattern.isNone()) {
            try self.open("(pattern", .{});
            try self.printPattern(row.pattern.unwrap());
            try self.close();
        }

        if (!row.method_path.isNone()) {
            try self.open("(method_path", .{});
            const seg_ids = self.exprs.method_path_pool.slice(row.method_path.asRange());
            for (seg_ids) |sid| {
                const seg = self.exprs.MethodPathSeg.get(sid);
                try self.leaf("(seg \"{s}\")", .{self.s(seg.name)});
            }
            try self.close();
        }

        if (!row.ty.isNone()) {
            try self.open("(type", .{});
            try self.printExpr(row.ty.unwrap());
            try self.close();
        }

        try self.open("(value", .{});
        try self.printExpr(row.value);
        try self.close();

        try self.close();
    }

    fn printStmt(self: *AstPrinter, id: StmtId) anyerror!void {
        const kind = self.stmts.index.kinds.items[id.toRaw()];
        return switch (kind) {
            .Expr => {
                const row = self.stmts.get(.Expr, id);
                try self.open("(expr_stmt", .{});
                try self.printExpr(row.expr);
                try self.close();
            },
            .Decl => {
                const row = self.stmts.get(.Decl, id);
                try self.printDecl(row.decl);
            },
            .Assign => {
                const row = self.stmts.get(.Assign, id);
                try self.open("(assign", .{});
                try self.open("(left", .{});
                try self.printExpr(row.left);
                try self.close();
                try self.open("(right", .{});
                try self.printExpr(row.right);
                try self.close();
                try self.close();
            },
            .Insert => {
                const row = self.stmts.get(.Insert, id);
                try self.open("(insert", .{});
                try self.printExpr(row.expr);
                try self.close();
            },
            .Return => {
                const row = self.stmts.get(.Return, id);
                try self.open("(return", .{});
                if (!row.value.isNone()) {
                    try self.open("(value", .{});
                    try self.printExpr(row.value.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .Break => {
                const row = self.stmts.get(.Break, id);
                try self.open("(break", .{});
                if (!row.label.isNone()) try self.leaf("label=\"{s}\"", .{self.s(row.label.unwrap())});
                if (!row.value.isNone()) {
                    try self.open("(value", .{});
                    try self.printExpr(row.value.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .Continue => {
                _ = self.stmts.get(.Continue, id);
                try self.leaf("(continue)", .{});
            },
            .Unreachable => {
                _ = self.stmts.get(.Unreachable, id);
                try self.leaf("(unreachable)", .{});
            },
            .Defer => {
                const row = self.stmts.get(.Defer, id);
                try self.open("(defer", .{});
                try self.printExpr(row.expr);
                try self.close();
            },
            .ErrDefer => {
                const row = self.stmts.get(.ErrDefer, id);
                try self.open("(errdefer", .{});
                try self.printExpr(row.expr);
                try self.close();
            },
        };
    }

    pub fn printExpr(self: *AstPrinter, id: ExprId) anyerror!void {
        const kind = self.exprs.index.kinds.items[id.toRaw()];
        switch (kind) {
            .Literal => {
                const node = self.exprs.get(.Literal, id);
                switch (node.kind) {
                    .int => {
                        const info = node.data.int;
                        try self.leaf("(literal kind=int \"{s}\")", .{self.s(info.text)});
                    },
                    .float => {
                        const info = node.data.float;
                        try self.leaf("(literal kind=float \"{s}\")", .{self.s(info.text)});
                    },
                    .string => {
                        const sid = node.data.string;
                        try self.leaf("(literal kind=string \"{s}\")", .{self.s(sid)});
                    },
                    .imaginary => {
                        const info = node.data.imaginary;
                        try self.leaf("(literal kind=imaginary \"{s}i\")", .{self.s(info.text)});
                    },
                    .bool => try self.leaf("(literal kind=bool {})", .{node.data.bool}),
                    .char => try self.leaf("(literal kind=char {d})", .{node.data.char}),
                }
            },
            .Ident => {
                const node = self.exprs.get(.Ident, id);
                try self.leaf("(ident \"{s}\")", .{self.s(node.name)});
            },
            .Unary => {
                const node = self.exprs.get(.Unary, id);
                try self.open("(unary op={s}", .{@tagName(node.op)});
                try self.printExpr(node.expr);
                try self.close();
            },
            .Binary => {
                const node = self.exprs.get(.Binary, id);
                try self.open("(binary op={s} wrap={} saturate={})", .{ @tagName(node.op), node.wrap, node.saturate });
                try self.printExpr(node.left);
                try self.printExpr(node.right);
                try self.close();
            },
            .Range => {
                const node = self.exprs.get(.Range, id);
                try self.open("(range inclusive_right={})", .{node.inclusive_right});
                if (!node.start.isNone()) try self.printExpr(node.start.unwrap());
                if (!node.end.isNone()) try self.printExpr(node.end.unwrap());
                try self.close();
            },
            .Deref => {
                const node = self.exprs.get(.Deref, id);
                try self.open("(deref", .{});
                try self.printExpr(node.expr);
                try self.close();
            },
            .ArrayLit => {
                const node = self.exprs.get(.ArrayLit, id);
                try self.printExprRange("array", node.elems);
            },
            .TupleLit => {
                const node = self.exprs.get(.TupleLit, id);
                try self.printExprRange("tuple", node.elems);
            },
            .MapLit => {
                const node = self.exprs.get(.MapLit, id);
                try self.open("(map", .{});
                const entries = self.exprs.kv_pool.slice(node.entries);
                for (entries) |kv_id| {
                    const kv = self.exprs.KeyValue.get(kv_id);
                    try self.open("(entry", .{});
                    try self.open("(key", .{});
                    try self.printExpr(kv.key);
                    try self.close();
                    try self.open("(value", .{});
                    try self.printExpr(kv.value);
                    try self.close();
                    try self.close();
                }
                try self.close();
            },
            .Call => {
                const node = self.exprs.get(.Call, id);
                try self.open("(call", .{});
                try self.open("(callee", .{});
                try self.printExpr(node.callee);
                try self.close();
                try self.printExprRange("args", node.args);
                try self.close();
            },
            .IndexAccess => {
                const node = self.exprs.get(.IndexAccess, id);
                try self.open("(index", .{});
                try self.open("(collection", .{});
                try self.printExpr(node.collection);
                try self.close();
                try self.open("(expr", .{});
                try self.printExpr(node.index);
                try self.close();
                try self.close();
            },
            .FieldAccess => {
                const node = self.exprs.get(.FieldAccess, id);
                try self.open("(field name=\"{s}\" is_tuple={})", .{ self.s(node.field), node.is_tuple });
                try self.printExpr(node.parent);
                try self.close();
            },
            .StructLit => {
                const node = self.exprs.get(.StructLit, id);
                try self.open("(struct_literal", .{});
                const fields = self.exprs.sfv_pool.slice(node.fields);
                for (fields) |fid| {
                    const field = self.exprs.StructFieldValue.get(fid);
                    try self.open("(field", .{});
                    if (!field.name.isNone())
                        try self.leaf("name=\"{s}\"", .{self.s(field.name.unwrap())})
                    else
                        try self.leaf("name=null", .{});
                    try self.open("(value", .{});
                    try self.printExpr(field.value);
                    try self.close();
                    try self.close();
                }
                try self.close();
            },
            .FunctionLit => {
                const node = self.exprs.get(.FunctionLit, id);
                try self.open("({s}", .{if (node.flags.is_proc) "procedure" else "function"});
                if (node.flags.is_async) try self.leaf("(async)", .{});
                if (node.flags.is_variadic) try self.leaf("(variadic)", .{});
                if (node.flags.is_extern) try self.leaf("(extern)", .{});
                if (!node.attrs.isNone()) try self.printAttrs(node.attrs);
                try self.printParams(node.params);
                if (!node.result_ty.isNone()) {
                    try self.open("(result", .{});
                    try self.printExpr(node.result_ty.unwrap());
                    try self.close();
                }
                if (!node.body.isNone()) {
                    try self.open("(body", .{});
                    try self.printExpr(node.body.unwrap());
                    try self.close();
                } else if (!node.raw_asm.isNone()) {
                    try self.leaf("(asm \"{s}\")", .{self.s(node.raw_asm.unwrap())});
                }
                try self.close();
            },
            .Block => {
                const node = self.exprs.get(.Block, id);
                try self.open("(block", .{});
                const stmts = self.stmts.stmt_pool.slice(node.items);
                for (stmts) |sid| try self.printStmt(sid);
                try self.close();
            },
            .ComptimeBlock => {
                const node = self.exprs.get(.ComptimeBlock, id);
                try self.open("(comptime_block", .{});
                try self.printExpr(node.block);
                try self.close();
            },
            .CodeBlock => {
                const node = self.exprs.get(.CodeBlock, id);
                try self.open("(code_block", .{});
                try self.printExpr(node.block);
                try self.close();
            },
            .AsyncBlock => {
                const node = self.exprs.get(.AsyncBlock, id);
                try self.open("(async_block", .{});
                try self.printExpr(node.body);
                try self.close();
            },
            .MlirBlock => {
                const node = self.exprs.get(.MlirBlock, id);
                try self.open("(mlir kind={s}", .{@tagName(node.kind)});
                try self.leaf("(text \"{s}\")", .{self.s(node.text)});
                const pieces = self.exprs.mlir_piece_pool.slice(node.pieces);
                try self.open("(pieces", .{});
                for (pieces) |pid| {
                    const piece = self.exprs.MlirPiece.get(pid);
                    switch (piece.kind) {
                        .literal => try self.leaf("(literal \"{s}\")", .{self.s(piece.text)}),
                        .splice => try self.leaf("(splice {s})", .{self.s(piece.text)}),
                    }
                }
                try self.close();
                try self.printExprRange("args", node.args);
                try self.close();
            },
            .Insert => {
                const node = self.exprs.get(.Insert, id);
                try self.open("(insert", .{});
                try self.printExpr(node.expr);
                try self.close();
            },
            .Return => {
                const node = self.exprs.get(.Return, id);
                try self.open("(return", .{});
                if (!node.value.isNone()) {
                    try self.open("(value", .{});
                    try self.printExpr(node.value.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .If => {
                const node = self.exprs.get(.If, id);
                try self.open("(if", .{});
                try self.open("(cond", .{});
                try self.printExpr(node.cond);
                try self.close();
                try self.open("(then", .{});
                try self.printExpr(node.then_block);
                try self.close();
                if (!node.else_block.isNone()) {
                    try self.open("(else", .{});
                    try self.printExpr(node.else_block.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .While => {
                const node = self.exprs.get(.While, id);
                try self.open("(while is_pattern={})", .{node.is_pattern});
                if (!node.label.isNone()) try self.leaf("label=\"{s}\"", .{self.s(node.label.unwrap())});
                if (!node.pattern.isNone()) {
                    try self.open("(pattern", .{});
                    try self.printPattern(node.pattern.unwrap());
                    try self.close();
                }
                if (!node.cond.isNone()) {
                    try self.open("(cond", .{});
                    try self.printExpr(node.cond.unwrap());
                    try self.close();
                }
                try self.open("(body", .{});
                try self.printExpr(node.body);
                try self.close();
                try self.close();
            },
            .For => {
                const node = self.exprs.get(.For, id);
                try self.open("(for", .{});
                try self.open("(pattern", .{});
                try self.printPattern(node.pattern);
                try self.close();
                try self.open("(iterable", .{});
                try self.printExpr(node.iterable);
                try self.close();
                try self.open("(body", .{});
                try self.printExpr(node.body);
                try self.close();
                if (!node.label.isNone()) try self.leaf("label=\"{s}\"", .{self.s(node.label.unwrap())});
                try self.close();
            },
            .Match => {
                const node = self.exprs.get(.Match, id);
                try self.open("(match", .{});
                try self.open("(expr", .{});
                try self.printExpr(node.expr);
                try self.close();
                const arms = self.exprs.arm_pool.slice(node.arms);
                for (arms) |aid| {
                    const arm = self.exprs.MatchArm.get(aid);
                    try self.open("(arm", .{});
                    try self.open("(pattern", .{});
                    try self.printPattern(arm.pattern);
                    try self.close();
                    if (!arm.guard.isNone()) {
                        try self.open("(guard", .{});
                        try self.printExpr(arm.guard.unwrap());
                        try self.close();
                    }
                    try self.open("(body", .{});
                    try self.printExpr(arm.body);
                    try self.close();
                    try self.close();
                }
                try self.close();
            },
            .Break => {
                const node = self.exprs.get(.Break, id);
                try self.open("(break", .{});
                if (!node.label.isNone()) try self.leaf("label=\"{s}\"", .{self.s(node.label.unwrap())});
                if (!node.value.isNone()) {
                    try self.open("(value", .{});
                    try self.printExpr(node.value.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .Continue => {
                _ = self.exprs.get(.Continue, id);
                try self.leaf("(continue)", .{});
            },
            .Unreachable => {
                _ = self.exprs.get(.Unreachable, id);
                try self.leaf("(unreachable)", .{});
            },
            .NullLit => {
                _ = self.exprs.get(.NullLit, id);
                try self.leaf("(null)", .{});
            },
            .UndefLit => {
                _ = self.exprs.get(.UndefLit, id);
                try self.leaf("(undef)", .{});
            },
            .Defer => {
                const node = self.exprs.get(.Defer, id);
                try self.open("(defer", .{});
                try self.printExpr(node.expr);
                try self.close();
            },
            .ErrDefer => {
                const node = self.exprs.get(.ErrDefer, id);
                try self.open("(errdefer", .{});
                try self.printExpr(node.expr);
                try self.close();
            },
            .ErrUnwrap => {
                const node = self.exprs.get(.ErrUnwrap, id);
                try self.open("(error_unwrap", .{});
                try self.printExpr(node.expr);
                try self.close();
            },
            .OptionalUnwrap => {
                const node = self.exprs.get(.OptionalUnwrap, id);
                try self.open("(optional_unwrap", .{});
                try self.printExpr(node.expr);
                try self.close();
            },
            .Await => {
                const node = self.exprs.get(.Await, id);
                try self.open("(await", .{});
                try self.printExpr(node.expr);
                try self.close();
            },
            .Closure => {
                const node = self.exprs.get(.Closure, id);
                try self.open("(closure", .{});
                try self.printParams(node.params);
                if (!node.result_ty.isNone()) {
                    try self.open("(result", .{});
                    try self.printExpr(node.result_ty.unwrap());
                    try self.close();
                }
                try self.open("(body", .{});
                try self.printExpr(node.body);
                try self.close();
                try self.close();
            },
            .Cast => {
                const node = self.exprs.get(.Cast, id);
                try self.open("(cast kind={s}", .{@tagName(node.kind)});
                try self.open("(expr", .{});
                try self.printExpr(node.expr);
                try self.close();
                try self.open("(type", .{});
                try self.printExpr(node.ty);
                try self.close();
                try self.close();
            },
            .Catch => {
                const node = self.exprs.get(.Catch, id);
                try self.open("(catch", .{});
                try self.open("(expr", .{});
                try self.printExpr(node.expr);
                try self.close();
                if (!node.binding_name.isNone()) try self.leaf("binding=\"{s}\"", .{self.s(node.binding_name.unwrap())});
                try self.open("(handler", .{});
                try self.printExpr(node.handler);
                try self.close();
                try self.close();
            },
            .Import => {
                const node = self.exprs.get(.Import, id);
                try self.open("(import", .{});
                try self.open("(path", .{});
                try self.leaf("\"{s}\"", .{self.s(node.path)});
                try self.close();
                try self.close();
            },
            .TypeOf => {
                const node = self.exprs.get(.TypeOf, id);
                try self.open("(typeof", .{});
                try self.open("(expr", .{});
                try self.printExpr(node.expr);
                try self.close();
                try self.close();
            },
            .TupleType => {
                const node = self.exprs.get(.TupleType, id);
                try self.printExprRange("tuple_type", node.elems);
            },
            .ArrayType => {
                const node = self.exprs.get(.ArrayType, id);
                try self.open("(array_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(node.elem);
                try self.close();
                try self.open("(size", .{});
                try self.printExpr(node.size);
                try self.close();
                try self.close();
            },
            .DynArrayType => {
                const node = self.exprs.get(.DynArrayType, id);
                try self.open("(dyn_array_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(node.elem);
                try self.close();
                try self.close();
            },
            .MapType => {
                const node = self.exprs.get(.MapType, id);
                try self.open("(map_type", .{});
                try self.open("(key", .{});
                try self.printExpr(node.key);
                try self.close();
                try self.open("(value", .{});
                try self.printExpr(node.value);
                try self.close();
                try self.close();
            },
            .SliceType => {
                const node = self.exprs.get(.SliceType, id);
                try self.open("(slice_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(node.elem);
                try self.close();
                try self.close();
            },
            .OptionalType => {
                const node = self.exprs.get(.OptionalType, id);
                try self.open("(optional_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(node.elem);
                try self.close();
                try self.close();
            },
            .ErrorSetType => {
                const node = self.exprs.get(.ErrorSetType, id);
                try self.open("(error_set_type", .{});
                try self.open("(err", .{});
                try self.printExpr(node.err);
                try self.close();
                try self.open("(value", .{});
                try self.printExpr(node.value);
                try self.close();
                try self.close();
            },
            .ErrorType => {
                const node = self.exprs.get(.ErrorType, id);
                try self.open("(error_type", .{});
                const fields = self.exprs.vfield_pool.slice(node.fields);
                for (fields) |vid| try self.printVariantField(vid);
                try self.close();
            },
            .StructType => {
                const node = self.exprs.get(.StructType, id);
                try self.open("(struct_type is_extern={})", .{node.is_extern});
                if (!node.attrs.isNone()) try self.printAttrs(node.attrs);
                const fields = self.exprs.sfield_pool.slice(node.fields);
                for (fields) |fid| try self.printStructField(fid);
                try self.close();
            },
            .EnumType => {
                const node = self.exprs.get(.EnumType, id);
                try self.open("(enum_type is_extern={})", .{node.is_extern});
                if (!node.attrs.isNone()) try self.printAttrs(node.attrs);
                if (!node.discriminant.isNone()) {
                    try self.open("(discriminant", .{});
                    try self.printExpr(node.discriminant.unwrap());
                    try self.close();
                }
                const fields = self.exprs.efield_pool.slice(node.fields);
                for (fields) |eid| {
                    const field = self.exprs.EnumField.get(eid);
                    try self.open("(field name=\"{s}\"", .{self.s(field.name)});
                    if (!field.attrs.isNone()) try self.printAttrs(field.attrs);
                    if (!field.value.isNone()) {
                        try self.open("(value", .{});
                        try self.printExpr(field.value.unwrap());
                        try self.close();
                    }
                    try self.close();
                }
                try self.close();
            },
            .VariantType => {
                const node = self.exprs.get(.VariantType, id);
                try self.open("(variant_type", .{});
                const fields = self.exprs.vfield_pool.slice(node.fields);
                for (fields) |vid| try self.printVariantField(vid);
                try self.close();
            },
            .UnionType => {
                const node = self.exprs.get(.UnionType, id);
                try self.open("(union_type is_extern={})", .{node.is_extern});
                if (!node.attrs.isNone()) try self.printAttrs(node.attrs);
                const fields = self.exprs.sfield_pool.slice(node.fields);
                for (fields) |fid| try self.printStructField(fid);
                try self.close();
            },
            .PointerType => {
                const node = self.exprs.get(.PointerType, id);
                try self.open("(pointer_type is_const={})", .{node.is_const});
                try self.open("(elem", .{});
                try self.printExpr(node.elem);
                try self.close();
                try self.close();
            },
            .SimdType => {
                const node = self.exprs.get(.SimdType, id);
                try self.open("(simd_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(node.elem);
                try self.close();
                try self.open("(lanes", .{});
                try self.printExpr(node.lanes);
                try self.close();
                try self.close();
            },
            .ComplexType => {
                const node = self.exprs.get(.ComplexType, id);
                try self.open("(complex_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(node.elem);
                try self.close();
                try self.close();
            },
            .TensorType => {
                const node = self.exprs.get(.TensorType, id);
                try self.open("(tensor_type", .{});
                try self.open("(elem", .{});
                try self.printExpr(node.elem);
                try self.close();
                try self.printExprRange("shape", node.shape);
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

    fn printExprRange(self: *AstPrinter, comptime name: []const u8, r: RangeOf(ExprId)) anyerror!void {
        try self.open("(" ++ name, .{});
        const ids = self.exprs.expr_pool.slice(r);
        for (ids) |eid| try self.printExpr(eid);
        try self.close();
    }

    fn printAttrs(self: *AstPrinter, opt_r: OptRangeAttr) anyerror!void {
        if (opt_r.isNone()) return;
        const r = opt_r.asRange();
        const attrs = self.exprs.attr_pool.slice(r);
        if (attrs.len == 0) return;

        try self.open("(attributes", .{});
        for (attrs) |aid| {
            const attr = self.exprs.Attribute.get(aid);
            if (attr.value.isNone()) {
                try self.leaf("(attr name=\"{s}\")", .{self.s(attr.name)});
            } else {
                try self.open("(attr name=\"{s}\"", .{self.s(attr.name)});
                try self.open("(value", .{});
                try self.printExpr(attr.value.unwrap());
                try self.close();
                try self.close();
            }
        }
        try self.close();
    }

    fn printParams(self: *AstPrinter, r: RangeOf(ParamId)) anyerror!void {
        const params = self.exprs.param_pool.slice(r);
        for (params) |pid| {
            const param = self.exprs.Param.get(pid);
            try self.open("(param", .{});
            if (!param.attrs.isNone()) try self.printAttrs(param.attrs);
            if (param.is_comptime) try self.leaf("(comptime)", .{});
            if (!param.pat.isNone()) {
                try self.open("(pattern", .{});
                try self.printPattern(param.pat.unwrap());
                try self.close();
            }
            if (!param.ty.isNone()) {
                try self.open("(type", .{});
                try self.printExpr(param.ty.unwrap());
                try self.close();
            }
            if (!param.value.isNone()) {
                try self.open("(value", .{});
                try self.printExpr(param.value.unwrap());
                try self.close();
            }
            try self.close();
        }
    }

    fn printStructField(self: *AstPrinter, id: StructFieldId) anyerror!void {
        const field = self.exprs.StructField.get(id);
        try self.open("(field name=\"{s}\"", .{self.s(field.name)});
        if (!field.attrs.isNone()) try self.printAttrs(field.attrs);
        try self.open("(type", .{});
        try self.printExpr(field.ty);
        try self.close();
        if (!field.value.isNone()) {
            try self.open("(value", .{});
            try self.printExpr(field.value.unwrap());
            try self.close();
        }
        try self.close();
    }

    fn printVariantField(self: *AstPrinter, id: VariantFieldId) anyerror!void {
        const field = self.exprs.VariantField.get(id);
        try self.open("(field name=\"{s}\"", .{self.s(field.name)});
        if (!field.attrs.isNone()) try self.printAttrs(field.attrs);
        switch (field.payload_kind) {
            .none => {},
            .tuple => {
                std.debug.assert(!field.payload_elems.isNone());
                try self.printExprRange("tuple", field.payload_elems.asRange());
            },
            .@"struct" => {
                std.debug.assert(!field.payload_fields.isNone());
                try self.open("(struct", .{});
                const payload_fields = self.exprs.sfield_pool.slice(field.payload_fields.asRange());
                for (payload_fields) |fid| try self.printStructField(fid);
                try self.close();
            },
        }
        if (!field.value.isNone()) {
            try self.open("(value", .{});
            try self.printExpr(field.value.unwrap());
            try self.close();
        }
        try self.close();
    }

    pub fn printPattern(self: *AstPrinter, id: PatternId) anyerror!void {
        const kind = self.pats.index.kinds.items[id.toRaw()];
        switch (kind) {
            .Wildcard => try self.leaf("(wildcard)", .{}),
            .Literal => {
                const node = self.pats.get(.Literal, id);
                try self.open("(literal", .{});
                try self.printExpr(node.expr);
                try self.close();
            },
            .Path => {
                const node = self.pats.get(.Path, id);
                try self.open("(path", .{});
                const segs = self.pats.seg_pool.slice(node.segments);
                for (segs) |sid| {
                    const seg = self.pats.PathSeg.get(sid);
                    try self.leaf("(seg \"{s}\" by_ref={} is_mut={})", .{ self.s(seg.name), seg.by_ref, seg.is_mut });
                }
                try self.close();
            },
            .Binding => {
                const node = self.pats.get(.Binding, id);
                try self.leaf("(binding name=\"{s}\" by_ref={} is_mut={})", .{ self.s(node.name), node.by_ref, node.is_mut });
            },
            .Tuple => {
                const node = self.pats.get(.Tuple, id);
                try self.open("(tuple", .{});
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems) |pid| try self.printPattern(pid);
                try self.close();
            },
            .Slice => {
                const node = self.pats.get(.Slice, id);
                try self.open("(slice has_rest={} rest_index={})", .{ node.has_rest, node.rest_index });
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems) |pid| try self.printPattern(pid);
                if (!node.rest_binding.isNone()) {
                    try self.open("(rest", .{});
                    try self.printPattern(node.rest_binding.unwrap());
                    try self.close();
                }
                try self.close();
            },
            .Struct => {
                const node = self.pats.get(.Struct, id);
                try self.open("(struct has_rest={})", .{node.has_rest});
                try self.printPatternPath(node.path);
                const fields = self.pats.field_pool.slice(node.fields);
                for (fields) |fid| try self.printPatternField(fid);
                try self.close();
            },
            .VariantTuple => {
                const node = self.pats.get(.VariantTuple, id);
                try self.open("(variant_tuple", .{});
                try self.printPatternPath(node.path);
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems) |pid| try self.printPattern(pid);
                try self.close();
            },
            .VariantStruct => {
                const node = self.pats.get(.VariantStruct, id);
                try self.open("(variant_struct has_rest={})", .{node.has_rest});
                try self.printPatternPath(node.path);
                const fields = self.pats.field_pool.slice(node.fields);
                for (fields) |fid| try self.printPatternField(fid);
                try self.close();
            },
            .Range => {
                const node = self.pats.get(.Range, id);
                try self.open("(range inclusive_right={})", .{node.inclusive_right});
                if (!node.start.isNone()) try self.printExpr(node.start.unwrap());
                if (!node.end.isNone()) try self.printExpr(node.end.unwrap());
                try self.close();
            },
            .Or => {
                const node = self.pats.get(.Or, id);
                try self.open("(or", .{});
                const alts = self.pats.pat_pool.slice(node.alts);
                for (alts) |pid| try self.printPattern(pid);
                try self.close();
            },
            .At => {
                const node = self.pats.get(.At, id);
                try self.open("(at binder=\"{s}\"", .{self.s(node.binder)});
                try self.printPattern(node.pattern);
                try self.close();
            },
        }
    }

    fn printPatternPath(self: *AstPrinter, path: RangeOf(PathSegId)) anyerror!void {
        const segs = self.pats.seg_pool.slice(path);
        if (segs.len == 0) return;
        try self.open("(path", .{});
        for (segs) |sid| {
            const seg = self.pats.PathSeg.get(sid);
            try self.leaf("(seg \"{s}\" by_ref={} is_mut={})", .{ self.s(seg.name), seg.by_ref, seg.is_mut });
        }
        try self.close();
    }

    fn printPatternField(self: *AstPrinter, id: PatFieldId) anyerror!void {
        const field = self.pats.StructField.get(id);
        try self.open("(field name=\"{s}\"", .{self.s(field.name)});
        try self.printPattern(field.pattern);
        try self.close();
    }
};

pub const CodePrinter = struct {
    writer: *std.io.Writer,
    indent: usize = 0,
    needs_indent: bool = true,

    exprs: *const ExprStore,
    stmts: *const StmtStore,
    pats: *const PatternStore,

    pub fn init(writer: anytype, exprs: *const ExprStore, stmts: *const StmtStore, pats: *const PatternStore) CodePrinter {
        return .{ .writer = writer, .exprs = exprs, .stmts = stmts, .pats = pats };
    }

    fn ws(self: *CodePrinter) anyerror!void {
        if (!self.needs_indent) return;
        var i: usize = 0;
        while (i < self.indent) : (i += 1) try self.writer.writeByte(' ');
        self.needs_indent = false;
    }

    fn newline(self: *CodePrinter) anyerror!void {
        try self.writer.writeByte('\n');
        self.needs_indent = true;
    }

    fn printf(self: *CodePrinter, comptime fmt: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(fmt, args);
    }

    inline fn s(self: *const CodePrinter, id: StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    pub fn printUnit(self: *CodePrinter, unit: *const Unit) anyerror!void {
        if (!unit.package_name.isNone()) {
            try self.printf("package {s}", .{self.s(unit.package_name.unwrap())});
            try self.newline();
            try self.newline();
        }

        const decl_ids = self.exprs.decl_pool.slice(unit.decls);
        for (decl_ids, 0..) |did, i| {
            if (i > 0) {
                try self.newline();
                try self.newline();
            }
            try self.printDecl(did);
        }
        try self.newline();
        try self.writer.flush();
    }

    fn printDecl(self: *CodePrinter, id: DeclId) anyerror!void {
        const row = self.exprs.Decl.get(id);

        if (!row.pattern.isNone()) {
            try self.printPattern(row.pattern.unwrap());
        }

        if (!row.ty.isNone()) {
            try self.printf(": ", .{});
            try self.printExpr(row.ty.unwrap());
            if (row.flags.is_const) {
                try self.printf(" : ", .{});
            } else {
                try self.printf(" = ", .{});
            }
        } else {
            if (row.flags.is_const) {
                try self.printf(" :: ", .{});
            } else {
                try self.printf(" := ", .{});
            }
        }
        try self.printExpr(row.value);
    }

    fn printStmt(self: *CodePrinter, id: StmtId) anyerror!void {
        const kind = self.stmts.index.kinds.items[id.toRaw()];
        try self.ws();
        return switch (kind) {
            .Expr => {
                const row = self.stmts.get(.Expr, id);
                try self.printExpr(row.expr);
            },
            .Decl => {
                const row = self.stmts.get(.Decl, id);
                try self.printDecl(row.decl);
            },
            .Assign => {
                const row = self.stmts.get(.Assign, id);
                try self.printExpr(row.left);
                try self.printf(" = ", .{});
                try self.printExpr(row.right);
            },
            .Insert => {
                const row = self.stmts.get(.Insert, id);
                try self.printf("insert ", .{});
                try self.printExpr(row.expr);
            },
            .Return => {
                const row = self.stmts.get(.Return, id);
                try self.printf("return", .{});
                if (!row.value.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(row.value.unwrap());
                }
            },
            .Break => {
                const row = self.stmts.get(.Break, id);
                try self.printf("break", .{});
                if (!row.label.isNone()) try self.printf(" :{s}", .{self.s(row.label.unwrap())});
                if (!row.value.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(row.value.unwrap());
                }
            },
            .Continue => {
                _ = self.stmts.get(.Continue, id);
                try self.printf("continue", .{});
            },
            .Unreachable => {
                _ = self.stmts.get(.Unreachable, id);
                try self.printf("unreachable", .{});
            },
            .Defer => {
                const row = self.stmts.get(.Defer, id);
                try self.printf("defer ", .{});
                try self.printExpr(row.expr);
            },
            .ErrDefer => {
                const row = self.stmts.get(.ErrDefer, id);
                try self.printf("errdefer ", .{});
                try self.printExpr(row.expr);
            },
        };
    }

    pub fn printExpr(self: *CodePrinter, id: ExprId) anyerror!void {
        const kind = self.exprs.index.kinds.items[id.toRaw()];
        switch (kind) {
            .Literal => {
                const node = self.exprs.get(.Literal, id);
                switch (node.kind) {
                    .int => {
                        const info = node.data.int;
                        try self.printf("{s}", .{self.s(info.text)});
                    },
                    .float => {
                        const info = node.data.float;
                        try self.printf("{s}", .{self.s(info.text)});
                    },
                    .imaginary => {
                        const info = node.data.imaginary;
                        try self.printf("{s}i", .{self.s(info.text)});
                    },
                    .string => {
                        const sid = node.data.string;
                        const text = self.s(sid);
                        try self.printf("\"", .{});
                        try std.zig.stringEscape(text, self.writer);
                        try self.printf("\"", .{});
                    },
                    .bool => try self.printf("{}", .{node.data.bool}),
                    .char => {
                        const char_val: u8 = @truncate(node.data.char);
                        try self.printf("'{c}'", .{char_val});
                    },
                }
            },
            .Ident => {
                const node = self.exprs.get(.Ident, id);
                try self.printf("{s}", .{self.s(node.name)});
            },
            .Unary => {
                const node = self.exprs.get(.Unary, id);
                const op_str = switch (node.op) {
                    .pos => "+",
                    .neg => "-",
                    .address_of => "&",
                    .logical_not => "!",
                };
                try self.printf("{s}", .{op_str});
                try self.printExpr(node.expr);
            },
            .Binary => {
                const node = self.exprs.get(.Binary, id);
                try self.printExpr(node.left);
                const op_str = switch (node.op) {
                    .add => "+",
                    .sub => "-",
                    .mul => "*",
                    .div => "/",
                    .mod => "%",
                    .shl => "<<",
                    .shr => ">>",
                    .bit_and => "&",
                    .bit_or => "|",
                    .bit_xor => "^",
                    .eq => "==",
                    .neq => "!=",
                    .lt => "<",
                    .lte => "<=",
                    .gt => ">",
                    .gte => ">=",
                    .logical_and => "and",
                    .logical_or => "or",
                    .@"orelse" => "orelse",
                };
                if (node.wrap) {
                    try self.printf(" {s}w ", .{op_str});
                } else if (node.saturate) {
                    try self.printf(" {s}s ", .{op_str});
                } else {
                    try self.printf(" {s} ", .{op_str});
                }
                try self.printExpr(node.right);
            },
            .Range => {
                const node = self.exprs.get(.Range, id);
                if (!node.start.isNone()) try self.printExpr(node.start.unwrap());
                if (node.inclusive_right) {
                    try self.printf("..=", .{});
                } else {
                    try self.printf("..", .{});
                }
                if (!node.end.isNone()) try self.printExpr(node.end.unwrap());
            },
            .Deref => {
                const node = self.exprs.get(.Deref, id);
                try self.printExpr(node.expr);
                try self.printf(".*", .{});
            },
            .ArrayLit => {
                const node = self.exprs.get(.ArrayLit, id);
                try self.printf("[", .{});
                const elems = self.exprs.expr_pool.slice(node.elems);
                for (elems, 0..) |el, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printExpr(el);
                }
                try self.printf("]", .{});
            },
            .TupleLit => {
                const node = self.exprs.get(.TupleLit, id);
                try self.printf("(", .{});
                const elems = self.exprs.expr_pool.slice(node.elems);
                for (elems, 0..) |el, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printExpr(el);
                }
                try self.printf(")", .{});
            },
            .MapLit => {
                const node = self.exprs.get(.MapLit, id);
                try self.printf("[", .{});
                const entries = self.exprs.kv_pool.slice(node.entries);
                for (entries, 0..) |kv_id, i| {
                    if (i > 0) try self.printf(", ", .{});
                    const kv = self.exprs.KeyValue.get(kv_id);
                    try self.printExpr(kv.key);
                    try self.printf(": ", .{});
                    try self.printExpr(kv.value);
                }
                try self.printf("]", .{});
            },
            .Call => {
                const node = self.exprs.get(.Call, id);
                try self.printExpr(node.callee);
                try self.printf("(", .{});
                const args = self.exprs.expr_pool.slice(node.args);
                for (args, 0..) |arg, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printExpr(arg);
                }
                try self.printf(")", .{});
            },
            .IndexAccess => {
                const node = self.exprs.get(.IndexAccess, id);
                try self.printExpr(node.collection);
                try self.printf("[", .{});
                try self.printExpr(node.index);
                try self.printf("]", .{});
            },
            .FieldAccess => {
                const node = self.exprs.get(.FieldAccess, id);
                try self.printExpr(node.parent);
                try self.printf(".{s}", .{self.s(node.field)});
            },
            .StructLit => {
                const node = self.exprs.get(.StructLit, id);
                if (!node.ty.isNone()) {
                    try self.printExpr(node.ty.unwrap());
                }
                try self.printf(" {{", .{});
                const fields = self.exprs.sfv_pool.slice(node.fields);
                for (fields, 0..) |fid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    const field = self.exprs.StructFieldValue.get(fid);
                    if (!field.name.isNone()) {
                        try self.printf("{s}: ", .{self.s(field.name.unwrap())});
                    }
                    try self.printExpr(field.value);
                }
                try self.printf("}}", .{});
            },
            .FunctionLit => {
                const node = self.exprs.get(.FunctionLit, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.flags.is_async) try self.printf("async ", .{});
                if (node.flags.is_extern) try self.printf("extern ", .{});
                if (node.flags.is_proc) {
                    try self.printf("proc", .{});
                } else {
                    try self.printf("fn", .{});
                }

                try self.printf("(", .{});
                try self.printParams(node.params);
                try self.printf(")", .{});

                if (!node.result_ty.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.result_ty.unwrap());
                }
                if (!node.body.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.body.unwrap());
                } else if (!node.raw_asm.isNone()) {
                    try self.printf(" asm {s}", .{self.s(node.raw_asm.unwrap())});
                }
            },
            .Block => {
                const node = self.exprs.get(.Block, id);
                try self.printf("{{", .{});
                self.indent += 4;
                const stmts = self.stmts.stmt_pool.slice(node.items);
                for (stmts) |sid| {
                    try self.newline();
                    try self.printStmt(sid);
                }
                self.indent -= 4;
                try self.newline();
                try self.printf("}}", .{});
            },
            .ComptimeBlock => {
                const node = self.exprs.get(.ComptimeBlock, id);
                try self.printf("comptime ", .{});
                try self.printExpr(node.block);
            },
            .CodeBlock => {
                const node = self.exprs.get(.CodeBlock, id);
                try self.printf("code ", .{});
                try self.printExpr(node.block);
            },
            .AsyncBlock => {
                const node = self.exprs.get(.AsyncBlock, id);
                try self.printf("async ", .{});
                try self.printExpr(node.body);
            },
            .MlirBlock => {
                const node = self.exprs.get(.MlirBlock, id);
                const k = switch (node.kind) {
                    .Operation => " op",
                    .Attribute => " attribute",
                    .Type => " type",
                    .Module => "",
                };
                try self.printf("mlir{s}", .{k});
                const args = self.exprs.expr_pool.slice(node.args);
                if (args.len > 0) {
                    try self.printf("(", .{});
                    for (args, 0..) |arg, i| {
                        if (i > 0) try self.printf(", ", .{});
                        try self.printExpr(arg);
                    }
                    try self.printf(")", .{});
                }
                try self.printf(" {{ {s} }}", .{self.s(node.text)});
            },
            .Insert => {
                const node = self.exprs.get(.Insert, id);
                try self.printf("insert ", .{});
                try self.printExpr(node.expr);
            },
            .Return => {
                const node = self.exprs.get(.Return, id);
                try self.printf("return", .{});
                if (!node.value.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.value.unwrap());
                }
            },
            .If => {
                const node = self.exprs.get(.If, id);
                try self.printf("if ", .{});
                try self.printExpr(node.cond);
                try self.printf(" ", .{});
                try self.printExpr(node.then_block);
                if (!node.else_block.isNone()) {
                    try self.printf(" else ", .{});
                    try self.printExpr(node.else_block.unwrap());
                }
            },
            .While => {
                const node = self.exprs.get(.While, id);
                if (!node.label.isNone()) try self.printf("{s}: ", .{self.s(node.label.unwrap())});
                try self.printf("while ", .{});
                if (node.is_pattern) {
                    try self.printf("is ", .{});
                    if (!node.pattern.isNone()) {
                        try self.printPattern(node.pattern.unwrap());
                        try self.printf(" := ", .{});
                    }
                }
                if (!node.cond.isNone()) {
                    try self.printExpr(node.cond.unwrap());
                }
                try self.printf(" ", .{});
                try self.printExpr(node.body);
            },
            .For => {
                const node = self.exprs.get(.For, id);
                if (!node.label.isNone()) try self.printf("{s}: ", .{self.s(node.label.unwrap())});
                try self.printf("for ", .{});
                try self.printPattern(node.pattern);
                try self.printf(" in ", .{});
                try self.printExpr(node.iterable);
                try self.printf(" ", .{});
                try self.printExpr(node.body);
            },
            .Match => {
                const node = self.exprs.get(.Match, id);
                try self.printf("match ", .{});
                try self.printExpr(node.expr);
                try self.printf(" {{", .{});
                const arms = self.exprs.arm_pool.slice(node.arms);
                for (arms, 0..) |aid, i| {
                    if (i > 0) try self.printf(",", .{});
                    const arm = self.exprs.MatchArm.get(aid);
                    try self.newline();
                    self.indent += 4;
                    try self.ws();
                    try self.printPattern(arm.pattern);
                    if (!arm.guard.isNone()) {
                        try self.printf(" if ", .{});
                        try self.printExpr(arm.guard.unwrap());
                    }
                    try self.printf(" => ", .{});
                    try self.printExpr(arm.body);
                    self.indent -= 4;
                }
                try self.newline();
                try self.printf("}}", .{});
            },
            .Break => {
                const node = self.exprs.get(.Break, id);
                try self.printf("break", .{});
                if (!node.label.isNone()) try self.printf(" :{s}", .{self.s(node.label.unwrap())});
                if (!node.value.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.value.unwrap());
                }
            },
            .Continue => {
                _ = self.exprs.get(.Continue, id);
                try self.printf("continue", .{});
            },
            .Unreachable => {
                _ = self.exprs.get(.Unreachable, id);
                try self.printf("unreachable", .{});
            },
            .NullLit => {
                _ = self.exprs.get(.NullLit, id);
                try self.printf("null", .{});
            },
            .UndefLit => {
                _ = self.exprs.get(.UndefLit, id);
                try self.printf("undefined", .{});
            },
            .Defer => {
                const node = self.exprs.get(.Defer, id);
                try self.printf("defer ", .{});
                try self.printExpr(node.expr);
            },
            .ErrDefer => {
                const node = self.exprs.get(.ErrDefer, id);
                try self.printf("errdefer ", .{});
                try self.printExpr(node.expr);
            },
            .ErrUnwrap => {
                const node = self.exprs.get(.ErrUnwrap, id);
                try self.printExpr(node.expr);
                try self.printf("!", .{});
            },
            .OptionalUnwrap => {
                const node = self.exprs.get(.OptionalUnwrap, id);
                try self.printExpr(node.expr);
                try self.printf("?", .{});
            },
            .Await => {
                const node = self.exprs.get(.Await, id);
                try self.printExpr(node.expr);
                try self.printf(".await ", .{});
            },
            .Closure => {
                const node = self.exprs.get(.Closure, id);
                try self.printf("|", .{});
                try self.printParams(node.params);
                try self.printf("|", .{});
                if (!node.result_ty.isNone()) {
                    try self.printf(" ", .{});
                    try self.printExpr(node.result_ty.unwrap());
                }
                try self.printf(" ", .{});
                try self.printExpr(node.body);
            },
            .Cast => {
                const node = self.exprs.get(.Cast, id);
                try self.printExpr(node.expr);
                switch (node.kind) {
                    .normal => {
                        try self.printf(".(", .{});
                        try self.printExpr(node.ty);
                        try self.printf(")", .{});
                    },
                    .bitcast => {
                        try self.printf(".^", .{});
                        try self.printExpr(node.ty);
                    },
                    .wrap => {
                        try self.printf(".%", .{});
                        try self.printExpr(node.ty);
                    },
                    .saturate => {
                        try self.printf(".|", .{});
                        try self.printExpr(node.ty);
                    },
                    .checked => {
                        try self.printf(".?", .{});
                        try self.printExpr(node.ty);
                    },
                }
            },
            .Catch => {
                const node = self.exprs.get(.Catch, id);
                try self.printExpr(node.expr);
                try self.printf(" catch ", .{});
                if (!node.binding_name.isNone()) {
                    try self.printf("|{s}| ", .{self.s(node.binding_name.unwrap())});
                }
                try self.printExpr(node.handler);
            },
            .Import => {
                const node = self.exprs.get(.Import, id);
                try self.printf("import ", .{});
                try self.printf("\"{s}\"", .{self.s(node.path)});
            },
            .TypeOf => {
                const node = self.exprs.get(.TypeOf, id);
                try self.printf("typeof(", .{});
                try self.printExpr(node.expr);
                try self.printf(")", .{});
            },
            .TupleType => {
                const node = self.exprs.get(.TupleType, id);
                try self.printf("(", .{});
                const elems = self.exprs.expr_pool.slice(node.elems);
                for (elems, 0..) |el, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printExpr(el);
                }
                try self.printf(")", .{});
            },
            .ArrayType => {
                const node = self.exprs.get(.ArrayType, id);
                try self.printf("[", .{});
                try self.printExpr(node.size);
                try self.printf("]", .{});
                try self.printExpr(node.elem);
            },
            .DynArrayType => {
                const node = self.exprs.get(.DynArrayType, id);
                try self.printf("[]", .{});
                try self.printExpr(node.elem);
            },
            .MapType => {
                const node = self.exprs.get(.MapType, id);
                try self.printf("[", .{});
                try self.printExpr(node.key);
                try self.printf(": ", .{});
                try self.printExpr(node.value);
                try self.printf("]", .{});
            },
            .SliceType => {
                const node = self.exprs.get(.SliceType, id);
                try self.printf("[]", .{});
                try self.printExpr(node.elem);
            },
            .OptionalType => {
                const node = self.exprs.get(.OptionalType, id);
                try self.printf("?", .{});
                try self.printExpr(node.elem);
            },
            .ErrorSetType => {
                const node = self.exprs.get(.ErrorSetType, id);
                try self.printExpr(node.err);
                try self.printf("!", .{});
                try self.printExpr(node.value);
            },
            .ErrorType => {
                const node = self.exprs.get(.ErrorType, id);
                try self.printf("error {{ ", .{});
                const fields = self.exprs.vfield_pool.slice(node.fields);
                if (fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printVariantField(fid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                }
                try self.printf("}}", .{});
            },
            .StructType => {
                const node = self.exprs.get(.StructType, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.is_extern) try self.printf("extern ", .{});
                try self.printf("struct {{", .{});
                const fields = self.exprs.sfield_pool.slice(node.fields);
                if (fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printStructField(fid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                }
                try self.printf("}}", .{});
            },
            .EnumType => {
                const node = self.exprs.get(.EnumType, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.is_extern) try self.printf("extern ", .{});
                try self.printf("enum", .{});
                if (!node.discriminant.isNone()) {
                    try self.printf("(", .{});
                    try self.printExpr(node.discriminant.unwrap());
                    try self.printf(")", .{});
                }
                try self.printf(" {{", .{});
                const fields = self.exprs.efield_pool.slice(node.fields);
                if (fields.len > 0) {
                    self.indent += 4;
                    for (fields) |eid| {
                        const field = self.exprs.EnumField.get(eid);
                        try self.newline();
                        try self.ws();
                        try self.printAttrs(field.attrs, .Before);
                        try self.printf("{s}", .{self.s(field.name)});
                        if (!field.value.isNone()) {
                            try self.printf(" = ", .{});
                            try self.printExpr(field.value.unwrap());
                        }
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                }
                try self.printf("}}", .{});
            },
            .VariantType => {
                const node = self.exprs.get(.VariantType, id);
                try self.printf("variant {{ ", .{});
                const fields = self.exprs.vfield_pool.slice(node.fields);
                if (fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printVariantField(fid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                }
                try self.printf("}}", .{});
            },
            .UnionType => {
                const node = self.exprs.get(.UnionType, id);
                try self.printAttrs(node.attrs, .Before);
                if (node.is_extern) try self.printf("extern ", .{});
                try self.printf("union {{", .{});
                const fields = self.exprs.sfield_pool.slice(node.fields);
                if (fields.len > 0) {
                    self.indent += 4;
                    for (fields) |fid| {
                        try self.newline();
                        try self.ws();
                        try self.printStructField(fid);
                        try self.printf(",", .{});
                    }
                    self.indent -= 4;
                    try self.newline();
                    try self.ws();
                }
                try self.printf("}}", .{});
            },
            .PointerType => {
                const node = self.exprs.get(.PointerType, id);
                try self.printf("*", .{});
                if (node.is_const) try self.printf("const ", .{});
                try self.printExpr(node.elem);
            },
            .SimdType => {
                const node = self.exprs.get(.SimdType, id);
                try self.printf("simd(", .{});
                try self.printExpr(node.lanes);
                try self.printf(", ", .{});
                try self.printExpr(node.elem);
                try self.printf(")", .{});
            },
            .ComplexType => {
                const node = self.exprs.get(.ComplexType, id);
                try self.printf("complex(", .{});
                try self.printExpr(node.elem);
                try self.printf(")", .{});
            },
            .TensorType => {
                const node = self.exprs.get(.TensorType, id);
                try self.printf("tensor(", .{});
                const shape = self.exprs.expr_pool.slice(node.shape);
                for (shape, 0..) |si, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printExpr(si);
                }
                try self.printf(", ", .{});
                try self.printExpr(node.elem);
                try self.printf(")", .{});
            },
            .TypeType => {
                _ = self.exprs.get(.TypeType, id);
                try self.printf("type", .{});
            },
            .AnyType => {
                _ = self.exprs.get(.AnyType, id);
                try self.printf("any", .{});
            },
            .NoreturnType => {
                _ = self.exprs.get(.NoreturnType, id);
                try self.printf("noreturn", .{});
            },
        }
    }

    fn printExprs(self: *CodePrinter, r: RangeOf(ExprId), sep: []const u8) anyerror!void {
        const ids = self.exprs.expr_pool.slice(r);
        for (ids, 0..) |eid, i| {
            if (i > 0) try self.printf("{s}", .{sep});
            try self.printExpr(eid);
        }
    }

    const AttrPos = enum { Before, After };
    fn printAttrs(self: *CodePrinter, opt_r: OptRangeAttr, pos: AttrPos) anyerror!void {
        if (opt_r.isNone()) return;
        const r = opt_r.asRange();
        const attrs = self.exprs.attr_pool.slice(r);
        if (attrs.len == 0) return;

        try self.printf("@[", .{});
        for (attrs, 0..) |aid, i| {
            if (i > 0) try self.printf(", ", .{});
            const attr = self.exprs.Attribute.get(aid);
            try self.ws();
            try self.printf("{s}", .{self.s(attr.name)});
            if (!attr.value.isNone()) {
                try self.printf(" = ", .{});
                try self.printExpr(attr.value.unwrap());
            }
            _ = pos;
            // switch (pos) {
            //     .Before => try self.newline(),
            //     .After => try self.printf(" ", .{}),
            // }
        }
        try self.printf("] ", .{});
    }

    fn printParams(self: *CodePrinter, r: RangeOf(ParamId)) anyerror!void {
        const params = self.exprs.param_pool.slice(r);
        for (params, 0..) |pid, i| {
            if (i > 0) try self.printf(", ", .{});
            const param = self.exprs.Param.get(pid);
            try self.printAttrs(param.attrs, .After);
            if (param.is_comptime) {
                try self.printf("comptime ", .{});
            }
            if (!param.pat.isNone()) {
                try self.printPattern(param.pat.unwrap());
            }
            if (!param.pat.isNone() and !param.ty.isNone()) {
                try self.printf(": ", .{});
            }
            if (!param.ty.isNone()) {
                try self.printExpr(param.ty.unwrap());
            }
            if (!param.value.isNone()) {
                try self.printf(" = ", .{});
                try self.printExpr(param.value.unwrap());
            }
        }
    }

    fn printStructField(self: *CodePrinter, id: StructFieldId) anyerror!void {
        const field = self.exprs.StructField.get(id);
        try self.printAttrs(field.attrs, .Before);
        try self.printf("{s}: ", .{self.s(field.name)});
        try self.printExpr(field.ty);
        if (!field.value.isNone()) {
            try self.printf(" = ", .{});
            try self.printExpr(field.value.unwrap());
        }
    }

    fn printVariantField(self: *CodePrinter, id: VariantFieldId) anyerror!void {
        const field = self.exprs.VariantField.get(id);
        try self.printAttrs(field.attrs, .Before);
        try self.printf("{s}", .{self.s(field.name)});
        switch (field.payload_kind) {
            .none => {},
            .tuple => {
                std.debug.assert(!field.payload_elems.isNone());
                try self.printf("(", .{});
                try self.printExprs(field.payload_elems.asRange(), ", ");
                try self.printf(")", .{});
            },
            .@"struct" => {
                std.debug.assert(!field.payload_fields.isNone());
                try self.printf(" {{", .{});
                const payload_fields = self.exprs.sfield_pool.slice(field.payload_fields.asRange());
                for (payload_fields, 0..) |fid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printStructField(fid);
                }
                try self.printf("}}", .{});
            },
        }
        if (!field.value.isNone()) {
            try self.printf(" = ", .{});
            try self.printExpr(field.value.unwrap());
        }
    }

    pub fn printPattern(self: *CodePrinter, id: PatternId) anyerror!void {
        const kind = self.pats.index.kinds.items[id.toRaw()];
        switch (kind) {
            .Wildcard => try self.printf("_", .{}),
            .Literal => {
                const node = self.pats.get(.Literal, id);
                try self.printExpr(node.expr);
            },
            .Path => {
                const node = self.pats.get(.Path, id);
                const segs = self.pats.seg_pool.slice(node.segments);
                for (segs, 0..) |sid, i| {
                    if (i > 0) try self.printf(".", .{});
                    const seg = self.pats.PathSeg.get(sid);
                    if (seg.by_ref) try self.printf("ref ", .{});
                    if (seg.is_mut) try self.printf("mut ", .{});
                    try self.printf("{s}", .{self.s(seg.name)});
                }
            },
            .Binding => {
                const node = self.pats.get(.Binding, id);
                if (node.by_ref) try self.printf("ref ", .{});
                if (node.is_mut) try self.printf("mut ", .{});
                try self.printf("{s}", .{self.s(node.name)});
            },
            .Tuple => {
                const node = self.pats.get(.Tuple, id);
                try self.printf("(", .{});
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems, 0..) |pid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printPattern(pid);
                }
                try self.printf(")", .{});
            },
            .Slice => {
                const node = self.pats.get(.Slice, id);
                try self.printf("[", .{});
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems, 0..) |pid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    if (node.has_rest and node.rest_index == i) {
                        try self.printf("..", .{});
                        if (!node.rest_binding.isNone()) {
                            try self.printPattern(node.rest_binding.unwrap());
                        }
                        if (i < elems.len) try self.printf(", ", .{});
                    }
                    try self.printPattern(pid);
                }
                try self.printf("]", .{});
            },
            .Struct => {
                const node = self.pats.get(.Struct, id);
                try self.printPatternPath(node.path);
                try self.printf(" {{", .{});
                const fields = self.pats.field_pool.slice(node.fields);
                for (fields, 0..) |fid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printPatternField(fid);
                }
                if (node.has_rest) {
                    if (fields.len > 0) try self.printf(", ", .{});
                    try self.printf("..", .{});
                }
                try self.printf("}}", .{});
            },
            .VariantTuple => {
                const node = self.pats.get(.VariantTuple, id);
                try self.printPatternPath(node.path);
                try self.printf("(", .{});
                const elems = self.pats.pat_pool.slice(node.elems);
                for (elems, 0..) |pid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printPattern(pid);
                }
                try self.printf(")", .{});
            },
            .VariantStruct => {
                const node = self.pats.get(.VariantStruct, id);
                try self.printPatternPath(node.path);
                try self.printf(" {{", .{});
                const fields = self.pats.field_pool.slice(node.fields);
                for (fields, 0..) |fid, i| {
                    if (i > 0) try self.printf(", ", .{});
                    try self.printPatternField(fid);
                }
                if (node.has_rest) {
                    if (fields.len > 0) try self.printf(", ", .{});
                    try self.printf("..", .{});
                }
                try self.printf("}}", .{});
            },
            .Range => {
                const node = self.pats.get(.Range, id);
                if (!node.start.isNone()) try self.printExpr(node.start.unwrap());
                if (node.inclusive_right) {
                    try self.printf("..=", .{});
                } else {
                    try self.printf("..", .{});
                }
                if (!node.end.isNone()) try self.printExpr(node.end.unwrap());
            },
            .Or => {
                const node = self.pats.get(.Or, id);
                const alts = self.pats.pat_pool.slice(node.alts);
                for (alts, 0..) |pid, i| {
                    if (i > 0) try self.printf(" | ", .{});
                    try self.printPattern(pid);
                }
            },
            .At => {
                const node = self.pats.get(.At, id);
                try self.printf("{s} @ ", .{self.s(node.binder)});
                try self.printPattern(node.pattern);
            },
        }
    }

    fn printPatternPath(self: *CodePrinter, path: RangeOf(PathSegId)) anyerror!void {
        const segs = self.pats.seg_pool.slice(path);
        for (segs, 0..) |sid, i| {
            if (i > 0) try self.printf(".", .{});
            const seg = self.pats.PathSeg.get(sid);
            try self.printf("{s}", .{self.s(seg.name)});
        }
    }

    fn printPatternField(self: *CodePrinter, id: PatFieldId) anyerror!void {
        const field = self.pats.StructField.get(id);
        try self.printf("{s}: ", .{self.s(field.name)});
        try self.printPattern(field.pattern);
    }
};

comptime {
    for (@typeInfo(ExprKind).@"enum".fields) |f| {
        _ = @field(Rows, f.name);
    }
    for (@typeInfo(StmtKind).@"enum".fields) |f| {
        _ = @field(StmtRows, f.name);
    }
    for (@typeInfo(PatternKind).@"enum".fields) |f| {
        _ = @field(PatRows, f.name);
    }
    std.debug.assert(@sizeOf(ExprId) == 4);
    std.debug.assert(@sizeOf(StmtId) == 4);
    std.debug.assert(@sizeOf(PatternId) == 4);
    std.debug.assert(@sizeOf(StrId) == 4);
    std.debug.assert(@sizeOf(LocId) == 4);
}
