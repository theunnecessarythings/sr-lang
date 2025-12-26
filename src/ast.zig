const std = @import("std");
const dod = @import("cst.zig");
const TypeInfo = @import("types.zig").TypeInfo;
const TypeStore = @import("types.zig").TypeStore;

// Re-exports
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

// Tags
pub const ExprTag = struct {};
pub const StmtTag = struct {};
pub const PatternTag = struct {};

// IDs
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

// Optional IDs
pub const OptExprId = SentinelIndex(ExprTag);
pub const OptStmtId = SentinelIndex(StmtTag);
pub const OptDeclId = SentinelIndex(Rows.Decl);
pub const OptParamId = SentinelIndex(Rows.Param);
pub const OptPatternId = SentinelIndex(PatternTag);

// Ranges
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

// Optional Ranges
pub const OptRangeExpr = OptRangeOf(ExprId);
pub const OptRangeStmt = OptRangeOf(StmtId);
pub const OptRangeDecl = OptRangeOf(DeclId);
pub const OptRangeAttr = OptRangeOf(AttributeId);
pub const OptRangeField = OptRangeOf(StructFieldId);
pub const OptRangePat = OptRangeOf(PatternId);
pub const OptRangeMethodPathSeg = OptRangeOf(MethodPathSegId);

// Enums
pub const LiteralKind = enum(u8) { int, float, bool, string, char, imaginary };
pub const UnaryOp = enum(u8) { pos, neg, address_of, logical_not };
pub const BinaryOp = enum(u8) { add, sub, mul, div, mod, shl, shr, bit_and, bit_or, bit_xor, eq, neq, lt, lte, gt, gte, logical_and, logical_or, @"orelse", contains };
pub const VariantPayloadKind = enum(u2) { none, tuple, @"struct" };
pub const ExprKind = enum(u16) { Literal, Ident, Unary, Binary, Range, Deref, ArrayLit, TupleLit, MapLit, Call, IndexAccess, FieldAccess, StructLit, FunctionLit, Block, ComptimeBlock, CodeBlock, AsyncBlock, MlirBlock, Insert, Return, If, While, For, Match, Break, Continue, Unreachable, NullLit, UndefLit, Defer, ErrDefer, ErrUnwrap, OptionalUnwrap, Await, Closure, Cast, Catch, Import, TypeOf, TupleType, ArrayType, DynArrayType, MapType, SliceType, OptionalType, ErrorSetType, ErrorType, StructType, EnumType, VariantType, UnionType, PointerType, SimdType, ComplexType, TensorType, TypeType, AnyType, NoreturnType };
pub const StmtKind = enum(u8) { Expr, Decl, Assign, Insert, Return, Break, Continue, Unreachable, Defer, ErrDefer };
pub const PatternKind = enum(u16) { Wildcard, Literal, Path, Binding, Tuple, Slice, Struct, VariantTuple, VariantStruct, Range, Or, At };

// Unit
pub const Unit = struct {
    decls: RangeDecl,
    package_name: OptStrId,
    package_loc: OptLocId,
    pub fn empty() Unit {
        return .{ .decls = .empty(), .package_name = .none(), .package_loc = .none() };
    }
};

// Row Definitions
pub const Rows = struct {
    pub const Literal = struct { kind: LiteralKind, data: LiteralValue, loc: LocId };
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
    pub const FnFlags = packed struct(u8) { is_proc: bool, is_async: bool, is_variadic: bool, is_extern: bool, is_test: bool, _pad: u3 = 0 };
    pub const FunctionLit = struct { params: RangeParam, result_ty: OptExprId, body: OptExprId, raw_asm: OptStrId, attrs: OptRangeAttr, flags: FnFlags, loc: LocId };
    pub const Block = struct { items: RangeStmt, loc: LocId };
    pub const ComptimeBlock = struct { block: ExprId, loc: LocId };
    pub const CodeBlock = struct { block: ExprId, loc: LocId };
    pub const AsyncBlock = struct { body: ExprId, loc: LocId };
    pub const MlirPiece = struct { kind: MlirPieceKind, text: StrId };
    pub const MlirBlock = struct { kind: MlirKind, text: StrId, pieces: RangeMlirPiece, args: RangeExpr, result_ty: OptExprId, loc: LocId };
    pub const Insert = struct { expr: ExprId, loc: LocId };
    pub const Return = struct { value: OptExprId, loc: LocId };
    pub const If = struct { cond: ExprId, then_block: ExprId, else_block: OptExprId, loc: LocId };
    pub const While = struct { cond: OptExprId, pattern: OptPatternId, body: ExprId, is_pattern: bool, label: OptStrId, loc: LocId };
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
    pub const Param = struct { pat: OptPatternId, ty: OptExprId, value: OptExprId, attrs: OptRangeAttr, is_comptime: bool, loc: LocId };
    pub const Attribute = struct { name: StrId, value: OptExprId, loc: LocId };
    pub const MethodPathSeg = struct { name: StrId, loc: LocId };
    pub const DeclFlags = struct { is_const: bool };
    pub const Decl = struct { pattern: OptPatternId, value: ExprId, ty: OptExprId, method_path: OptRangeMethodPathSeg, flags: DeclFlags, loc: LocId };
    pub const TupleType = struct { elems: RangeExpr, loc: LocId };
    pub const ArrayType = struct { elem: ExprId, size: ExprId, loc: LocId };
    pub const DynArrayType = struct { elem: ExprId, loc: LocId };
    pub const MapType = struct { key: ExprId, value: ExprId, loc: LocId };
    pub const SliceType = struct { elem: ExprId, is_const: bool, loc: LocId };
    pub const OptionalType = struct { elem: ExprId, loc: LocId };
    pub const ErrorSetType = struct { err: ExprId, value: ExprId, loc: LocId };
    pub const StructField = struct { name: StrId, ty: ExprId, value: OptExprId, attrs: OptRangeAttr, loc: LocId };
    pub const StructType = struct { fields: RangeField, is_extern: bool, attrs: OptRangeAttr, loc: LocId };
    pub const EnumField = struct { name: StrId, value: OptExprId, attrs: OptRangeAttr, loc: LocId };
    pub const EnumType = struct { fields: RangeEnumField, discriminant: OptExprId, is_extern: bool, attrs: OptRangeAttr, loc: LocId };
    pub const VariantField = struct { name: StrId, payload_kind: VariantPayloadKind, payload_elems: OptRangeExpr, payload_fields: OptRangeField, value: OptExprId, attrs: OptRangeAttr, loc: LocId };
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

pub const PatRows = struct {
    pub const Wildcard = struct { loc: LocId };
    pub const Literal = struct { expr: ExprId, loc: LocId };
    pub const PathSeg = struct { name: StrId, by_ref: bool, is_mut: bool, loc: LocId };
    pub const Path = struct { segments: RangePathSeg, loc: LocId };
    pub const Binding = struct { name: StrId, by_ref: bool, is_mut: bool, loc: LocId };
    pub const Tuple = struct { elems: RangePat, loc: LocId };
    pub const Slice = struct { elems: RangePat, has_rest: bool, rest_index: u32, rest_binding: OptPatternId, loc: LocId };
    pub const StructField = struct { name: StrId, pattern: PatternId, loc: LocId };
    pub const Struct = struct { path: RangePathSeg, fields: RangePatField, has_rest: bool, loc: LocId };
    pub const VariantTuple = struct { path: RangePathSeg, elems: RangePat, loc: LocId };
    pub const VariantStruct = struct { path: RangePathSeg, fields: RangePatField, has_rest: bool, loc: LocId };
    pub const Range = struct { start: OptExprId, end: OptExprId, inclusive_right: bool, loc: LocId };
    pub const Or = struct { alts: RangePat, loc: LocId };
    pub const At = struct { binder: StrId, pattern: PatternId, loc: LocId };
};

pub inline fn RowT(comptime K: ExprKind) type {
    return @field(Rows, @tagName(K));
}
pub inline fn StmtRowT(comptime K: StmtKind) type {
    return @field(StmtRows, @tagName(K));
}
pub inline fn PatRowT(comptime K: PatternKind) type {
    return @field(PatRows, @tagName(K));
}

pub const LiteralInt = struct { text: StrId, value: u128, base: u8, valid: bool };
pub const LiteralFloat = struct { text: StrId, value: f64, valid: bool };
pub const LiteralValue = union(enum) { none, bool: bool, char: u32, string: StrId, int: LiteralInt, float: LiteralFloat, imaginary: LiteralFloat };

// Stores
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
    pub fn kind(self: *const @This(), id: ExprId) ExprKind {
        return self.index.kinds.items[id.toRaw()];
    }
    pub fn add(self: *@This(), comptime K: ExprKind, row: RowT(K)) ExprId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        return self.index.newId(self.gpa, K, tbl.add(self.gpa, row).toRaw(), ExprId);
    }
    pub fn get(self: *@This(), comptime K: ExprKind, id: ExprId) RowT(K) {
        return @field(self, @tagName(K)).get(.{ .index = self.index.rows.items[id.toRaw()] });
    }
    pub fn addParam(self: *@This(), row: Rows.Param) ParamId {
        return self.Param.add(self.gpa, row);
    }
    pub fn addAttribute(self: *@This(), row: Rows.Attribute) AttributeId {
        return self.Attribute.add(self.gpa, row);
    }
    pub fn addMethodPathSeg(self: *@This(), row: Rows.MethodPathSeg) MethodPathSegId {
        return self.MethodPathSeg.add(self.gpa, row);
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
    pub fn add(self: *@This(), comptime K: StmtKind, row: StmtRowT(K)) StmtId {
        const tbl: *Table(StmtRowT(K)) = &@field(self, @tagName(K));
        return self.index.newId(self.gpa, K, tbl.add(self.gpa, row).toRaw(), StmtId);
    }
    pub fn get(self: *@This(), comptime K: StmtKind, id: StmtId) StmtRowT(K) {
        return @field(self, @tagName(K)).get(.{ .index = self.index.rows.items[id.toRaw()] });
    }
    pub fn kind(self: *StmtStore, id: StmtId) StmtKind {
        return self.index.kinds.items[id.toRaw()];
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
    pub fn kind(self: *@This(), id: PatternId) PatternKind {
        return self.index.kinds.items[id.toRaw()];
    }
    pub fn add(self: *@This(), comptime K: PatternKind, row: PatRowT(K)) PatternId {
        const tbl: *Table(PatRowT(K)) = &@field(self, @tagName(K));
        return self.index.newId(self.gpa, K, tbl.add(self.gpa, row).toRaw(), PatternId);
    }
    pub fn get(self: *@This(), comptime K: PatternKind, id: PatternId) PatRowT(K) {
        return @field(self, @tagName(K)).get(.{ .index = self.index.rows.items[id.toRaw()] });
    }
};

pub const Ast = struct {
    arena: *std.heap.ArenaAllocator,
    backing_gpa: std.mem.Allocator,
    gpa: std.mem.Allocator,
    file_id: usize,
    unit: Unit,
    exprs: ExprStore,
    stmts: StmtStore,
    pats: PatternStore,
    type_info: TypeInfo,
    pub fn init(gpa: std.mem.Allocator, interner: *StringInterner, locs: *const LocStore, type_store: *TypeStore, file_id: usize) Ast {
        const arena = gpa.create(std.heap.ArenaAllocator) catch @panic("OOM");
        arena.* = std.heap.ArenaAllocator.init(gpa);
        const alloc = arena.allocator();
        return .{
            .arena = arena,
            .backing_gpa = gpa,
            .gpa = alloc,
            .file_id = file_id,
            .unit = .empty(),
            .exprs = .init(alloc, interner, locs),
            .stmts = .init(alloc),
            .pats = .init(alloc, interner),
            .type_info = .init(gpa, type_store),
        };
    }
    pub fn kind(self: *Ast, id: anytype) if (@TypeOf(id) == ExprId) ExprKind else if (@TypeOf(id) == PatternId) PatternKind else StmtKind {
        if (@TypeOf(id) == ExprId) return self.exprs.kind(id);
        if (@TypeOf(id) == PatternId) return self.pats.kind(id);
        return self.stmts.index.kinds.items[id.toRaw()];
    }
    pub fn deinit(self: *Ast) void {
        self.type_info.deinit();
        self.arena.deinit();
        self.backing_gpa.destroy(self.arena);
    }
};

// --- Printers ---

pub const AstPrinter = struct {
    writer: *std.io.Writer,
    indent: usize = 0,
    exprs: *ExprStore,
    stmts: *StmtStore,
    pats: *PatternStore,
    pub fn init(writer: anytype, exprs: *ExprStore, stmts: *StmtStore, pats: *PatternStore) AstPrinter {
        return .{ .writer = writer, .exprs = exprs, .stmts = stmts, .pats = pats };
    }
    fn ws(self: *AstPrinter) !void {
        var i: usize = 0;
        while (i < self.indent) : (i += 1) {
            try self.writer.writeByte(' ');
        }
    }
    fn open(self: *AstPrinter, comptime head: []const u8, args: anytype) !void {
        try self.ws();
        try self.writer.print(head, args);
        try self.writer.writeAll("\n");
        self.indent += 2;
    }
    fn openTag(self: *AstPrinter, head: []const u8) !void {
        try self.ws();
        try self.writer.writeByte('(');
        try self.writer.writeAll(head);
        try self.writer.writeAll("\n");
        self.indent += 2;
    }
    fn close(self: *AstPrinter) !void {
        self.indent -= 2;
        try self.ws();
        try self.writer.writeAll(")\n");
    }
    fn leaf(self: *AstPrinter, comptime fmt: []const u8, args: anytype) !void {
        try self.ws();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
    }
    inline fn s(self: *const AstPrinter, id: StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    pub fn printUnit(self: *AstPrinter, unit: *const Unit) !void {
        try self.open("(unit", .{});
        if (!unit.package_name.isNone()) try self.leaf("(package \"{s}\")", .{self.s(unit.package_name.unwrap())});
        for (self.exprs.decl_pool.slice(unit.decls)) |did| try self.printDecl(did);
        try self.close();
        try self.writer.flush();
    }
    fn printDecl(self: *AstPrinter, id: DeclId) !void {
        const row = self.exprs.Decl.get(id);
        try self.open("(decl is_const={})", .{row.flags.is_const});
        if (!row.pattern.isNone()) {
            try self.open("(pattern", .{});
            try self.printPattern(row.pattern.unwrap());
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
    fn printStmt(self: *AstPrinter, id: StmtId) !void {
        const kind = self.stmts.kind(id);
        switch (kind) {
            inline else => |k| {
                const r = self.stmts.get(k, id);
                try self.open("(" ++ @tagName(k), .{});
                inline for (@typeInfo(@TypeOf(r)).@"struct".fields) |f| {
                    if (f.type == ExprId) try self.printExpr(@field(r, f.name)) else if (f.type == DeclId) try self.printDecl(@field(r, f.name)) else if (f.type == OptExprId and !@field(r, f.name).isNone()) try self.printExpr(@field(r, f.name).unwrap());
                }
                try self.close();
            },
        }
    }
    pub fn printExpr(self: *AstPrinter, id: ExprId) !void {
        const kind = self.exprs.kind(id);
        if (kind == .Literal) {
            const node = self.exprs.get(.Literal, id);
            switch (node.kind) {
                .int => try self.leaf("(literal kind=int \"{s}\")", .{self.s(node.data.int.text)}),
                .float => try self.leaf("(literal kind=float \"{s}\")", .{self.s(node.data.float.text)}),
                .string => try self.leaf("(literal kind=string \"{s}\")", .{self.s(node.data.string)}),
                .bool => try self.leaf("(literal kind=bool {})", .{node.data.bool}),
                .char => try self.leaf("(literal kind=char {d})", .{node.data.char}),
                else => try self.leaf("(literal kind={s})", .{@tagName(node.kind)}),
            }
            return;
        } else if (kind == .Ident) {
            try self.leaf("(ident \"{s}\")", .{self.s(self.exprs.get(.Ident, id).name)});
            return;
        }
        switch (kind) {
            inline else => |k| {
                const r = self.exprs.get(k, id);
                try self.open("(" ++ @tagName(k), .{});
                inline for (@typeInfo(@TypeOf(r)).@"struct".fields) |f| {
                    if (comptime std.mem.eql(u8, f.name, "loc")) continue;
                    if (f.type == ExprId) try self.printExpr(@field(r, f.name)) else if (f.type == OptExprId) {
                        if (!@field(r, f.name).isNone()) try self.printExpr(@field(r, f.name).unwrap());
                    } else if (f.type == StrId)
                        try self.leaf("{s}=\"{s}\"", .{ f.name, self.s(@field(r, f.name)) })
                    else if (f.type == RangeExpr) for (self.exprs.expr_pool.slice(@field(r, f.name))) |e| try self.printExpr(e) else if (f.type == RangeStmt) for (self.stmts.stmt_pool.slice(@field(r, f.name))) |st|
                        try self.printStmt(st)
                    else if (f.type == RangeMatchArm) for (self.exprs.arm_pool.slice(@field(r, f.name))) |a| {
                        const arm = self.exprs.MatchArm.get(a);
                        try self.open("(arm", .{});
                        try self.printPattern(arm.pattern);
                        if (!arm.guard.isNone()) try self.printExpr(arm.guard.unwrap());
                        try self.printExpr(arm.body);
                        try self.close();
                    };
                }
                try self.close();
            },
        }
    }
    pub fn printPattern(self: *AstPrinter, id: PatternId) !void {
        const kind = self.pats.kind(id);
        try self.openTag(@tagName(kind));
        switch (kind) {
            inline else => |k| {
                const r = self.pats.get(k, id);
                inline for (@typeInfo(@TypeOf(r)).@"struct".fields) |f| {
                    if (comptime std.mem.eql(u8, f.name, "loc")) continue;
                    if (f.type == PatternId) try self.printPattern(@field(r, f.name)) else if (f.type == RangePat) for (self.pats.pat_pool.slice(@field(r, f.name))) |p| try self.printPattern(p) else if (f.type == StrId) try self.leaf("{s}=\"{s}\"", .{ f.name, self.s(@field(r, f.name)) }) else if (f.type == ExprId) try self.printExpr(@field(r, f.name));
                }
            },
        }
        try self.close();
    }
};

comptime {
    std.debug.assert(@sizeOf(ExprId) == 4);
    std.debug.assert(@sizeOf(StmtId) == 4);
}
