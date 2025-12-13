const std = @import("std");
const dod = @import("cst.zig");
const TypeInfo = @import("types.zig").TypeInfo;
const TypeStore = @import("types.zig").TypeStore;
const ArrayList = std.array_list.Managed;

/// Alias to the generic indexed storage helper used for expression ids.
pub const Index = dod.Index;
/// Alias for sentinel ids that denote optional presence.
pub const SentinelIndex = dod.SentinelIndex;
/// Range type helper for sequential pools.
pub const RangeOf = dod.RangeOf;
/// Optional range helper for pools that may be empty.
pub const OptRangeOf = dod.OptRangeOf;
/// Pool helper storing identifiers for rows.
pub const Pool = dod.Pool;
/// Table helper wrapping lookup/storage for row structs.
pub const Table = dod.Table;
/// Store index helper that maps between kinds and raw ids.
pub const StoreIndex = dod.StoreIndex;
/// Re-exported name interner used for identifiers.
pub const StringInterner = dod.StringInterner;
/// Re-exported location storage used by AST nodes.
pub const LocStore = dod.LocStore;
/// Identifier type for interned strings.
pub const StrId = dod.StrId;
/// Identifier type for source locations.
pub const LocId = dod.LocId;
/// Optional identifier type for interned strings.
pub const OptStrId = dod.OptStrId;
/// Optional identifier type for source locations.
pub const OptLocId = dod.OptLocId;
/// MLIR kind discriminator reused by AST MLIR nodes.
pub const MlirKind = dod.MlirKind;
/// MLIR cast kind discriminator reused by AST `cast`.
pub const CastKind = dod.CastKind;
/// MLIR piece kind discriminator used by MLIR snippets.
pub const MlirPieceKind = dod.MlirPieceKind;

/// Zero-sized tag that distinguishes expression indexes from other pools.
pub const ExprTag = struct {};
/// Zero-sized tag used for statement allocations.
pub const StmtTag = struct {};
/// Zero-sized tag for pattern storage identifiers.
pub const PatternTag = struct {};

/// Index for expressions stored in `Rows`.
pub const ExprId = Index(ExprTag);
/// Identifier for declarations in the global declaration storage.
pub const DeclId = Index(Rows.Decl);
/// Index for AST statements.
pub const StmtId = Index(StmtTag);
/// Index for attribute nodes (e.g., annotations).
pub const AttributeId = Index(Rows.Attribute);
/// Identifier for function/closure parameters.
pub const ParamId = Index(Rows.Param);
/// ID for struct field declarations.
pub const StructFieldId = Index(Rows.StructField);
/// ID for enum field definitions.
pub const EnumFieldId = Index(Rows.EnumField);
/// Index for variant field descriptors.
pub const VariantFieldId = Index(Rows.VariantField);
/// Storage index for map literal key/value entries.
pub const KeyValueId = Index(Rows.KeyValue);
/// Index for a match arm.
pub const MatchArmId = Index(Rows.MatchArm);
/// ID that tracks struct literal field values.
pub const StructFieldValueId = Index(Rows.StructFieldValue);
/// Identifier for method path segments.
pub const MethodPathSegId = Index(Rows.MethodPathSeg);
/// Identifier for embedded MLIR snippets.
pub const MlirPieceId = Index(Rows.MlirPiece);
/// Index for path segments within pattern paths.
pub const PathSegId = Index(PatRows.PathSeg);
/// Identifier for patterns stored in `PatRows`.
pub const PatternId = Index(PatternTag);
/// Index for pattern struct fields.
pub const PatFieldId = Index(PatRows.StructField);

/// Optional expression index (allows sentinel for none).
pub const OptExprId = SentinelIndex(ExprTag);
/// Optional statement index (sentinel when missing).
pub const OptStmtId = SentinelIndex(StmtTag);
/// Optional declaration index.
pub const OptDeclId = SentinelIndex(Rows.Decl);
/// Optional parameter identifier.
pub const OptParamId = SentinelIndex(Rows.Param);
/// Optional pattern identifier.
pub const OptPatternId = SentinelIndex(PatternTag);

/// Dense range covering a contiguous segment of expressions.
pub const RangeExpr = RangeOf(ExprId);
/// Range that walks a run of statements.
pub const RangeStmt = RangeOf(StmtId);
/// Range used for declaration sequences.
pub const RangeDecl = RangeOf(DeclId);
/// Range covering parameter slots.
pub const RangeParam = RangeOf(ParamId);
/// Range of attribute entries.
pub const RangeAttr = RangeOf(AttributeId);
/// Range over struct field declarations.
pub const RangeField = RangeOf(StructFieldId);
/// Range over enum field declarations.
pub const RangeEnumField = RangeOf(EnumFieldId);
/// Range over variant field declarations.
pub const RangeVariantField = RangeOf(VariantFieldId);
/// Range mapping map literal entries.
pub const RangeKeyValue = RangeOf(KeyValueId);
/// Range over struct literal field values.
pub const RangeStructFieldValue = RangeOf(StructFieldValueId);
/// Range covering all arms of a match.
pub const RangeMatchArm = RangeOf(MatchArmId);
/// Range that represents method path segments.
pub const RangeMethodPathSeg = RangeOf(MethodPathSegId);
/// Range for embedded MLIR pieces.
pub const RangeMlirPiece = RangeOf(MlirPieceId);
/// Range covering multiple patterns.
pub const RangePat = RangeOf(PatternId);
/// Range delimiting path segments in patterns.
pub const RangePathSeg = RangeOf(PathSegId);
/// Range for struct fields inside patterns.
pub const RangePatField = RangeOf(PatFieldId);

/// Optional range of expressions.
pub const OptRangeExpr = OptRangeOf(ExprId);
/// Optional range of statements.
pub const OptRangeStmt = OptRangeOf(StmtId);
/// Optional range of declarations.
pub const OptRangeDecl = OptRangeOf(DeclId);
/// Optional range of attributes.
pub const OptRangeAttr = OptRangeOf(AttributeId);
/// Optional range of struct fields.
pub const OptRangeField = OptRangeOf(StructFieldId);
/// Optional range of patterns.
pub const OptRangePat = OptRangeOf(PatternId);
/// Optional range of path segments.
pub const OptRangeMethodPathSeg = OptRangeOf(MethodPathSegId);

/// Tags that distinguish literal flavors parsed from source.
pub const LiteralKind = enum(u8) { int, float, bool, string, char, imaginary };
/// Operators that operate on a single operand.
pub const UnaryOp = enum(u8) { pos, neg, address_of, logical_not };
/// Operators that combine two operands or operate as comparisons.
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
    contains,
};
/// Layout patterns for variant payloads.
pub const VariantPayloadKind = enum(u2) { none, tuple, @"struct" };

/// AST translation unit plus metadata captured after parsing a package.
pub const Unit = struct {
    /// All declarations that belong to this translation unit.
    decls: RangeDecl,
    /// Interned name of the package containing this unit, if any.
    package_name: OptStrId,
    /// Source location of the package declaration, if present.
    package_loc: OptLocId,

    /// Construct an empty `Unit` with no declarations or package info.
    pub fn empty() Unit {
        return .{
            .decls = .empty(),
            .package_name = .none(),
            .package_loc = .none(),
        };
    }
};

/// Discriminates every kind of expression node in the AST.
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

/// Storage layout for each AST row kind.
pub const Rows = struct {
    /// Row describing a literal expression and its payload.
    pub const Literal = struct {
        /// Discriminator identifying the literal flavor (int, float, etc.).
        kind: LiteralKind,
        /// Actual literal payload.
        data: LiteralValue,
        /// Source span of the literal.
        loc: LocId,
    };
    /// Row capturing identifier name and location.
    pub const Ident = struct {
        /// Identifier name in the string interner.
        name: StrId,
        /// Location where the identifier was parsed.
        loc: LocId,
    };
    /// Row storing the operand and operator for unary ops.
    pub const Unary = struct {
        /// Operand of the unary operation.
        expr: ExprId,
        /// Operator applied to `expr`.
        op: UnaryOp,
        /// Location of the operator token.
        loc: LocId,
    };
    /// Row containing both operands for a binary operation.
    pub const Binary = struct {
        /// Left-hand operand.
        left: ExprId,
        /// Right-hand operand.
        right: ExprId,
        /// Binary operator.
        op: BinaryOp,
        /// Whether the operation wraps on overflow (wrapping semantics).
        wrap: bool,
        /// Whether the operation saturates on overflow.
        saturate: bool,
        /// Location covering the entire binary expression.
        loc: LocId,
    };
    /// Row representing a range literal used with `..`.
    pub const Range = struct {
        /// Optional start expression (inclusive).
        start: OptExprId,
        /// Optional end expression (inclusive or exclusive depending on the flag).
        end: OptExprId,
        /// Whether the right bound is inclusive.
        inclusive_right: bool,
        /// Location of the range expression.
        loc: LocId,
    };
    /// Row for dereference expressions.
    pub const Deref = struct {
        /// Value being dereferenced.
        expr: ExprId,
        /// Location of the dereference.
        loc: LocId,
    };
    /// Row storing array literal elements and location.
    pub const ArrayLit = struct {
        /// Elements of the array literal.
        elems: RangeExpr,
        /// Location of the literal.
        loc: LocId,
    };
    /// Row representing tuple literals with element spans.
    pub const TupleLit = struct {
        /// Elements of the tuple literal.
        elems: RangeExpr,
        /// Location of the literal.
        loc: LocId,
    };
    /// Row representing map literals with entries.
    pub const MapLit = struct {
        /// Key/value entries in the map literal.
        entries: RangeKeyValue,
        /// Location of the literal.
        loc: LocId,
    };
    /// Row for individual key-value entries inside map literals.
    pub const KeyValue = struct {
        /// Expression used for the key.
        key: ExprId,
        /// Expression used for the value.
        value: ExprId,
        /// Location of the key/value pair.
        loc: LocId,
    };
    /// Row for a generic call expression and its arguments.
    pub const Call = struct {
        /// Expression representing the function being invoked.
        callee: ExprId,
        /// Argument list passed to the call.
        args: RangeExpr,
        /// Source range covering the call expression.
        loc: LocId,
    };
    /// Row for indexing expressions (e.g., `foo[bar]`).
    pub const IndexAccess = struct {
        /// Collection being indexed.
        collection: ExprId,
        /// Index expression applied to the collection.
        index: ExprId,
        /// Location of the access expression.
        loc: LocId,
    };
    /// Row describing field access or tuple element reads.
    pub const FieldAccess = struct {
        /// Base expression from which the field is read.
        parent: ExprId,
        /// Name of the field or tuple index.
        field: StrId,
        /// Set when the field-access is tuple-like.
        is_tuple: bool,
        /// Location of the field access.
        loc: LocId,
    };
    /// Row holding struct literal fields that include an optional name.
    pub const StructFieldValue = struct {
        /// Optional explicit field name.
        name: OptStrId,
        /// Expression supplying the field value.
        value: ExprId,
        /// Location of the initializer.
        loc: LocId,
    };
    /// Row representing a literal struct construction.
    pub const StructLit = struct {
        /// Field initializers.
        fields: RangeStructFieldValue,
        /// Optional explicit type annotation for the struct literal.
        ty: OptExprId,
        /// Location of the struct literal.
        loc: LocId,
    };

    /// Packed flags describing function literal qualifiers.
    pub const FnFlags = packed struct(u8) {
        /// Literal declared as `proc`.
        is_proc: bool,
        /// Literal marked `async`.
        is_async: bool,
        /// Literal accepts variadic arguments.
        is_variadic: bool,
        /// Literal declared `extern`.
        is_extern: bool,
        /// Literal produced by a `test` declaration.
        is_test: bool,
        _pad: u3 = 0,
    };

    /// Row for function literal declarations.
    pub const FunctionLit = struct {
        /// Declared parameters for the literal.
        params: RangeParam,
        /// Optional explicit return type.
        result_ty: OptExprId,
        /// Body expression for inline literals.
        body: OptExprId,
        /// Optional raw `asm` text attached to the literal.
        raw_asm: OptStrId,
        /// Attributes applied to this literal.
        attrs: OptRangeAttr,
        /// Qualifying flags such as `proc`, `async`, or `extern`.
        flags: FnFlags,
        /// Location of the literal keyword/token span.
        loc: LocId,
    };

    /// Row for explicit block expressions.
    pub const Block = struct {
        /// Statements contained in the block.
        items: RangeStmt,
        /// Location covering the block braces.
        loc: LocId,
    };
    /// Row for compile-time evaluated block expressions.
    pub const ComptimeBlock = struct {
        /// Expression representing the block body.
        block: ExprId,
        /// Location of the block.
        loc: LocId,
    };
    /// Row representing `code { ... }` injections.
    pub const CodeBlock = struct {
        /// Expression containing the injected code.
        block: ExprId,
        /// Location of the injection.
        loc: LocId,
    };
    /// Row for `async` block expressions.
    pub const AsyncBlock = struct {
        /// Body expression executed asynchronously.
        body: ExprId,
        /// Location of the `async` block.
        loc: LocId,
    };
    /// Row storing a literal MLIR snippet.
    pub const MlirPiece = struct {
        /// Kind of MLIR fragment (literal vs splice).
        kind: MlirPieceKind,
        /// Interned text for the fragment.
        text: StrId,
    };
    /// Row for embedded MLIR blocks with pieces and argument ranges.
    pub const MlirBlock = struct {
        /// MLIR object kind (Module, Operation, etc.).
        kind: MlirKind,
        /// Raw MLIR text for the block.
        text: StrId,
        /// Pieces that reference interpolated values.
        pieces: RangeMlirPiece,
        /// External arguments supplied to the block.
        args: RangeExpr,
        /// Location of the `mlir { }` block.
        loc: LocId,
    };
    /// Row representing MLIR piece insertions.
    pub const Insert = struct {
        /// Expression whose result should be inserted.
        expr: ExprId,
        /// Location of the insertion.
        loc: LocId,
    };

    /// Row for return statements, optionally carrying a value.
    pub const Return = struct {
        /// Expression being returned (if any).
        value: OptExprId,
        /// Location of the `return`.
        loc: LocId,
    };
    /// Row for `if` expressions with optional `else`.
    pub const If = struct {
        /// Condition determining which branch runs.
        cond: ExprId,
        /// Block executed when `cond` is truthy.
        then_block: ExprId,
        /// Optional `else` expression.
        else_block: OptExprId,
        /// Location of the entire `if`.
        loc: LocId,
    };
    /// Row for `while` loops capturing condition, pattern, and body.
    pub const While = struct {
        /// Optional condition expression.
        cond: OptExprId,
        /// Optional `while let` pattern.
        pattern: OptPatternId,
        /// Loop body expression.
        body: ExprId,
        /// Set when the loop uses a pattern guard.
        is_pattern: bool,
        /// Optional label on the loop.
        label: OptStrId,
        /// Location covering the loop keywords/braces.
        loc: LocId,
    };
    /// Row for `for` loops with their pattern and iterable.
    pub const For = struct {
        /// Pattern binding each item.
        pattern: PatternId,
        /// Expression providing the iteration source.
        iterable: ExprId,
        /// Body executed every iteration.
        body: ExprId,
        /// Optional label for nested loops.
        label: OptStrId,
        /// Location covering the `for`.
        loc: LocId,
    };
    /// Row for `match` expressions with arms.
    pub const Match = struct {
        /// Expression being matched.
        expr: ExprId,
        /// Arms within the match.
        arms: RangeMatchArm,
        /// Location covering the `match`.
        loc: LocId,
    };
    /// Row describing a single match arm, guard, and body.
    pub const MatchArm = struct {
        /// Pattern tested by this arm.
        pattern: PatternId,
        /// Optional guard expression.
        guard: OptExprId,
        /// Body expression for the arm.
        body: ExprId,
        /// Location of the arm.
        loc: LocId,
    };

    /// Row for `break` statements with optional value and label.
    pub const Break = struct {
        /// Optional label that is broken out of.
        label: OptStrId,
        /// Optional result passed to the label.
        value: OptExprId,
        /// Location of the break.
        loc: LocId,
    };
    /// Row for `continue` statements within loops.
    pub const Continue = struct {
        /// Optional label target for `continue`.
        label: OptStrId,
        /// Location of the statement.
        loc: LocId,
    };
    /// Row for `unreachable` markers.
    pub const Unreachable = struct { loc: LocId };
    /// Row for literal `null`.
    pub const NullLit = struct { loc: LocId };
    /// Row for literal `undefined`.
    pub const UndefLit = struct { loc: LocId };
    /// Row for `defer` statements.
    pub const Defer = struct { expr: ExprId, loc: LocId };
    /// Row for `errdefer` statements.
    pub const ErrDefer = struct { expr: ExprId, loc: LocId };
    /// Row for `err` unwrap expressions.
    pub const ErrUnwrap = struct { expr: ExprId, loc: LocId };
    /// Row for optional unwrap operations.
    pub const OptionalUnwrap = struct { expr: ExprId, loc: LocId };
    /// Row for `await` expressions.
    pub const Await = struct { expr: ExprId, loc: LocId };
    /// Row capturing closure literals with params and body.
    pub const Closure = struct { params: RangeParam, result_ty: OptExprId, body: ExprId, loc: LocId };
    /// Row for `cast` expressions detailing target type and kind.
    pub const Cast = struct { expr: ExprId, ty: ExprId, kind: CastKind, loc: LocId };
    /// Row for `catch` clauses including optional binding info.
    pub const Catch = struct { expr: ExprId, binding_name: OptStrId, binding_loc: OptLocId, handler: ExprId, loc: LocId };
    /// Row holding an `import` declaration with path metadata.
    pub const Import = struct { path: StrId, loc: LocId };
    /// Row representing `typeof` expressions.
    pub const TypeOf = struct { expr: ExprId, loc: LocId };

    /// Row storing parameter metadata for functions or closures.
    pub const Param = struct {
        /// Optional pattern that binds the parameter.
        pat: OptPatternId,
        /// Optional type annotation.
        ty: OptExprId,
        /// Default value expression when provided.
        value: OptExprId,
        /// Attributes applied to the parameter.
        attrs: OptRangeAttr,
        /// Set when the parameter is a compile-time binding.
        is_comptime: bool,
        /// Location of the parameter declaration.
        loc: LocId,
    };
    /// Row describing an attribute (annotation) and its optional value.
    pub const Attribute = struct {
        /// Attribute name.
        name: StrId,
        /// Optional value attached to the attribute.
        value: OptExprId,
        /// Location of the attribute token.
        loc: LocId,
    };

    /// Row for a segment inside a method path (`foo.bar`).
    pub const MethodPathSeg = struct {
        /// Name of the path segment.
        name: StrId,
        /// Location of the segment.
        loc: LocId,
    };
    /// Flags that describe declaration qualifiers.
    pub const DeclFlags = struct {
        /// Whether the declaration is marked `const`.
        is_const: bool,
    };
    /// Row that attaches an expression to a declaration pattern.
    pub const Decl = struct {
        /// Optional pattern that binds the declared name(s).
        pattern: OptPatternId,
        /// Expression/value belonging to the declaration.
        value: ExprId,
        /// Optional explicit type annotation.
        ty: OptExprId,
        /// Optional method path when declaring associated functions.
        method_path: OptRangeMethodPathSeg,
        /// Declaration qualifiers.
        flags: DeclFlags,
        /// Location covering the declaration statement.
        loc: LocId,
    };

    /// Row for tuple type annotations.
    pub const TupleType = struct {
        /// Element type expressions.
        elems: RangeExpr,
        /// Location of the tuple type.
        loc: LocId,
    };
    /// Row for array type annotations.
    pub const ArrayType = struct {
        /// Element type expression.
        elem: ExprId,
        /// Length expression.
        size: ExprId,
        /// Location of the array type.
        loc: LocId,
    };
    /// Row for dynamic array type annotations.
    pub const DynArrayType = struct {
        /// Element type expression.
        elem: ExprId,
        /// Location of the type.
        loc: LocId,
    };
    /// Row for map type annotations.
    pub const MapType = struct {
        /// Key type expression.
        key: ExprId,
        /// Value type expression.
        value: ExprId,
        /// Location of the map type.
        loc: LocId,
    };
    /// Row for slice type annotations.
    pub const SliceType = struct {
        /// Element type expression.
        elem: ExprId,
        /// Whether the slice is `const`.
        is_const: bool,
        /// Location of the slice type.
        loc: LocId,
    };
    /// Row for optional type annotations.
    pub const OptionalType = struct {
        /// Element type expression.
        elem: ExprId,
        /// Location of the optional type.
        loc: LocId,
    };
    /// Row for error set type annotations (Ok/Err).
    pub const ErrorSetType = struct {
        /// Error type expression.
        err: ExprId,
        /// Value type expression.
        value: ExprId,
        /// Location of the error set type.
        loc: LocId,
    };

    /// Row describing a struct field declaration.
    pub const StructField = struct {
        /// Field name.
        name: StrId,
        /// Field type expression.
        ty: ExprId,
        /// Optional initializer value.
        value: OptExprId,
        /// Attributes applied to the field.
        attrs: OptRangeAttr,
        /// Location of the field.
        loc: LocId,
    };
    /// Row for struct type annotations.
    pub const StructType = struct {
        /// Fields contained in the struct.
        fields: RangeField,
        /// Whether the struct is declared `extern`.
        is_extern: bool,
        /// Attributes on the struct.
        attrs: OptRangeAttr,
        /// Location of the struct type.
        loc: LocId,
    };

    /// Row describing an enum member.
    pub const EnumField = struct {
        /// Variant name.
        name: StrId,
        /// Optional discriminant initializer.
        value: OptExprId,
        /// Attributes on the variant.
        attrs: OptRangeAttr,
        /// Location of the variant.
        loc: LocId,
    };
    /// Row for enum type annotations.
    pub const EnumType = struct {
        /// Enum variant list.
        fields: RangeEnumField,
        /// Optional discriminant type expression.
        discriminant: OptExprId,
        /// Whether the enum is `extern`.
        is_extern: bool,
        /// Attributes applied to the enum.
        attrs: OptRangeAttr,
        /// Location of the enum type.
        loc: LocId,
    };

    /// Row describing a variant (sum type) field.
    pub const VariantField = struct {
        /// Name of the variant.
        name: StrId,
        /// Layout kind (none, tuple, struct).
        payload_kind: VariantPayloadKind,
        /// Expression operands when the payload is tuple-like.
        payload_elems: OptRangeExpr,
        /// Field definitions when the payload is struct-like.
        payload_fields: OptRangeField,
        /// Optional initializer.
        value: OptExprId,
        /// Attributes attached to the variant.
        attrs: OptRangeAttr,
        /// Location of the variant.
        loc: LocId,
    };
    /// Row for variant type annotations.
    pub const VariantType = struct {
        /// Fields representing each variant.
        fields: RangeVariantField,
        /// Location of the variant type.
        loc: LocId,
    };
    /// Alias for variant types reused as error type rows.
    pub const ErrorType = VariantType;

    /// Row for anonymous union type annotations.
    pub const UnionType = struct {
        /// Variant fields stored in the union.
        fields: RangeField,
        /// Whether the union is externally defined.
        is_extern: bool,
        /// Attributes applied to the union.
        attrs: OptRangeAttr,
        /// Location of the union type.
        loc: LocId,
    };

    /// Row for pointer type annotations.
    pub const PointerType = struct {
        /// Element being pointed to.
        elem: ExprId,
        /// Whether the pointer is const.
        is_const: bool,
        /// Location of the pointer type.
        loc: LocId,
    };
    /// Row for SIMD type annotations.
    pub const SimdType = struct {
        /// Element type of the vector.
        elem: ExprId,
        /// Lane count expression.
        lanes: ExprId,
        /// Location of the SIMD type.
        loc: LocId,
    };
    /// Row for complex number type annotations.
    pub const ComplexType = struct {
        /// Element type expression (real/imag parts).
        elem: ExprId,
        /// Location of the complex type.
        loc: LocId,
    };
    /// Row for tensor type annotations.
    pub const TensorType = struct {
        /// Element type expression.
        elem: ExprId,
        /// Shape dimensions.
        shape: RangeExpr,
        /// Location of the tensor type.
        loc: LocId,
    };
    /// Row representing the `type` metatype.
    pub const TypeType = struct {
        /// Location of the `type` literal.
        loc: LocId,
    };
    /// Row for the `any` type placeholder.
    pub const AnyType = struct {
        /// Location of the `any` expression.
        loc: LocId,
    };
    /// Row for the `noreturn` type.
    pub const NoreturnType = struct {
        /// Location of the `noreturn` annotation.
        loc: LocId,
    };
};

/// Map an `ExprKind` discriminant to the matching `Rows` struct descriptor.
pub inline fn RowT(comptime K: ExprKind) type {
    return @field(Rows, @tagName(K));
}

/// Identifies which statement form a `StmtId` refers to.
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

/// Repository of statement row layouts.
pub const StmtRows = struct {
    /// Expression statements.
    pub const Expr = struct {
        /// Expression executed as a statement.
        expr: ExprId,
    };
    /// Declaration statements.
    pub const Decl = struct {
        /// Declaration stored by this statement.
        decl: DeclId,
    };
    /// Assignment statements.
    pub const Assign = struct {
        /// Left-hand target of the assignment.
        left: ExprId,
        /// Right-hand value expression.
        right: ExprId,
        /// Location covering the assignment.
        loc: LocId,
    };
    /// MLIR insert statements (reuse `Rows.Insert` layout).
    pub const Insert = Rows.Insert;
    /// Return statements (reuse `Rows.Return` layout).
    pub const Return = Rows.Return;
    /// Break statements (reuse `Rows.Break` layout).
    pub const Break = Rows.Break;
    /// Continue statements (reuse `Rows.Continue` layout).
    pub const Continue = Rows.Continue;
    /// Unreachable statements (reuse `Rows.Unreachable` layout).
    pub const Unreachable = Rows.Unreachable;
    /// Defer statements (reuse `Rows.Defer` layout).
    pub const Defer = Rows.Defer;
    /// Errdefer statements (reuse `Rows.ErrDefer` layout).
    pub const ErrDefer = Rows.ErrDefer;
};

/// Map a `StmtKind` discriminant to the corresponding `StmtRows` layout.
pub inline fn StmtRowT(comptime K: StmtKind) type {
    return @field(StmtRows, @tagName(K));
}

/// Discriminates all pattern forms.
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

/// Storage for pattern-specific rows used to instantiate `PatternId`s.
pub const PatRows = struct {
    /// Row for wildcard (`_`) patterns.
    pub const Wildcard = struct {
        /// Location of the wildcard token.
        loc: LocId,
    };
    /// Row for literal matching patterns.
    pub const Literal = struct {
        /// Expression containing the literal value.
        expr: ExprId,
        /// Location of the literal pattern.
        loc: LocId,
    };

    /// Row for a path segment used inside pattern matching.
    pub const PathSeg = struct {
        /// Segment name.
        name: StrId,
        /// Whether the path is borrowed.
        by_ref: bool,
        /// Whether the path is mutable.
        is_mut: bool,
        /// Location of the segment.
        loc: LocId,
    };
    /// Row for pattern paths composed of multiple segments.
    pub const Path = struct {
        /// Segments describing the path.
        segments: RangePathSeg,
        /// Location of the entire path.
        loc: LocId,
    };

    /// Row for binding patterns (naming a value).
    pub const Binding = struct {
        /// Name being introduced.
        name: StrId,
        /// Whether the binding borrows the matched value.
        by_ref: bool,
        /// Whether the binding is mutable.
        is_mut: bool,
        /// Location recording the binding.
        loc: LocId,
    };

    /// Row for tuple patterns.
    pub const Tuple = struct {
        /// Element patterns inside the tuple.
        elems: RangePat,
        /// Location of the tuple pattern.
        loc: LocId,
    };

    /// Row for slice patterns (`[head, tail...]`).
    pub const Slice = struct {
        /// Element patterns before the rest.
        elems: RangePat,
        /// Whether the slice uses a rest pattern.
        has_rest: bool,
        /// Index where the rest begins.
        rest_index: u32,
        /// Optional pattern binding for the rest.
        rest_binding: OptPatternId,
        /// Location of the slice pattern.
        loc: LocId,
    };

    /// Row for a single field inside a struct pattern.
    pub const StructField = struct {
        /// Field name.
        name: StrId,
        /// Pattern matching the field value.
        pattern: PatternId,
        /// Location of the field binding.
        loc: LocId,
    };

    /// Row for struct patterns.
    pub const Struct = struct {
        /// Path describing the struct type.
        path: RangePathSeg,
        /// Field patterns matching each struct field.
        fields: RangePatField,
        /// Whether the pattern allows unspecified fields.
        has_rest: bool,
        /// Location of the struct pattern.
        loc: LocId,
    };

    /// Row for tuple-like variant patterns.
    pub const VariantTuple = struct {
        /// Variant path being matched.
        path: RangePathSeg,
        /// Element patterns inside the variant payload.
        elems: RangePat,
        /// Location of the pattern.
        loc: LocId,
    };

    /// Row for struct-like variant patterns.
    pub const VariantStruct = struct {
        /// Variant path identifier.
        path: RangePathSeg,
        /// Field patterns within the payload.
        fields: RangePatField,
        /// Whether the struct variant permits rest fields.
        has_rest: bool,
        /// Location of the variant pattern.
        loc: LocId,
    };

    /// Row for range patterns (`x..y`).
    pub const Range = struct {
        /// Optional start expression.
        start: OptExprId,
        /// Optional end expression.
        end: OptExprId,
        /// Whether the end bound is inclusive.
        inclusive_right: bool,
        /// Location of the range.
        loc: LocId,
    };
    /// Row for pattern alternatives (`p1 | p2`).
    pub const Or = struct {
        /// Alternative patterns.
        alts: RangePat,
        /// Location covering the alternatives.
        loc: LocId,
    };
    /// Row for `@binder` patterns.
    pub const At = struct {
        /// Name bound by the `@`.
        binder: StrId,
        /// Pattern being bound.
        pattern: PatternId,
        /// Location of the `@`.
        loc: LocId,
    };
};

/// Resolve storage row type for a `PatternKind`.
inline fn PatRowT(comptime K: PatternKind) type {
    return @field(PatRows, @tagName(K));
}

/// Metadata for integer literals.
pub const LiteralInt = struct {
    /// Interned literal text.
    text: StrId,
    /// Parsed numeric value.
    value: u128,
    /// Radix/base of the literal.
    base: u8,
    /// Whether the literal parsed successfully.
    valid: bool,
};

/// Metadata for floating-point literals.
pub const LiteralFloat = struct {
    /// Interned literal text.
    text: StrId,
    /// Parsed floating-point value.
    value: f64,
    /// Whether parsing succeeded.
    valid: bool,
};

/// Union storing the payload of literal expressions.
pub const LiteralValue = union(enum) {
    /// No payload (placeholder).
    none,
    /// Boolean literal payload.
    bool: bool,
    /// Character literal payload.
    char: u32,
    /// String literal payload.
    string: StrId,
    /// Integer literal payload.
    int: LiteralInt,
    /// Floating-point literal payload.
    float: LiteralFloat,
    /// Imaginary literal payload (float metadata).
    imaginary: LiteralFloat,
};

/// Central storage for AST expression rows and their pools.
pub const ExprStore = struct {
    /// Allocator that backs all tables and pools within the expression store.
    gpa: std.mem.Allocator,
    /// Global indexer that maps kinds to `ExprId`.
    index: StoreIndex(ExprKind) = .{},

    /// Storage for literal AST nodes.
    Literal: Table(Rows.Literal) = .{},
    /// Storage for identifier nodes tied to `StrId`.
    Ident: Table(Rows.Ident) = .{},
    /// Storage for unary operator expressions.
    Unary: Table(Rows.Unary) = .{},
    /// Storage for binary operator expressions.
    Binary: Table(Rows.Binary) = .{},
    /// Storage for range expressions (e.g., `start..end`).
    Range: Table(Rows.Range) = .{},
    /// Storage for dereference operations.
    Deref: Table(Rows.Deref) = .{},

    /// Storage for array literal nodes.
    ArrayLit: Table(Rows.ArrayLit) = .{},
    /// Storage for tuple literal nodes.
    TupleLit: Table(Rows.TupleLit) = .{},
    /// Storage for map literal entries.
    MapLit: Table(Rows.MapLit) = .{},
    /// Storage for key/value literal rows.
    KeyValue: Table(Rows.KeyValue) = .{},

    /// Storage for call expressions.
    Call: Table(Rows.Call) = .{},
    /// Storage for index access expressions (collection[index]).
    IndexAccess: Table(Rows.IndexAccess) = .{},
    /// Storage for field/tuple-slot access expressions.
    FieldAccess: Table(Rows.FieldAccess) = .{},

    /// Storage for struct literal field initializer metadata.
    StructFieldValue: Table(Rows.StructFieldValue) = .{},
    /// Storage for struct literal nodes.
    StructLit: Table(Rows.StructLit) = .{},

    /// Storage for function literal nodes.
    FunctionLit: Table(Rows.FunctionLit) = .{},
    /// Storage for block literals.
    Block: Table(Rows.Block) = .{},
    /// Storage for comptime block wrappers.
    ComptimeBlock: Table(Rows.ComptimeBlock) = .{},
    /// Storage for code block literals (lambda-like).
    CodeBlock: Table(Rows.CodeBlock) = .{},
    /// Storage for async block expressions.
    AsyncBlock: Table(Rows.AsyncBlock) = .{},
    /// Storage for MLIR block literals embedded in the AST.
    MlirBlock: Table(Rows.MlirBlock) = .{},
    /// Storage for pieces belonging to MLIR blocks.
    MlirPiece: Table(Rows.MlirPiece) = .{},
    /// Storage for `insert` statements (macro-like).
    Insert: Table(Rows.Insert) = .{},

    /// Storage for return statements.
    Return: Table(Rows.Return) = .{},
    /// Storage for `if` statements/expressions.
    If: Table(Rows.If) = .{},
    /// Storage for `while` loops.
    While: Table(Rows.While) = .{},
    /// Storage for `for` loops.
    For: Table(Rows.For) = .{},
    /// Storage for `match` expressions.
    Match: Table(Rows.Match) = .{},
    /// Storage for each match arm inside a `match`.
    MatchArm: Table(Rows.MatchArm) = .{},

    /// Storage for `break` statements.
    Break: Table(Rows.Break) = .{},
    /// Storage for `continue` statements.
    Continue: Table(Rows.Continue) = .{},
    /// Storage for explicit `unreachable`.
    Unreachable: Table(Rows.Unreachable) = .{},
    /// Storage for explicit `null` literals.
    NullLit: Table(Rows.NullLit) = .{},
    /// Storage for explicit `undef` literals.
    UndefLit: Table(Rows.UndefLit) = .{},
    /// Storage for `defer` statements.
    Defer: Table(Rows.Defer) = .{},
    /// Storage for `err defer` statements.
    ErrDefer: Table(Rows.ErrDefer) = .{},
    /// Storage for `err.unwrap` expressions.
    ErrUnwrap: Table(Rows.ErrUnwrap) = .{},
    /// Storage for optional `unwrap` expressions.
    OptionalUnwrap: Table(Rows.OptionalUnwrap) = .{},
    /// Storage for `await` expressions.
    Await: Table(Rows.Await) = .{},
    /// Storage for closure expressions.
    Closure: Table(Rows.Closure) = .{},
    /// Storage for explicit cast expressions.
    Cast: Table(Rows.Cast) = .{},
    /// Storage for `catch` expressions.
    Catch: Table(Rows.Catch) = .{},
    /// Storage for `import` directives.
    Import: Table(Rows.Import) = .{},
    /// Storage for `typeof` expressions.
    TypeOf: Table(Rows.TypeOf) = .{},

    /// Storage for tuple type nodes.
    TupleType: Table(Rows.TupleType) = .{},
    /// Storage for array type nodes.
    ArrayType: Table(Rows.ArrayType) = .{},
    /// Storage for dynamic array type nodes.
    DynArrayType: Table(Rows.DynArrayType) = .{},
    /// Storage for map type nodes.
    MapType: Table(Rows.MapType) = .{},
    /// Storage for slice type nodes.
    SliceType: Table(Rows.SliceType) = .{},
    /// Storage for optional type nodes.
    OptionalType: Table(Rows.OptionalType) = .{},
    /// Storage for error-set type annotations.
    ErrorSetType: Table(Rows.ErrorSetType) = .{},

    /// Storage for individual struct field definitions.
    StructField: Table(Rows.StructField) = .{},
    /// Storage for struct type declarations.
    StructType: Table(Rows.StructType) = .{},

    /// Storage for enum field declarations.
    EnumField: Table(Rows.EnumField) = .{},
    /// Storage for enum type declarations.
    EnumType: Table(Rows.EnumType) = .{},

    /// Storage for variant field declarations.
    VariantField: Table(Rows.VariantField) = .{},
    /// Storage for variant type declarations.
    VariantType: Table(Rows.VariantType) = .{},
    /// Storage for error type declarations.
    ErrorType: Table(Rows.ErrorType) = .{},
    /// Storage for union type declarations.
    UnionType: Table(Rows.UnionType) = .{},
    /// Storage for pointer type nodes.
    PointerType: Table(Rows.PointerType) = .{},
    /// Storage for SIMD type nodes.
    SimdType: Table(Rows.SimdType) = .{},
    /// Storage for complex number type nodes.
    ComplexType: Table(Rows.ComplexType) = .{},
    /// Storage for tensor type declarations.
    TensorType: Table(Rows.TensorType) = .{},
    /// Storage for the `type` literal nodes.
    TypeType: Table(Rows.TypeType) = .{},
    /// Storage for the `any` type node.
    AnyType: Table(Rows.AnyType) = .{},
    /// Storage for the `noreturn` type node.
    NoreturnType: Table(Rows.NoreturnType) = .{},

    /// Storage for function parameter definitions.
    Param: Table(Rows.Param) = .{},
    /// Storage for function attributes (e.g., visibility, comptime).
    Attribute: Table(Rows.Attribute) = .{},
    /// Storage for top-level declarations.
    Decl: Table(Rows.Decl) = .{},
    /// Storage for method-path segments used during type resolution.
    MethodPathSeg: Table(Rows.MethodPathSeg) = .{},

    /// Pool that keeps each expression identifier.
    expr_pool: Pool(ExprId) = .{},
    /// Pool that keeps declaration identifiers.
    decl_pool: Pool(DeclId) = .{},
    /// Pool backing parameter identifiers.
    param_pool: Pool(ParamId) = .{},
    /// Pool backing attribute identifiers.
    attr_pool: Pool(AttributeId) = .{},
    /// Pool for struct field value ids.
    sfv_pool: Pool(StructFieldValueId) = .{},
    /// Pool for key/value argument nodes.
    kv_pool: Pool(KeyValueId) = .{},
    /// Pool for match arm identifiers.
    arm_pool: Pool(MatchArmId) = .{},
    /// Pool for defined struct fields.
    sfield_pool: Pool(StructFieldId) = .{},
    /// Pool for defined enum fields.
    efield_pool: Pool(EnumFieldId) = .{},
    /// Pool for defined variant fields.
    vfield_pool: Pool(VariantFieldId) = .{},
    /// Pool for method path segments.
    method_path_pool: Pool(MethodPathSegId) = .{},
    /// Pool for MLIR pieces attached to AST nodes.
    mlir_piece_pool: Pool(MlirPieceId) = .{},

    /// Shared string interner used for identifier names.
    strs: *StringInterner,
    /// Immutable location table for source spans.
    locs: *const LocStore,

    /// Initialize the expression store with its allocator, interner, and locations table.
    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner, locs: *const LocStore) ExprStore {
        return .{ .gpa = gpa, .strs = strs, .locs = locs };
    }

    /// Release all resources owned by the store, including tables and pools.
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

    pub fn kind(self: *const @This(), id: ExprId) ExprKind {
        return self.index.kinds.items[id.toRaw()];
    }

    /// Add a row of kind `K` to the store and return the newly issued `ExprId`.
    pub fn add(self: *@This(), comptime K: ExprKind, row: RowT(K)) ExprId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), ExprId);
    }

    /// Retrieve the stored row for `id`, asserting that it matches kind `K`.
    pub fn get(self: *@This(), comptime K: ExprKind, id: ExprId) RowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
    }

    /// Add a key/value literal row and return its identifier.
    pub fn addKeyValue(self: *@This(), row: Rows.KeyValue) KeyValueId {
        return self.KeyValue.add(self.gpa, row);
    }

    /// Insert a struct field value initializer row.
    pub fn addStructFieldValue(self: *@This(), row: Rows.StructFieldValue) StructFieldValueId {
        return self.StructFieldValue.add(self.gpa, row);
    }

    /// Push a match arm definition into its storage table.
    pub fn addMatchArm(self: *@This(), row: Rows.MatchArm) MatchArmId {
        return self.MatchArm.add(self.gpa, row);
    }

    /// Store a parameter row and return its identifier.
    pub fn addParam(self: *@This(), row: Rows.Param) ParamId {
        return self.Param.add(self.gpa, row);
    }

    /// Store an attribute row (e.g., visibility or extern) and return its `AttributeId`.
    pub fn addAttribute(self: *@This(), row: Rows.Attribute) AttributeId {
        return self.Attribute.add(self.gpa, row);
    }

    /// Store a declaration row (function, struct, etc.) and return its `DeclId`.
    pub fn addDecl(self: *@This(), row: Rows.Decl) DeclId {
        return self.Decl.add(self.gpa, row);
    }

    /// Insert a method path segment used during method lookup.
    pub fn addMethodPathSeg(self: *@This(), row: Rows.MethodPathSeg) MethodPathSegId {
        return self.MethodPathSeg.add(self.gpa, row);
    }

    /// Store a struct field definition.
    pub fn addStructField(self: *@This(), row: Rows.StructField) StructFieldId {
        return self.StructField.add(self.gpa, row);
    }

    /// Store an enum field definition.
    pub fn addEnumField(self: *@This(), row: Rows.EnumField) EnumFieldId {
        return self.EnumField.add(self.gpa, row);
    }

    /// Store a variant field definition.
    pub fn addVariantField(self: *@This(), row: Rows.VariantField) VariantFieldId {
        return self.VariantField.add(self.gpa, row);
    }

    /// Store an MLIR piece node and return its identifier.
    pub fn addMlirPiece(self: *@This(), row: Rows.MlirPiece) MlirPieceId {
        return self.MlirPiece.add(self.gpa, row);
    }
};

/// Statement-specific tables coordinating `StmtKind` to `StmtId`.
pub const StmtStore = struct {
    /// Allocator backing every statement table.
    gpa: std.mem.Allocator,
    /// Index tracker for mapping `StmtKind` to `StmtId`.
    index: StoreIndex(StmtKind) = .{},

    /// Table holding expression statements.
    Expr: Table(StmtRows.Expr) = .{},
    /// Table holding declaration statements.
    Decl: Table(StmtRows.Decl) = .{},
    /// Table holding assignment statements.
    Assign: Table(StmtRows.Assign) = .{},
    /// Table holding `insert` statements.
    Insert: Table(StmtRows.Insert) = .{},
    /// Table holding `return` statements.
    Return: Table(StmtRows.Return) = .{},
    /// Table holding `break` statements.
    Break: Table(StmtRows.Break) = .{},
    /// Table holding `continue` statements.
    Continue: Table(StmtRows.Continue) = .{},
    /// Table holding `unreachable` statements.
    Unreachable: Table(StmtRows.Unreachable) = .{},
    /// Table holding `defer` statements.
    Defer: Table(StmtRows.Defer) = .{},
    /// Table holding `err defer` statements.
    ErrDefer: Table(StmtRows.ErrDefer) = .{},

    /// Pool for statement identifiers.
    stmt_pool: Pool(StmtId) = .{},

    /// Initialize statement storage with allocator `gpa`.
    pub fn init(gpa: std.mem.Allocator) StmtStore {
        return .{ .gpa = gpa };
    }

    /// Deinitialize tables and release their memory through `gpa`.
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;

        self.index.deinit(gpa);
        inline for (@typeInfo(StmtKind).@"enum".fields) |f| {
            @field(self, f.name).deinit(gpa);
        }
        self.stmt_pool.deinit(gpa);
    }

    /// Add a statement row of kind `K` and get its `StmtId`.
    pub fn add(self: *@This(), comptime K: StmtKind, row: StmtRowT(K)) StmtId {
        const tbl: *Table(StmtRowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), StmtId);
    }

    /// Fetch the statement row for identifier `id`, verifying its kind.
    pub fn get(self: *@This(), comptime K: StmtKind, id: StmtId) StmtRowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *Table(StmtRowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
    }

    /// Return the kind associated with statement `id`.
    pub fn kind(self: *StmtStore, id: StmtId) StmtKind {
        return self.index.kinds.items[id.toRaw()];
    }
};

/// Storage for pattern nodes used by matches, loops, and bindings.
pub const PatternStore = struct {
    /// Allocator backing pattern tables and pools.
    gpa: std.mem.Allocator,
    /// Tracks `PatternKind` to the assigned ones.
    index: StoreIndex(PatternKind) = .{},

    /// Table for wildcard patterns.
    Wildcard: Table(PatRows.Wildcard) = .{},
    /// Table for literal patterns.
    Literal: Table(PatRows.Literal) = .{},
    /// Table for method path segments referenced from paths.
    PathSeg: Table(PatRows.PathSeg) = .{},
    /// Table for path patterns.
    Path: Table(PatRows.Path) = .{},
    /// Table for binding patterns (name + qualifiers).
    Binding: Table(PatRows.Binding) = .{},
    /// Table for tuple patterns.
    Tuple: Table(PatRows.Tuple) = .{},
    /// Table for slice patterns.
    Slice: Table(PatRows.Slice) = .{},
    /// Table for struct field patterns.
    StructField: Table(PatRows.StructField) = .{},
    /// Table for struct patterns.
    Struct: Table(PatRows.Struct) = .{},
    /// Table for variant tuple patterns.
    VariantTuple: Table(PatRows.VariantTuple) = .{},
    /// Table for variant struct patterns.
    VariantStruct: Table(PatRows.VariantStruct) = .{},
    /// Table for range patterns.
    Range: Table(PatRows.Range) = .{},
    /// Table for disjunctive (`|`) patterns.
    Or: Table(PatRows.Or) = .{},
    /// Table for `@` binder patterns.
    At: Table(PatRows.At) = .{},

    /// Pool storing assigned `PatternId`s.
    pat_pool: Pool(PatternId) = .{},
    /// Pool storing path segment identifiers.
    seg_pool: Pool(PathSegId) = .{},
    /// Pool storing struct field identifiers.
    field_pool: Pool(PatFieldId) = .{},

    /// Shared string interner used while constructing patterns.
    strs: *StringInterner,

    /// Initialize the pattern store with `gpa` and string interner.
    pub fn init(gpa: std.mem.Allocator, strs: *StringInterner) PatternStore {
        return .{ .gpa = gpa, .strs = strs };
    }

    /// Deinitialize pattern tables/pools and release memory.
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

    pub fn kind(self: *@This(), id: PatternId) PatternKind {
        return self.index.kinds.items[id.toRaw()];
    }

    /// Insert a pattern row of kind `K` and return its identifier.
    pub fn add(self: *@This(), comptime K: PatternKind, row: PatRowT(K)) PatternId {
        const tbl: *Table(PatRowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), PatternId);
    }

    /// Retrieve the stored pattern row for `id`.
    pub fn get(self: *@This(), comptime K: PatternKind, id: PatternId) PatRowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *Table(PatRowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
    }

    /// Add a path-segment row and obtain its `PathSegId`.
    pub fn addPathSeg(self: *@This(), row: PatRows.PathSeg) PathSegId {
        const idx = self.PathSeg.add(self.gpa, row);
        return PathSegId.fromRaw(idx);
    }

    /// Add a struct field pattern row and obtain its identifier.
    pub fn addPatField(self: *@This(), row: PatRows.StructField) PatFieldId {
        const idx = self.StructField.add(self.gpa, row);
        return PatFieldId.fromRaw(idx);
    }
};

/// Top-level AST context that owns stores for expressions, statements, and patterns.
pub const Ast = struct {
    /// Allocator shared across the AST stores in this unit.
    gpa: std.mem.Allocator,
    /// Identifier assigned to the source file for diagnostics.
    file_id: usize,
    /// Root declaration unit containing global declarations.
    unit: Unit,
    /// Expression storage used throughout the AST.
    exprs: ExprStore,
    /// Statement storage used by blocks and functions.
    stmts: StmtStore,
    /// Pattern storage required for match/loop constructs.
    pats: PatternStore,
    /// Auxiliary type info pulled from `types.zig`.
    type_info: TypeInfo,

    /// Build an AST container for `file_id` backed by `gpa`, `interner`, `locs`, and `type_store`.
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
            .unit = .empty(),
            .exprs = .init(gpa, interner, locs),
            .stmts = .init(gpa),
            .pats = .init(gpa, interner),
            .type_info = .init(gpa, type_store),
        };
    }

    fn KindType(T: type) type {
        if (T == ExprId) return ExprKind;
        if (T == PatternId) return PatternKind;
        if (T == StmtId) return StmtKind;
        @compileError("Unsupported id type: " ++ @typeName(T));
    }

    pub fn kind(self: *Ast, id: anytype) KindType(@TypeOf(id)) {
        if (@TypeOf(id) == ExprId)
            return self.exprs.kind(id);
        if (@TypeOf(id) == PatternId)
            return self.pats.kind(id);
        if (@TypeOf(id) == StmtId)
            return self.stmts.index.kinds.items[id.toRaw()];
        @compileError("Unsupported id type: " ++ @typeName(@TypeOf(id)));
    }

    /// Tear down every internal store and release the allocator-backed memory.
    pub fn deinit(self: *Ast) void {
        self.type_info.deinit();
        self.exprs.deinit();
        self.stmts.deinit();
        self.pats.deinit();
    }
};

/// Debug printer that writes the AST tree structure in a s-expression-like form.
pub const AstPrinter = struct {
    /// Output writer that receives the formatted AST tree.
    writer: *std.io.Writer,
    /// Current indentation depth used by `ws`.
    indent: usize = 0,

    /// Expression store read by the printer.
    exprs: *ExprStore,
    /// Statement store read by the printer.
    stmts: *StmtStore,
    /// Pattern store read by the printer.
    pats: *PatternStore,

    /// Create an AST printer bound to the provided stores and writer.
    pub fn init(writer: anytype, exprs: *ExprStore, stmts: *StmtStore, pats: *PatternStore) AstPrinter {
        return .{ .writer = writer, .exprs = exprs, .stmts = stmts, .pats = pats };
    }

    /// Emit the indentation prefix corresponding to `self.indent`.
    fn ws(self: *AstPrinter) anyerror!void {
        var i: usize = 0;
        while (i < self.indent) : (i += 1) try self.writer.writeByte(' ');
    }

    /// Emit `head` at the current indent and then increase the indent depth.
    fn open(self: *AstPrinter, comptime head: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(head, args);
        try self.writer.writeAll("\n");
        self.indent += 2;
    }

    /// Decrease the indent depth and emit a closing parenthesis line.
    fn close(self: *AstPrinter) anyerror!void {
        self.indent = if (self.indent >= 2) self.indent - 2 else 0;
        try self.ws();
        try self.writer.writeAll(")\n");
    }

    /// Print a single-line entry at the current indent using `fmt`.
    fn leaf(self: *AstPrinter, comptime fmt: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
    }

    /// Resolve a `StrId` to its string bytes via the shared interner.
    inline fn s(self: *const AstPrinter, id: StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    /// Print the entire contents of `unit` (declarations, package info, etc.).
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

    /// Pretty-print the declaration referred to by `id`.
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

    /// Dispatch and print the statement identified by `id`.
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

    /// Print an expression subtree rooted at `id`.
    pub fn printExpr(self: *AstPrinter, id: ExprId) anyerror!void {
        const kind = self.exprs.kind(id);
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
                try self.open("(slice_type is_const={})", .{node.is_const});
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

    /// Print multiple expressions from `r` labeled by `name`.
    fn printExprRange(self: *AstPrinter, comptime name: []const u8, r: RangeOf(ExprId)) anyerror!void {
        try self.open("(" ++ name, .{});
        const ids = self.exprs.expr_pool.slice(r);
        for (ids) |eid| try self.printExpr(eid);
        try self.close();
    }

    /// Print the attribute range `opt_r`, if present, using `(attr ...)` nodes.
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

    /// Print each parameter referenced by `r`, including attributes/ty/value.
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

    /// Print a struct field definition referenced by `id`, including type/value.
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

    /// Print the variant field payload structure for the given `id`.
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

    /// Print the pattern `id` tree, using nested `(pattern ...)` nodes.
    pub fn printPattern(self: *AstPrinter, id: PatternId) anyerror!void {
        const kind = self.pats.kind(id);
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

    /// Print the components of a pattern path from `path`.
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

    /// Print a struct pattern field entry identified by `id`.
    fn printPatternField(self: *AstPrinter, id: PatFieldId) anyerror!void {
        const field = self.pats.StructField.get(id);
        try self.open("(field name=\"{s}\"", .{self.s(field.name)});
        try self.printPattern(field.pattern);
        try self.close();
    }
};

/// Source-like pretty-printer for the AST, emitting human-readable syntax.
pub const CodePrinter = struct {
    /// Writer used to emit source-like text.
    writer: *std.io.Writer,
    /// Current indentation width for structured output.
    indent: usize = 0,
    /// Tracks whether the indentation prefix has been emitted yet.
    needs_indent: bool = true,

    /// Expression store that backs code printing.
    exprs: *ExprStore,
    /// Statement store that backs code printing.
    stmts: *StmtStore,
    /// Pattern store that backs code printing.
    pats: *PatternStore,

    /// Create a code printer wired to the given stores and writer.
    pub fn init(writer: anytype, exprs: *ExprStore, stmts: *StmtStore, pats: *PatternStore) CodePrinter {
        return .{ .writer = writer, .exprs = exprs, .stmts = stmts, .pats = pats };
    }

    /// Emit indentation spaces if they have not been emitted since the last newline.
    fn ws(self: *CodePrinter) anyerror!void {
        if (!self.needs_indent) return;
        var i: usize = 0;
        while (i < self.indent) : (i += 1) try self.writer.writeByte(' ');
        self.needs_indent = false;
    }

    /// Emit a newline and mark that indentation needs to be written on the next line.
    fn newline(self: *CodePrinter) anyerror!void {
        try self.writer.writeByte('\n');
        self.needs_indent = true;
    }

    /// Write formatted text after ensuring indentation has been printed.
    fn printf(self: *CodePrinter, comptime fmt: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(fmt, args);
    }

    /// Resolve a `StrId` to bytes using the shared interner.
    inline fn s(self: *const CodePrinter, id: StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    /// Print source-like code for the translation `unit`.
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

    /// Emit source syntax for the declaration identified by `id`.
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

    /// Emit the statement `id` in source form, preserving indentation.
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

    /// Emit code for the expression tree rooted at `id`.
    pub fn printExpr(self: *CodePrinter, id: ExprId) anyerror!void {
        const kind = self.exprs.kind(id);
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
                    .contains => "in",
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

    /// Print expressions from `r` separated by `sep`.
    fn printExprs(self: *CodePrinter, r: RangeOf(ExprId), sep: []const u8) anyerror!void {
        const ids = self.exprs.expr_pool.slice(r);
        for (ids, 0..) |eid, i| {
            if (i > 0) try self.printf("{s}", .{sep});
            try self.printExpr(eid);
        }
    }

    /// Position hint for attribute printing relative to the main node.
    const AttrPos = enum { Before, After };
    /// Print the attribute list `opt_r` at the given `pos` (before or after the node).
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

    /// Print function/closure parameters contained in `r`.
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

    /// Emit source text for the struct field referenced by `id`.
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

    /// Emit source text for the variant field `id`, including payload description.
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

    /// Emit source form for the pattern tree rooted at `id`.
    pub fn printPattern(self: *CodePrinter, id: PatternId) anyerror!void {
        const kind = self.pats.kind(id);
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

    /// Print the dotted pattern path described by `path`.
    fn printPatternPath(self: *CodePrinter, path: RangeOf(PathSegId)) anyerror!void {
        const segs = self.pats.seg_pool.slice(path);
        for (segs, 0..) |sid, i| {
            if (i > 0) try self.printf(".", .{});
            const seg = self.pats.PathSeg.get(sid);
            try self.printf("{s}", .{self.s(seg.name)});
        }
    }

    /// Print the struct pattern field `id` along with its nested pattern.
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
