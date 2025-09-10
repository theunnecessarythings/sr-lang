const std = @import("std");
const List = std.array_list.Managed;
const cst = @import("cst.zig");
const Tag = @import("lexer.zig").Token.Tag;
const Loc = @import("lexer.zig").Token.Loc;

pub const Unit = struct {
    decls: List(Decl),
    package: ?PackageDecl,
};

pub const PackageDecl = struct {
    name: []const u8,
    loc: Loc,
};

pub const Decl = struct {
    binding: ?*Pattern,
    value: *Expr,
    ty: ?*Expr,
    is_const: bool,
    loc: Loc,
};

pub const Expr = union(enum) {
    // Basic Lits
    IntLit: IntLit,
    FloatLit: FloatLit,
    BoolLit: BoolLit,
    StringLit: StringLit,
    CharLit: CharLit,
    NullLit: NullLit,
    UndefLit: UndefLit,

    Identifier: Identifier,

    Type: BuiltinType,

    // Compound Lits
    TupleLit: TupleLit,
    ArrayLit: ArrayLit,
    MapLit: MapLit,
    StructLit: StructLit,
    VariantLit: VariantLit,
    EnumLit: EnumLit,
    FunctionLit: FunctionLit,

    // Prefix Ops
    UnaryPlus: UnaryPlus,
    UnaryMinus: UnaryMinus,
    AddressOf: AddressOf,
    LogicalNot: LogicalNot,

    // Range Op
    Range: Range,

    // Infix Ops
    InfixAdd: InfixAdd,
    InfixSub: InfixSub,
    InfixMul: InfixMul,
    InfixDiv: InfixDiv,
    InfixMod: InfixMod,
    InfixShl: InfixShl,
    InfixShr: InfixShr,
    InfixBitAnd: InfixBitAnd,
    InfixBitOr: InfixBitOr,
    InfixBitXor: InfixBitXor,

    InfixEq: InfixEq,
    InfixNeq: InfixNeq,
    InfixLt: InfixLt,
    InfixLte: InfixLte,
    InfixGt: InfixGt,
    InfixGte: InfixGte,
    InfixLogicalAnd: InfixLogicalAnd,
    InfixLogicalOr: InfixLogicalOr,

    InfixCatch: InfixCatch,
    InfixOrelse: InfixOrelse,

    // Postfix Ops
    PostfixErrorUnwrap: PostfixErrorUnwrap,
    PostfixOptionalUnwrap: PostfixOptionalUnwrap,
    PostfixDeref: PostfixDeref,
    PostfixIndex: PostfixIndex,
    PostfixField: PostfixField,
    PostfixCall: PostfixCall,
    PostfixAwait: PostfixAwait,

    // Cast Ops
    CastNormal: CastNormal,
    CastBit: CastBit,
    CastSaturate: CastSaturate,
    CastWrap: CastWrap,
    CastChecked: CastChecked,

    // Control Flow Ops
    If: If,
    While: While,
    For: For,
    Match: Match,

    // Block Ops
    Block: Block,
    ComptimeBlock: ComptimeBlock,
    CodeBlock: CodeBlock,
    AsyncBlock: AsyncBlock,
    MlirBlock: MlirBlock,
    Closure: Closure,

    Import: Import,
    TypeOf: TypeOf,
};

pub const Statement = union(enum) {
    Expr: Expr,
    Decl: Decl,
    Assign: Assign,
    Insert: Insert,
    Return: Return,
    Break: Break,
    Continue: Continue,
    Unreachable: Unreachable,
    Defer: Defer,
    ErrDefer: ErrDefer,
};

pub const Attribute = struct {
    name: []const u8,
    value: ?*Expr,
    loc: Loc,
};

//===========================================================================
// Expression Nodes
//===========================================================================

pub const IntLit = struct { value: []const u8, loc: Loc };
pub const FloatLit = struct { value: []const u8, loc: Loc };
pub const BoolLit = struct { value: bool, loc: Loc };
pub const StringLit = struct { value: []const u8, loc: Loc };
pub const CharLit = struct { value: u32, loc: Loc };
pub const NullLit = struct { loc: Loc };
pub const UndefLit = struct { loc: Loc };
pub const Identifier = struct { name: []const u8, loc: Loc };

pub const TupleLit = struct { elems: List(*Expr), loc: Loc };
pub const ArrayLit = struct { elems: List(*Expr), loc: Loc };
pub const MapLit = struct { entries: List(KeyValue), loc: Loc };
pub const StructLit = struct { fields: List(StructFieldValue), loc: Loc };
pub const VariantLit = struct { name: []const u8, value: ?*Expr, loc: Loc };
pub const EnumLit = struct { name: []const u8, value: ?*Expr, loc: Loc };
pub const FunctionLit = struct {
    params: List(Param),
    result_ty: ?*Expr,
    body: ?Block,
    loc: Loc,
    is_proc: bool,
    is_async: bool,
    is_variadic: bool,
    is_extern: bool,
    raw_asm: ?[]const u8 = null,
    attrs: ?List(Attribute) = null,
};
pub const UnaryPlus = struct { right: *Expr, loc: Loc };
pub const UnaryMinus = struct { right: *Expr, loc: Loc };
pub const AddressOf = struct { right: *Expr, loc: Loc };
pub const LogicalNot = struct { right: *Expr, loc: Loc };
pub const Range = struct { start: ?*Expr, end: ?*Expr, inclusive_right: bool, loc: Loc };
pub const InfixAdd = struct { left: *Expr, right: *Expr, loc: Loc, wrap: bool, saturate: bool };
pub const InfixSub = struct { left: *Expr, right: *Expr, loc: Loc, wrap: bool, saturate: bool };
pub const InfixMul = struct { left: *Expr, right: *Expr, loc: Loc, wrap: bool, saturate: bool };
pub const InfixDiv = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixMod = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixShl = struct { left: *Expr, right: *Expr, loc: Loc, saturate: bool };
pub const InfixShr = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixBitAnd = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixBitOr = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixBitXor = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixEq = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixNeq = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixLt = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixLte = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixGt = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixGte = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixLogicalAnd = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixLogicalOr = struct { left: *Expr, right: *Expr, loc: Loc };
pub const InfixCatch = struct { left: *Expr, right: *Expr, binding: ?Identifier, loc: Loc };
pub const InfixOrelse = struct { left: *Expr, right: *Expr, loc: Loc };

pub const PostfixErrorUnwrap = struct { expr: *Expr, loc: Loc };
pub const PostfixOptionalUnwrap = struct { expr: *Expr, loc: Loc };
pub const PostfixDeref = struct { expr: *Expr, loc: Loc };
pub const PostfixIndex = struct { collection: *Expr, index: *Expr, loc: Loc };
pub const PostfixField = struct { parent: *Expr, field: []const u8, is_tuple: bool, loc: Loc };
pub const PostfixCall = struct { callee: *Expr, args: List(*Expr), loc: Loc };
pub const PostfixAwait = struct { expr: *Expr, loc: Loc };

pub const CastNormal = struct { expr: *Expr, ty: *Expr, loc: Loc };
pub const CastBit = struct { expr: *Expr, ty: *Expr, loc: Loc };
pub const CastSaturate = struct { expr: *Expr, ty: *Expr, loc: Loc };
pub const CastWrap = struct { expr: *Expr, ty: *Expr, loc: Loc };
pub const CastChecked = struct { expr: *Expr, ty: *Expr, loc: Loc };

pub const If = struct {
    cond: *Expr,
    then_block: Block,
    else_block: ?*Expr,
    loc: Loc,
};
pub const While = struct {
    cond: ?*Expr,
    pattern: ?*Pattern,
    body: Block,
    loc: Loc,
    is_pattern: bool,
    label: ?[]const u8 = null,
};
pub const For = struct {
    pattern: *Pattern,
    iterable: *Expr,
    body: Block,
    loc: Loc,
    label: ?[]const u8 = null,
};
pub const Match = struct { expr: *Expr, arms: List(MatchArm), loc: Loc };
pub const MatchArm = struct { pattern: *Pattern, guard: ?*Expr, body: *Expr, loc: Loc };
pub const Block = struct { items: List(Statement), loc: Loc };
pub const ComptimeBlock = struct { block: Block, loc: Loc };
pub const CodeBlock = struct { block: Block, loc: Loc };
pub const MlirBlock = struct { kind: MlirKind, text: []const u8, loc: Loc };
pub const MlirKind = enum { Module, Type, Attribute, Operation };
pub const AsyncBlock = struct { body: *Expr, loc: Loc };
pub const Closure = struct {
    params: List(Param),
    result_ty: ?*Expr,
    body: *Expr,
    loc: Loc,
};
pub const Import = struct { expr: *Expr, loc: Loc };
pub const TypeOf = struct { expr: *Expr, loc: Loc };

pub const Assign = struct { left: *Expr, right: *Expr, loc: Loc };
pub const KeyValue = struct { key: *Expr, value: *Expr, loc: Loc };
pub const StructFieldValue = struct { name: ?[]const u8, value: *Expr, loc: Loc };
pub const Param = struct {
    pat: ?*Pattern,
    ty: ?*Expr,
    value: ?*Expr,
    loc: Loc,
    attrs: ?List(Attribute) = null,
};

//===========================================================================
// Statement Nodes
//===========================================================================
pub const Return = struct { value: ?*Expr, loc: Loc };
pub const Break = struct { loc: Loc, label: ?[]const u8 = null, value: ?*Expr = null };
pub const Continue = struct { loc: Loc };
pub const Unreachable = struct { loc: Loc };
pub const Defer = struct { expr: *Expr, loc: Loc };
pub const ErrDefer = struct { expr: *Expr, loc: Loc };
pub const Insert = struct { expr: *Expr, loc: Loc };

pub const BuiltinType = union(enum) {
    Tuple: TupleType,
    Array: ArrayType,
    DynArray: UnaryType,
    MapType: MapType,
    Slice: UnaryType,
    Optional: UnaryType,
    ErrorSet: ErrorSetType,
    Error: VariantLikeType,
    Struct: StructLikeType,
    Enum: EnumType,
    Variant: VariantLikeType,
    Union: StructLikeType,
    Pointer: PointerType,
    Simd: SimdType,
    Complex: ComplexType,
    Tensor: TensorType,
    Type: TypeType,
    Any: AnyType,
    Noreturn: NoreturnType,
};

pub const UnaryType = struct {
    elem: *Expr,
    loc: Loc,
};

pub const StructLikeType = struct {
    fields: List(StructField),
    loc: Loc,
    is_extern: bool,
    attrs: ?List(Attribute) = null,
};

pub const VariantLikeType = struct {
    fields: List(VariantField),
    loc: Loc,
};

pub const ArrayType = struct {
    elem: *Expr,
    size: *Expr,
    loc: Loc,
};

pub const MapType = struct {
    key: *Expr,
    value: *Expr,
    loc: Loc,
};

pub const ErrorSetType = struct {
    err: *Expr,
    value: *Expr,
    loc: Loc,
};

pub const StructField = struct {
    name: []const u8,
    ty: *Expr,
    value: ?*Expr,
    loc: Loc,
    attrs: ?List(Attribute) = null,
};

pub const EnumField = struct {
    name: []const u8,
    value: ?*Expr,
    loc: Loc,
    attrs: ?List(Attribute) = null,
};

pub const EnumType = struct {
    fields: List(EnumField),
    discriminant: ?*Expr,
    is_extern: bool,
    loc: Loc,
    attrs: ?List(Attribute) = null,
};

pub const VariantField = struct {
    name: []const u8,
    ty: ?VariantPayload,
    value: ?*Expr,
    loc: Loc,
    attrs: ?List(Attribute) = null,
};

pub const VariantPayload = union(enum) {
    Tuple: List(*Expr),
    Struct: List(StructField),
};

pub const PointerType = struct {
    elem: *Expr,
    is_const: bool,
    loc: Loc,
};

pub const SimdType = struct {
    elem: *Expr,
    lanes: *Expr,
    loc: Loc,
};

pub const ComplexType = struct {
    elem: *Expr,
    loc: Loc,
};

pub const TensorType = struct {
    elem: *Expr,
    shape: List(*Expr),
    loc: Loc,
};

pub const TypeType = struct {
    loc: Loc,
};

pub const AnyType = struct {
    loc: Loc,
};

pub const NoreturnType = struct {
    loc: Loc,
};

pub const TupleType = struct {
    elems: List(*Expr),
    loc: Loc,
};

pub const Pattern = union(enum) {
    Wildcard: WildcardPattern, // _
    Literal: *Expr, // reuse existing literal expr nodes
    Path: PathPattern, // foo::bar::Baz
    Binding: BindingPattern, // x, mut x, ref x, ref mut x
    Tuple: TuplePattern, // (p1, p2, p3)
    Slice: SlicePattern, // [p1, p2, .., pN]
    Struct: StructPattern, // Path { field1: p1, field2: p2, .. }
    VariantTuple: VariantTuplePattern, // Path(p1, p2, p3)
    VariantStruct: VariantStructPattern, // Path { field1: p1, field2: p2, .. }
    Range: RangePattern, // start .. end, start ..= end
    Or: OrPattern, // pat1 | pat2 | pat3
    At: AtPattern, // binder @ pat
};

pub const RangePattern = struct {
    start: ?*Expr,
    end: ?*Expr,
    inclusive_right: bool,
    loc: Loc,
};

pub const OrPattern = struct {
    alts: List(*Pattern),
    loc: Loc,
};

pub const AtPattern = struct {
    binder: []const u8,
    pattern: *Pattern,
    loc: Loc,
};

pub const VariantTuplePattern = struct {
    path: List(BindingPattern),
    elems: List(*Pattern),
    loc: Loc,
};

pub const VariantStructPattern = struct {
    path: List(BindingPattern),
    fields: List(StructPatternField),
    has_rest: bool,
    loc: Loc,
};

pub const StructPattern = struct {
    path: List(BindingPattern),
    fields: List(StructPatternField),
    has_rest: bool,
    loc: Loc,
};

pub const StructPatternField = struct {
    name: []const u8,
    pattern: *Pattern,
    loc: Loc,
};

pub const PathPattern = struct {
    segments: List(BindingPattern),
    loc: Loc,
};

pub const BindingPattern = struct {
    name: []const u8,
    by_ref: bool = false,
    is_mut: bool = false,
    loc: Loc,
};

pub const WildcardPattern = struct {
    loc: Loc,
};

pub const TuplePattern = struct {
    elems: List(*Pattern),
    loc: Loc,
};

pub const SlicePattern = struct {
    elems: List(*Pattern),
    has_rest: bool,
    rest_index: usize,
    rest_binding: ?*Pattern,
    loc: Loc,
};

// AST Printer (LISP-style), mirroring CST printer style
pub const AstPrinter = struct {
    writer: *std.io.Writer,
    indent_size: usize = 0,

    pub fn init(writer: *std.io.Writer) AstPrinter {
        return .{ .writer = writer };
    }

    fn printIndent(self: *AstPrinter) !void {
        for (0..self.indent_size) |_| {
            try self.writer.print(" ", .{});
        }
    }

    inline fn deindent(self: *AstPrinter) void {
        if (self.indent_size >= 2) self.indent_size -= 2;
    }

    inline fn indent(self: *AstPrinter) void {
        self.indent_size += 2;
    }

    fn beginNode(self: *AstPrinter, comptime fmt: []const u8, args: anytype) !void {
        try self.printIndent();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
        self.indent();
    }

    fn endNode(self: *AstPrinter) !void {
        self.deindent();
        try self.printIndent();
        try self.writer.writeAll(")\n");
    }

    fn printLeaf(self: *AstPrinter, comptime fmt: []const u8, args: anytype) !void {
        try self.printIndent();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
    }

    fn printAttributes(self: *AstPrinter, attrs: List(Attribute)) !void {
        try self.beginNode("(attributes", .{});
        for (attrs.items) |a| {
            try self.beginNode("(attr name=\"{s}\"", .{a.name});
            if (a.value) |v| try self.printNamedExpr("value", v);
            try self.endNode();
        }
        try self.endNode();
    }

    fn printNamedExpr(self: *AstPrinter, name: []const u8, expr: *const Expr) !void {
        try self.beginNode("({s}", .{name});
        try self.printExpr(expr);
        try self.endNode();
    }

    fn printUnary(self: *AstPrinter, name: []const u8, expr: *const Expr) !void {
        try self.beginNode("({s}", .{name});
        try self.printExpr(expr);
        try self.endNode();
    }

    fn printBinary(self: *AstPrinter, name: []const u8, left: *const Expr, right: *const Expr) !void {
        try self.beginNode("({s}", .{name});
        try self.printExpr(left);
        try self.printExpr(right);
        try self.endNode();
    }

    fn printExprList(self: *AstPrinter, name: []const u8, exprs: List(*Expr)) anyerror!void {
        try self.beginNode("({s}", .{name});
        for (exprs.items) |item| try self.printExpr(item);
        try self.endNode();
    }

    fn printStructField(self: *AstPrinter, field: *const StructField) !void {
        try self.beginNode("(field name=\"{s}\"", .{field.name});
        if (field.attrs) |attrs| try self.printAttributes(attrs);
        try self.printExpr(field.ty);
        if (field.value) |val| try self.printNamedExpr("value", val);
        try self.endNode();
    }

    pub fn print(self: *AstPrinter, unit: *const Unit) !void {
        self.indent_size = 0;
        try self.beginNode("(unit package={s}", .{if (unit.package) |pkg| pkg.name else "null"});
        for (unit.decls.items) |decl| try self.printDecl(&decl);
        try self.endNode();
    }

    fn printDecl(self: *AstPrinter, decl: *const Decl) !void {
        try self.beginNode("(decl is_const={}", .{decl.is_const});
        if (decl.ty) |ty| try self.printNamedExpr("type", ty);
        if (decl.binding) |b| try self.printPattern(b);
        try self.beginNode("(value", .{});
        try self.printExpr(decl.value);
        try self.endNode();
        try self.endNode();
    }

    fn printStatement(self: *AstPrinter, stmt: *const Statement) anyerror!void {
        switch (stmt.*) {
            .Expr => |e| {
                try self.beginNode("(expr_stmt", .{});
                try self.printExpr(&e);
                try self.endNode();
            },
            .Decl => |d| try self.printDecl(&d),
            .Assign => |as| try self.printBinary("assign", as.left, as.right),
            .Insert => |ins| {
                try self.beginNode("(insert", .{});
                try self.printExpr(ins.expr);
                try self.endNode();
            },
            .Return => |ret| {
                try self.beginNode("(return", .{});
                if (ret.value) |val| try self.printNamedExpr("value", val);
                try self.endNode();
            },
            .Break => |b| {
                try self.beginNode("(break", .{});
                if (b.label) |lbl| try self.printLeaf("label=\"{s}\"", .{lbl});
                if (b.value) |val| try self.printNamedExpr("value", val);
                try self.endNode();
            },
            .Continue => |_| try self.printLeaf("(continue)", .{}),
            .Unreachable => |_| try self.printLeaf("(unreachable)", .{}),
            .Defer => |d| {
                try self.beginNode("(defer", .{});
                try self.printExpr(d.expr);
                try self.endNode();
            },
            .ErrDefer => |d| {
                try self.beginNode("(errdefer", .{});
                try self.printExpr(d.expr);
                try self.endNode();
            },
        }
    }

    fn printExpr(self: *AstPrinter, expr: *const Expr) anyerror!void {
        switch (expr.*) {
            .IntLit => |lit| try self.printLeaf("(int \"{s}\")", .{lit.value}),
            .FloatLit => |lit| try self.printLeaf("(float \"{s}\")", .{lit.value}),
            .BoolLit => |lit| try self.printLeaf("(bool {})", .{lit.value}),
            .StringLit => |lit| try self.printLeaf("(string \"{s}\")", .{lit.value}),
            .CharLit => |lit| try self.printLeaf("(char {d})", .{lit.value}),
            .NullLit => |_| try self.printLeaf("(null)", .{}),
            .UndefLit => |_| try self.printLeaf("(undef)", .{}),

            .Identifier => |ident| try self.printLeaf("(ident \"{s}\")", .{ident.name}),

            .Type => |b| try self.printBuiltinType(&b),

            .TupleLit => |t| try self.printExprList("tuple", t.elems),
            .ArrayLit => |a| try self.printExprList("array", a.elems),
            .MapLit => |m| {
                try self.beginNode("(map", .{});
                for (m.entries.items) |entry| {
                    try self.beginNode("(entry", .{});
                    try self.printNamedExpr("key", entry.key);
                    try self.printNamedExpr("value", entry.value);
                    try self.endNode();
                }
                try self.endNode();
            },
            .StructLit => |st| {
                try self.beginNode("(struct_literal", .{});
                for (st.fields.items) |field| {
                    try self.beginNode("(field", .{});
                    if (field.name) |name| try self.printLeaf("name=\"{s}\"", .{name}) else try self.printLeaf("name=null", .{});
                    try self.printNamedExpr("value", field.value);
                    try self.endNode();
                }
                try self.endNode();
            },
            .VariantLit => |vl| {
                try self.beginNode("(variant_literal name=\"{s}\"", .{vl.name});
                if (vl.value) |v| try self.printNamedExpr("value", v);
                try self.endNode();
            },
            .EnumLit => |el| {
                try self.beginNode("(enum_literal name=\"{s}\"", .{el.name});
                if (el.value) |v| try self.printNamedExpr("value", v);
                try self.endNode();
            },
            .FunctionLit => |fun| {
                try self.beginNode("({s}", .{if (fun.is_proc) "procedure" else "function"});
                if (fun.attrs) |attrs| try self.printAttributes(attrs);
                if (fun.is_async) try self.printLeaf("(async)", .{});
                if (fun.is_variadic) try self.printLeaf("(variadic)", .{});
                if (fun.is_extern) try self.printLeaf("(extern)", .{});
                for (fun.params.items) |param| {
                    try self.beginNode("(param", .{});
                    if (param.attrs) |attrs| try self.printAttributes(attrs);
                    if (param.pat) |pat| {
                        try self.beginNode("(pat", .{});
                        try self.printPattern(pat);
                        try self.endNode();
                    }
                    if (param.ty) |pty| try self.printNamedExpr("type", pty);
                    if (param.value) |pv| try self.printNamedExpr("value", pv);
                    try self.endNode();
                }
                if (fun.result_ty) |res| try self.printNamedExpr("result", res);
                if (fun.body) |body| {
                    try self.beginNode("(body", .{});
                    for (body.items.items) |item| try self.printStatement(&item);
                    try self.endNode();
                } else if (fun.raw_asm) |asm_text| {
                    try self.printLeaf("(asm_body \"{s}\")", .{asm_text});
                }
                try self.endNode();
            },

            .UnaryPlus => |u| try self.printUnary("unary_plus", u.right),
            .UnaryMinus => |u| try self.printUnary("unary_minus", u.right),
            .AddressOf => |u| try self.printUnary("address_of", u.right),
            .LogicalNot => |u| try self.printUnary("logical_not", u.right),

            .Range => |r| {
                try self.beginNode("(range inclusive_right={}", .{r.inclusive_right});
                if (r.start) |s| try self.printNamedExpr("start", s);
                if (r.end) |e| try self.printNamedExpr("end", e);
                try self.endNode();
            },

            .InfixAdd => |i| {
                try self.beginNode("(add wrap={} saturate={}", .{ i.wrap, i.saturate });
                try self.printExpr(i.left);
                try self.printExpr(i.right);
                try self.endNode();
            },
            .InfixSub => |i| {
                try self.beginNode("(sub wrap={} saturate={}", .{ i.wrap, i.saturate });
                try self.printExpr(i.left);
                try self.printExpr(i.right);
                try self.endNode();
            },
            .InfixMul => |i| {
                try self.beginNode("(mul wrap={} saturate={}", .{ i.wrap, i.saturate });
                try self.printExpr(i.left);
                try self.printExpr(i.right);
                try self.endNode();
            },
            .InfixDiv => |i| try self.printBinary("div", i.left, i.right),
            .InfixMod => |i| try self.printBinary("mod", i.left, i.right),
            .InfixShl => |i| {
                try self.beginNode("(shl saturate={}", .{i.saturate});
                try self.printExpr(i.left);
                try self.printExpr(i.right);
                try self.endNode();
            },
            .InfixShr => |i| try self.printBinary("shr", i.left, i.right),
            .InfixBitAnd => |i| try self.printBinary("bit_and", i.left, i.right),
            .InfixBitOr => |i| try self.printBinary("bit_or", i.left, i.right),
            .InfixBitXor => |i| try self.printBinary("bit_xor", i.left, i.right),
            .InfixEq => |i| try self.printBinary("eq", i.left, i.right),
            .InfixNeq => |i| try self.printBinary("neq", i.left, i.right),
            .InfixLt => |i| try self.printBinary("lt", i.left, i.right),
            .InfixLte => |i| try self.printBinary("lte", i.left, i.right),
            .InfixGt => |i| try self.printBinary("gt", i.left, i.right),
            .InfixGte => |i| try self.printBinary("gte", i.left, i.right),
            .InfixLogicalAnd => |i| try self.printBinary("and", i.left, i.right),
            .InfixLogicalOr => |i| try self.printBinary("or", i.left, i.right),
            .InfixCatch => |i| {
                try self.beginNode("(catch", .{});
                try self.printExpr(i.left);
                if (i.binding) |b| try self.printLeaf("binding=\"{s}\"", .{b.name});
                try self.printExpr(i.right);
                try self.endNode();
            },
            .InfixOrelse => |i| try self.printBinary("orelse", i.left, i.right),

            .PostfixErrorUnwrap => |p| try self.printUnary("error_unwrap", p.expr),
            .PostfixOptionalUnwrap => |p| try self.printUnary("optional_unwrap", p.expr),
            .PostfixDeref => |p| try self.printUnary("deref", p.expr),
            .PostfixIndex => |p| {
                try self.beginNode("(index", .{});
                try self.printNamedExpr("collection", p.collection);
                try self.printNamedExpr("index", p.index);
                try self.endNode();
            },
            .PostfixField => |p| {
                try self.beginNode("(field name=\"{s}\" is_tuple={}", .{ p.field, p.is_tuple });
                try self.printExpr(p.parent);
                try self.endNode();
            },
            .PostfixCall => |p| {
                try self.beginNode("(call", .{});
                try self.printNamedExpr("callee", p.callee);
                try self.printExprList("args", p.args);
                try self.endNode();
            },
            .PostfixAwait => |p| try self.printUnary("await", p.expr),

            .CastNormal => |c| {
                try self.beginNode("(cast", .{});
                try self.printNamedExpr("expr", c.expr);
                try self.printNamedExpr("type", c.ty);
                try self.endNode();
            },
            .CastBit => |c| {
                try self.beginNode("(bitcast", .{});
                try self.printNamedExpr("expr", c.expr);
                try self.printNamedExpr("type", c.ty);
                try self.endNode();
            },
            .CastSaturate => |c| {
                try self.beginNode("(saturating_cast", .{});
                try self.printNamedExpr("expr", c.expr);
                try self.printNamedExpr("type", c.ty);
                try self.endNode();
            },
            .CastWrap => |c| {
                try self.beginNode("(wrapping_cast", .{});
                try self.printNamedExpr("expr", c.expr);
                try self.printNamedExpr("type", c.ty);
                try self.endNode();
            },
            .CastChecked => |c| {
                try self.beginNode("(checked_cast", .{});
                try self.printNamedExpr("expr", c.expr);
                try self.printNamedExpr("type", c.ty);
                try self.endNode();
            },

            .If => |if_expr| {
                try self.beginNode("(if", .{});
                try self.printNamedExpr("cond", if_expr.cond);
                try self.beginNode("(then", .{});
                for (if_expr.then_block.items.items) |item| try self.printStatement(&item);
                try self.endNode();
                if (if_expr.else_block) |else_e| try self.printNamedExpr("else", else_e);
                try self.endNode();
            },
            .While => |w| {
                try self.beginNode("(while is_pattern={}", .{w.is_pattern});
                if (w.label) |lbl| try self.printLeaf("label=\"{s}\"", .{lbl});
                if (w.pattern) |pat| {
                    try self.beginNode("(pattern", .{});
                    try self.printPattern(pat);
                    try self.endNode();
                }
                if (w.cond) |c| try self.printNamedExpr("cond", c);
                try self.beginNode("(body", .{});
                for (w.body.items.items) |item| try self.printStatement(&item);
                try self.endNode();
                try self.endNode();
            },
            .For => |f| {
                try self.beginNode("(for", .{});
                if (f.label) |lbl| try self.printLeaf("label=\"{s}\"", .{lbl});
                try self.beginNode("(pattern", .{});
                try self.printPattern(f.pattern);
                try self.endNode();
                try self.printNamedExpr("iterable", f.iterable);
                try self.beginNode("(body", .{});
                for (f.body.items.items) |item| try self.printStatement(&item);
                try self.endNode();
                try self.endNode();
            },
            .Match => |m| {
                try self.beginNode("(match", .{});
                try self.printNamedExpr("expr", m.expr);
                for (m.arms.items) |arm| {
                    try self.beginNode("(arm", .{});
                    try self.beginNode("(pattern", .{});
                    try self.printPattern(arm.pattern);
                    try self.endNode();
                    if (arm.guard) |g| try self.printNamedExpr("guard", g);
                    try self.printNamedExpr("body", arm.body);
                    try self.endNode();
                }
                try self.endNode();
            },

            .Block => |blk| {
                try self.beginNode("(block", .{});
                for (blk.items.items) |item| try self.printStatement(&item);
                try self.endNode();
            },
            .ComptimeBlock => |cb| {
                try self.beginNode("(comptime_block", .{});
                for (cb.block.items.items) |item| try self.printStatement(&item);
                try self.endNode();
            },
            .CodeBlock => |cb| {
                try self.beginNode("(code_block", .{});
                for (cb.block.items.items) |item| try self.printStatement(&item);
                try self.endNode();
            },
            .AsyncBlock => |ab| {
                try self.beginNode("(async", .{});
                try self.printExpr(ab.body);
                try self.endNode();
            },
            .MlirBlock => |ml| {
                const kind_str = switch (ml.kind) {
                    .Module => "module",
                    .Type => "type",
                    .Attribute => "attribute",
                    .Operation => "operation",
                };
                try self.beginNode("(mlir", .{});
                try self.printLeaf("kind={s}", .{kind_str});
                try self.printLeaf("text:{s}", .{ml.text});
                try self.endNode();
            },
            .Closure => |cl| {
                try self.beginNode("(closure", .{});
                for (cl.params.items) |param| {
                    try self.beginNode("(param", .{});
                    if (param.attrs) |attrs| try self.printAttributes(attrs);
                    if (param.pat) |pat| {
                        try self.beginNode("(pat", .{});
                        try self.printPattern(pat);
                        try self.endNode();
                    }
                    if (param.ty) |pty| try self.printNamedExpr("type", pty);
                    if (param.value) |pv| try self.printNamedExpr("value", pv);
                    try self.endNode();
                }
                if (cl.result_ty) |res| try self.printNamedExpr("result", res);
                try self.printNamedExpr("body", cl.body);
                try self.endNode();
            },

            .Import => |imp| {
                try self.beginNode("(import", .{});
                try self.printExpr(imp.expr);
                try self.endNode();
            },
            .TypeOf => |t| {
                try self.beginNode("(typeof", .{});
                try self.printExpr(t.expr);
                try self.endNode();
            },
        }
    }

    fn printPattern(self: *AstPrinter, pattern: *const Pattern) anyerror!void {
        switch (pattern.*) {
            .Wildcard => try self.printLeaf("(wildcard)", .{}),
            .Literal => |lit| try self.printNamedExpr("literal", lit),
            .Path => |path| {
                try self.beginNode("(path", .{});
                for (path.segments.items) |seg| try self.printLeaf("segment=\"{s}\"", .{seg.name});
                try self.endNode();
            },
            .Binding => |bind| {
                try self.printLeaf(
                    "(binding name=\"{s}\" by_ref={} is_mut={})",
                    .{ bind.name, bind.by_ref, bind.is_mut },
                );
            },
            .Tuple => |t| {
                try self.beginNode("(tuple_pattern", .{});
                for (t.elems.items) |elem| try self.printPattern(elem);
                try self.endNode();
            },
            .Slice => |slice| {
                try self.beginNode("(slice_pattern has_rest={}", .{slice.has_rest});
                for (slice.elems.items) |elem| try self.printPattern(elem);
                if (slice.rest_binding) |rest| {
                    try self.beginNode("(rest_binding", .{});
                    try self.printPattern(rest);
                    try self.endNode();
                }
                try self.endNode();
            },
            .Struct => |st| {
                try self.beginNode("(struct_pattern has_rest={}", .{st.has_rest});
                for (st.path.items) |seg| try self.printLeaf("segment=\"{s}\"", .{seg.name});
                for (st.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\"", .{field.name});
                    try self.printPattern(field.pattern);
                    try self.endNode();
                }
                try self.endNode();
            },
            .VariantTuple => |vt| {
                try self.beginNode("(variant_tuple_pattern", .{});
                for (vt.path.items) |seg| try self.printLeaf("segment=\"{s}\"", .{seg.name});
                for (vt.elems.items) |elem| try self.printPattern(elem);
                try self.endNode();
            },
            .VariantStruct => |vs| {
                try self.beginNode("(variant_struct_pattern has_rest={}", .{vs.has_rest});
                for (vs.path.items) |seg| try self.printLeaf("segment=\"{s}\"", .{seg.name});
                for (vs.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\"", .{field.name});
                    try self.printPattern(field.pattern);
                    try self.endNode();
                }
                try self.endNode();
            },
            .Range => |range| {
                try self.beginNode("(range_pattern inclusive_right={}", .{range.inclusive_right});
                if (range.start) |start| try self.printNamedExpr("start", start);
                if (range.end) |end| try self.printNamedExpr("end", end);
                try self.endNode();
            },
            .Or => |or_p| {
                try self.beginNode("(or_pattern", .{});
                for (or_p.alts.items) |alt| try self.printPattern(alt);
                try self.endNode();
            },
            .At => |at| {
                try self.beginNode("(at_pattern binder=\"{s}\"", .{at.binder});
                try self.printPattern(at.pattern);
                try self.endNode();
            },
        }
    }

    fn printBuiltinType(self: *AstPrinter, btype: *const BuiltinType) anyerror!void {
        switch (btype.*) {
            .Tuple => |t| try self.printExprList("tuple", t.elems),
            .Array => |a| try self.printBinary("array", a.elem, a.size),
            .DynArray => |u| try self.printUnary("dyn_array", u.elem),
            .MapType => |m| try self.printBinary("map", m.key, m.value),
            .Slice => |u| try self.printUnary("slice", u.elem),
            .Optional => |u| try self.printUnary("optional", u.elem),
            .ErrorSet => |es| try self.printBinary("error_set", es.err, es.value),
            .Struct => |st| {
                try self.beginNode("(struct", .{});
                if (st.attrs) |attrs| try self.printAttributes(attrs);
                try self.printLeaf("is_extern={}", .{st.is_extern});
                for (st.fields.items) |field| try self.printStructField(&field);
                try self.endNode();
            },
            .Enum => |en| {
                try self.beginNode("(enum", .{});
                if (en.attrs) |attrs| try self.printAttributes(attrs);
                try self.printLeaf("is_extern={}", .{en.is_extern});
                if (en.discriminant) |disc| try self.printNamedExpr("discriminant", disc);
                for (en.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\"", .{field.name});
                    if (field.attrs) |attrs| try self.printAttributes(attrs);
                    if (field.value) |val| try self.printExpr(val);
                    try self.endNode();
                }
                try self.endNode();
            },
            .Variant => |variant| {
                try self.beginNode("(variant", .{});
                for (variant.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\"", .{field.name});
                    if (field.attrs) |attrs| try self.printAttributes(attrs);
                    if (field.ty) |ty| {
                        switch (ty) {
                            .Tuple => |tup| try self.printExprList("tuple", tup),
                            .Struct => |st_fields| {
                                try self.beginNode("(struct", .{});
                                for (st_fields.items) |f| try self.printStructField(&f);
                                try self.endNode();
                            },
                        }
                    }
                    if (field.value) |val| try self.printNamedExpr("value", val);
                    try self.endNode();
                }
                try self.endNode();
            },
            .Union => |un| {
                try self.beginNode("(union", .{});
                if (un.attrs) |attrs| try self.printAttributes(attrs);
                try self.printLeaf("is_extern={}", .{un.is_extern});
                for (un.fields.items) |field| try self.printStructField(&field);
                try self.endNode();
            },
            .Error => |err| {
                try self.beginNode("(error", .{});
                for (err.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\"", .{field.name});
                    if (field.attrs) |attrs| try self.printAttributes(attrs);
                    if (field.ty) |ty| {
                        switch (ty) {
                            .Tuple => |tup| try self.printExprList("tuple", tup),
                            .Struct => |st_fields| {
                                try self.beginNode("(struct", .{});
                                for (st_fields.items) |f| try self.printStructField(&f);
                                try self.endNode();
                            },
                        }
                    }
                    try self.endNode();
                }
                try self.endNode();
            },
            .Pointer => |ptr| {
                try self.beginNode("(pointer is_const={}", .{ptr.is_const});
                try self.printExpr(ptr.elem);
                try self.endNode();
            },
            .Simd => |simd| try self.printBinary("simd", simd.elem, simd.lanes),
            .Complex => |comp| try self.printUnary("complex", comp.elem),
            .Tensor => |tensor| {
                try self.beginNode("(tensor", .{});
                try self.printExpr(tensor.elem);
                try self.printExprList("shape", tensor.shape);
                try self.endNode();
            },
            .Type => try self.printLeaf("(type)", .{}),
            .Any => try self.printLeaf("(any)", .{}),
            .Noreturn => try self.printLeaf("(noreturn)", .{}),
        }
    }
};
