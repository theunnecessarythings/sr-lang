const std = @import("std");
const List = std.array_list.Managed;
const Loc = @import("lexer.zig").Token.Loc;
const Tag = @import("lexer.zig").Token.Tag;

pub const Program = struct {
    decls: List(Decl),
    package: ?PackageDecl,
};

pub const PackageDecl = struct {
    name: []const u8,
    loc: Loc,
};

pub const Decl = struct {
    lhs: ?*Expr,
    rhs: *Expr,
    ty: ?*Expr,
    loc: Loc,
    is_const: bool,
    is_assign: bool,
};

pub const Attribute = struct {
    name: []const u8,
    value: ?*Expr,
    loc: Loc,
};

pub const Expr = union(enum) {
    Literal: Literal,
    Ident: Ident,
    Prefix: Prefix,
    Infix: Infix,
    Deref: Deref,
    BuiltinType: BuiltinType,
    Array: Array,
    Tuple: Tuple, // NOTE: used for both tuple literals and tuple types
    Map: Map,
    Function: Function,
    Block: Block,
    // Metaprogramming and low-level constructs
    Comptime: Comptime,
    Code: CodeBlock,
    Insert: Insert,
    Mlir: Mlir,
    Call: Call,
    Index: Index,
    Field: Field,
    Struct: StructLiteral,
    Return: Return,
    If: If,
    While: While,
    For: For,
    Match: Match,
    Break: Break,
    Continue: Continue,
    Unreachable: Unreachable,
    Null: Null,
    Defer: Defer,
    ErrDefer: ErrDefer,
    ErrUnwrap: ErrUnwrap,
    Catch: Catch,
    Await: Await,
    Closure: Closure,
    Async: Async,
    Cast: Cast,
    Import: Import,
    TypeOf: TypeOf,
};

pub const Literal = struct {
    value: []const u8,
    loc: Loc,
    kind: Tag,
};

pub const Array = struct {
    elems: List(*Expr),
    loc: Loc,
};

pub const Tuple = struct {
    elems: List(*Expr),
    loc: Loc,
};

pub const Map = struct {
    entries: List(KeyValue),
    loc: Loc,
};

pub const KeyValue = struct {
    key: *Expr,
    value: *Expr,
    loc: Loc,
};

pub const Ident = struct {
    name: []const u8,
    loc: Loc,
};

pub const PrefixOp = enum {
    plus,
    minus,
    address_of,
    logical_not,
    range,
    range_inclusive,
};

pub const Prefix = struct {
    right: *Expr,
    loc: Loc,
    op: PrefixOp,
};

pub const Deref = struct {
    expr: *Expr,
    loc: Loc,
};

pub const InfixOp = enum {
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
};

pub const Infix = struct {
    left: *Expr,
    right: *Expr,
    loc: Loc,
    op: InfixOp,
};

pub const Function = struct {
    params: List(Param),
    result_ty: ?*Expr,
    body: ?Block,
    loc: Loc,
    is_proc: bool,
    is_async: bool,
    is_variadic: bool,
    is_extern: bool,
    // If present, the function body is provided as a raw asm block ("asm { ... }")
    raw_asm: ?[]const u8 = null,
    attrs: ?List(Attribute) = null,
};

pub const Block = struct {
    items: List(Decl),
    loc: Loc,
};

// Metaprogramming: a comptime block or expression
pub const Comptime = union(enum) {
    Block: Block,
    Expr: *Expr,
};

// Metaprogramming: an AST captured as a value
pub const CodeBlock = struct {
    block: Block,
    loc: Loc,
};

// Metaprogramming: insert a code block/value into current scope
pub const Insert = struct {
    expr: *Expr,
    loc: Loc,
};

// MLIR block captured as raw text, with a simple kind tag
pub const MlirKind = enum { Module, Type, Attribute, Operation };

pub const Mlir = struct {
    kind: MlirKind,
    text: []const u8,
    loc: Loc,
};

pub const Call = struct {
    callee: *Expr,
    args: List(*Expr),
    loc: Loc,
};

pub const Index = struct {
    collection: *Expr,
    index: *Expr,
    loc: Loc,
};

pub const Field = struct {
    parent: *Expr,
    field: []const u8,
    is_tuple: bool,
    loc: Loc,
};

pub const StructLiteral = struct {
    fields: List(StructFieldValue),
    loc: Loc,
};

pub const StructFieldValue = struct {
    name: ?[]const u8,
    value: *Expr,
    loc: Loc,
};

pub const Return = struct {
    value: ?*Expr,
    loc: Loc,
};

pub const If = struct {
    cond: *Expr,
    then_block: Block,
    else_block: ?*Expr, // can be another If or a Block
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

pub const Match = struct {
    expr: *Expr,
    arms: List(MatchArm),
    loc: Loc,
};

pub const MatchArm = struct {
    pattern: *Pattern,
    guard: ?*Expr,
    body: *Expr,
    loc: Loc,
};

pub const Break = struct {
    loc: Loc,
    label: ?[]const u8 = null,
    value: ?*Expr = null,
};

pub const Continue = struct {
    loc: Loc,
};

pub const Unreachable = struct {
    loc: Loc,
};

pub const Null = struct {
    loc: Loc,
};

pub const Defer = struct {
    expr: *Expr,
    loc: Loc,
};

pub const ErrDefer = struct {
    expr: *Expr,
    loc: Loc,
};

pub const ErrUnwrap = struct {
    expr: *Expr,
    loc: Loc,
};

pub const Await = struct {
    expr: *Expr,
    loc: Loc,
};

pub const Closure = struct {
    params: List(Param),
    result_ty: ?*Expr,
    body: *Expr,
    loc: Loc,
};

pub const Async = struct {
    body: *Expr,
    loc: Loc,
};

pub const CastKind = enum {
    normal, // .(T)
    bitcast, // .^T
    saturate, // .|T
    wrap, // .%T
    checked, // .?T
};

pub const Cast = struct {
    expr: *Expr,
    ty: *Expr,
    kind: CastKind,
    loc: Loc,
};

pub const Catch = struct {
    expr: *Expr,
    binding: ?Ident,
    handler: *Expr,
    loc: Loc,
};

pub const Import = struct {
    expr: *Expr,
    loc: Loc,
};

pub const TypeOf = struct {
    expr: *Expr,
    loc: Loc,
};

pub const Param = struct {
    pat: ?*Expr,
    ty: ?*Expr,
    value: ?*Expr,
    loc: Loc,
    attrs: ?List(Attribute) = null,
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

// NOTE: Not exhaustive, these are unambiguous types during parsing
pub const BuiltinType = union(enum) {
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
    ty: ?union(enum) {
        Tuple: List(*Expr),
        Struct: List(StructField),
    },
    value: ?*Expr,
    loc: Loc,
    attrs: ?List(Attribute) = null,
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
    // Ref: *Pattern, // &pat
    // Deref: *Pattern, // *pat
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
    path: List(Ident),
    elems: List(*Pattern),
    loc: Loc,
};

pub const VariantStructPattern = struct {
    path: List(Ident),
    fields: List(StructPatternField),
    has_rest: bool,
    loc: Loc,
};

pub const StructPattern = struct {
    path: List(Ident),
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
    segments: List(Ident),
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

// CST Printer (LISP-style)
pub const CstPrinter = struct {
    writer: *std.io.Writer,
    indent_size: usize = 0,

    pub fn init(writer: *std.io.Writer) CstPrinter {
        return .{ .writer = writer };
    }

    fn printIndent(self: *CstPrinter) !void {
        for (0..self.indent_size) |_| {
            try self.writer.print(" ", .{});
        }
    }

    inline fn deindent(self: *CstPrinter) void {
        if (self.indent_size >= 2) {
            self.indent_size -= 2;
        }
    }

    inline fn indent(self: *CstPrinter) void {
        self.indent_size += 2;
    }

    fn beginNode(self: *CstPrinter, comptime fmt: []const u8, args: anytype) !void {
        try self.printIndent();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
        self.indent();
    }

    fn endNode(self: *CstPrinter) !void {
        self.deindent();
        try self.printIndent();
        try self.writer.writeAll(")\n");
    }

    fn printLeaf(self: *CstPrinter, comptime fmt: []const u8, args: anytype) !void {
        try self.printIndent();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
    }

    fn printAttributes(self: *CstPrinter, attrs: List(Attribute)) !void {
        try self.beginNode("(attributes", .{});
        for (attrs.items) |a| {
            try self.beginNode("(attr name=\"{s}\"", .{a.name});
            if (a.value) |v| {
                try self.printNamedExpr("value", v);
            }
            try self.endNode();
        }
        try self.endNode();
    }

    fn printNamedExpr(self: *CstPrinter, name: []const u8, expr: *const Expr) !void {
        try self.beginNode("({s}", .{name});
        try self.printExpr(expr);
        try self.endNode();
    }

    fn printUnary(self: *CstPrinter, name: []const u8, expr: *const Expr) !void {
        try self.beginNode("({s}", .{name});
        try self.printExpr(expr);
        try self.endNode();
    }

    fn printBinary(self: *CstPrinter, name: []const u8, left: *const Expr, right: *const Expr) !void {
        try self.beginNode("({s}", .{name});
        try self.printExpr(left);
        try self.printExpr(right);
        try self.endNode();
    }

    fn printExprList(self: *CstPrinter, name: []const u8, exprs: List(*Expr)) anyerror!void {
        try self.beginNode("({s}", .{name});
        for (exprs.items) |item| {
            try self.printExpr(item);
        }
        try self.endNode();
    }

    fn printStructField(self: *CstPrinter, field: *const StructField) !void {
        try self.beginNode("(field name=\"{s}\"", .{field.name});
        if (field.attrs) |attrs| {
            try self.printAttributes(attrs);
        }
        try self.printExpr(field.ty);
        if (field.value) |val| {
            try self.printNamedExpr("value", val);
        }
        try self.endNode();
    }

    pub fn print(self: *CstPrinter, program: *const Program) !void {
        self.indent_size = 0;
        try self.beginNode(
            "(program package={s}",
            .{if (program.package) |pkg| pkg.name else "null"},
        );
        for (program.decls.items) |decl| {
            try self.printDecl(&decl);
        }
        try self.endNode();
    }

    fn printDecl(self: *CstPrinter, decl: *const Decl) !void {
        try self.beginNode("(decl is_const={} is_assign={}", .{ decl.is_const, decl.is_assign });
        if (decl.ty) |ty| {
            try self.printNamedExpr("type", ty);
        }
        if (decl.lhs) |lhs| {
            try self.printNamedExpr("lhs", lhs);
        }
        try self.printNamedExpr("rhs", decl.rhs);
        try self.endNode();
    }

    fn printExpr(self: *CstPrinter, expr: *const Expr) anyerror!void {
        switch (expr.*) {
            .Literal => |lit| try self.printLeaf("(literal kind={} \"{s}\")", .{ lit.kind, lit.value }),
            .Ident => |ident| try self.printLeaf("(ident \"{s}\")", .{ident.name}),
            .Prefix => |prefix| {
                try self.beginNode("(prefix op={}", .{prefix.op});
                try self.printExpr(prefix.right);
                try self.endNode();
            },
            .Deref => |d| {
                try self.beginNode("(deref", .{});
                try self.printExpr(d.expr);
                try self.endNode();
            },
            .Infix => |infix| {
                try self.beginNode("(infix op={}", .{infix.op});
                try self.printExpr(infix.left);
                try self.printExpr(infix.right);
                try self.endNode();
            },
            .Await => |aw| {
                try self.beginNode("(await", .{});
                try self.printExpr(aw.expr);
                try self.endNode();
            },
            .BuiltinType => |btype| try self.printBuiltinType(&btype),
            .Array => |array| {
                try self.beginNode("(array", .{});
                try self.printExprList("elems", array.elems);
                try self.endNode();
            },
            .Tuple => |tuple| {
                try self.beginNode("(tuple", .{});
                try self.printExprList("elems", tuple.elems);
                try self.endNode();
            },
            .Map => |map| {
                try self.beginNode("(map", .{});
                for (map.entries.items) |entry| {
                    try self.beginNode("(entry", .{});
                    try self.printNamedExpr("key", entry.key);
                    try self.printNamedExpr("value", entry.value);
                    try self.endNode();
                }
                try self.endNode();
            },
            .Block => |block| {
                try self.beginNode("(block", .{});
                for (block.items.items) |decl| {
                    try self.printDecl(&decl);
                }
                try self.endNode();
            },
            .Call => |call| {
                try self.beginNode("(call", .{});
                try self.printNamedExpr("callee", call.callee);
                try self.printExprList("args", call.args);
                try self.endNode();
            },
            .Index => |index| {
                try self.beginNode("(index", .{});
                try self.printNamedExpr("collection", index.collection);
                try self.printNamedExpr("index", index.index);
                try self.endNode();
            },
            .Field => |field| {
                try self.beginNode("(field name=\"{s}\" is_tuple={}", .{ field.field, field.is_tuple });
                try self.printExpr(field.parent);
                try self.endNode();
            },
            .Struct => |st| {
                try self.beginNode("(struct_literal", .{});
                for (st.fields.items) |field| {
                    try self.beginNode("(field", .{});
                    if (field.name) |name| {
                        try self.printLeaf("name=\"{s}\"", .{name});
                    } else {
                        try self.printLeaf("name=null", .{});
                    }
                    try self.printNamedExpr("value", field.value);
                    try self.endNode();
                }
                try self.endNode();
            },
            .Return => |ret| {
                try self.beginNode("(return", .{});
                if (ret.value) |val| {
                    try self.printNamedExpr("value", val);
                }
                try self.endNode();
            },
            .Catch => |c| {
                try self.beginNode("(catch", .{});
                try self.printNamedExpr("expr", c.expr);
                if (c.binding) |b| {
                    try self.beginNode("(binding name=\"{s}\")", .{b.name});
                    try self.endNode();
                }
                try self.printNamedExpr("handler", c.handler);
                try self.endNode();
            },
            .If => |if_expr| {
                try self.beginNode("(if", .{});
                try self.printNamedExpr("cond", if_expr.cond);
                try self.beginNode("(then", .{});
                for (if_expr.then_block.items.items) |decl| {
                    try self.printDecl(&decl);
                }
                try self.endNode();
                if (if_expr.else_block) |else_blk| {
                    try self.printNamedExpr("else", else_blk);
                }
                try self.endNode();
            },
            .While => |while_expr| {
                try self.beginNode("(while is_pattern={}", .{while_expr.is_pattern});
                if (while_expr.label) |lbl| {
                    try self.printLeaf("label=\"{s}\"", .{lbl});
                }
                if (while_expr.pattern) |pat| {
                    try self.beginNode("(pattern", .{});
                    try self.printPattern(pat);
                    try self.endNode();
                }
                if (while_expr.cond) |cond| {
                    try self.printNamedExpr("cond", cond);
                }
                try self.beginNode("(body", .{});
                for (while_expr.body.items.items) |decl| {
                    try self.printDecl(&decl);
                }
                try self.endNode();
                try self.endNode();
            },
            .Match => |match| {
                try self.beginNode("(match", .{});
                try self.printNamedExpr("expr", match.expr);
                for (match.arms.items) |arm| {
                    try self.beginNode("(arm", .{});
                    try self.beginNode("(pattern", .{});
                    try self.printPattern(arm.pattern);
                    try self.endNode();
                    if (arm.guard) |guard| {
                        try self.printNamedExpr("guard", guard);
                    }
                    try self.printNamedExpr("body", arm.body);
                    try self.endNode();
                }
                try self.endNode();
            },
            .For => |for_expr| {
                try self.beginNode("(for", .{});
                if (for_expr.label) |lbl| {
                    try self.printLeaf("label=\"{s}\"", .{lbl});
                }
                try self.beginNode("(pattern", .{});
                try self.printPattern(for_expr.pattern);
                try self.endNode();
                try self.printNamedExpr("iterable", for_expr.iterable);
                try self.beginNode("(body", .{});
                for (for_expr.body.items.items) |decl| {
                    try self.printDecl(&decl);
                }
                try self.endNode();
                try self.endNode();
            },
            .ErrUnwrap => |err_unwrap| {
                try self.beginNode("(err_unwrap", .{});
                try self.printExpr(err_unwrap.expr);
                try self.endNode();
            },
            .Defer => |e| {
                try self.beginNode("(defer", .{});
                try self.printExpr(e.expr);
                try self.endNode();
            },
            .ErrDefer => |err_defer| {
                try self.beginNode("(err_defer", .{});
                try self.printExpr(err_defer.expr);
                try self.endNode();
            },
            .Closure => |closure| {
                try self.beginNode("(closure", .{});
                for (closure.params.items) |param| {
                    try self.beginNode("(param", .{});
                    if (param.pat) |pat|
                        try self.printNamedExpr("pat", pat);
                    if (param.ty) |ty|
                        try self.printNamedExpr("type", ty);
                    if (param.value) |val| {
                        try self.printNamedExpr("value", val);
                    }
                    try self.endNode();
                }
                if (closure.result_ty) |res| {
                    try self.printNamedExpr("result", res);
                }
                try self.printNamedExpr("body", closure.body);
                try self.endNode();
            },
            .Async => |asyn| {
                try self.beginNode("(async", .{});
                try self.printExpr(asyn.body);
                try self.endNode();
            },
            .Cast => |c| {
                const kind_str = switch (c.kind) {
                    .normal => "cast",
                    .bitcast => "bitcast",
                    .saturate => "saturating_cast",
                    .wrap => "wrapping_cast",
                    .checked => "checked_cast",
                };
                try self.beginNode("({s}", .{kind_str});
                try self.printNamedExpr("expr", c.expr);
                try self.printNamedExpr("type", c.ty);
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
            .Comptime => |ct| {
                switch (ct) {
                    .Block => |blk| {
                        try self.beginNode("(comptime_block", .{});
                        for (blk.items.items) |decl| {
                            try self.printDecl(&decl);
                        }
                        try self.endNode();
                    },
                    .Expr => |e| {
                        try self.beginNode("(comptime_expr", .{});
                        try self.printExpr(e);
                        try self.endNode();
                    },
                }
            },
            .Code => |code_blk| {
                try self.beginNode("(code", .{});
                for (code_blk.block.items.items) |decl| {
                    try self.printDecl(&decl);
                }
                try self.endNode();
            },
            .Insert => |ins| {
                try self.beginNode("(insert", .{});
                try self.printExpr(ins.expr);
                try self.endNode();
            },
            .Mlir => |ml| {
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
            .Break => |b| {
                try self.beginNode("(break", .{});
                if (b.label) |lbl| try self.printLeaf("label=\"{s}\"", .{lbl});
                if (b.value) |val| try self.printNamedExpr("value", val);
                try self.endNode();
            },
            .Continue => |_| try self.printLeaf("(continue)", .{}),
            .Unreachable => |_| try self.printLeaf("(unreachable)", .{}),
            .Null => |_| try self.printLeaf("(null)", .{}),
            .Function => |fun| {
                try self.beginNode("({s}", .{if (fun.is_proc) "procedure" else "function"});
                if (fun.attrs) |attrs| {
                    try self.printAttributes(attrs);
                }
                if (fun.is_async) {
                    try self.printLeaf("(async)", .{});
                }
                if (fun.is_variadic) {
                    try self.printLeaf("(variadic)", .{});
                }
                if (fun.is_extern) {
                    try self.printLeaf("(extern)", .{});
                }
                for (fun.params.items) |param| {
                    try self.beginNode("(param", .{});
                    if (param.attrs) |attrs| {
                        try self.printAttributes(attrs);
                    }
                    if (param.pat) |pat|
                        try self.printNamedExpr("pat", pat);
                    try self.printNamedExpr("type", param.ty.?);
                    if (param.value) |val| {
                        try self.printNamedExpr("value", val);
                    }
                    try self.endNode();
                }
                if (fun.result_ty) |res| {
                    try self.printNamedExpr("result", res);
                }
                if (fun.body) |body| {
                    try self.beginNode("(body", .{});
                    for (body.items.items) |decl| {
                        try self.printDecl(&decl);
                    }
                    try self.endNode();
                } else if (fun.raw_asm) |asm_text| {
                    try self.printLeaf("(asm_body \"{s}\")", .{asm_text});
                }
                try self.endNode();
            },
        }
    }

    fn printPattern(self: *CstPrinter, pattern: *const Pattern) anyerror!void {
        switch (pattern.*) {
            .Wildcard => try self.printLeaf("(wildcard)", .{}),
            .Literal => |lit| try self.printNamedExpr("literal", lit),
            .Path => |path| {
                try self.beginNode("(path", .{});
                for (path.segments.items) |seg| {
                    try self.printLeaf("segment=\"{s}\"", .{seg.name});
                }
                try self.endNode();
            },
            .Binding => |bind| {
                try self.printLeaf(
                    "(binding name=\"{s}\" by_ref={} is_mut={})",
                    .{ bind.name, bind.by_ref, bind.is_mut },
                );
            },
            .Tuple => |tup| {
                try self.beginNode("(tuple_pattern", .{});
                for (tup.elems.items) |elem| {
                    try self.printPattern(elem);
                }
                try self.endNode();
            },
            .Slice => |slice| {
                try self.beginNode("(slice_pattern has_rest={}", .{slice.has_rest});
                for (slice.elems.items) |elem| {
                    try self.printPattern(elem);
                }
                if (slice.rest_binding) |rest| {
                    try self.beginNode("(rest_binding", .{});
                    try self.printPattern(rest);
                    try self.endNode();
                }
                try self.endNode();
            },
            .Struct => |st| {
                try self.beginNode("(struct_pattern has_rest={}", .{st.has_rest});
                for (st.path.items) |seg| {
                    try self.printLeaf("segment=\"{s}\"", .{seg.name});
                }
                for (st.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\"", .{field.name});
                    try self.printPattern(field.pattern);
                    try self.endNode();
                }
                try self.endNode();
            },
            .VariantTuple => |vt| {
                try self.beginNode("(variant_tuple_pattern", .{});
                for (vt.path.items) |seg| {
                    try self.printLeaf("segment=\"{s}\"", .{seg.name});
                }
                for (vt.elems.items) |elem| {
                    try self.printPattern(elem);
                }
                try self.endNode();
            },
            .VariantStruct => |vs| {
                try self.beginNode("(variant_struct_pattern has_rest={}", .{vs.has_rest});
                for (vs.path.items) |seg| {
                    try self.printLeaf("segment=\"{s}\"", .{seg.name});
                }
                for (vs.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\"", .{field.name});
                    try self.printPattern(field.pattern);
                    try self.endNode();
                }
                try self.endNode();
            },
            .Range => |range| {
                try self.beginNode("(range_pattern inclusive_right={}", .{range.inclusive_right});
                if (range.start) |start| {
                    try self.printNamedExpr("start", start);
                }
                if (range.end) |end| {
                    try self.printNamedExpr("end", end);
                }
                try self.endNode();
            },
            .Or => |or_p| {
                try self.beginNode("(or_pattern", .{});
                for (or_p.alts.items) |opt| {
                    try self.printPattern(opt);
                }
                try self.endNode();
            },
            .At => |at| {
                try self.beginNode("(at_pattern binder=\"{s}\"", .{at.binder});
                try self.printPattern(at.pattern);
                try self.endNode();
            },
        }
    }

    fn printBuiltinType(self: *CstPrinter, btype: *const BuiltinType) anyerror!void {
        switch (btype.*) {
            .Array => |array| try self.printBinary("array", array.elem, array.size),
            .DynArray => |darray| try self.printUnary("dyn_array", darray.elem),
            .MapType => |map| try self.printBinary("map", map.key, map.value),
            .Slice => |slice| try self.printUnary("slice", slice.elem),
            .Optional => |opt| try self.printUnary("optional", opt.elem),
            .ErrorSet => |eset| try self.printBinary("error_set", eset.err, eset.value),
            .Struct => |st| {
                try self.beginNode("(struct", .{});
                if (st.attrs) |attrs| try self.printAttributes(attrs);
                try self.printLeaf("is_extern={}", .{st.is_extern});
                for (st.fields.items) |field| {
                    try self.printStructField(&field);
                }
                try self.endNode();
            },
            .Enum => |en| {
                try self.beginNode("(enum", .{});
                if (en.attrs) |attrs| try self.printAttributes(attrs);
                try self.printLeaf("is_extern={}", .{en.is_extern});
                if (en.discriminant) |disc| {
                    try self.printNamedExpr("discriminant", disc);
                }
                for (en.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\")", .{field.name});
                    if (field.attrs) |attrs| try self.printAttributes(attrs);
                    if (field.value) |val| {
                        try self.printExpr(val);
                    }
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
                                for (st_fields.items) |f| {
                                    try self.printStructField(&f);
                                }
                                try self.endNode();
                            },
                        }
                    }
                    if (field.value) |val| {
                        try self.printNamedExpr("value", val);
                    }
                    try self.endNode();
                }
                try self.endNode();
            },
            .Union => |un| {
                try self.beginNode("(union", .{});
                if (un.attrs) |attrs| try self.printAttributes(attrs);
                try self.printLeaf("is_extern={}", .{un.is_extern});
                for (un.fields.items) |field| {
                    try self.printStructField(&field);
                }
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
                                for (st_fields.items) |f| {
                                    try self.printStructField(&f);
                                }
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
