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

pub const Expr = union(enum) {
    Literal: Literal,
    Ident: Ident,
    Prefix: Prefix,
    Infix: Infix,
    BuiltinType: BuiltinType,
    Array: Array,
    Tuple: Tuple, // NOTE: used for both tuple literals and tuple types
    Map: Map,
    Function: Function,
    Block: Block,
    Call: Call,
    Index: Index,
    Field: Field,
    Struct: StructLiteral,
    Return: Return,
    If: If,
    While: While,
    Break: Break,
    Continue: Continue,
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
    is_variadic: bool,
};

pub const Block = struct {
    items: List(Decl),
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
    body: Block,
    loc: Loc,
    is_pattern: bool,
};

pub const Break = struct {
    loc: Loc,
};

pub const Continue = struct {
    loc: Loc,
};

pub const Param = struct {
    pat: ?*Expr,
    ty: *Expr,
    value: ?*Expr,
    loc: Loc,
};

pub const UnaryType = struct {
    elem: *Expr,
    loc: Loc,
};

pub const StructLikeType = struct {
    fields: List(StructField),
    loc: Loc,
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
};

pub const EnumField = struct {
    name: []const u8,
    value: ?*Expr,
    loc: Loc,
};

pub const EnumType = struct {
    fields: List(EnumField),
    discriminant: ?*Expr,
    loc: Loc,
};

pub const VariantField = struct {
    name: []const u8,
    ty: ?union(enum) {
        Tuple: List(*Expr),
        Struct: List(StructField),
    },
    value: ?*Expr,
    loc: Loc,
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

// AST Printer (LISP-style)
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
        if (self.indent_size >= 2) {
            self.indent_size -= 2;
        }
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
        for (exprs.items) |item| {
            try self.printExpr(item);
        }
        try self.endNode();
    }

    fn printStructField(self: *AstPrinter, field: *const StructField) !void {
        try self.beginNode("(field name=\"{s}\"", .{field.name});
        try self.printExpr(field.ty);
        if (field.value) |val| {
            try self.printNamedExpr("value", val);
        }
        try self.endNode();
    }

    pub fn print(self: *AstPrinter, program: *const Program) !void {
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

    fn printDecl(self: *AstPrinter, decl: *const Decl) !void {
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

    fn printExpr(self: *AstPrinter, expr: *const Expr) anyerror!void {
        switch (expr.*) {
            .Literal => |lit| try self.printLeaf("(literal kind={} \"{s}\")", .{ lit.kind, lit.value }),
            .Ident => |ident| try self.printLeaf("(ident \"{s}\")", .{ident.name}),
            .Prefix => |prefix| {
                try self.beginNode("(prefix op={}", .{prefix.op});
                try self.printExpr(prefix.right);
                try self.endNode();
            },
            .Infix => |infix| {
                try self.beginNode("(infix op={}", .{infix.op});
                try self.printExpr(infix.left);
                try self.printExpr(infix.right);
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
            .Break => |_| try self.printLeaf("(break)", .{}),
            .Continue => |_| try self.printLeaf("(continue)", .{}),
            .Function => |fun| {
                try self.beginNode("({s}", .{if (fun.is_proc) "procedure" else "function"});
                for (fun.params.items) |param| {
                    try self.beginNode("(param", .{});
                    if (param.pat) |pat|
                        try self.printNamedExpr("pat", pat);
                    try self.printNamedExpr("type", param.ty);
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
                }
                try self.endNode();
            },
        }
    }

    fn printBuiltinType(self: *AstPrinter, btype: *const BuiltinType) anyerror!void {
        switch (btype.*) {
            .Array => |array| try self.printBinary("array", array.elem, array.size),
            .DynArray => |darray| try self.printUnary("dyn_array", darray.elem),
            .MapType => |map| try self.printBinary("map", map.key, map.value),
            .Slice => |slice| try self.printUnary("slice", slice.elem),
            .Optional => |opt| try self.printUnary("optional", opt.elem),
            .ErrorSet => |eset| try self.printBinary("error_set", eset.err, eset.value),
            .Struct => |st| {
                try self.beginNode("(struct", .{});
                for (st.fields.items) |field| {
                    try self.printStructField(&field);
                }
                try self.endNode();
            },
            .Enum => |en| {
                try self.beginNode("(enum", .{});
                if (en.discriminant) |disc| {
                    try self.printNamedExpr("discriminant", disc);
                }
                for (en.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\")", .{field.name});
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
                for (un.fields.items) |field| {
                    try self.printStructField(&field);
                }
                try self.endNode();
            },
            .Error => |err| {
                try self.beginNode("(error", .{});
                for (err.fields.items) |field| {
                    try self.beginNode("(field name=\"{s}\"", .{field.name});
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
