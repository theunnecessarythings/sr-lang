const std = @import("std");
const testing = std.testing;
const compiler = @import("compiler");
const cst = compiler.cst_v2;
const Parser = compiler.parser_v2.Parser;
const Diagnostics = compiler.diagnostics_v2.Diagnostics;

fn parseProgramFromText(gpa: std.mem.Allocator, src: [:0]const u8) !cst.CST {
    var diags = Diagnostics.init(gpa);
    defer diags.deinit();
    var parser = Parser.init(gpa, src, &diags);
    var ast = try parser.parse();
    errdefer ast.deinit();
    if (diags.count() != 0) {
        std.debug.print(
            "Errors during parsing: {}\n",
            .{diags.messages.items[0]},
        );
    }
    try testing.expectEqual(@as(usize, 0), diags.count());
    return ast;
}

fn parseOneExpr(gpa: std.mem.Allocator, src: [:0]const u8) !struct { ast: cst.CST, id: cst.ExprId } {
    var ast = try parseProgramFromText(gpa, src);
    const decl_ids = ast.exprs.decl_pool.slice(ast.program.top_decls);
    try testing.expectEqual(@as(usize, 1), decl_ids.len);

    const decl_row = ast.exprs.Decl.get(decl_ids[0].toRaw());
    return .{ .ast = ast, .id = decl_row.rhs };
}

fn expectKind(ast: *const cst.CST, id: cst.ExprId, k: cst.ExprKind) !void {
    const got = ast.exprs.index.kinds.items[id.toRaw()];
    try testing.expectEqual(k, got);
}

fn expectLit(ast: *const cst.CST, id: cst.ExprId, s: []const u8) !void {
    try expectKind(ast, id, .Literal);
    const row = ast.exprs.get(.Literal, id);
    const got = ast.exprs.strs.get(row.value);
    try testing.expectEqualStrings(s, got);
}

fn expectInfix(ast: *const cst.CST, id: cst.ExprId, op: cst.InfixOp) !struct { left: cst.ExprId, right: cst.ExprId } {
    try expectKind(ast, id, .Infix);
    const row = ast.exprs.get(.Infix, id);
    try testing.expectEqual(op, row.op);
    return .{ .left = row.left, .right = row.right };
}

test "expr: precedence 1 + 2 * 3" {
    const gpa = testing.allocator;
    var r = try parseOneExpr(gpa, "x = 1 + 2 * 3;");
    defer r.ast.deinit();

    const ast = &r.ast;

    const add = try expectInfix(ast, r.id, .add);
    try expectLit(ast, add.left, "1");

    const mul = try expectInfix(ast, add.right, .mul);
    try expectLit(ast, mul.left, "2");
    try expectLit(ast, mul.right, "3");
}

test "expr: optional unwrap postfix vs range infix" {
    const gpa = testing.allocator;
    var r1 = try parseOneExpr(gpa, "x = a?;");
    defer r1.ast.deinit();
    try expectKind(&r1.ast, r1.id, .OptionalUnwrap);

    var r2 = try parseOneExpr(gpa, "x = a..b;");
    defer r2.ast.deinit();
    const range = try expectInfix(&r2.ast, r2.id, .range);
    _ = range;
}

test "expr: ctor-like struct literal Foo{a:1}" {
    const gpa = testing.allocator;
    var r = try parseOneExpr(gpa, "Foo{ a: 1 };");
    defer r.ast.deinit();

    try expectKind(&r.ast, r.id, .StructLit);
    const row = r.ast.exprs.get(.StructLit, r.id);
    const fields = r.ast.exprs.sfv_pool.slice(row.fields);
    try testing.expectEqual(@as(usize, 1), fields.len);

    const frow = r.ast.exprs.StructFieldValue.get(fields[0].toRaw());
    const fname = r.ast.exprs.strs.get(frow.name.unwrap());
    try testing.expectEqualStrings("a", fname);
    try expectLit(&r.ast, frow.value, "1");
}

test "match with guard" {
    const gpa = testing.allocator;
    const src =
        \\match x {
        \\  1 | 2 if cond => { y = 1; },
        \\  x              => {y = 0; },
        \\}
    ;
    var ast = try parseProgramFromText(gpa, src);
    defer ast.deinit();

    const decl_ids = ast.exprs.decl_pool.slice(ast.program.top_decls);
    const rhs = ast.exprs.Decl.get(decl_ids[0].toRaw()).rhs;

    try expectKind(&ast, rhs, .Match);
    const m = ast.exprs.get(.Match, rhs);
    const arms = ast.exprs.arm_pool.slice(m.arms);
    try testing.expect(arms.len >= 2);
}

test "full success test" {
    const gpa = testing.allocator;
    const src = try std.fs.cwd().readFileAlloc(gpa, "examples/test_success.sr", 8192);
    defer gpa.free(src);

    const src0 = try gpa.dupeZ(u8, src);
    defer gpa.free(src0);
    var ast = try parseProgramFromText(gpa, src0);
    defer ast.deinit();
}
