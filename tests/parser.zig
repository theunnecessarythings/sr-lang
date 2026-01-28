const std = @import("std");
const testing = std.testing;
const compiler = @import("compiler");
const cst = compiler.cst;
const Parser = compiler.parser.Parser;
const Diagnostics = compiler.diagnostics.Diagnostics;
const Context = compiler.compile.Context;

fn parseProgramFromText(gpa: std.mem.Allocator, context: *Context, src: [:0]const u8) !cst.CST {
    const file_path = "in_memory.sr";
    const file_id = try context.source_manager.setVirtualSourceByPath(file_path, src);

    var parser = Parser.init(gpa, src, file_id, context.diags, context);
    var ast = try parser.parse();
    errdefer ast.deinit();
    if (context.parse_worklist.capacity != 0) {
        var i: usize = 0;
        while (i < context.parse_worklist.items.len) : (i += 1) {
            const work = context.parse_worklist.items[i];
            work.thread.join();
            work.diags.deinit();
            gpa.destroy(work.diags);
            work.parser.cst_u.deinit();
            gpa.free(work.parser.src);
            gpa.destroy(work.parser);
        }
        context.parse_worklist.deinit(gpa);
    }
    if (context.diags.count() != 0) {
        std.debug.print(
            "Errors during parsing: {}\n",
            .{context.diags.messages.items[0]},
        );
    }
    try testing.expectEqual(@as(usize, 0), context.diags.count());
    return ast;
}

fn parseProgramFromPath(gpa: std.mem.Allocator, context: *Context, path: []const u8, src: [:0]const u8) !cst.CST {
    const file_id = try context.source_manager.setVirtualSourceByPath(path, src);
    var parser = Parser.init(gpa, src, file_id, context.diags, context);
    var ast = try parser.parse();
    errdefer ast.deinit();
    if (context.parse_worklist.capacity != 0) {
        var i: usize = 0;
        while (i < context.parse_worklist.items.len) : (i += 1) {
            const work = context.parse_worklist.items[i];
            work.thread.join();
            work.diags.deinit();
            gpa.destroy(work.diags);
            work.parser.cst_u.deinit();
            const to_free = work.parser.src.ptr[0 .. work.parser.src.len + 1];
            gpa.free(to_free);
            gpa.destroy(work.parser);
        }
        context.parse_worklist.deinit(gpa);
    }
    if (context.diags.count() != 0) {
        std.debug.print(
            "Errors during parsing: {}\n",
            .{context.diags.messages.items[0]},
        );
    }
    try testing.expectEqual(@as(usize, 0), context.diags.count());
    return ast;
}

fn parseOneExpr(gpa: std.mem.Allocator, context: *Context, src: [:0]const u8) !struct { ast: cst.CST, id: cst.ExprId } {
    var ast = try parseProgramFromText(gpa, context, src);
    const decl_ids = ast.exprs.decl_pool.slice(ast.program.top_decls);
    try testing.expectEqual(@as(usize, 1), decl_ids.len);

    const decl_row = ast.exprs.Decl.get(decl_ids[0]);
    return .{ .ast = ast, .id = decl_row.rhs };
}

fn expectKind(ast: *cst.CST, id: cst.ExprId, k: cst.ExprKind) !void {
    const got = ast.exprs.index.kinds.items[id.toRaw()];
    try testing.expectEqual(k, got);
}

fn expectLit(ast: *cst.CST, id: cst.ExprId, s: []const u8) !void {
    try expectKind(ast, id, .Literal);
    const row = ast.exprs.get(.Literal, id);
    const got = ast.exprs.strs.get(row.value);
    try testing.expectEqualStrings(s, got);
}

fn expectInfix(ast: *cst.CST, id: cst.ExprId, op: cst.InfixOp) !struct { left: cst.ExprId, right: cst.ExprId } {
    try expectKind(ast, id, .Infix);
    const row = ast.exprs.get(.Infix, id);
    try testing.expectEqual(op, row.op);
    return .{ .left = row.left, .right = row.right };
}

test "expr: precedence 1 + 2 * 3" {
    const gpa = testing.allocator;
    var context = Context.init(gpa);
    defer context.deinit();
    var r = try parseOneExpr(gpa, &context, "x = 1 + 2 * 3;");
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
    var context = Context.init(gpa);
    defer context.deinit();
    var r1 = try parseOneExpr(gpa, &context, "x = a?;");
    defer r1.ast.deinit();
    try expectKind(&r1.ast, r1.id, .OptionalUnwrap);

    var r2 = try parseOneExpr(gpa, &context, "x = a..b;");
    defer r2.ast.deinit();
    const range = try expectInfix(&r2.ast, r2.id, .range);
    _ = range;
}

test "expr: ctor-like struct literal Foo{a:1}" {
    const gpa = testing.allocator;
    var context = Context.init(gpa);
    defer context.deinit();
    var r = try parseOneExpr(gpa, &context, "Foo{ a: 1 };");
    defer r.ast.deinit();

    try expectKind(&r.ast, r.id, .StructLit);
    const row = r.ast.exprs.get(.StructLit, r.id);
    const fields = r.ast.exprs.sfv_pool.slice(row.fields);
    try testing.expectEqual(@as(usize, 1), fields.len);

    const frow = r.ast.exprs.StructFieldValue.get(fields[0]);
    const fname = r.ast.exprs.strs.get(frow.name.unwrap());
    try testing.expectEqualStrings("a", fname);
    try expectLit(&r.ast, frow.value, "1");
}

test "match with guard" {
    const gpa = testing.allocator;
    var context = Context.init(gpa);
    defer context.deinit();
    const src =
        \\match x {
        \\  1 | 2 if cond => { y = 1; },
        \\  x              => {y = 0; },
        \\}
    ;
    var ast = try parseProgramFromText(gpa, &context, src);
    defer ast.deinit();

    const decl_ids = ast.exprs.decl_pool.slice(ast.program.top_decls);
    const rhs = ast.exprs.Decl.get(decl_ids[0]).rhs;

    try expectKind(&ast, rhs, .Match);
    const m = ast.exprs.get(.Match, rhs);
    const arms = ast.exprs.arm_pool.slice(m.arms);
    try testing.expect(arms.len >= 2);
}

test "full success test" {
    const gpa = testing.allocator;
    var context = Context.init(gpa);
    defer context.deinit();
    const src = try std.fs.cwd().readFileAlloc(gpa, "examples/test_success.sr", 8192);
    defer gpa.free(src);

    const src0 = try gpa.dupeZ(u8, src);
    defer gpa.free(src0);
    var result = try parseProgramFromPath(gpa, &context, "examples/test_success.sr", src0);
    defer result.deinit();
}

test "decl: method path segments recorded" {
    const gpa = testing.allocator;
    var context = Context.init(gpa);
    defer context.deinit();

    const src =
        \\Point :: struct {
        \\  x: i32,
        \\};
        \\Point.distance :: fn(self: Point) i32 {
        \\  return self.x;
        \\};
    ;

    const src0 = try gpa.dupeZ(u8, src);
    defer gpa.free(src0);

    var ast = try parseProgramFromText(gpa, &context, src0);
    defer ast.deinit();

    const decl_ids = ast.exprs.decl_pool.slice(ast.program.top_decls);
    try testing.expectEqual(@as(usize, 2), decl_ids.len);

    const method_decl = ast.exprs.Decl.get(decl_ids[1]);
    try testing.expect(!method_decl.method_path.isNone());

    const range = method_decl.method_path.asRange();
    const seg_ids = ast.exprs.method_path_pool.slice(range);
    try testing.expectEqual(@as(usize, 2), seg_ids.len);

    const owner_seg = ast.exprs.MethodPathSeg.get(seg_ids[0]);
    const method_seg = ast.exprs.MethodPathSeg.get(seg_ids[1]);
    try testing.expectEqualStrings("Point", ast.exprs.strs.get(owner_seg.name));
    try testing.expectEqualStrings("distance", ast.exprs.strs.get(method_seg.name));
}

test "test decl parses into const proc with test attribute" {
    const gpa = testing.allocator;
    var context = Context.init(gpa);
    defer context.deinit();

    const src =
        \\test "hello world" {
        \\  return;
        \\}
    ;

    const src0 = try gpa.dupeZ(u8, src);
    defer gpa.free(src0);

    var ast = try parseProgramFromText(gpa, &context, src0);
    defer ast.deinit();

    const decl_ids = ast.exprs.decl_pool.slice(ast.program.top_decls);
    try testing.expectEqual(@as(usize, 1), decl_ids.len);

    const decl = ast.exprs.Decl.get(decl_ids[0]);
    try testing.expect(decl.flags.is_const);
    try testing.expect(!decl.lhs.isNone());

    const lhs = ast.exprs.get(.Ident, decl.lhs.unwrap());
    try testing.expectEqualStrings("__test_0_0", ast.exprs.strs.get(lhs.name));

    try expectKind(&ast, decl.rhs, .Function);
    const fnr = ast.exprs.get(.Function, decl.rhs);
    try testing.expect(!fnr.body.isNone());
    try testing.expect(!fnr.attrs.isNone());
    try testing.expect(fnr.flags.is_test);
    try testing.expect(fnr.flags.is_proc);

    try testing.expect(!fnr.result_ty.isNone());
    const res_id = fnr.result_ty.unwrap();
    try expectKind(&ast, res_id, .Infix);
    const res = ast.exprs.get(.Infix, res_id);
    try testing.expectEqual(cst.InfixOp.error_union, res.op);
    try expectKind(&ast, res.left, .Ident);
    try expectKind(&ast, res.right, .Ident);
    try testing.expectEqualStrings("Error", ast.exprs.strs.get(ast.exprs.get(.Ident, res.left).name));
    try testing.expectEqualStrings("void", ast.exprs.strs.get(ast.exprs.get(.Ident, res.right).name));

    const attr_range = fnr.attrs.asRange();
    const attrs = ast.exprs.attr_pool.slice(attr_range);
    try testing.expectEqual(@as(usize, 1), attrs.len);

    const attr = ast.exprs.Attribute.get(attrs[0]);
    try testing.expectEqualStrings("test", ast.exprs.strs.get(attr.name));
    try testing.expect(!attr.value.isNone());

    const lit = ast.exprs.get(.Literal, attr.value.unwrap());
    try testing.expectEqual(cst.LiteralKind.string, lit.tag_small);
    try testing.expectEqualStrings("\"hello world\"", ast.exprs.strs.get(lit.value));
}

test "multiple tests synthesize unique names" {
    const gpa = testing.allocator;
    var context = Context.init(gpa);
    defer context.deinit();

    const src =
        \\test "first" {}
        \\test "second" {}
    ;

    const src0 = try gpa.dupeZ(u8, src);
    defer gpa.free(src0);

    var ast = try parseProgramFromText(gpa, &context, src0);
    defer ast.deinit();

    const decl_ids = ast.exprs.decl_pool.slice(ast.program.top_decls);
    try testing.expectEqual(@as(usize, 2), decl_ids.len);

    const lhs0 = ast.exprs.get(.Ident, ast.exprs.Decl.get(decl_ids[0]).lhs.unwrap());
    const lhs1 = ast.exprs.get(.Ident, ast.exprs.Decl.get(decl_ids[1]).lhs.unwrap());
    try testing.expectEqualStrings("__test_0_0", ast.exprs.strs.get(lhs0.name));
    try testing.expectEqualStrings("__test_0_1", ast.exprs.strs.get(lhs1.name));
}
