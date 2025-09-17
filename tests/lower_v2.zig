const std = @import("std");
const testing = std.testing;
const compiler = @import("compiler");

const cst = compiler.cst_v2;
const Parser = compiler.parser_v2.Parser;
const Diagnostics = compiler.diagnostics_v2.Diagnostics;
const lower_v2 = compiler.lower_v2;
const ast_v2 = compiler.ast_v2;

fn parseProgramFromText(gpa: std.mem.Allocator, src: [:0]const u8) !cst.CST {
    var diags = Diagnostics.init(gpa);
    defer diags.deinit();
    var parser = Parser.init(gpa, src, &diags);
    var prog = try parser.parse();
    errdefer prog.deinit();
    try testing.expectEqual(@as(usize, 0), diags.count());
    return prog;
}

fn lowerProgramFromText(gpa: std.mem.Allocator, src: [:0]const u8) !struct { cst: cst.CST, ast: ast_v2.Ast } {
    var c = try parseProgramFromText(gpa, src);
    errdefer c.deinit();
    var lower = lower_v2.LowerV2.init(gpa, &c);
    const a = try lower.run();
    // do not lower.deinit(); ownership of a stays with caller
    return .{ .cst = c, .ast = a };
}

fn printAstToString(gpa: std.mem.Allocator, a: *const ast_v2.Ast) ![]u8 {
    var buf = std.array_list.Managed(u8).init(gpa);
    defer buf.deinit();
    var printer = ast_v2.AstPrinter.init(buf.writer(), &a.exprs, &a.stmts, &a.pats);
    try printer.printUnit(&a.unit);
    return buf.toOwnedSlice();
}

test "lower v2: precedence 1 + 2 * 3" {
    const gpa = testing.allocator;
    var res = try lowerProgramFromText(gpa, "x = 1 + 2 * 3;");
    defer res.cst.deinit();
    defer res.ast.deinit();

    const s = try printAstToString(gpa, &res.ast);
    defer gpa.free(s);

    try testing.expect(std.mem.indexOf(u8, s, "(binary op=add") != null);
    try testing.expect(std.mem.indexOf(u8, s, "(binary op=mul") != null);
}

test "lower v2: struct literal Foo{a:1}" {
    const gpa = testing.allocator;
    var res = try lowerProgramFromText(gpa, "Foo{ a: 1 };");
    defer res.cst.deinit();
    defer res.ast.deinit();

    const s = try printAstToString(gpa, &res.ast);
    defer gpa.free(s);
    try testing.expect(std.mem.indexOf(u8, s, "(struct_literal") != null);
    try testing.expect(std.mem.indexOf(u8, s, "(field") != null);
}

test "lower v2: match with guard" {
    const gpa = testing.allocator;
    const src =
        \\match x {
        \\  1 | 2 if cond => { y = 1; },
        \\  x              => { y = 0; },
        \\}
    ;
    var res = try lowerProgramFromText(gpa, src);
    defer res.cst.deinit();
    defer res.ast.deinit();

    const s = try printAstToString(gpa, &res.ast);
    defer gpa.free(s);
    try testing.expect(std.mem.indexOf(u8, s, "(match") != null);
}

test "lower v2: full success example" {
    const gpa = testing.allocator;
    const src = try std.fs.cwd().readFileAlloc(gpa, "examples/test_success.sr", 8192);
    defer gpa.free(src);
    const src0 = try gpa.dupeZ(u8, src);
    defer gpa.free(src0);

    var res = try lowerProgramFromText(gpa, src0);
    defer res.cst.deinit();
    defer res.ast.deinit();

    // Ensure printing works for the whole unit
    const s = try printAstToString(gpa, &res.ast);
    defer gpa.free(s);
    try testing.expect(s.len > 0);
}

