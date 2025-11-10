const std = @import("std");
const compiler = @import("compiler");
const package_graph = compiler.package.graph;

fn setPackageRoot(
    context: *compiler.compile.Context,
    root_name: []const u8,
    root_path: []const u8,
    preludes: []const package_graph.PreludeConfig,
) !void {
    const RootConfig = @TypeOf(context.module_graph.config.roots[0]);
    var roots = std.ArrayList(RootConfig).init(std.testing.allocator);
    defer roots.deinit();
    try roots.appendSlice(context.module_graph.config.roots);
    try roots.append(.{ .name = root_name, .path = root_path, .prelude_imports = preludes });
    const combined = try roots.toOwnedSlice();
    defer std.testing.allocator.free(combined);
    try context.module_graph.setConfig(.{ .roots = combined, .discovery = context.module_graph.config.discovery });
}

fn freeResult(result: compiler.pipeline.Result, context: *compiler.compile.Context, allocator: std.mem.Allocator) void {
    if (result.tir) |*t| t.deinit();
    if (result.ast) |*a| a.deinit();
    if (result.cst) |*c| c.deinit();
    if (result.type_info) |ti| {
        if (!context.module_graph.ownsTypeInfo(ti)) {
            ti.deinit();
            allocator.destroy(ti);
        }
    }
}

test "package preludes automatically expose reexported symbols" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.makePath("pkg");
    try tmp.dir.writeFile(.{ .sub_path = "pkg/prelude.sr", .data = "package pkg\nfoo :: proc() i32 { return 42 }\n" });
    try tmp.dir.writeFile(.{ .sub_path = "pkg/lib.sr", .data = "package pkg\nmain :: proc() i32 { return foo() }\n" });

    const root_path = try tmp.dir.realpathAlloc(gpa, "pkg");
    defer gpa.free(root_path);

    var context = compiler.compile.Context.init(gpa);
    defer context.deinit();

    const preludes = [_]package_graph.PreludeConfig{
        .{ .path = "pkg/prelude", .reexport = .all },
    };
    try setPackageRoot(&context, "pkg", root_path, &preludes);

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);
    const file_path = try std.fs.path.join(gpa, &.{ root_path, "lib.sr" });
    defer gpa.free(file_path);

    var result = try pipeline.runWithImports(file_path, &.{}, .check);
    defer freeResult(result, &context, gpa);

    try std.testing.expectEqual(@as(usize, 0), context.diags.count());
}

test "package preludes reexport only selected symbols" {
    const gpa = std.testing.allocator;
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.makePath("pkg");
    try tmp.dir.writeFile(.{
        .sub_path = "pkg/limited.sr",
        .data = "package pkg\nonly :: proc() i32 { return 1 }\nhidden :: proc() i32 { return 2 }\n",
    });
    try tmp.dir.writeFile(.{
        .sub_path = "pkg/ok.sr",
        .data = "package pkg\nvalue :: proc() i32 { return only() }\n",
    });
    try tmp.dir.writeFile(.{
        .sub_path = "pkg/bad.sr",
        .data = "package pkg\nvalue :: proc() i32 { return hidden() }\n",
    });

    const root_path = try tmp.dir.realpathAlloc(gpa, "pkg");
    defer gpa.free(root_path);

    var context = compiler.compile.Context.init(gpa);
    defer context.deinit();

    const preludes = [_]package_graph.PreludeConfig{
        .{ .path = "pkg/limited", .reexport = .{ .symbols = &.{ "only" } } },
    };
    try setPackageRoot(&context, "pkg", root_path, &preludes);

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);

    const ok_path = try std.fs.path.join(gpa, &.{ root_path, "ok.sr" });
    defer gpa.free(ok_path);
    var ok_result = try pipeline.runWithImports(ok_path, &.{}, .check);
    defer freeResult(ok_result, &context, gpa);
    try std.testing.expectEqual(@as(usize, 0), context.diags.count());

    const bad_path = try std.fs.path.join(gpa, &.{ root_path, "bad.sr" });
    defer gpa.free(bad_path);
    _ = pipeline.runWithImports(bad_path, &.{}, .check) catch |err| {
        try std.testing.expectEqual(error.TypeCheckFailed, err);
        try std.testing.expectEqual(@as(usize, 1), context.diags.count());
        try std.testing.expectEqual(
            compiler.diagnostics.DiagnosticCode.undefined_identifier,
            context.diags.messages.items[0].code,
        );
        return;
    };
    try std.testing.expect(false);
}
