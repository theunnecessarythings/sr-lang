const std = @import("std");
const compiler = @import("compiler");
const diag = compiler.diagnostics;
const gpa = std.testing.allocator;

fn extendRoots(
    context: *compiler.compile.Context,
    root_name: []const u8,
    root_path: []const u8,
) !void {
    const RootConfig = @TypeOf(context.module_graph.config.roots[0]);
    var roots = std.ArrayList(RootConfig).init(gpa);
    defer roots.deinit();
    try roots.appendSlice(context.module_graph.config.roots);
    try roots.append(.{ .name = root_name, .path = root_path });
    const combined = try roots.toOwnedSlice();
    defer gpa.free(combined);
    try context.module_graph.setConfig(.{
        .roots = combined,
        .discovery = context.module_graph.config.discovery,
    });
}

fn runAndCleanup(
    pipeline: *compiler.pipeline.Pipeline,
    path: []const u8,
    mode: compiler.pipeline.Pipeline.Mode,
) !compiler.pipeline.Result {
    var result = try pipeline.runWithImports(path, &.{}, mode);
    return result;
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

test "package validation: matching declaration" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.makePath("pkg");
    try tmp.dir.writeFile(.{
        .sub_path = "pkg/lib.sr",
        .data = "package lib\nvalue :: 1\n",
    });

    const root_path = try tmp.dir.realpathAlloc(gpa, "pkg");
    defer gpa.free(root_path);

    var context = compiler.compile.Context.init(gpa);
    defer context.deinit();
    try extendRoots(&context, "pkg", root_path);

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);
    const file_path = try std.fs.path.join(gpa, &.{ root_path, "lib.sr" });
    defer gpa.free(file_path);

    var result = try runAndCleanup(&pipeline, file_path, .check);
    defer freeResult(result, &context, gpa);

    try std.testing.expectEqual(@as(usize, 0), context.diags.count());
}

test "package validation: missing declaration" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.makePath("pkg");
    try tmp.dir.writeFile(.{
        .sub_path = "pkg/lib.sr",
        .data = "value :: 1\n",
    });

    const root_path = try tmp.dir.realpathAlloc(gpa, "pkg");
    defer gpa.free(root_path);

    var context = compiler.compile.Context.init(gpa);
    defer context.deinit();
    try extendRoots(&context, "pkg", root_path);

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);
    const file_path = try std.fs.path.join(gpa, &.{ root_path, "lib.sr" });
    defer gpa.free(file_path);

    const run_result = pipeline.runWithImports(file_path, &.{}, .check) catch |err| {
        try std.testing.expectEqual(error.PackageValidationFailed, err);
        try std.testing.expectEqual(@as(usize, 1), context.diags.count());
        try std.testing.expectEqual(diag.DiagnosticCode.package_missing_declaration, context.diags.messages.items[0].code);
        return;
    };
    defer freeResult(run_result, &context, gpa);
    try std.testing.expect(false);
}

test "package validation: mismatched declaration" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.makePath("pkg");
    try tmp.dir.writeFile(.{
        .sub_path = "pkg/lib.sr",
        .data = "package wrong\nvalue :: 1\n",
    });

    const root_path = try tmp.dir.realpathAlloc(gpa, "pkg");
    defer gpa.free(root_path);

    var context = compiler.compile.Context.init(gpa);
    defer context.deinit();
    try extendRoots(&context, "pkg", root_path);

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);
    const file_path = try std.fs.path.join(gpa, &.{ root_path, "lib.sr" });
    defer gpa.free(file_path);

    const run_result = pipeline.runWithImports(file_path, &.{}, .check) catch |err| {
        try std.testing.expectEqual(error.PackageValidationFailed, err);
        try std.testing.expectEqual(@as(usize, 1), context.diags.count());
        try std.testing.expectEqual(diag.DiagnosticCode.package_mismatch, context.diags.messages.items[0].code);
        return;
    };
    defer freeResult(run_result, &context, gpa);
    try std.testing.expect(false);
}

test "package validation: entry module must be main" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.writeFile(.{
        .sub_path = "main.sr",
        .data = "package not_main\nmain :: proc() i32 { return 0 }\n",
    });

    const file_path = try tmp.dir.realpathAlloc(gpa, "main.sr");
    defer gpa.free(file_path);

    var context = compiler.compile.Context.init(gpa);
    defer context.deinit();

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);

    const run_result = pipeline.runWithImports(file_path, &.{}, .check) catch |err| {
        try std.testing.expectEqual(error.PackageValidationFailed, err);
        try std.testing.expectEqual(@as(usize, 1), context.diags.count());
        try std.testing.expectEqual(diag.DiagnosticCode.entry_package_not_main, context.diags.messages.items[0].code);
        return;
    };
    defer freeResult(run_result, &context, gpa);
    try std.testing.expect(false);
}
