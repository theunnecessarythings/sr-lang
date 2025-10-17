const std = @import("std");
const module_graph = @import("compiler").module_graph;

const ModuleGraph = module_graph.ModuleGraph;

fn makeTempFile(dir: *std.fs.Dir, path: []const u8) !void {
    try dir.writeFile(.{
        .data = "// temp\n",
        .sub_path = path,
    });
}

test "ModuleGraph resolves relative file" {
    var graph = ModuleGraph.init(std.testing.allocator);
    defer graph.deinit();

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try makeTempFile(&tmp.dir, "module.sr");

    const base_path = try tmp.dir.realpathAlloc(std.testing.allocator, ".");
    defer std.testing.allocator.free(base_path);

    const resolved = try graph.resolvePath(base_path, "module.sr");
    defer std.testing.allocator.free(resolved);

    const expected = try tmp.dir.realpathAlloc(std.testing.allocator, "module.sr");
    defer std.testing.allocator.free(expected);

    try std.testing.expectEqualStrings(expected, resolved);
}

test "ModuleGraph resolves directory main file" {
    var graph = ModuleGraph.init(std.testing.allocator);
    defer graph.deinit();

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.makePath("lib");
    var lib_dir = try tmp.dir.openDir("lib", .{});
    defer lib_dir.close();
    try makeTempFile(&lib_dir, "main.sr");

    const base_path = try tmp.dir.realpathAlloc(std.testing.allocator, ".");
    defer std.testing.allocator.free(base_path);

    const resolved = try graph.resolvePath(base_path, "lib");
    defer std.testing.allocator.free(resolved);

    const expected = try tmp.dir.realpathAlloc(std.testing.allocator, "lib/main.sr");
    defer std.testing.allocator.free(expected);

    try std.testing.expectEqualStrings(expected, resolved);
}

test "ModuleGraph discovery finds std, vendor, examples, and workspace modules" {
    var graph = ModuleGraph.init(std.testing.allocator);
    defer graph.deinit();

    const std_path = try graph.resolvePath("", "std/array");
    defer std.testing.allocator.free(std_path);
    try std.testing.expect(std.mem.endsWith(u8, std_path, "std/array.sr"));

    const vendor_path = try graph.resolvePath("", "vendor/raylib");
    defer std.testing.allocator.free(vendor_path);
    try std.testing.expect(std.mem.endsWith(u8, vendor_path, "vendor/raylib.sr"));

    const example_path = try graph.resolvePath("", "examples/imports");
    defer std.testing.allocator.free(example_path);
    try std.testing.expect(std.mem.endsWith(u8, example_path, "examples/imports/main.sr"));

    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    try tmp.dir.makePath("workspace_main");
    try tmp.dir.writeFile(.{ .sub_path = "workspace_main/main.sr", .data = "// main\n" });
    try tmp.dir.writeFile(.{ .sub_path = "workspace_main/app.sr", .data = "// app\n" });

    try tmp.dir.makePath("workspace_named");
    try tmp.dir.writeFile(.{ .sub_path = "workspace_named/workspace_named.sr", .data = "// named\n" });

    const workspace_main_path = try tmp.dir.realpathAlloc(std.testing.allocator, "workspace_main");
    defer std.testing.allocator.free(workspace_main_path);
    const workspace_named_path = try tmp.dir.realpathAlloc(std.testing.allocator, "workspace_named");
    defer std.testing.allocator.free(workspace_named_path);

    const RootConfig = @TypeOf(graph.config.roots[0]);
    const gpa = std.testing.allocator;
    var roots: std.ArrayList(RootConfig) = .{};
    defer roots.deinit(gpa);
    try roots.appendSlice(gpa, graph.config.roots);
    try roots.append(gpa, .{ .name = "workspace_main", .path = workspace_main_path });
    try roots.append(gpa, .{ .name = "workspace_named", .path = workspace_named_path });
    const combined = try roots.toOwnedSlice(gpa);
    defer std.testing.allocator.free(combined);

    try graph.setConfig(.{ .roots = combined, .discovery = graph.config.discovery });

    const workspace_main = try graph.resolvePath("", "workspace_main");
    defer std.testing.allocator.free(workspace_main);
    try std.testing.expect(std.mem.endsWith(u8, workspace_main, "workspace_main/main.sr"));

    const workspace_member = try graph.resolvePath("", "workspace_main/app");
    defer std.testing.allocator.free(workspace_member);
    try std.testing.expect(std.mem.endsWith(u8, workspace_member, "workspace_main/app.sr"));

    const workspace_named = try graph.resolvePath("", "workspace_named");
    defer std.testing.allocator.free(workspace_named);
    try std.testing.expect(std.mem.endsWith(u8, workspace_named, "workspace_named/workspace_named.sr"));
}
