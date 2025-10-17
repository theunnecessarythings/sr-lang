const std = @import("std");
const module_graph = @import("../src/module_graph.zig");

const ModuleGraph = module_graph.ModuleGraph;

fn makeTempFile(dir: *std.fs.Dir, path: []const u8) !void {
    try dir.writeFile(path, "// temp\n");
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
