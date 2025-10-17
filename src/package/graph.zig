const std = @import("std");
const discovery = @import("discovery.zig");

pub const PackageId = struct {
    index: usize = std.math.maxInt(usize),

    pub fn init(index: usize) PackageId {
        return .{ .index = index };
    }

    pub fn isValid(self: PackageId) bool {
        return self.index != std.math.maxInt(usize);
    }
};

pub const ModuleInfo = struct {
    path: []u8,
};

pub const PackageInfo = struct {
    id: PackageId,
    name: []u8,
    root_path: []u8,
    modules: std.StringHashMapUnmanaged(ModuleInfo) = .{},

    pub fn init(
        gpa: std.mem.Allocator,
        id: PackageId,
        name: []const u8,
        root_path: []const u8,
    ) !PackageInfo {
        return .{
            .id = id,
            .name = try gpa.dupe(u8, name),
            .root_path = try gpa.dupe(u8, root_path),
        };
    }

    pub fn deinit(self: *PackageInfo, gpa: std.mem.Allocator) void {
        var it = self.modules.iterator();
        while (it.next()) |entry| {
            gpa.free(entry.key_ptr.*);
            gpa.free(entry.value_ptr.path);
        }
        self.modules.deinit(gpa);
        gpa.free(self.name);
        gpa.free(self.root_path);
    }

    pub fn addModule(
        self: *PackageInfo,
        gpa: std.mem.Allocator,
        key: []const u8,
        canonical_path: []const u8,
    ) !void {
        const gop = try self.modules.getOrPut(gpa, key);
        if (gop.found_existing) return;
        gop.key_ptr.* = try gpa.dupe(u8, key);
        gop.value_ptr.* = .{ .path = try gpa.dupe(u8, canonical_path) };
    }

    pub fn lookup(self: *const PackageInfo, key: []const u8) ?*const ModuleInfo {
        return self.modules.get(key);
    }

    pub fn absolutePathFor(
        self: *const PackageInfo,
        gpa: std.mem.Allocator,
        remainder: []const u8,
    ) ![]u8 {
        if (remainder.len == 0) {
            return try gpa.dupe(u8, self.root_path);
        }
        return try std.fs.path.join(gpa, &.{ self.root_path, remainder });
    }
};

pub const ModuleMatch = struct {
    pkg: *const PackageInfo,
    key: []const u8,
};

pub const RootConfig = struct {
    name: []const u8,
    path: []const u8,
};

pub const PackageGraph = struct {
    gpa: std.mem.Allocator,
    packages: std.ArrayListUnmanaged(PackageInfo) = .{},
    name_to_id: std.StringHashMapUnmanaged(PackageId) = .{},

    pub const Match = struct {
        pkg: *const PackageInfo,
        remainder: []const u8,
    };

    pub fn init(gpa: std.mem.Allocator) PackageGraph {
        return .{ .gpa = gpa };
    }

    pub fn deinit(self: *PackageGraph) void {
        self.clear();
        self.name_to_id.deinit(self.gpa);
        self.packages.deinit(self.gpa);
    }

    fn clear(self: *PackageGraph) void {
        self.name_to_id.clearRetainingCapacity();
        for (self.packages.items) |*pkg| {
            pkg.deinit(self.gpa);
        }
        self.packages.clearRetainingCapacity();
    }

    pub fn rebuild(
        self: *PackageGraph,
        roots: []const RootConfig,
        rules: discovery.Rules,
    ) !void {
        self.clear();

        for (roots, 0..) |root, idx| {
            const canonical = std.fs.cwd().realpathAlloc(self.gpa, root.path) catch |err| switch (err) {
                error.FileNotFound, error.AccessDenied => try self.gpa.dupe(u8, root.path),
                else => return err,
            };
            defer self.gpa.free(canonical);

            var pkg = try PackageInfo.init(self.gpa, PackageId.init(idx), root.name, canonical);
            errdefer pkg.deinit(self.gpa);

            try self.packages.append(self.gpa, pkg);
            const pkg_ptr = &self.packages.items[self.packages.items.len - 1];

            const gop = try self.name_to_id.getOrPut(self.gpa, pkg_ptr.name);
            if (!gop.found_existing) {
                gop.key_ptr.* = pkg_ptr.name;
            }
            gop.value_ptr.* = pkg_ptr.id;

            try self.populatePackage(pkg_ptr, rules);
        }
    }

    fn populatePackage(
        self: *PackageGraph,
        pkg: *PackageInfo,
        rules: discovery.Rules,
    ) !void {
        var dir = std.fs.openDirAbsolute(pkg.root_path, .{ .iterate = true }) catch return;
        defer dir.close();

        try self.scanDirectory(pkg, pkg.root_path, "", &dir, rules);
    }

    fn scanDirectory(
        self: *PackageGraph,
        pkg: *PackageInfo,
        abs_dir: []const u8,
        rel_prefix: []const u8,
        dir: *std.fs.Dir,
        rules: discovery.Rules,
    ) !void {
        var iterator = dir.iterate();
        while (iterator.next()) |entry| {
            switch (entry.kind) {
                .directory => {
                    const sub_abs = try std.fs.path.join(self.gpa, &.{ abs_dir, entry.name });
                    defer self.gpa.free(sub_abs);
                    var sub_dir = std.fs.openDirAbsolute(sub_abs, .{ .iterate = true }) catch continue;
                    defer sub_dir.close();
                    const sub_rel = try self.joinRelative(rel_prefix, entry.name);
                    defer self.gpa.free(sub_rel);
                    try self.scanDirectory(pkg, sub_abs, sub_rel, &sub_dir, rules);
                },
                .file => {
                    const matched_ext = rules.matchExtension(entry.name) orelse continue;
                    const rel_with_ext = try self.joinRelative(rel_prefix, entry.name);
                    defer self.gpa.free(rel_with_ext);

                    const abs_path = try std.fs.path.join(self.gpa, &.{ abs_dir, entry.name });
                    defer self.gpa.free(abs_path);
                    const canonical = std.fs.cwd().realpathAlloc(self.gpa, abs_path) catch |err| switch (err) {
                        error.FileNotFound, error.AccessDenied => continue,
                        else => return err,
                    };
                    defer self.gpa.free(canonical);

                    const module_keys = try rules.generateModuleKeys(self.gpa, pkg.name, rel_with_ext, matched_ext);
                    defer module_keys.deinit();

                    for (module_keys.items) |key| {
                        try pkg.addModule(self.gpa, key, canonical);
                    }
                },
                else => continue,
            }
        }
    }

    fn joinRelative(
        self: *PackageGraph,
        prefix: []const u8,
        name: []const u8,
    ) ![]u8 {
        if (prefix.len == 0) {
            return try self.gpa.dupe(u8, name);
        }
        return try std.fmt.allocPrint(self.gpa, "{s}/{s}", .{ prefix, name });
    }

    pub fn matchImport(self: *const PackageGraph, import_path: []const u8) ?Match {
        const idx = std.mem.indexOfScalar(u8, import_path, '/') orelse import_path.len;
        const prefix = import_path[0..idx];
        const id = self.name_to_id.get(prefix) orelse return null;
        return .{ .pkg = &self.packages.items[id.index], .remainder = if (idx == import_path.len) "" else import_path[idx + 1 ..] };
    }

    pub fn getByName(self: *const PackageGraph, name: []const u8) ?*const PackageInfo {
        if (self.name_to_id.get(name)) |id| {
            return &self.packages.items[id.index];
        }
        return null;
    }

    pub fn get(self: *const PackageGraph, id: PackageId) ?*const PackageInfo {
        if (!id.isValid()) return null;
        if (id.index >= self.packages.items.len) return null;
        return &self.packages.items[id.index];
    }

    pub fn findModuleByPath(
        self: *const PackageGraph,
        canonical_path: []const u8,
    ) ?ModuleMatch {
        var best: ?struct {
            pkg: *const PackageInfo,
            key: []const u8,
            score: u8,
        } = null;

        for (self.packages.items) |*pkg| {
            var it = pkg.modules.iterator();
            while (it.next()) |entry| {
                if (!std.mem.eql(u8, entry.value_ptr.path, canonical_path)) continue;
                const key = entry.key_ptr.*;
                const score = keyPriority(key);
                if (best) |b| {
                    if (score < b.score) continue;
                    if (score == b.score and key.len <= b.key.len) continue;
                }
                best = .{ .pkg = pkg, .key = key, .score = score };
            }
        }

        if (best) |b| {
            return .{ .pkg = b.pkg, .key = b.key };
        }
        return null;
    }
};

fn keyPriority(key: []const u8) u8 {
    if (key.len == 0) return 0;
    if (std.mem.indexOfScalar(u8, key, '/')) |_| return 3;
    if (std.mem.endsWith(u8, key, ".sr")) return 2;
    return 1;
}
