const std = @import("std");

pub const Rules = struct {
    extensions: []const []const u8 = &.{".sr"},
    directory_defaults: []const []const u8 = &.{"main.sr"},
    package_entry_files: []const []const u8 = &.{},
    include_package_basename: bool = true,

    pub fn matchExtension(self: Rules, name: []const u8) ?[]const u8 {
        for (self.extensions) |ext| {
            if (std.mem.endsWith(u8, name, ext)) return ext;
        }
        return null;
    }

    pub fn hasAnyExtension(self: Rules, path: []const u8) bool {
        for (self.extensions) |ext| {
            if (std.mem.endsWith(u8, path, ext)) return true;
        }
        return false;
    }

    pub fn appendImportCandidates(
        self: Rules,
        list: *std.ArrayList([]const u8),
        gpa: std.mem.Allocator,
        base: []const u8,
    ) !void {
        try push(list, gpa, base);

        if (!self.hasAnyExtension(base)) {
            for (self.extensions) |ext| {
                const with_ext = try std.fmt.allocPrint(gpa, "{s}{s}", .{ base, ext });
                defer gpa.free(with_ext);
                try push(list, gpa, with_ext);
            }
        }

        for (self.directory_defaults) |default_name| {
            const with_default = if (base.len == 0)
                try gpa.dupe(u8, default_name)
            else
                try std.fmt.allocPrint(gpa, "{s}/{s}", .{ base, default_name });
            defer gpa.free(with_default);
            try push(list, gpa, with_default);
        }

        if (base.len == 0) {
            for (self.package_entry_files) |entry| {
                try push(list, gpa, entry);
            }
        }
    }

    pub const ModuleKeys = struct {
        allocator: std.mem.Allocator,
        items: []const []const u8,

        pub fn deinit(self: *ModuleKeys) void {
            for (self.items) |item| self.allocator.free(item);
            self.allocator.free(self.items);
        }
    };

    pub fn generateModuleKeys(
        self: Rules,
        gpa: std.mem.Allocator,
        pkg_name: []const u8,
        rel_with_ext: []const u8,
        matched_ext: []const u8,
    ) !ModuleKeys {
        var list = std.ArrayList([]const u8).init(gpa);
        errdefer {
            for (list.items) |item| gpa.free(item);
            list.deinit();
        }

        try appendNormalized(&list, gpa, rel_with_ext);

        if (rel_with_ext.len > matched_ext.len and std.mem.endsWith(u8, rel_with_ext, matched_ext)) {
            const without_ext = rel_with_ext[0 .. rel_with_ext.len - matched_ext.len];
            try appendNormalized(&list, gpa, without_ext);
        }

        try self.addDirectoryAliases(&list, gpa, rel_with_ext);

        if (self.include_package_basename and self.matchesPackageBasename(pkg_name, rel_with_ext)) {
            try appendKey(&list, gpa, "");
        }

        for (self.package_entry_files) |entry| {
            if (std.mem.eql(u8, entry, rel_with_ext)) {
                try appendKey(&list, gpa, "");
                break;
            }
        }

        return ModuleKeys{
            .allocator = gpa,
            .items = try list.toOwnedSlice(),
        };
    }

    pub fn expectedPackageName(self: Rules, key: []const u8) []const u8 {
        if (key.len == 0) return "main";
        var trimmed = key;
        for (self.extensions) |ext| {
            if (trimmed.len > ext.len and std.mem.endsWith(u8, trimmed, ext)) {
                trimmed = trimmed[0 .. trimmed.len - ext.len];
                break;
            }
        }
        if (std.mem.lastIndexOfScalar(u8, trimmed, '/')) |idx| {
            return trimmed[idx + 1 ..];
        }
        return trimmed;
    }

    fn addDirectoryAliases(
        self: Rules,
        list: *std.ArrayList([]const u8),
        gpa: std.mem.Allocator,
        rel_with_ext: []const u8,
    ) !void {
        for (self.directory_defaults) |default_name| {
            if (!std.mem.endsWith(u8, rel_with_ext, default_name)) continue;
            if (rel_with_ext.len == default_name.len) {
                try appendKey(list, gpa, "");
            } else if (rel_with_ext.len > default_name.len + 1 and rel_with_ext[rel_with_ext.len - default_name.len - 1] == '/') {
                const alias_slice = rel_with_ext[0 .. rel_with_ext.len - default_name.len - 1];
                try appendNormalized(list, gpa, alias_slice);
            }
        }
    }

    fn matchesPackageBasename(self: Rules, pkg_name: []const u8, rel_with_ext: []const u8) bool {
        if (pkg_name.len == 0) return false;
        if (rel_with_ext.len <= pkg_name.len) return false;
        if (!std.mem.startsWith(u8, rel_with_ext, pkg_name)) return false;
        if (rel_with_ext.len > pkg_name.len + 1 and rel_with_ext[pkg_name.len] == '/') return false;
        const suffix = rel_with_ext[pkg_name.len..];
        if (suffix.len == 0 or suffix[0] != '.') return false;
        for (self.extensions) |ext| {
            if (std.mem.eql(u8, suffix, ext)) return true;
        }
        return false;
    }
};

fn appendNormalized(
    list: *std.ArrayList([]const u8),
    gpa: std.mem.Allocator,
    key: []const u8,
) !void {
    const normalized = try normalizeKey(gpa, key);
    errdefer gpa.free(normalized);
    if (contains(list.items, normalized)) {
        gpa.free(normalized);
        return;
    }
    try list.append(normalized);
}

fn appendKey(
    list: *std.ArrayList([]const u8),
    gpa: std.mem.Allocator,
    key: []const u8,
) !void {
    const duped = try gpa.dupe(u8, key);
    errdefer gpa.free(duped);
    if (contains(list.items, duped)) {
        gpa.free(duped);
        return;
    }
    try list.append(duped);
}

fn contains(items: []const []const u8, key: []const u8) bool {
    for (items) |item| {
        if (std.mem.eql(u8, item, key)) return true;
    }
    return false;
}

pub fn normalizeKey(gpa: std.mem.Allocator, input: []const u8) ![]u8 {
    var out = try gpa.dupe(u8, input);
    if (std.fs.path.sep != '/') {
        for (out) |*c| {
            if (c.* == std.fs.path.sep) {
                c.* = '/';
            }
        }
    }
    return out;
}

fn push(list: *std.ArrayList([]const u8), gpa: std.mem.Allocator, s: []const u8) !void {
    try list.append(gpa, try gpa.dupe(u8, s));
}
