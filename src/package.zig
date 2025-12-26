const std = @import("std");
const SourceManager = @import("compile.zig").SourceManager;
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const compile = @import("compile.zig");

const DependencySet = std.AutoHashMapUnmanaged(ast.StrId, void);
const DependencyGraph = std.AutoHashMapUnmanaged(u32, DependencySet);

/// Global compilation state tracking packages and dependency graphs.
pub const CompilationUnit = struct {
    gpa: std.mem.Allocator,
    packages: std.StringArrayHashMapUnmanaged(Package) = .{},
    mutex: std.Thread.Mutex = .{},
    dependencies: DependencyGraph = .{},

    pub fn init(gpa: std.mem.Allocator) CompilationUnit {
        return .{
            .gpa = gpa,
            .packages = .{},
            .dependencies = .{},
        };
    }

    /// Release all dependency sets and package tables.
    pub fn deinit(self: *CompilationUnit) void {
        var dep_iter = self.dependencies.iterator();
        while (dep_iter.next()) |entry| {
            entry.value_ptr.deinit(self.gpa);
        }
        self.dependencies.deinit(self.gpa);
        self.packages.deinit(self.gpa);
    }

    /// Track that `file_id` depends on `dependency`.
    pub fn addDependency(self: *CompilationUnit, file_id: u32, dependency: ast.StrId) !void {
        self.mutex.lock();
        defer self.mutex.unlock();

        if (self.dependencies.getPtr(file_id)) |deps| {
            try deps.put(self.gpa, dependency, {});
            return;
        }

        var deps: DependencySet = .{};
        errdefer deps.deinit(self.gpa);
        try deps.put(self.gpa, dependency, {});
        try self.dependencies.put(self.gpa, file_id, deps);
    }

    /// Create the implicit `main` package entry.
    pub fn createMain(self: *CompilationUnit) !void {
        try self.packages.put(self.gpa, "main", .{
            .source_manager = self.context.source_manager,
            .sources = .{},
        });
    }
};

/// Tracks the parsed data associated with a single source file.
pub const FileUnit = struct {
    file_id: u32,
    cst: ?cst.CST,
    ast: ?*ast.Ast,
    tir: ?*tir.TIR,
    type_info: ?types.TypeInfo,
};

/// Represents a collection of source files and shared package metadata.
pub const Package = struct {
    name: []const u8,
    gpa: std.mem.Allocator,
    sources: std.StringArrayHashMapUnmanaged(FileUnit),
    source_manager: *SourceManager,

    /// Construct a package with `name` and `source_manager`.
    pub fn init(gpa: std.mem.Allocator, name: []const u8, source_manager: *SourceManager) Package {
        return .{ .gpa = gpa, .name = name, .sources = .{}, .source_manager = source_manager };
    }

    /// Tear down the package-owned source table.
    pub fn deinit(self: *Package) void {
        self.sources.deinit(self.gpa);
    }
};
