const std = @import("std");
const SourceManager = @import("compile.zig").SourceManager;
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const compile = @import("compile.zig");

pub const CompilationUnit = struct {
    gpa: std.mem.Allocator,
    packages: std.StringArrayHashMapUnmanaged(Package) = .{},
    mutex: std.Thread.Mutex = .{},

    pub fn init(gpa: std.mem.Allocator) CompilationUnit {
        return .{
            .gpa = gpa,
            .packages = .{},
        };
    }

    pub fn deinit(self: *CompilationUnit) void {
        self.packages.deinit(self.gpa);
    }

    pub fn createMain(self: *CompilationUnit) !void {
        try self.packages.put(self.gpa, "main", .{
            .source_manager = self.context.source_manager,
            .sources = .{},
        });
    }
};

pub const FileUnit = struct {
    file_id: u32, // index into SourceManager
    cst: ?cst.CST,
    ast: ?*ast.Ast,
    tir: ?tir.TIR,
    type_info: ?types.TypeInfo,
};

pub const Package = struct {
    name: []const u8,
    gpa: std.mem.Allocator,
    sources: std.StringArrayHashMapUnmanaged(FileUnit),
    source_manager: *SourceManager,

    pub fn init(gpa: std.mem.Allocator, name: []const u8, source_manager: *SourceManager) Package {
        return .{
            .gpa = gpa,
            .name = name,
            .sources = .{},
            .source_manager = source_manager,
        };
    }

    pub fn deinit(self: *Package) void {
        self.sources.deinit(self.gpa);
    }
};
