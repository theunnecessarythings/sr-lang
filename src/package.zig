const std = @import("std");
const SourceManager = @import("compile.zig").SourceManager;
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const compile = @import("compile.zig");

pub const CompilationUnit = struct {
    gpa: std.mem.Allocator,
    context: *compile.Context,
    packages: std.ArrayList(Package) = .{},

    pub fn init(gpa: std.mem.Allocator, context: *compile.Context) CompilationUnit {
        return .{
            .gpa = gpa,
            .context = context,
            .packages = .{},
        };
    }

    pub fn deinit(self: *CompilationUnit) void {
        self.packages.deinit(self.gpa);
    }

    pub fn createMain(self: *CompilationUnit) !void {
        try self.packages.append(self.gpa, .{
            .source_manager = self.context.source_manager,
            .sources = .{},
        });
    }
};

pub const FileUnit = struct {
    file_id: u32, // index into SourceManager
    package_id: u32, // index into CompilationUnit.packages
    cst: *const cst.CST,
    ast: *const ast.Ast,
    tir: *const tir.TIR,
    type_info: *types.TypeInfo,
};

pub const Package = struct {
    name: []const u8,
    gpa: std.mem.Allocator,
    sources: std.ArrayList(FileUnit),
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
