const std = @import("std");
const ast = @import("ast.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const symbols = @import("symbols.zig");

pub const Typer = struct {
    allocator: std.mem.Allocator,
    diags: *Diagnostics,
    symtab: *symbols.SymbolTable,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics, symtab: *symbols.SymbolTable) Typer {
        return .{ .allocator = allocator, .diags = diags, .symtab = symtab };
    }

    pub fn run(self: *Typer, program: *ast.Unit) !void {
        // Placeholder: walk decls to set the stage for inference.
        _ = self;
        _ = program;
    }
};
