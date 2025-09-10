const std = @import("std");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const lower = @import("lower.zig");
const checker = @import("checker.zig");
const bind = @import("bind.zig");
const infer = @import("infer.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;

pub const Result = struct {
    hir: ast.Unit,
    binder: ?bind.Binder,
    type_info: ?*infer.TypeInfo,
};

pub const Pipeline = struct {
    allocator: std.mem.Allocator,
    diags: *Diagnostics,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics) Pipeline {
        return .{ .allocator = allocator, .diags = diags };
    }

    pub fn run(self: *Pipeline, program: *const cst.Program) !Result {
        // 1) Lower + desugar (future) from CST to AST
        var lower_pass = lower.Lower.init(self.allocator, self.diags);
        var hir = try lower_pass.run(program);

        // 2) Bind names into symbol table
        var binder = bind.Binder.init(self.allocator);
        try binder.run(&hir);
        //
        // 3) Checker pass over HIR (structural checks)
        var chk = checker.Checker.init(self.allocator, self.diags);
        defer chk.deinit();
        try chk.run(&hir);
        //
        // 4) Type inference: produce a side table of types
        var typer = infer.Typer.init(self.allocator, self.diags, &binder.symtab);
        const type_info = try self.allocator.create(infer.TypeInfo);
        type_info.* = try typer.run(&hir);
        //
        // // 5) Meta pipeline looping would go here (fixed-point driver)

        return .{ .hir = hir, .binder = binder, .type_info = type_info };
    }
};
