const std = @import("std");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");

// Minimal AST -> TIR lowering for hello-world demo:
// - Finds top-level proc named "main"
// - Emits TIR function with void result
// - Recognizes print(<string>) calls and lowers to TIR.Call "print" with a ConstString arg
// - Always emits a return at end of entry block

pub const LowerTir = struct {
    allocator: std.mem.Allocator,
    type_arena: *types.TypeArena,

    pub fn init(allocator: std.mem.Allocator, arena: *types.TypeArena) LowerTir {
        return .{ .allocator = allocator, .type_arena = arena };
    }

    pub fn run(self: *LowerTir, unit: *const ast.Unit) !tir.Module {
        var module = tir.Module.init(self.allocator, self.type_arena);
        var builder = tir.Builder.init(self.allocator, &module);

        const void_t = try self.type_arena.mk(.{ .Void = {} });
        const str_t = try self.type_arena.mk(.{ .String = {} });

        for (unit.decls.items) |*decl| {
            if (decl.binding) |pat| {
                if (pat.* == .Binding) {
                    const name = pat.Binding.name;
                    if (std.mem.eql(u8, name, "main")) {
                        try self.lowerFunction(&builder, name, decl.value, void_t, str_t);
                    }
                }
            }
        }
        return module;
    }

    fn lowerFunction(self: *LowerTir, b: *tir.Builder, name: []const u8, expr: *const ast.Expr, void_t: types.TypeId, str_t: types.TypeId) !void {
        _ = self;
        switch (expr.*) {
            .FunctionLit => |fun| {
                const f = try b.addFunction(name, void_t, &[_]tir.Param{});
                const entry = try b.addBlock(f);
                if (fun.body) |body| {
                    for (body.items.items) |*stmt| {
                        try lowerStmt(b, entry, void_t, str_t, stmt);
                    }
                }
                b.retVoid(entry);
            },
            else => {},
        }
    }
};

fn lowerStmt(b: *tir.Builder, entry: *tir.Block, void_t: types.TypeId, str_t: types.TypeId, stmt: *const ast.Statement) !void {
    switch (stmt.*) {
        .Expr => |e| try lowerExpr(b, entry, void_t, str_t, &e),
        else => {},
    }
}

fn lowerExpr(b: *tir.Builder, entry: *tir.Block, void_t: types.TypeId, str_t: types.TypeId, expr: *const ast.Expr) !void {
    switch (expr.*) {
        .PostfixCall => |call| {
            // Recognize print("...")
            if (call.callee.* == .Identifier) {
                const callee = call.callee.Identifier.name;
                if (std.mem.eql(u8, callee, "print") and call.args.items.len == 1) {
                    const arg0 = call.args.items[0];
                    if (arg0.* == .StringLit) {
                        const s = arg0.StringLit.value;
                        const v = try b.constString(entry, str_t, s);
                        _ = try b.call(entry, void_t, "print", &[_]tir.ValueId{v});
                        return;
                    }
                }
            }
        },
        else => {},
    }
}
