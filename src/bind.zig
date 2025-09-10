const std = @import("std");
const ast = @import("ast.zig");
const symbols = @import("symbols.zig");

pub const Binder = struct {
    allocator: std.mem.Allocator,
    symtab: symbols.SymbolTable,

    pub fn init(allocator: std.mem.Allocator) Binder {
        return .{ .allocator = allocator, .symtab = symbols.SymbolTable.init(allocator) };
    }

    pub fn deinit(self: *Binder) void {
        self.symtab.deinit();
    }

    pub fn run(self: *Binder, program: *ast.Unit) !void {
        _ = try self.symtab.push(); // root scope
        for (program.decls.items) |decl| {
            if (decl.binding) |pat| {
                self.bindPattern(pat);
            }
        }
    }

    fn bindPattern(self: *Binder, p: *const ast.Pattern) void {
        switch (p.*) {
            .Wildcard => {},
            .Binding => |b| {
                const sym = symbols.Symbol{ .name = b.name, .kind = .Var, .loc = b.loc };
                _ = self.symtab.current().declare(sym) catch {};
            },
            .Tuple => |tup| {
                for (tup.elems.items) |sub| self.bindPattern(sub);
            },
            .Slice => |sl| {
                for (sl.elems.items) |sub| self.bindPattern(sub);
                if (sl.rest_binding) |rb| self.bindPattern(rb);
            },
            .Struct => |st| {
                for (st.fields.items) |f| self.bindPattern(f.pattern);
            },
            .VariantTuple => |vt| {
                for (vt.elems.items) |sub| self.bindPattern(sub);
            },
            .VariantStruct => |vs| {
                for (vs.fields.items) |f| self.bindPattern(f.pattern);
            },
            .Range => |_| {},
            .Or => |o| {
                for (o.alts.items) |alt| self.bindPattern(alt);
            },
            .At => |a| {
                // binder name is a.binder but also bind inner pattern
                const sym = symbols.Symbol{ .name = a.binder, .kind = .Var, .loc = a.loc };
                _ = self.symtab.current().declare(sym) catch {};
                self.bindPattern(a.pattern);
            },
            .Literal => |_| {},
            .Path => |_| {},
        }
    }
};
