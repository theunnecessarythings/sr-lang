const std = @import("std");
const Loc = @import("lexer.zig").Token.Loc;
const ast = @import("ast.zig");

pub const SymbolKind = enum { Var, Const, Function, Type, Param, Field };

pub const SymbolOrigin = union(enum) {
    Decl: *ast.Decl,
    Param: *ast.Param,
};

pub const Symbol = struct {
    name: []const u8,
    kind: SymbolKind,
    loc: Loc,
    origin: SymbolOrigin,
};

pub const Scope = struct {
    allocator: std.mem.Allocator,
    parent: ?*Scope,
    table: std.StringHashMap(Symbol),

    pub fn init(allocator: std.mem.Allocator, parent: ?*Scope) Scope {
        return .{ .allocator = allocator, .parent = parent, .table = std.StringHashMap(Symbol).init(allocator) };
    }

    pub fn deinit(self: *Scope) void {
        self.table.deinit();
    }

    pub fn declare(self: *Scope, sym: Symbol) !void {
        try self.table.put(sym.name, sym);
    }

    pub fn lookup(self: *Scope, name: []const u8) ?Symbol {
        var s: ?*Scope = self;
        while (s) |scope| {
            if (scope.table.get(name)) |sym| return sym;
            s = scope.parent;
        }
        return null;
    }
};

pub const SymbolTable = struct {
    allocator: std.mem.Allocator,
    scopes: std.ArrayListUnmanaged(*Scope),

    pub fn init(allocator: std.mem.Allocator) SymbolTable {
        return .{ .allocator = allocator, .scopes = .{} };
    }

    pub fn deinit(self: *SymbolTable) void {
        // Pop and free allocated scopes
        var i: usize = self.scopes.items.len;
        while (i > 0) {
            i -= 1;
            const s = self.scopes.items[i];
            s.deinit();
            self.allocator.destroy(s);
        }
        self.scopes.deinit(self.allocator);
    }

    pub fn push(self: *SymbolTable) !*Scope {
        const parent = if (self.scopes.items.len > 0) self.scopes.items[self.scopes.items.len - 1] else null;
        const scope = try self.allocator.create(Scope);
        scope.* = Scope.init(self.allocator, parent);
        try self.scopes.append(self.allocator, scope);
        return scope;
    }

    pub fn pop(self: *SymbolTable) void {
        if (self.scopes.pop()) |scope| {
            scope.deinit();
            self.allocator.destroy(scope);
        }
    }

    pub fn current(self: *SymbolTable) *Scope {
        return self.scopes.items[self.scopes.items.len - 1];
    }
};

pub const SymPrinter = struct {
    out: *std.io.Writer,

    pub fn init(writer: *std.io.Writer) SymPrinter {
        return .{ .out = writer };
    }

    pub fn printTop(self: *SymPrinter, symbols: *SymbolTable) !void {
        try self.out.print("(Symbols\n", .{});
        if (symbols.scopes.items.len > 0) {
            const root = symbols.scopes.items[0];
            var it = root.table.iterator();
            while (it.next()) |entry| {
                const sym = entry.value_ptr.*;
                const kind = switch (sym.kind) {
                    .Var => "var",
                    .Const => "const",
                    .Function => "fn",
                    .Type => "type",
                    .Param => "param",
                    .Field => "field",
                };
                try self.out.print("  (sym {s} kind={s} loc=[{d},{d}])\n", .{ sym.name, kind, sym.loc.start, sym.loc.end });
            }
        }
        try self.out.print(")\n", .{});
        try self.out.flush();
    }
};
