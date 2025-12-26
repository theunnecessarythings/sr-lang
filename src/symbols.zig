const std = @import("std");
const ast = @import("ast.zig");
const dod = @import("cst.zig");
const types = @import("types.zig");

/// Classifies the kind of declaration a symbol represents.
pub const SymbolKind = enum { Var, Const, Function, Type, Param, Field };

pub const SymbolId = dod.Index(SymbolRow);
/// Range helper for symbol identifiers.
pub const RangeSym = dod.RangeOf(SymbolId);

/// Represents an individual symbol recorded by the store.
pub const SymbolRow = struct {
    name: ast.StrId,
    kind: SymbolKind,
    is_comptime: bool,
    loc: ast.LocId,
    origin_decl: ast.OptDeclId,
    origin_param: ast.OptParamId,
};

/// Tracks the parents and symbols belonging to a lexical scope.
pub const ScopeRow = struct {
    parent: dod.SentinelIndex(ScopeRow),
    symbols: RangeSym,
};

pub const ScopeId = dod.Index(ScopeRow);

/// Container managing symbol tables and scope stacks for semantic analysis.
pub const SymbolStore = struct {
    arena: *std.heap.ArenaAllocator,
    backing_gpa: std.mem.Allocator,
    gpa: std.mem.Allocator,

    syms: dod.Table(SymbolRow) = .{},
    scopes: dod.Table(ScopeRow) = .{},
    sym_pool: dod.Pool(SymbolId) = .{},

    stack: std.ArrayListUnmanaged(StackFrame) = .{},

    const StackFrame = struct { id: ScopeId, list: std.ArrayListUnmanaged(SymbolId) };
    /// Initialize an empty symbol store backed by `gpa`.
    pub fn init(gpa: std.mem.Allocator) SymbolStore {
        const arena = gpa.create(std.heap.ArenaAllocator) catch @panic("OOM");
        arena.* = std.heap.ArenaAllocator.init(gpa);
        return .{ .arena = arena, .backing_gpa = gpa, .gpa = arena.allocator() };
    }

    /// Release all allocated symbol tables and pools.
    pub fn deinit(self: *SymbolStore) void {
        self.arena.deinit();
        self.backing_gpa.destroy(self.arena);
    }

    /// Push a new scope with optional `parent` and return its ID.
    pub fn push(self: *SymbolStore, parent: ?ScopeId) !ScopeId {
        const sid = self.scopes.add(self.gpa, .{ .parent = if (parent) |p| .some(p) else .none(), .symbols = .empty() });
        try self.stack.append(self.gpa, .{ .id = sid, .list = .{} });
        return sid;
    }

    /// Pop the most recent scope, finalizing its symbols.
    pub fn pop(self: *SymbolStore) void {
        if (self.stack.items.len == 0) return;
        // Copy struct (ptr/len/cap) before popping from stack view
        var frame = self.stack.items[self.stack.items.len - 1];
        self.stack.items.len -= 1;

        // Move symbols from dynamic list to persistent pool
        const range = self.sym_pool.pushMany(self.gpa, frame.list.items);
        var scope = self.scopes.get(frame.id);
        scope.symbols = range;
        self.scopes.list.set(frame.id.toRaw(), scope);
        // No need to deinit frame.list; arena handles it.
    }

    /// Return the currently active scope identifier.
    pub fn currentId(self: *const SymbolStore) ScopeId {
        return self.stack.items[self.stack.items.len - 1].id;
    }

    /// Pretty-print the symbol store contents (diagnostic aid).
    pub fn print(self: *SymbolStore, a: *const ast.Ast, indent: usize) void {
        printIndent(indent);
        std.debug.print("SymbolStore:\n", .{});

        const num_scopes = self.scopes.list.len;
        for (0..num_scopes) |i| {
            const scope_id = ScopeId.fromRaw(@intCast(i));
            const scope = self.scopes.get(scope_id);

            printIndent(indent + 2);
            std.debug.print("Scope({d}) parent: ", .{i});
            if (scope.parent.isNone()) std.debug.print("null\n", .{}) else std.debug.print("{d}\n", .{scope.parent.unwrap().toRaw()});

            // Check if scope is active on stack
            var on_stack = false;
            // Reverse iteration to find active scope faster
            var s_idx = self.stack.items.len;
            while (s_idx > 0) {
                s_idx -= 1;
                const frame = &self.stack.items[s_idx];
                if (frame.id.eq(scope_id)) {
                    on_stack = true;
                    for (frame.list.items) |sym_id| self.printSym(a, sym_id, indent + 4);
                    break;
                }
            }

            // If not on stack, print from finalized pool
            if (!on_stack) {
                const ids = self.sym_pool.slice(scope.symbols);
                for (ids) |sym_id| self.printSym(a, sym_id, indent + 4);
            }
        }
    }

    fn printSym(self: *SymbolStore, a: *const ast.Ast, sym_id: SymbolId, indent: usize) void {
        const row = self.syms.get(sym_id);
        const name = a.exprs.strs.get(row.name);
        printIndent(indent);
        std.debug.print("{s}: {s} (loc={d})\n", .{ @tagName(row.kind), name, row.loc.toRaw() });
    }

    fn printIndent(n: usize) void {
        var i: usize = 0;
        while (i < n) : (i += 1) std.debug.print(" ", .{});
    }

    /// Record `sym` into the current scope and return its ID.
    pub fn declare(self: *SymbolStore, sym: SymbolRow) !SymbolId {
        const id = self.syms.add(self.gpa, sym);
        try self.stack.items[self.stack.items.len - 1].list.append(self.gpa, id);
        return id;
    }

    /// Lookup `name` starting from `scope_id` and walking parents.
    pub fn lookup(self: *SymbolStore, scope_id: ScopeId, name: ast.StrId) ?SymbolId {
        var sid_opt: dod.SentinelIndex(ScopeRow) = .some(scope_id);
        while (!sid_opt.isNone()) {
            const sid = sid_opt.unwrap();
            const srow = self.scopes.get(sid);

            // 1. Search symbols in the finalized pool
            const ids = self.sym_pool.slice(srow.symbols);
            for (ids) |sym_id| {
                if (self.syms.get(sym_id).name.eq(name)) return sym_id;
            }

            // 2. Search symbols if scope is currently active on stack
            // Reverse iterate stack as active scopes are likely near top
            var i = self.stack.items.len;
            while (i > 0) {
                i -= 1;
                const frame = &self.stack.items[i];
                if (frame.id.eq(sid)) {
                    for (frame.list.items) |sym_id| {
                        if (self.syms.get(sym_id).name.eq(name)) return sym_id;
                    }
                    break;
                }
            }

            sid_opt = srow.parent;
        }
        return null;
    }
};
