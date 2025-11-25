const std = @import("std");
const ast = @import("ast.zig");
const dod = @import("cst.zig");
const types = @import("types.zig");

/// Classifies the kind of declaration a symbol represents.
pub const SymbolKind = enum {
    /// Regular mutable variable binding.
    Var,
    /// Immutable constant binding.
    Const,
    /// Function declaration symbol.
    Function,
    /// Type symbol (struct/enum/alias).
    Type,
    /// Parameter binding.
    Param,
    /// Field symbol nested in a struct/union.
    Field,
};

pub const SymbolId = dod.Index(SymbolRow);
/// Range helper for symbol identifiers.
pub const RangeSym = dod.RangeOf(SymbolId);

/// Represents an individual symbol recorded by the store.
pub const SymbolRow = struct {
    /// Interned name of the symbol.
    name: ast.StrId,
    /// Classification of the symbol kind.
    kind: SymbolKind,
    /// Whether the symbol originates from comptime code.
    is_comptime: bool,
    /// Source location for the declaration.
    loc: ast.LocId,
    /// Optionally tracks the declaration ID for origin.
    origin_decl: ast.OptDeclId,
    /// Optionally tracks the parameter ID for origin.
    origin_param: ast.OptParamId,
};
/// Tracks the parents and symbols belonging to a lexical scope.
pub const ScopeRow = struct {
    /// Optional parent scope identifier.
    parent: dod.SentinelIndex(ScopeRow),
    /// Range of symbols closed when the scope pops.
    symbols: RangeSym,
};

pub const ScopeId = dod.Index(ScopeRow);

/// Container managing symbol tables and scope stacks for semantic analysis.
pub const SymbolStore = struct {
    /// Allocator backing the symbol tables.
    gpa: std.mem.Allocator,
    /// Table storing every symbol row.
    syms: dod.Table(SymbolRow) = .{},
    /// Table storing every scope row.
    scopes: dod.Table(ScopeRow) = .{},
    /// Pool caching symbols for finalized scopes.
    sym_pool: dod.Pool(SymbolId) = .{},

    /// Active scope stack used for building finalized symbol ranges.
    stack: std.ArrayListUnmanaged(struct { id: ScopeId, list: std.ArrayListUnmanaged(SymbolId) }) = .{},

    /// Initialize an empty symbol store backed by `gpa`.
    pub fn init(gpa: std.mem.Allocator) SymbolStore {
        return .{ .gpa = gpa };
    }
    /// Release all allocated symbol tables and pools.
    pub fn deinit(self: *SymbolStore) void {
        const gpa = self.gpa;
        for (self.stack.items) |*it| it.list.deinit(gpa);
        self.stack.deinit(gpa);
        self.syms.deinit(gpa);
        self.scopes.deinit(gpa);
        self.sym_pool.deinit(gpa);
    }

    /// Push a new scope with optional `parent` and return its ID.
    pub fn push(self: *SymbolStore, parent: ?ScopeId) !ScopeId {
        const sid = self.scopes.add(self.gpa, .{ .parent = if (parent) |p| .some(p) else .none(), .symbols = .empty() });
        try self.stack.append(self.gpa, .{ .id = sid, .list = .{} });
        return sid;
    }
    /// Pop the most recent scope, finalizing its symbols.
    pub fn pop(self: *SymbolStore) void {
        const gpa = self.gpa;
        if (self.stack.items.len == 0) return;
        var frame = self.stack.items[self.stack.items.len - 1];
        self.stack.items.len -= 1;
        const range = self.sym_pool.pushMany(gpa, frame.list.items);
        var scope = self.scopes.get(frame.id);
        scope.symbols = range;
        self.scopes.list.set(frame.id.toRaw(), scope);
        frame.list.deinit(gpa);
    }
    /// Return the currently active scope identifier.
    pub fn currentId(self: *const SymbolStore) ScopeId {
        return self.stack.items[self.stack.items.len - 1].id;
    }

    /// Pretty-print the symbol store contents (diagnostic aid).
    pub fn print(self: *const SymbolStore, a: *const ast.Ast, comptime indent: usize) void {
        var buffer: [128]u8 = undefined;
        const indent_str_slice = buffer[0..indent];
        @memset(indent_str_slice, ' ');
        const indent_str = indent_str_slice;

        std.debug.print("{s}SymbolStore:\n", .{indent_str});

        const scope_indent_str_slice = buffer[0 .. indent + 2];
        @memset(scope_indent_str_slice, ' ');
        const scope_indent_str = scope_indent_str_slice;

        const sym_indent_str_slice = buffer[0 .. indent + 4];
        @memset(sym_indent_str_slice, ' ');
        const sym_indent_str = sym_indent_str_slice;

        const num_scopes = self.scopes.list.len;
        for (0..num_scopes) |i| {
            const scope_id = ScopeId.fromRaw(@intCast(i));
            const scope = self.scopes.get(scope_id);
            const parent_to_print: ?ScopeId = if (scope.parent.isNone()) null else scope.parent.unwrap();
            std.debug.print("{s}Scope({d}) parent: {?}\n", .{ scope_indent_str, i, parent_to_print });

            // Check if scope is on the stack
            var on_stack = false;
            for (self.stack.items) |frame| {
                if (frame.id.eq(scope_id)) {
                    on_stack = true;
                    for (frame.list.items) |sym_id| {
                        const row = self.syms.get(sym_id);
                        const name = a.exprs.strs.get(row.name);
                        std.debug.print("{s}{s}: {s} (loc={d})\n", .{ sym_indent_str, @tagName(row.kind), name, row.loc.toRaw() });
                    }
                    break;
                }
            }

            if (!on_stack) {
                const ids = self.sym_pool.slice(scope.symbols);
                for (ids) |sym_id| {
                    const row = self.syms.get(sym_id);
                    const name = a.exprs.strs.get(row.name);
                    std.debug.print("{s}{s}: {s} (loc={d})\n", .{ sym_indent_str, @tagName(row.kind), name, row.loc.toRaw() });
                }
            }
        }
    }

    /// Record `sym` into the current scope and return its ID.
    pub fn declare(self: *SymbolStore, sym: SymbolRow) !SymbolId {
        const id = self.syms.add(self.gpa, sym);
        var frame_ptr = &self.stack.items[self.stack.items.len - 1];
        try frame_ptr.list.append(self.gpa, id);
        return id;
    }

    /// Lookup `name` starting from `scope_id` and walking parents.
    pub fn lookup(self: *SymbolStore, scope_id: ScopeId, name: ast.StrId) ?SymbolId {
        // linear search current scope and parents
        var sid_opt: dod.SentinelIndex(ScopeRow) = .some(scope_id);
        while (!sid_opt.isNone()) {
            const sid = sid_opt.unwrap();
            const srow = self.scopes.get(sid);

            // Search symbols in the finalized pool for this scope
            const ids = self.sym_pool.slice(srow.symbols);
            for (ids) |sym_id| {
                const row = self.syms.get(sym_id);
                if (row.name.eq(name)) return sym_id;
            }

            // Also search symbols for this scope if it's on the stack
            for (self.stack.items) |frame| {
                if (frame.id.eq(sid)) {
                    for (frame.list.items) |sym_id| {
                        const row = self.syms.get(sym_id);
                        if (row.name.eq(name)) return sym_id;
                    }
                    break; // Found the scope on the stack, no need to check other frames for this sid
                }
            }

            sid_opt = srow.parent;
        }
        return null;
    }
};
