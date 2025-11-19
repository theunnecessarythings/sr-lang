const std = @import("std");
const ast = @import("ast.zig");
const dod = @import("cst.zig");
const types = @import("types.zig");

pub const SymbolKind = enum { Var, Const, Function, Type, Param, Field };

pub const SymbolId = dod.Index(SymbolRow);
pub const RangeSym = dod.RangeOf(SymbolId);

pub const SymbolRow = struct {
    name: ast.StrId,
    kind: SymbolKind,
    is_comptime: bool,
    loc: ast.LocId,
    origin_decl: ast.OptDeclId,
    origin_param: ast.OptParamId,
};
pub const ScopeRow = struct { parent: dod.SentinelIndex(ScopeRow), symbols: RangeSym };

pub const ScopeId = dod.Index(ScopeRow);

pub const SymbolStore = struct {
    gpa: std.mem.Allocator,
    syms: dod.Table(SymbolRow) = .{},
    scopes: dod.Table(ScopeRow) = .{},
    sym_pool: dod.Pool(SymbolId) = .{},

    // active scope stack (for building ranges)
    stack: std.ArrayListUnmanaged(struct { id: ScopeId, list: std.ArrayListUnmanaged(SymbolId) }) = .{},

    pub fn init(gpa: std.mem.Allocator) SymbolStore {
        return .{ .gpa = gpa };
    }
    pub fn deinit(self: *SymbolStore) void {
        const gpa = self.gpa;
        for (self.stack.items) |*it| it.list.deinit(gpa);
        self.stack.deinit(gpa);
        self.syms.deinit(gpa);
        self.scopes.deinit(gpa);
        self.sym_pool.deinit(gpa);
    }

    pub fn push(self: *SymbolStore, parent: ?ScopeId) !ScopeId {
        const sid = self.scopes.add(self.gpa, .{ .parent = if (parent) |p| .some(p) else .none(), .symbols = .empty() });
        try self.stack.append(self.gpa, .{ .id = sid, .list = .{} });
        return sid;
    }
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
    pub fn currentId(self: *const SymbolStore) ScopeId {
        return self.stack.items[self.stack.items.len - 1].id;
    }

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

    pub fn declare(self: *SymbolStore, sym: SymbolRow) !SymbolId {
        const id = self.syms.add(self.gpa, sym);
        var frame_ptr = &self.stack.items[self.stack.items.len - 1];
        try frame_ptr.list.append(self.gpa, id);
        return id;
    }

    pub fn lookup(self: *const SymbolStore, scope_id: ScopeId, name: ast.StrId) ?SymbolId {
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
