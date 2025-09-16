const std = @import("std");
const ast = @import("ast_v2.zig");
const dod = @import("cst_v2.zig");

pub const SymbolKind = enum { Var, Const, Function, Type, Param, Field };

pub const SymTag = struct {};
pub const ScopeTag = struct {};

pub const SymbolId = dod.Index(SymTag);
pub const ScopeId = dod.Index(ScopeTag);
pub const RangeSym = dod.RangeOf(SymbolId);

pub const SymbolRow = struct { name: ast.StrId, kind: SymbolKind, loc: ast.LocId, origin_decl: ast.OptDeclId, origin_param: ast.OptParamId };
pub const ScopeRow = struct { parent: dod.SentinelIndex(ScopeTag), symbols: RangeSym };

pub const SymbolStore = struct {
    gpa: std.mem.Allocator,
    syms: dod.Table(SymbolRow) = .{},
    scopes: dod.Table(ScopeRow) = .{},
    sym_pool: dod.Pool(SymbolId) = .{},

    // active scope stack (for building ranges)
    stack: std.ArrayListUnmanaged(struct { id: ScopeId, list: std.ArrayListUnmanaged(SymbolId) }) = .{},

    pub fn init(gpa: std.mem.Allocator) SymbolStore { return .{ .gpa = gpa }; }
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;
        for (self.stack.items) |*it| it.list.deinit(gpa);
        self.stack.deinit(gpa);
        self.syms.deinit(gpa);
        self.scopes.deinit(gpa);
        self.sym_pool.deinit(gpa);
    }

    pub fn push(self: *@This(), parent: ?ScopeId) !ScopeId {
        const sid = ScopeId.fromRaw(self.scopes.add(self.gpa, .{ .parent = if (parent) |p| dod.SentinelIndex(ScopeTag).some(p) else dod.SentinelIndex(ScopeTag).none(), .symbols = RangeSym.empty() }));
        try self.stack.append(self.gpa, .{ .id = sid, .list = .{} });
        return sid;
    }
    pub fn pop(self: *@This()) void {
        const gpa = self.gpa;
        if (self.stack.items.len == 0) return;
        var frame = self.stack.items[self.stack.items.len - 1];
        self.stack.items.len -= 1;
        const range = self.sym_pool.pushMany(gpa, frame.list.items);
        var scope = self.scopes.get(frame.id.toRaw());
        scope.symbols = range;
        self.scopes.list.set(frame.id.toRaw(), scope);
        frame.list.deinit(gpa);
    }
    pub fn currentId(self: *const @This()) ScopeId { return self.stack.items[self.stack.items.len - 1].id; }

    pub fn declare(self: *@This(), sym: SymbolRow) !SymbolId {
        const id = SymbolId.fromRaw(self.syms.add(self.gpa, sym));
        var frame_ptr = &self.stack.items[self.stack.items.len - 1];
        try frame_ptr.list.append(self.gpa, id);
        return id;
    }

    pub fn lookup(self: *const @This(), a: *const ast.Ast, scope_id: ScopeId, name: ast.StrId) ?SymbolId {
        _ = a;
        // linear search current scope and parents
        var sid_opt: dod.SentinelIndex(ScopeTag) = dod.SentinelIndex(ScopeTag).some(scope_id);
        while (!sid_opt.isNone()) {
            const sid = sid_opt.unwrap();
            const srow = self.scopes.get(sid.toRaw());
            const ids = self.sym_pool.slice(srow.symbols);
            for (ids) |sym_id| {
                const row = self.syms.get(sym_id.toRaw());
                if (row.name.toRaw() == name.toRaw()) return sym_id;
            }
            sid_opt = srow.parent;
        }
        return null;
    }
};
