const std = @import("std");
const compile = @import("compile.zig");
const package = @import("package.zig");
const tir = @import("tir.zig");
const ast = @import("ast.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const Loc = @import("lexer.zig").Token.Loc;

const Allocator = std.mem.Allocator;
const DynBitSet = std.bit_set.DynamicBitSet;

pub const Options = struct { warn_unused: bool = false };

inline fn isThirdPartyUnit(context: *compile.Context, unit: *package.FileUnit) bool {
    const path = context.source_manager.get(unit.file_id) orelse return false;
    return std.mem.indexOf(u8, path, "/vendor/") != null or std.mem.indexOf(u8, path, "/std/") != null;
}

const FuncRef = struct { unit: *package.FileUnit, fid: tir.FuncId };

const Pruner = struct {
    arena: *std.heap.ArenaAllocator,
    backing_gpa: Allocator,
    alloc: Allocator,
    context: *compile.Context,
    comp_unit: *package.CompilationUnit,
    opts: Options,

    name_to_funcs: std.AutoHashMap(tir.StrId, std.ArrayList(FuncRef)),
    reachable_names: std.AutoHashMap(tir.StrId, void),
    referenced_globals: std.AutoHashMap(tir.StrId, void),
    worklist: std.array_list.Managed(tir.StrId),

    fn init(gpa: Allocator, ctx: *compile.Context, cu: *package.CompilationUnit, opts: Options) Pruner {
        const arena = gpa.create(std.heap.ArenaAllocator) catch @panic("OOM");
        arena.* = std.heap.ArenaAllocator.init(gpa);
        const alloc = arena.allocator();
        return .{
            .arena = arena,
            .backing_gpa = gpa,
            .alloc = alloc,
            .context = ctx,
            .comp_unit = cu,
            .opts = opts,
            .name_to_funcs = .init(alloc),
            .reachable_names = .init(alloc),
            .referenced_globals = .init(alloc),
            .worklist = .init(alloc),
        };
    }

    fn deinit(self: *Pruner) void {
        self.arena.deinit();
        self.backing_gpa.destroy(self.arena);
    }

    fn run(self: *Pruner) !void {
        try self.indexFunctions();
        try self.seedRoots();
        try self.propagateReachability();
        try self.scanGlobals();
        try self.applyPruning();
    }

    fn indexFunctions(self: *Pruner) !void {
        var pkg_it = self.comp_unit.packages.iterator();
        while (pkg_it.next()) |pkg| {
            var src_it = pkg.value_ptr.sources.iterator();
            while (src_it.next()) |entry| {
                const unit = entry.value_ptr;
                if (unit.tir) |t| {
                    for (t.funcs.func_pool.inner.data.items) |fid_raw| {
                        const fid = tir.FuncId.fromRaw(fid_raw);
                        const f = t.funcs.Function.get(fid);
                        const gop = try self.name_to_funcs.getOrPut(f.name);
                        if (!gop.found_existing) gop.value_ptr.* = .empty;
                        try gop.value_ptr.append(self.alloc, .{ .unit = unit, .fid = fid });
                        if (f.is_triton_fn) try self.worklist.append(f.name);
                    }
                }
            }
        }
    }

    fn seedRoots(self: *Pruner) !void {
        try self.worklist.append(self.context.interner.intern("main"));
        try self.worklist.append(self.context.interner.intern("__sr_global_mlir_init"));
    }

    fn propagateReachability(self: *Pruner) !void {
        while (self.worklist.pop()) |name| {
            if (self.reachable_names.contains(name)) continue;
            try self.reachable_names.put(name, {});

            if (self.name_to_funcs.get(name)) |refs| {
                for (refs.items) |ref| try self.scanFuncCalls(ref);
            }
        }
    }

    fn scanFuncCalls(self: *Pruner, ref: FuncRef) !void {
        const t = ref.unit.tir.?;
        const f = t.funcs.Function.get(ref.fid);
        const blocks = t.funcs.block_pool.slice(f.blocks);
        for (blocks) |bid| {
            const b = t.funcs.Block.get(bid);
            for (t.instrs.instr_pool.slice(b.instrs)) |iid| {
                switch (t.kind(iid)) {
                    .Call => try self.worklist.append(t.instrs.get(.Call, iid).callee),
                    .GlobalAddr => {
                        const gname = t.instrs.get(.GlobalAddr, iid).name;
                        if (self.name_to_funcs.contains(gname)) try self.worklist.append(gname);
                    },
                    else => {},
                }
            }
        }
    }

    fn scanGlobals(self: *Pruner) !void {
        var it = self.reachable_names.keyIterator();
        while (it.next()) |name| {
            if (self.name_to_funcs.get(name.*)) |refs| {
                for (refs.items) |ref| {
                    const t = ref.unit.tir.?;
                    const f = t.funcs.Function.get(ref.fid);
                    const blocks = t.funcs.block_pool.slice(f.blocks);
                    for (blocks) |bid| {
                        const b = t.funcs.Block.get(bid);
                        for (t.instrs.instr_pool.slice(b.instrs)) |iid| {
                            if (t.kind(iid) == .GlobalAddr) {
                                try self.referenced_globals.put(t.instrs.get(.GlobalAddr, iid).name, {});
                            }
                        }
                    }
                }
            }
        }
    }

    fn applyPruning(self: *Pruner) !void {
        var pkg_it = self.comp_unit.packages.iterator();
        while (pkg_it.next()) |pkg| {
            var src_it = pkg.value_ptr.sources.iterator();
            while (src_it.next()) |entry| {
                const unit = entry.value_ptr;
                if (unit.tir) |t| try self.pruneUnit(unit, t);
            }
        }
    }

    fn pruneUnit(self: *Pruner, unit: *package.FileUnit, t: *tir.TIR) !void {
        // Functions
        var kept_funcs = std.ArrayListUnmanaged(u32){};
        for (t.funcs.func_pool.inner.data.items) |fid_raw| {
            const fid = tir.FuncId.fromRaw(fid_raw);
            const f = t.funcs.Function.get(fid);
            if (self.reachable_names.contains(f.name)) {
                try kept_funcs.append(t.funcs.allocator, fid.toRaw());
                if (self.opts.warn_unused and !isThirdPartyUnit(self.context, unit)) {
                    try warnUnusedInFunc(self.alloc, self.context, unit, t, f);
                }
            } else if (self.opts.warn_unused and !isThirdPartyUnit(self.context, unit)) {
                if (t.funcs.block_pool.slice(f.blocks).len > 0) {
                    const anchor = functionNameLocFromAst(unit, f.name.toRaw()) orelse functionFirstLoc(self.context, t, f, unit.file_id);
                    _ = try self.context.diags.addWarning(anchor, .unused_function, .{t.instrs.strs.get(f.name)});
                }
            }
        }
        var old_funcs = t.funcs.func_pool.inner.data;
        t.funcs.func_pool.inner.data = kept_funcs;
        old_funcs.deinit(t.funcs.allocator);

        // Globals
        var kept_globals = std.ArrayListUnmanaged(u32){};
        for (t.funcs.global_pool.inner.data.items) |gid_raw| {
            const gid = tir.GlobalId.fromRaw(gid_raw);
            const g = t.funcs.Global.get(gid);
            var keep = false;
            if (self.context.type_store.getKind(g.ty) == .Function) {
                if (self.reachable_names.contains(g.name)) {
                    // Only keep extern decl if no local definition exists in this unit
                    var has_local = false;
                    for (kept_funcs.items) |kfid_raw| if (t.funcs.Function.get(tir.FuncId.fromRaw(kfid_raw)).name.eq(g.name)) {
                        has_local = true;
                        break;
                    };
                    keep = !has_local;
                }
            } else {
                keep = self.referenced_globals.contains(g.name);
            }
            if (keep) try kept_globals.append(t.funcs.allocator, gid.toRaw());
        }
        var old_globals = t.funcs.global_pool.inner.data;
        t.funcs.global_pool.inner.data = kept_globals;
        old_globals.deinit(t.funcs.allocator);
    }
};

pub fn pruneUnusedFunctions(gpa: Allocator, context: *compile.Context, comp_unit: *package.CompilationUnit, opts: Options) !void {
    var pruner = Pruner.init(gpa, context, comp_unit, opts);
    defer pruner.deinit();
    try pruner.run();
}

// --- Warning Logic ---

fn warnUnusedInFunc(alloc: Allocator, context: *compile.Context, unit: *package.FileUnit, t: *tir.TIR, frow: tir.FuncRows.Function) !void {
    @setEvalBranchQuota(10000);
    const blocks = t.funcs.block_pool.slice(frow.blocks);
    if (blocks.len == 0) return;

    const max_val = t.instrs.value_pool.inner.data.items.len + 1024;
    var used_values = try DynBitSet.initEmpty(alloc, max_val);
    var alloca_read = try DynBitSet.initEmpty(alloc, max_val);

    for (blocks) |bid| {
        const b = t.funcs.Block.get(bid);
        for (t.instrs.instr_pool.slice(b.instrs)) |iid| {
            if (t.kind(iid) == .Load) alloca_read.set(t.instrs.get(.Load, iid).ptr.toRaw());

            // Mark all operands as used
            switch (t.kind(iid)) {
                inline else => |k| {
                    const row = t.instrs.get(k, iid);
                    inline for (@typeInfo(@TypeOf(row)).@"struct".fields) |fld| {
                        if (comptime std.mem.startsWith(u8, fld.name, "result")) continue;
                        if (fld.type == tir.ValueId) {
                            used_values.set(@field(row, fld.name).toRaw());
                        } else if (fld.type == tir.OptValueId) {
                            if (!@field(row, fld.name).isNone()) used_values.set(@field(row, fld.name).unwrap().toRaw());
                        } else if (fld.type == tir.RangeValue) {
                            if (comptime std.mem.eql(u8, fld.name, "args") and (k == .Call or k == .IndirectCall)) {
                                for (t.instrs.val_list_pool.slice(@field(row, fld.name))) |v| used_values.set(v.toRaw());
                            } else {
                                for (t.instrs.value_pool.slice(@field(row, fld.name))) |v| used_values.set(v.toRaw());
                            }
                        }
                    }
                },
            }
        }
        // Terms
        switch (t.kind(b.term)) {
            .Return => if (!t.terms.get(.Return, b.term).value.isNone()) used_values.set(t.terms.get(.Return, b.term).value.unwrap().toRaw()),
            .CondBr => used_values.set(t.terms.get(.CondBr, b.term).cond.toRaw()),
            .SwitchInt => used_values.set(t.terms.get(.SwitchInt, b.term).scrut.toRaw()),
            else => {},
        }
    }

    // Params
    for (t.funcs.param_pool.slice(frow.params)) |pid| {
        const p = t.funcs.Param.get(pid);
        if (!used_values.isSet(p.value.toRaw())) {
            const pid_raw: ?u32 = if (!p.name.isNone()) p.name.unwrap().toRaw() else null;
            const loc = paramNameLocFromAst(unit, frow.name.toRaw(), pid_raw) orelse functionFirstLoc(context, t, frow, unit.file_id);
            _ = try context.diags.addWarning(loc, .unused_param, .{});
        }
    }

    // Allocas
    for (blocks) |bid| {
        const b = t.funcs.Block.get(bid);
        for (t.instrs.instr_pool.slice(b.instrs)) |iid| {
            if (t.kind(iid) == .Alloca) {
                const row = t.instrs.get(.Alloca, iid);
                if (!alloca_read.isSet(row.result.toRaw())) {
                    const loc = if (!row.loc.isNone()) context.loc_store.get(row.loc.unwrap()) else functionFirstLoc(context, t, frow, unit.file_id);
                    _ = try context.diags.addWarning(loc, .unused_variable, .{});
                }
            }
        }
    }
}

// --- Helpers ---

inline fn exprLocFromId(ast_unit: *ast.Ast, eid: ast.ExprId) Loc {
    return switch (ast_unit.kind(eid)) {
        inline else => |x| ast_unit.exprs.locs.get(ast_unit.exprs.get(x, eid).loc),
    };
}

fn bindingNameOfPattern(a: *ast.Ast, pid: ast.PatternId) ?ast.StrId {
    return if (a.kind(pid) == .Binding) a.pats.get(.Binding, pid).name else null;
}

fn bindingLocOfPattern(a: *ast.Ast, pid: ast.PatternId) ?Loc {
    return if (a.kind(pid) == .Binding) a.exprs.locs.get(a.pats.get(.Binding, pid).loc) else null;
}

fn findTopFuncDeclByName(a: *ast.Ast, name_sid_raw: u32) ?ast.DeclId {
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    for (decls) |did| {
        const d = a.exprs.Decl.get(did);
        if (a.kind(d.value) != .FunctionLit) continue;
        if (!d.pattern.isNone()) {
            if (bindingNameOfPattern(a, d.pattern.unwrap())) |nm| {
                if (nm.eq(ast.StrId.fromRaw(name_sid_raw))) return did;
            }
        }
    }
    return null;
}

fn functionNameLocFromAst(unit: *package.FileUnit, fname_sid_raw: u32) ?Loc {
    const a = unit.ast orelse return null;
    if (findTopFuncDeclByName(a, fname_sid_raw)) |did| {
        const d = a.exprs.Decl.get(did);
        if (!d.pattern.isNone()) if (bindingLocOfPattern(a, d.pattern.unwrap())) |bl| return bl;
        return exprLocFromId(a, d.value);
    }
    return null;
}

fn paramNameLocFromAst(unit: *package.FileUnit, func_name_sid_raw: u32, param_name_sid_raw: ?u32) ?Loc {
    const a = unit.ast orelse return null;
    const did_opt = findTopFuncDeclByName(a, func_name_sid_raw) orelse return null;
    const d = a.exprs.Decl.get(did_opt);
    if (a.kind(d.value) != .FunctionLit) return null;
    const fnr = a.exprs.get(.FunctionLit, d.value);
    for (a.exprs.param_pool.slice(fnr.params)) |pid| {
        const p = a.exprs.Param.get(pid);
        if (!p.pat.isNone() and param_name_sid_raw != null) {
            if (bindingNameOfPattern(a, p.pat.unwrap())) |nm| {
                if (nm.eq(ast.StrId.fromRaw(param_name_sid_raw.?))) {
                    return if (bindingLocOfPattern(a, p.pat.unwrap())) |loc| loc else a.exprs.locs.get(p.loc);
                }
            }
        }
    }
    return null;
}

fn instrOptLoc(t: *tir.TIR, iid: tir.InstrId) tir.OptLocId {
    return switch (t.kind(iid)) {
        inline else => |kind| t.instrs.get(kind, iid).loc,
    };
}

fn functionFirstLoc(context: *compile.Context, t: *tir.TIR, frow: tir.FuncRows.Function, file_id: u32) Loc {
    const blocks = t.funcs.block_pool.slice(frow.blocks);
    for (blocks) |bid| {
        const b = t.funcs.Block.get(bid);
        for (t.instrs.instr_pool.slice(b.instrs)) |iid| {
            const ol = instrOptLoc(t, iid);
            if (!ol.isNone()) return context.loc_store.get(ol.unwrap());
        }
        const tl: tir.OptLocId = switch (t.kind(b.term)) {
            .Return => t.terms.get(.Return, b.term).loc,
            .Br => t.terms.get(.Br, b.term).loc,
            .CondBr => t.terms.get(.CondBr, b.term).loc,
            .SwitchInt => t.terms.get(.SwitchInt, b.term).loc,
            .Unreachable => t.terms.get(.Unreachable, b.term).loc,
        };
        if (!tl.isNone()) return context.loc_store.get(tl.unwrap());
    }
    return .init(file_id, 0, 0);
}
