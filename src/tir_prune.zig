const std = @import("std");
const compile = @import("compile.zig");
const package = @import("package.zig");
const tir = @import("tir.zig");
const ast = @import("ast.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const Loc = @import("lexer.zig").Token.Loc;

const Allocator = std.mem.Allocator;

pub const Options = struct {
    warn_unused: bool = false,
};

inline fn isThirdPartyUnit(context: *compile.Context, unit: *package.FileUnit) bool {
    const path = context.source_manager.get(unit.file_id) orelse return false;
    return std.mem.indexOf(u8, path, "/vendor/") != null or std.mem.indexOf(u8, path, "/std/") != null;
}

pub fn pruneUnusedFunctions(
    gpa: Allocator,
    context: *compile.Context,
    comp_unit: *package.CompilationUnit,
    opts: Options,
) !void {
    // Build name -> functions map across all units, and find roots.
    var name_to_funcs = std.AutoHashMap(tir.StrId, std.ArrayListUnmanaged(tir.FuncId)).init(gpa);
    defer {
        var it = name_to_funcs.valueIterator();
        while (it.next()) |lst| lst.deinit(gpa);
        name_to_funcs.deinit();
    }

    // Do not bail on indirect calls; we simply won't add edges for them.

    // Track which unit each function id belongs to (per TIR module)
    // We only need to filter each module's func_pool, so we operate per-unit after analysis.

    var pkg_it = comp_unit.packages.iterator();
    while (pkg_it.next()) |pkg| {
        var src_it = pkg.value_ptr.sources.iterator();
        while (src_it.next()) |unit_entry| {
            const unit = unit_entry.value_ptr;
            if (unit.tir == null) continue;
            const t = unit.tir.?;
            const funcs = t.funcs.func_pool.data.items;
            // Index functions by name
            for (funcs) |fid| {
                const frow = t.funcs.Function.get(fid);
                const gop = try name_to_funcs.getOrPut(frow.name);
                if (!gop.found_existing) gop.value_ptr.* = .{};
                try gop.value_ptr.append(gpa, fid);
            }
            // No-op scan here
        }
    }

    // Proceed regardless of presence of indirect calls.

    // Worklist on function names reached by calls, starting from implicit roots
    var reachable_names = std.AutoHashMapUnmanaged(tir.StrId, void){};
    defer reachable_names.deinit(gpa);

    var wl = std.ArrayListUnmanaged(tir.StrId){};
    defer wl.deinit(gpa);

    const main_sid = context.interner.intern("main");
    const init_sid = context.interner.intern("__sr_global_mlir_init");
    try wl.append(gpa, main_sid);
    try wl.append(gpa, init_sid);

    // Do not special-case externs; unreachable externs will be pruned too.

    // Traverse calls and mark names
    while (wl.items.len != 0) {
        const name = wl.pop().?;
        if (reachable_names.get(name) != null) continue;
        _ = try reachable_names.put(gpa, name, {});
        // For each function with this name, traverse its calls
        if (name_to_funcs.get(name)) |lst| {
            for (lst.items) |fid| {
                // Locate the owning module for this fid by scanning (cheap enough)
                var found_unit: ?*package.FileUnit = null;
                var pkg_it3 = comp_unit.packages.iterator();
                search_unit: while (pkg_it3.next()) |pkg| {
                    var src_it3 = pkg.value_ptr.sources.iterator();
                    while (src_it3.next()) |unit_entry| {
                        const unit = unit_entry.value_ptr;
                        if (unit.tir == null) continue;
                        const t = unit.tir.?;
                        const funcs = t.funcs.func_pool.data.items;
                        var matched = false;
                        for (funcs) |cand| {
                            if (cand.toRaw() == fid.toRaw()) {
                                matched = true;
                                break;
                            }
                        }
                        if (matched) {
                            found_unit = unit;
                            break :search_unit;
                        }
                    }
                }
                if (found_unit) |unit| {
                    const t = unit.tir.?;
                    const frow = t.funcs.Function.get(fid);
                    const blocks = t.funcs.block_pool.slice(frow.blocks);
                    for (blocks) |bid| {
                        const b = t.funcs.Block.get(bid);
                        const instrs = t.instrs.instr_pool.slice(b.instrs);
                        for (instrs) |iid| {
                            const k = t.instrs.index.kinds.items[iid.toRaw()];
                            if (k == .Call) {
                                const row = t.instrs.get(.Call, iid);
                                try wl.append(gpa, row.callee);
                            } else if (k == .GlobalAddr) {
                                // Treat taking the address of a function as a use that makes it reachable.
                                // If the referenced symbol name corresponds to a function, add it to the worklist.
                                const row = t.instrs.get(.GlobalAddr, iid);
                                if (name_to_funcs.get(row.name) != null) {
                                    try wl.append(gpa, row.name);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Collect referenced globals by scanning reachable functions.
    var referenced_globals = std.AutoHashMapUnmanaged(tir.StrId, void){};
    defer referenced_globals.deinit(gpa);
    var pkg_it_rg = comp_unit.packages.iterator();
    while (pkg_it_rg.next()) |pkg| {
        var src_it_rg = pkg.value_ptr.sources.iterator();
        while (src_it_rg.next()) |unit_entry| {
            const unit = unit_entry.value_ptr;
            if (unit.tir == null) continue;
            const t = unit.tir.?;
            const funcs = t.funcs.func_pool.data.items;
            for (funcs) |fid| {
                const frow = t.funcs.Function.get(fid);
                if (reachable_names.get(frow.name) == null) continue;
                const blocks = t.funcs.block_pool.slice(frow.blocks);
                for (blocks) |bid| {
                    const b = t.funcs.Block.get(bid);
                    const instrs = t.instrs.instr_pool.slice(b.instrs);
                    for (instrs) |iid| {
                        const k = t.instrs.index.kinds.items[iid.toRaw()];
                        if (k == .GlobalAddr) {
                            const row = t.instrs.get(.GlobalAddr, iid);
                            _ = try referenced_globals.put(gpa, row.name, {});
                        }
                    }
                }
            }
        }
    }

    // With reachable names computed, filter each module's function and global pools.
    var pkg_it4 = comp_unit.packages.iterator();
    while (pkg_it4.next()) |pkg| {
        var src_it4 = pkg.value_ptr.sources.iterator();
        while (src_it4.next()) |unit_entry| {
            const unit = unit_entry.value_ptr;
            if (unit.tir == null) continue;
            const t = unit.tir.?;
            const funcs = t.funcs.func_pool.data.items;
            var kept = std.ArrayList(tir.FuncId){};
            defer kept.deinit(gpa);

            // For warnings: build used set per function (only for reachable ones)
            const U32Set = std.AutoHashMapUnmanaged(u32, void);
            var used: U32Set = .{};
            defer used.deinit(gpa);

            for (funcs) |fid| {
                const frow = t.funcs.Function.get(fid);
                const keep = (reachable_names.get(frow.name) != null);
                if (keep) {
                    try kept.append(gpa, fid);
                    if (opts.warn_unused) {
                        // Recompute used set for this function
                        used.clearRetainingCapacity();
                        // Collect uses from all blocks/terms/instrs
                        const blocks = t.funcs.block_pool.slice(frow.blocks);
                        for (blocks) |bid| {
                            const b = t.funcs.Block.get(bid);
                            // Terminators
                            const term_k = t.terms.index.kinds.items[b.term.toRaw()];
                            switch (term_k) {
                                .Return => {
                                    const r = t.terms.get(.Return, b.term);
                                    if (!r.value.isNone()) _ = used.put(gpa, r.value.unwrap().toRaw(), {}) catch {};
                                },
                                .CondBr => {
                                    const c = t.terms.get(.CondBr, b.term);
                                    _ = used.put(gpa, c.cond.toRaw(), {}) catch {};
                                },
                                .SwitchInt => {
                                    const s = t.terms.get(.SwitchInt, b.term);
                                    _ = used.put(gpa, s.scrut.toRaw(), {}) catch {};
                                },
                                else => {},
                            }
                            // Instructions
                            const instrs = t.instrs.instr_pool.slice(b.instrs);
                            for (instrs) |iid| {
                                const k = t.instrs.index.kinds.items[iid.toRaw()];
                                switch (k) {
                                    .Gep => {
                                        const row = t.instrs.get(.Gep, iid);
                                        _ = used.put(gpa, row.base.toRaw(), {}) catch {};
                                        const idxs = t.instrs.gep_pool.slice(row.indices);
                                        for (idxs) |gid| switch (t.instrs.GepIndex.get(gid)) {
                                            .Const => {},
                                            .Value => |vv| _ = used.put(gpa, vv.toRaw(), {}) catch {},
                                        };
                                    },
                                    .StructMake => {
                                        const row = t.instrs.get(.StructMake, iid);
                                        const fields = t.instrs.sfi_pool.slice(row.fields);
                                        for (fields) |fid_s| {
                                            const f = t.instrs.StructFieldInit.get(fid_s);
                                            _ = used.put(gpa, f.value.toRaw(), {}) catch {};
                                        }
                                    },
                                    .TupleMake => {
                                        const row = t.instrs.get(.TupleMake, iid);
                                        for (t.instrs.value_pool.slice(row.elems)) |v| _ = used.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .ArrayMake => {
                                        const row = t.instrs.get(.ArrayMake, iid);
                                        for (t.instrs.value_pool.slice(row.elems)) |v| _ = used.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .Select => {
                                        const row = t.instrs.get(.Select, iid);
                                        _ = used.put(gpa, row.cond.toRaw(), {}) catch {};
                                        _ = used.put(gpa, row.then_value.toRaw(), {}) catch {};
                                        _ = used.put(gpa, row.else_value.toRaw(), {}) catch {};
                                    },
                                    .Call => {
                                        const row = t.instrs.get(.Call, iid);
                                        for (t.instrs.val_list_pool.slice(row.args)) |v| _ = used.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .IndirectCall => {
                                        const row = t.instrs.get(.IndirectCall, iid);
                                        _ = used.put(gpa, row.callee.toRaw(), {}) catch {};
                                        for (t.instrs.val_list_pool.slice(row.args)) |v| _ = used.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .MlirBlock => {
                                        const row = t.instrs.get(.MlirBlock, iid);
                                        for (t.instrs.value_pool.slice(row.args)) |v| _ = used.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .Load => {
                                        const row = t.instrs.get(.Load, iid);
                                        _ = used.put(gpa, row.ptr.toRaw(), {}) catch {};
                                    },
                                    .Store => {
                                        const row = t.instrs.get(.Store, iid);
                                        _ = used.put(gpa, row.ptr.toRaw(), {}) catch {};
                                        _ = used.put(gpa, row.value.toRaw(), {}) catch {};
                                    },
                                    .Index => {
                                        const row = t.instrs.get(.Index, iid);
                                        _ = used.put(gpa, row.base.toRaw(), {}) catch {};
                                        _ = used.put(gpa, row.index.toRaw(), {}) catch {};
                                    },
                                    .AddressOf => {
                                        const row = t.instrs.get(.AddressOf, iid);
                                        _ = used.put(gpa, row.value.toRaw(), {}) catch {};
                                    },
                                    .ExtractElem => {
                                        const row = t.instrs.get(.ExtractElem, iid);
                                        _ = used.put(gpa, row.agg.toRaw(), {}) catch {};
                                    },
                                    .InsertElem => {
                                        const row = t.instrs.get(.InsertElem, iid);
                                        _ = used.put(gpa, row.agg.toRaw(), {}) catch {};
                                        _ = used.put(gpa, row.value.toRaw(), {}) catch {};
                                    },
                                    .ExtractField => {
                                        const row = t.instrs.get(.ExtractField, iid);
                                        _ = used.put(gpa, row.agg.toRaw(), {}) catch {};
                                    },
                                    .InsertField => {
                                        const row = t.instrs.get(.InsertField, iid);
                                        _ = used.put(gpa, row.agg.toRaw(), {}) catch {};
                                        _ = used.put(gpa, row.value.toRaw(), {}) catch {};
                                    },
                                    .VariantMake => {
                                        const row = t.instrs.get(.VariantMake, iid);
                                        if (!row.payload.isNone()) _ = used.put(gpa, row.payload.unwrap().toRaw(), {}) catch {};
                                    },
                                    .UnionField => {
                                        const row = t.instrs.get(.UnionField, iid);
                                        _ = used.put(gpa, row.base.toRaw(), {}) catch {};
                                    },
                                    .UnionFieldPtr => {
                                        const row = t.instrs.get(.UnionFieldPtr, iid);
                                        _ = used.put(gpa, row.base.toRaw(), {}) catch {};
                                    },
                                    .ComplexMake => {
                                        const row = t.instrs.get(.ComplexMake, iid);
                                        _ = used.put(gpa, row.re.toRaw(), {}) catch {};
                                        _ = used.put(gpa, row.im.toRaw(), {}) catch {};
                                    },
                                    .RangeMake => {
                                        const row = t.instrs.get(.RangeMake, iid);
                                        _ = used.put(gpa, row.start.toRaw(), {}) catch {};
                                        _ = used.put(gpa, row.end.toRaw(), {}) catch {};
                                        _ = used.put(gpa, row.inclusive.toRaw(), {}) catch {};
                                    },

                                    inline .VariantTag,
                                    .VariantPayloadPtr,
                                    .UnionMake,
                                    .Broadcast,
                                    .LogicalNot,
                                    .CastNormal,
                                    .CastBit,
                                    .CastWrap,
                                    .CastChecked,
                                    .CastSaturate,
                                    => |kind| {
                                        const row = t.instrs.get(kind, iid);
                                        try used.put(gpa, row.value.toRaw(), {});
                                    },
                                    // binary group
                                    inline .Add,
                                    .Sub,
                                    .Mul,
                                    .BinWrapAdd,
                                    .BinWrapSub,
                                    .BinWrapMul,
                                    .BinSatAdd,
                                    .BinSatSub,
                                    .BinSatMul,
                                    .BinSatShl,
                                    .Div,
                                    .Mod,
                                    .Shl,
                                    .Shr,
                                    .BitAnd,
                                    .BitOr,
                                    .BitXor,
                                    .LogicalAnd,
                                    .LogicalOr,
                                    .CmpEq,
                                    .CmpNe,
                                    .CmpLt,
                                    .CmpLe,
                                    .CmpGt,
                                    .CmpGe,
                                    => |kind| {
                                        const row = t.instrs.get(kind, iid);
                                        try used.put(gpa, row.lhs.toRaw(), {});
                                        try used.put(gpa, row.rhs.toRaw(), {});
                                    },

                                    else => {},
                                }
                            }
                        }
                        // Param warnings
                        const params = t.funcs.param_pool.slice(frow.params);
                        for (params) |pid| {
                            const p = t.funcs.Param.get(pid);
                            if (used.get(p.value.toRaw()) == null) {
                                // Prefer precise AST param location if available
                                const pname_sid_raw: ?u32 = if (!p.name.isNone()) p.name.unwrap().toRaw() else null;
                                const anchor2 = paramNameLocFromAst(unit, frow.name.toRaw(), pname_sid_raw) orelse
                                    functionNameLocFromAst(unit, frow.name.toRaw()) orelse
                                    functionFirstLoc(context, t, frow, unit.file_id);
                                const pname = if (!p.name.isNone()) t.instrs.strs.get(p.name.unwrap()) else "param";
                                if (!isThirdPartyUnit(context, unit))
                                    _ = try context.diags.addWarning(anchor2, .unused_param, .{pname});
                            }
                        }
                        // Unused local warning: alloca with no read
                        var defmap0 = try buildDefMap(gpa, t, frow);
                        defer defmap0.deinit(gpa);
                        var read_allocas0 = try computeReadAllocas(gpa, t, frow, &defmap0);
                        defer read_allocas0.deinit(gpa);
                        for (blocks) |bb| {
                            const b2 = t.funcs.Block.get(bb);
                            const instrs2 = t.instrs.instr_pool.slice(b2.instrs);
                            for (instrs2) |iid2| {
                                if (t.instrs.index.kinds.items[iid2.toRaw()] == .Alloca) {
                                    const arow = t.instrs.get(.Alloca, iid2);
                                    const hadr = read_allocas0.get(arow.result.toRaw()) orelse false;
                                    if (!hadr) {
                                        const loc = if (!arow.loc.isNone()) context.loc_store.get(arow.loc.unwrap()) else Loc.init(unit.file_id, 0, 0);
                                        if (!isThirdPartyUnit(context, unit))
                                            _ = try context.diags.addWarning(loc, .unused_variable, .{});
                                    }
                                }
                            }
                        }
                    }
                } else if (opts.warn_unused) {
                    // Warn about unused functions (only those with bodies) and also
                    // emit param/local warnings inside them.
                    const blocks = t.funcs.block_pool.slice(frow.blocks);
                    if (blocks.len > 0) {
                        const fname = t.instrs.strs.get(frow.name);
                        const anchor = functionNameLocFromAst(unit, frow.name.toRaw()) orelse
                            functionFirstLoc(context, t, frow, unit.file_id);
                        if (!isThirdPartyUnit(context, unit))
                            _ = try context.diags.addWarning(anchor, .unused_function, .{fname});

                        // Suppress parameter/local warnings inside unused functions to avoid noise.
                        const emit_inside_unused = false;
                        if (!emit_inside_unused) continue;

                        // Build used set and simple read flags for allocas
                        var used2: std.AutoHashMapUnmanaged(u32, void) = .{};
                        defer used2.deinit(gpa);
                        var read_map = std.AutoHashMapUnmanaged(u32, bool){}; // alloca value id -> had_load
                        defer read_map.deinit(gpa);

                        // First pass: collect loads to set read_map for direct loads of the alloca ptr
                        for (blocks) |bid| {
                            const b = t.funcs.Block.get(bid);
                            const instrs = t.instrs.instr_pool.slice(b.instrs);
                            for (instrs) |iid2| {
                                if (t.instrs.index.kinds.items[iid2.toRaw()] == .Load) {
                                    const lr = t.instrs.get(.Load, iid2);
                                    _ = read_map.put(gpa, lr.ptr.toRaw(), true) catch {};
                                }
                            }
                        }
                        // Second pass: general uses (for params)
                        for (blocks) |bid| {
                            const b = t.funcs.Block.get(bid);
                            // Terminators
                            const term_k = t.terms.index.kinds.items[b.term.toRaw()];
                            switch (term_k) {
                                .Return => {
                                    const r = t.terms.get(.Return, b.term);
                                    if (!r.value.isNone()) _ = used2.put(gpa, r.value.unwrap().toRaw(), {}) catch {};
                                },
                                .CondBr => {
                                    const c = t.terms.get(.CondBr, b.term);
                                    _ = used2.put(gpa, c.cond.toRaw(), {}) catch {};
                                },
                                .SwitchInt => {
                                    const s = t.terms.get(.SwitchInt, b.term);
                                    _ = used2.put(gpa, s.scrut.toRaw(), {}) catch {};
                                },
                                else => {},
                            }
                            // Instructions
                            const instrs = t.instrs.instr_pool.slice(b.instrs);
                            for (instrs) |iid3| {
                                const k3 = t.instrs.index.kinds.items[iid3.toRaw()];
                                switch (k3) {
                                    .Gep => {
                                        const row = t.instrs.get(.Gep, iid3);
                                        _ = used2.put(gpa, row.base.toRaw(), {}) catch {};
                                        const idxs = t.instrs.gep_pool.slice(row.indices);
                                        for (idxs) |gid| switch (t.instrs.GepIndex.get(gid)) {
                                            .Const => {},
                                            .Value => |vv| _ = used2.put(gpa, vv.toRaw(), {}) catch {},
                                        };
                                    },
                                    .StructMake => {
                                        const row = t.instrs.get(.StructMake, iid3);
                                        const f = t.instrs.sfi_pool.slice(row.fields);
                                        for (f) |sfid| {
                                            const sf = t.instrs.StructFieldInit.get(sfid);
                                            _ = used2.put(gpa, sf.value.toRaw(), {}) catch {};
                                        }
                                    },
                                    .TupleMake => {
                                        const row = t.instrs.get(.TupleMake, iid3);
                                        for (t.instrs.value_pool.slice(row.elems)) |v| _ = used2.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .ArrayMake => {
                                        const row = t.instrs.get(.ArrayMake, iid3);
                                        for (t.instrs.value_pool.slice(row.elems)) |v| _ = used2.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .Select => {
                                        const row = t.instrs.get(.Select, iid3);
                                        _ = used2.put(gpa, row.cond.toRaw(), {}) catch {};
                                        _ = used2.put(gpa, row.then_value.toRaw(), {}) catch {};
                                        _ = used2.put(gpa, row.else_value.toRaw(), {}) catch {};
                                    },
                                    .Call => {
                                        const row = t.instrs.get(.Call, iid3);
                                        for (t.instrs.val_list_pool.slice(row.args)) |v| _ = used2.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .IndirectCall => {
                                        const row = t.instrs.get(.IndirectCall, iid3);
                                        _ = used2.put(gpa, row.callee.toRaw(), {}) catch {};
                                        for (t.instrs.val_list_pool.slice(row.args)) |v| _ = used2.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .MlirBlock => {
                                        const row = t.instrs.get(.MlirBlock, iid3);
                                        for (t.instrs.value_pool.slice(row.args)) |v| _ = used2.put(gpa, v.toRaw(), {}) catch {};
                                    },
                                    .Load => {
                                        const row = t.instrs.get(.Load, iid3);
                                        _ = used2.put(gpa, row.ptr.toRaw(), {}) catch {};
                                    },
                                    .Store => {
                                        const row = t.instrs.get(.Store, iid3);
                                        _ = used2.put(gpa, row.ptr.toRaw(), {}) catch {};
                                        _ = used2.put(gpa, row.value.toRaw(), {}) catch {};
                                    },
                                    .Index => {
                                        const row = t.instrs.get(.Index, iid3);
                                        _ = used2.put(gpa, row.base.toRaw(), {}) catch {};
                                        _ = used2.put(gpa, row.index.toRaw(), {}) catch {};
                                    },
                                    .AddressOf => {
                                        const row = t.instrs.get(.AddressOf, iid3);
                                        _ = used2.put(gpa, row.value.toRaw(), {}) catch {};
                                    },
                                    .ExtractElem => {
                                        const row = t.instrs.get(.ExtractElem, iid3);
                                        _ = used2.put(gpa, row.agg.toRaw(), {}) catch {};
                                    },
                                    .InsertElem => {
                                        const row = t.instrs.get(.InsertElem, iid3);
                                        _ = used2.put(gpa, row.agg.toRaw(), {}) catch {};
                                        _ = used2.put(gpa, row.value.toRaw(), {}) catch {};
                                    },
                                    .ExtractField => {
                                        const row = t.instrs.get(.ExtractField, iid3);
                                        _ = used2.put(gpa, row.agg.toRaw(), {}) catch {};
                                    },
                                    .InsertField => {
                                        const row = t.instrs.get(.InsertField, iid3);
                                        _ = used2.put(gpa, row.agg.toRaw(), {}) catch {};
                                        _ = used2.put(gpa, row.value.toRaw(), {}) catch {};
                                    },
                                    .VariantMake => {
                                        const row = t.instrs.get(.VariantMake, iid3);
                                        if (!row.payload.isNone()) _ = used2.put(gpa, row.payload.unwrap().toRaw(), {}) catch {};
                                    },
                                    .UnionField => {
                                        const row = t.instrs.get(.UnionField, iid3);
                                        _ = used2.put(gpa, row.base.toRaw(), {}) catch {};
                                    },
                                    .UnionFieldPtr => {
                                        const row = t.instrs.get(.UnionFieldPtr, iid3);
                                        _ = used2.put(gpa, row.base.toRaw(), {}) catch {};
                                    },
                                    .ComplexMake => {
                                        const row = t.instrs.get(.ComplexMake, iid3);
                                        _ = used2.put(gpa, row.re.toRaw(), {}) catch {};
                                        _ = used2.put(gpa, row.im.toRaw(), {}) catch {};
                                    },
                                    .RangeMake => {
                                        const row = t.instrs.get(.RangeMake, iid3);
                                        _ = used2.put(gpa, row.start.toRaw(), {}) catch {};
                                        _ = used2.put(gpa, row.end.toRaw(), {}) catch {};
                                        _ = used2.put(gpa, row.inclusive.toRaw(), {}) catch {};
                                    },
                                    inline .Broadcast,
                                    .LogicalNot,
                                    .CastNormal,
                                    .CastBit,
                                    .CastWrap,
                                    .CastChecked,
                                    .CastSaturate,
                                    .VariantTag,
                                    .VariantPayloadPtr,
                                    .UnionMake,
                                    => |kind| {
                                        const row = t.instrs.get(kind, iid3);
                                        try used2.put(gpa, row.value.toRaw(), {});
                                    },
                                    inline .Add,
                                    .Sub,
                                    .Mul,
                                    .BinWrapAdd,
                                    .BinWrapSub,
                                    .BinWrapMul,
                                    .BinSatAdd,
                                    .BinSatSub,
                                    .BinSatMul,
                                    .BinSatShl,
                                    .Div,
                                    .Mod,
                                    .Shl,
                                    .Shr,
                                    .BitAnd,
                                    .BitOr,
                                    .BitXor,
                                    .LogicalAnd,
                                    .LogicalOr,
                                    .CmpEq,
                                    .CmpNe,
                                    .CmpLt,
                                    .CmpLe,
                                    .CmpGt,
                                    .CmpGe,
                                    => |kind| {
                                        const row = t.instrs.get(kind, iid3);
                                        try used2.put(gpa, row.lhs.toRaw(), {});
                                        try used2.put(gpa, row.rhs.toRaw(), {});
                                    },
                                    else => {},
                                }
                            }
                        }
                        // Param warnings
                        const params2 = t.funcs.param_pool.slice(frow.params);
                        for (params2) |pid2| {
                            const p2 = t.funcs.Param.get(pid2);
                            if (used2.get(p2.value.toRaw()) == null) {
                                const pname = if (!p2.name.isNone()) t.instrs.strs.get(p2.name.unwrap()) else "param";
                                const pname_sid2: ?u32 = if (!p2.name.isNone()) p2.name.unwrap().toRaw() else null;
                                const ploc = paramNameLocFromAst(unit, frow.name.toRaw(), pname_sid2) orelse
                                    functionNameLocFromAst(unit, frow.name.toRaw()) orelse
                                    functionFirstLoc(context, t, frow, unit.file_id);
                                if (!isThirdPartyUnit(context, unit))
                                    _ = try context.diags.addWarning(ploc, .unused_param, .{pname});
                            }
                        }
                        // Simple unused local warning: alloca with no direct load
                        for (blocks) |bid3| {
                            const b3 = t.funcs.Block.get(bid3);
                            const instrs3 = t.instrs.instr_pool.slice(b3.instrs);
                            for (instrs3) |iid4| {
                                if (t.instrs.index.kinds.items[iid4.toRaw()] == .Alloca) {
                                    const arow2 = t.instrs.get(.Alloca, iid4);
                                    const had_read = read_map.get(arow2.result.toRaw()) orelse false;
                                    if (!had_read) {
                                        const loc2 = if (!arow2.loc.isNone()) context.loc_store.get(arow2.loc.unwrap()) else anchor;
                                        if (!isThirdPartyUnit(context, unit))
                                            _ = try context.diags.addWarning(loc2, .unused_variable, .{});
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // Overwrite pool with kept list
            t.funcs.func_pool.data.items = kept.toOwnedSlice(gpa) catch @panic("OOM");

            // Filter globals: keep only referenced ones, plus extern function decls that are reachable by name
            const globals = t.funcs.global_pool.data.items;
            var kept_g = std.ArrayList(tir.GlobalId){};
            defer kept_g.deinit(gpa);
            for (globals) |gid| {
                const grow = t.funcs.Global.get(gid);
                const kind = context.type_store.getKind(grow.ty);
                var keep_g = false;
                if (kind == .Function) {
                    // Retain extern function decl only if reachable by name and not defined locally in this module
                    const reachable = reachable_names.get(grow.name) != null;
                    if (reachable) {
                        var has_local_def = false;
                        for (funcs) |fid2| {
                            const fr2 = t.funcs.Function.get(fid2);
                            if (fr2.name.toRaw() == grow.name.toRaw()) {
                                const blks = t.funcs.block_pool.slice(fr2.blocks);
                                if (blks.len > 0) {
                                    has_local_def = true;
                                    break;
                                }
                            }
                        }
                        keep_g = !has_local_def;
                    }
                } else {
                    keep_g = referenced_globals.get(grow.name) != null;
                }
                if (keep_g) try kept_g.append(gpa, gid);
            }
            t.funcs.global_pool.data.items = kept_g.toOwnedSlice(gpa) catch @panic("OOM");
        }
    }
}

fn buildDefMap(
    gpa: std.mem.Allocator,
    t: *tir.TIR,
    frow: tir.FuncRows.Function,
) !std.AutoHashMapUnmanaged(u32, tir.InstrId) {
    var defmap: std.AutoHashMapUnmanaged(u32, tir.InstrId) = .{};
    const it_blocks = t.funcs.block_pool.slice(frow.blocks);
    for (it_blocks) |bid| {
        const b = t.funcs.Block.get(bid);
        const instrs = t.instrs.instr_pool.slice(b.instrs);
        for (instrs) |iid| {
            const k = t.instrs.index.kinds.items[iid.toRaw()];
            switch (k) {
                .MlirBlock => {
                    const row = t.instrs.get(.MlirBlock, iid);
                    if (!row.result.isNone()) _ = defmap.put(gpa, row.result.unwrap().toRaw(), iid) catch {};
                },
                else => {
                    // Most ops have a concrete result field
                    inline for (@typeInfo(tir.OpKind).@"enum".fields) |f| {
                        if (@field(tir.OpKind, f.name) == k) {
                            const Row = tir.RowT(@field(tir.OpKind, f.name));
                            if (@hasField(Row, "result")) {
                                const row = t.instrs.get(@field(tir.OpKind, f.name), iid);
                                _ = defmap.put(gpa, row.result.toRaw(), iid) catch {};
                            }
                            break;
                        }
                    }
                },
            }
        }
    }
    return defmap;
}

fn computeReadAllocas(
    gpa: std.mem.Allocator,
    t: *tir.TIR,
    frow: tir.FuncRows.Function,
    defmap: *std.AutoHashMapUnmanaged(u32, tir.InstrId),
) !std.AutoHashMapUnmanaged(u32, bool) {
    var read_allocas: std.AutoHashMapUnmanaged(u32, bool) = .{};
    var visited: std.AutoHashMapUnmanaged(u32, bool) = .{};
    defer visited.deinit(gpa);
    var queue = std.ArrayListUnmanaged(u32){};
    defer queue.deinit(gpa);

    const blocks = t.funcs.block_pool.slice(frow.blocks);
    for (blocks) |bid| {
        const b = t.funcs.Block.get(bid);
        const instrs = t.instrs.instr_pool.slice(b.instrs);
        for (instrs) |iid| {
            const kind = t.instrs.index.kinds.items[iid.toRaw()];
            switch (kind) {
                .Load => {
                    const lr = t.instrs.get(.Load, iid);
                    try queue.append(gpa, lr.ptr.toRaw());
                },
                .Call => {
                    const cr = t.instrs.get(.Call, iid);
                    for (t.instrs.val_list_pool.slice(cr.args)) |v| try queue.append(gpa, v.toRaw());
                },
                .IndirectCall => {
                    const icr = t.instrs.get(.IndirectCall, iid);
                    try queue.append(gpa, icr.callee.toRaw());
                    for (t.instrs.val_list_pool.slice(icr.args)) |v| try queue.append(gpa, v.toRaw());
                },
                else => {},
            }
        }
    }

    while (queue.pop()) |vraw| {
        if (visited.get(vraw) != null) continue;
        _ = visited.put(gpa, vraw, true) catch {};
        if (defmap.get(vraw)) |iid| {
            const k = t.instrs.index.kinds.items[iid.toRaw()];
            switch (k) {
                .Alloca => {
                    const ar = t.instrs.get(.Alloca, iid);
                    _ = read_allocas.put(gpa, ar.result.toRaw(), true) catch {};
                },
                .Gep => {
                    const gr = t.instrs.get(.Gep, iid);
                    try queue.append(gpa, gr.base.toRaw());
                },
                .UnionFieldPtr => {
                    const ur = t.instrs.get(.UnionFieldPtr, iid);
                    try queue.append(gpa, ur.base.toRaw());
                },
                .VariantPayloadPtr => {
                    const vr = t.instrs.get(.VariantPayloadPtr, iid);
                    try queue.append(gpa, vr.value.toRaw());
                },
                .AddressOf => {
                    const ar = t.instrs.get(.AddressOf, iid);
                    try queue.append(gpa, ar.value.toRaw());
                },
                else => {},
            }
        }
    }

    return read_allocas;
}

fn instrOptLoc(t: *tir.TIR, iid: tir.InstrId) tir.OptLocId {
    const k = t.instrs.index.kinds.items[iid.toRaw()];
    return switch (k) {
        inline else => |kind| t.instrs.get(kind, iid).loc,
    };
}

fn functionFirstLoc(context: *compile.Context, t: *tir.TIR, frow: tir.FuncRows.Function, file_id: u32) Loc {
    const blocks = t.funcs.block_pool.slice(frow.blocks);
    for (blocks) |bid| {
        const b = t.funcs.Block.get(bid);
        const instrs = t.instrs.instr_pool.slice(b.instrs);
        for (instrs) |iid| {
            const ol = instrOptLoc(t, iid);
            if (!ol.isNone()) return context.loc_store.get(ol.unwrap());
        }
        const termk = t.terms.index.kinds.items[b.term.toRaw()];
        const tl: tir.OptLocId = switch (termk) {
            .Return => t.terms.get(.Return, b.term).loc,
            .Br => t.terms.get(.Br, b.term).loc,
            .CondBr => t.terms.get(.CondBr, b.term).loc,
            .SwitchInt => t.terms.get(.SwitchInt, b.term).loc,
            .Unreachable => t.terms.get(.Unreachable, b.term).loc,
        };
        if (!tl.isNone()) return context.loc_store.get(tl.unwrap());
    }
    return Loc.init(file_id, 0, 0);
}

// =========================
// AST location utilities
// =========================

inline fn exprLocFromId(ast_unit: *ast.Ast, eid: ast.ExprId) Loc {
    const k = ast_unit.exprs.index.kinds.items[eid.toRaw()];
    return switch (k) {
        inline else => |x| exprLoc(ast_unit, ast_unit.exprs.get(x, eid)),
    };
}
inline fn exprLoc(ast_unit: *ast.Ast, expr: anytype) Loc {
    return ast_unit.exprs.locs.get(expr.loc);
}

fn bindingNameOfPattern(a: *ast.Ast, pid: ast.PatternId) ?ast.StrId {
    const k = a.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Binding => a.pats.get(.Binding, pid).name,
        else => null,
    };
}

fn bindingLocOfPattern(a: *ast.Ast, pid: ast.PatternId) ?Loc {
    const k = a.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Binding => blk: {
            const b = a.pats.get(.Binding, pid);
            break :blk a.exprs.locs.get(b.loc);
        },
        else => null,
    };
}

fn findTopFuncDeclByName(a: *ast.Ast, name_sid_raw: u32) ?ast.DeclId {
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    for (decls) |did| {
        const d = a.exprs.Decl.get(did);
        // Only consider top-level named function declarations
        const kind = a.exprs.index.kinds.items[d.value.toRaw()];
        if (kind != .FunctionLit) continue;
        if (!d.pattern.isNone()) {
            if (bindingNameOfPattern(a, d.pattern.unwrap())) |nm| {
                if (nm.toRaw() == name_sid_raw) return did;
            }
        }
    }
    return null;
}

fn functionNameLocFromAst(unit: *package.FileUnit, fname_sid_raw: u32) ?Loc {
    const a = unit.ast orelse return null;
    if (findTopFuncDeclByName(a, fname_sid_raw)) |did| {
        const d = a.exprs.Decl.get(did);
        if (!d.pattern.isNone()) {
            if (bindingLocOfPattern(a, d.pattern.unwrap())) |bl| return bl;
        }
        // Fallback to function literal location
        return exprLocFromId(a, d.value);
    }
    return null;
}

fn paramNameLocFromAst(unit: *package.FileUnit, func_name_sid_raw: u32, param_name_sid_raw: ?u32) ?Loc {
    const a = unit.ast orelse return null;
    const did_opt = findTopFuncDeclByName(a, func_name_sid_raw) orelse return null;
    const d = a.exprs.Decl.get(did_opt);
    const kind = a.exprs.index.kinds.items[d.value.toRaw()];
    if (kind != .FunctionLit) return null;
    const fnr = a.exprs.get(.FunctionLit, d.value);
    const params = a.exprs.param_pool.slice(fnr.params);
    for (params) |pid| {
        const p = a.exprs.Param.get(pid);
        if (!p.pat.isNone() and param_name_sid_raw != null) {
            if (bindingNameOfPattern(a, p.pat.unwrap())) |nm| {
                if (nm.toRaw() == param_name_sid_raw.?) {
                    // Prefer binding loc if available, else use whole param loc
                    if (bindingLocOfPattern(a, p.pat.unwrap())) |loc| return loc;
                    return a.exprs.locs.get(p.loc);
                }
            }
        }
    }
    return null;
}
