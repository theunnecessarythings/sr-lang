const std = @import("std");
const compile = @import("compile.zig");
const package = @import("package.zig");
const tir = @import("tir.zig");
const ast = @import("ast.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const Loc = @import("lexer.zig").Token.Loc;

const Allocator = std.mem.Allocator;

inline fn insertValueKey(gpa: Allocator, map: *std.AutoHashMapUnmanaged(u32, void), value: tir.ValueId) void {
    _ = map.put(gpa, value.toRaw(), {}) catch {};
}

inline fn containsValueKey(map: *std.AutoHashMapUnmanaged(u32, void), value: tir.ValueId) bool {
    return map.get(value.toRaw()) != null;
}

inline fn insertValueBool(gpa: Allocator, map: *std.AutoHashMapUnmanaged(u32, bool), value: tir.ValueId) void {
    _ = map.put(gpa, value.toRaw(), true) catch {};
}

inline fn valueBool(map: *std.AutoHashMapUnmanaged(u32, bool), value: tir.ValueId) bool {
    return map.get(value.toRaw()) orelse false;
}

inline fn insertValueInstr(gpa: Allocator, map: *std.AutoHashMapUnmanaged(u32, tir.InstrId), value: tir.ValueId, iid: tir.InstrId) void {
    _ = map.put(gpa, value.toRaw(), iid) catch {};
}

inline fn insertOptValueInstr(gpa: Allocator, map: *std.AutoHashMapUnmanaged(u32, tir.InstrId), value: tir.OptValueId, iid: tir.InstrId) void {
    if (value.isNone()) return;
    insertValueInstr(gpa, map, value.unwrap(), iid);
}

inline fn lookupValueInstr(map: *std.AutoHashMapUnmanaged(u32, tir.InstrId), value: tir.ValueId) ?tir.InstrId {
    if (map.get(value.toRaw())) |entry| return entry;
    return null;
}

/// Configuration knobs controlling the pruning run.
pub const Options = struct {
    /// Emit warnings for reachable functions that expose unused values.
    warn_unused: bool = false,
};

/// Determine whether `unit` was loaded from a third-party / vendor path.
/// This lets pruning ignore standard library and vendor packages.
inline fn isThirdPartyUnit(context: *compile.Context, unit: *package.FileUnit) bool {
    const path = context.source_manager.get(unit.file_id) orelse return false;
    return std.mem.indexOf(u8, path, "/vendor/") != null or std.mem.indexOf(u8, path, "/std/") != null;
}

/// Prune unreferenced functions/globals from every TIR module.
/// `opts` controls optional warnings emitted during the pass.
pub fn pruneUnusedFunctions(
    gpa: Allocator,
    context: *compile.Context,
    comp_unit: *package.CompilationUnit,
    opts: Options,
) !void {
    // Helper that keeps track of the `FileUnit` owning a function while scanning calls.
    const FuncRef = struct {
        /// File unit that owns the referenced function.
        unit: *package.FileUnit,
        /// Identifier of the function within its owning TIR module.
        fid: tir.FuncId,
    };

    // Build name -> functions map across all units, and find roots.
    var name_to_funcs: std.AutoHashMap(tir.StrId, std.ArrayListUnmanaged(FuncRef)) = .init(gpa);
    defer {
        var it = name_to_funcs.valueIterator();
        while (it.next()) |lst| lst.deinit(gpa);
        name_to_funcs.deinit();
    }

    // Worklist on function names reached by calls, starting from implicit roots
    var reachable_names = std.AutoHashMapUnmanaged(tir.StrId, void){};
    defer reachable_names.deinit(gpa);

    var wl = std.ArrayListUnmanaged(tir.StrId){};
    defer wl.deinit(gpa);

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
                try gop.value_ptr.append(gpa, .{ .unit = unit, .fid = fid });
                if (frow.is_triton_fn) {
                    try wl.append(gpa, frow.name);
                }
                // // DEBUG
                // std.debug.print("Registered: {s}\n", .{t.instrs.strs.get(frow.name)});
            }
            // No-op scan here
        }
    }

    // Proceed regardless of presence of indirect calls.

    const main_sid = context.interner.intern("main");
    const init_sid = context.interner.intern("__sr_global_mlir_init");
    try wl.append(gpa, main_sid);
    try wl.append(gpa, init_sid);
    // DEBUG
    // std.debug.print("Roots: main, __sr_global_mlir_init\n", .{});

    // Do not special-case externs; unreachable externs will be pruned too.

    // Traverse calls and mark names
    while (wl.items.len != 0) {
        const name = wl.pop().?;
        if (reachable_names.get(name) != null) continue;
        _ = try reachable_names.put(gpa, name, {});

        // DEBUG
        // std.debug.print("Pop: {s}\n", .{context.interner.get(name)});

        // For each function with this name, traverse its calls
        if (name_to_funcs.get(name)) |lst| {
            for (lst.items) |ref| {
                if (ref.unit.tir == null) continue;
                const t = ref.unit.tir.?;
                const frow = t.funcs.Function.get(ref.fid);
                const blocks = t.funcs.block_pool.slice(frow.blocks);
                for (blocks) |bid| {
                    const b = t.funcs.Block.get(bid);
                    const instrs = t.instrs.instr_pool.slice(b.instrs);
                    for (instrs) |iid| {
                        if (t.kind(iid) == .Call) {
                            const row = t.instrs.get(.Call, iid);
                            try wl.append(gpa, row.callee);
                            // DEBUG
                            // std.debug.print("  Call: {s}\n", .{t.instrs.strs.get(row.callee)});
                        } else if (t.kind(iid) == .GlobalAddr) {
                            // Treat taking the address of a function as a use that makes it reachable.
                            // If the referenced symbol name corresponds to a function, add it to the worklist.
                            const row = t.instrs.get(.GlobalAddr, iid);
                            if (name_to_funcs.get(row.name) != null) {
                                try wl.append(gpa, row.name);
                                // DEBUG
                                // std.debug.print("  GlobalAddr: {s}\n", .{t.instrs.strs.get(row.name)});
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
                        if (t.kind(iid) == .GlobalAddr) {
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
                            switch (t.kind(b.term)) {
                                .Return => {
                                    const r = t.terms.get(.Return, b.term);
                                    if (!r.value.isNone()) insertValueKey(gpa, &used, r.value.unwrap());
                                },
                                .CondBr => {
                                    const c = t.terms.get(.CondBr, b.term);
                                    insertValueKey(gpa, &used, c.cond);
                                },
                                .SwitchInt => {
                                    const s = t.terms.get(.SwitchInt, b.term);
                                    insertValueKey(gpa, &used, s.scrut);
                                },
                                else => {},
                            }
                            // Instructions
                            const instrs = t.instrs.instr_pool.slice(b.instrs);
                            for (instrs) |iid| {
                                switch (t.kind(iid)) {
                                    .Gep => {
                                        const row = t.instrs.get(.Gep, iid);
                                        insertValueKey(gpa, &used, row.base);
                                        const idxs = t.instrs.gep_pool.slice(row.indices);
                                        for (idxs) |gid| switch (t.instrs.GepIndex.get(gid)) {
                                            .Const => {},
                                            .Value => |vv| insertValueKey(gpa, &used, vv),
                                        };
                                    },
                                    .StructMake => {
                                        const row = t.instrs.get(.StructMake, iid);
                                        const fields = t.instrs.sfi_pool.slice(row.fields);
                                        for (fields) |fid_s| {
                                            const f = t.instrs.StructFieldInit.get(fid_s);
                                            insertValueKey(gpa, &used, f.value);
                                        }
                                    },
                                    .TupleMake => {
                                        const row = t.instrs.get(.TupleMake, iid);
                                        for (t.instrs.value_pool.slice(row.elems)) |v| insertValueKey(gpa, &used, v);
                                    },
                                    .ArrayMake => {
                                        const row = t.instrs.get(.ArrayMake, iid);
                                        for (t.instrs.value_pool.slice(row.elems)) |v| insertValueKey(gpa, &used, v);
                                    },
                                    .Select => {
                                        const row = t.instrs.get(.Select, iid);
                                        insertValueKey(gpa, &used, row.cond);
                                        insertValueKey(gpa, &used, row.then_value);
                                        insertValueKey(gpa, &used, row.else_value);
                                    },
                                    .Call => {
                                        const row = t.instrs.get(.Call, iid);
                                        for (t.instrs.val_list_pool.slice(row.args)) |v| insertValueKey(gpa, &used, v);
                                    },
                                    .IndirectCall => {
                                        const row = t.instrs.get(.IndirectCall, iid);
                                        insertValueKey(gpa, &used, row.callee);
                                        for (t.instrs.val_list_pool.slice(row.args)) |v| insertValueKey(gpa, &used, v);
                                    },
                                    .MlirBlock => {
                                        const row = t.instrs.get(.MlirBlock, iid);
                                        for (t.instrs.value_pool.slice(row.args)) |v| insertValueKey(gpa, &used, v);
                                    },
                                    .Load => {
                                        const row = t.instrs.get(.Load, iid);
                                        insertValueKey(gpa, &used, row.ptr);
                                    },
                                    .Store => {
                                        const row = t.instrs.get(.Store, iid);
                                        insertValueKey(gpa, &used, row.ptr);
                                        insertValueKey(gpa, &used, row.value);
                                    },
                                    .Index => {
                                        const row = t.instrs.get(.Index, iid);
                                        insertValueKey(gpa, &used, row.base);
                                        insertValueKey(gpa, &used, row.index);
                                    },
                                    .AddressOf => {
                                        const row = t.instrs.get(.AddressOf, iid);
                                        insertValueKey(gpa, &used, row.value);
                                    },
                                    .ExtractElem => {
                                        const row = t.instrs.get(.ExtractElem, iid);
                                        insertValueKey(gpa, &used, row.agg);
                                    },
                                    .InsertElem => {
                                        const row = t.instrs.get(.InsertElem, iid);
                                        insertValueKey(gpa, &used, row.agg);
                                        insertValueKey(gpa, &used, row.value);
                                    },
                                    .ExtractField => {
                                        const row = t.instrs.get(.ExtractField, iid);
                                        insertValueKey(gpa, &used, row.agg);
                                    },
                                    .InsertField => {
                                        const row = t.instrs.get(.InsertField, iid);
                                        insertValueKey(gpa, &used, row.agg);
                                        insertValueKey(gpa, &used, row.value);
                                    },
                                    .VariantMake => {
                                        const row = t.instrs.get(.VariantMake, iid);
                                        if (!row.payload.isNone()) insertValueKey(gpa, &used, row.payload.unwrap());
                                    },
                                    .UnionField => {
                                        const row = t.instrs.get(.UnionField, iid);
                                        insertValueKey(gpa, &used, row.base);
                                    },
                                    .UnionFieldPtr => {
                                        const row = t.instrs.get(.UnionFieldPtr, iid);
                                        insertValueKey(gpa, &used, row.base);
                                    },
                                    .ComplexMake => {
                                        const row = t.instrs.get(.ComplexMake, iid);
                                        insertValueKey(gpa, &used, row.re);
                                        insertValueKey(gpa, &used, row.im);
                                    },
                                    .RangeMake => {
                                        const row = t.instrs.get(.RangeMake, iid);
                                        insertValueKey(gpa, &used, row.start);
                                        insertValueKey(gpa, &used, row.end);
                                        insertValueKey(gpa, &used, row.inclusive);
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
                                        insertValueKey(gpa, &used, row.value);
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
                                        insertValueKey(gpa, &used, row.lhs);
                                        insertValueKey(gpa, &used, row.rhs);
                                    },

                                    else => {},
                                }
                            }
                        }
                        // Param warnings
                        const params = t.funcs.param_pool.slice(frow.params);
                        for (params) |pid| {
                            const p = t.funcs.Param.get(pid);
                            if (!containsValueKey(&used, p.value)) {
                                // Prefer precise AST param location if available
                                const pname_sid_raw: ?u32 = if (!p.name.isNone()) p.name.unwrap().toRaw() else null;
                                const anchor2 = paramNameLocFromAst(unit, frow.name.toRaw(), pname_sid_raw) orelse
                                    functionNameLocFromAst(unit, frow.name.toRaw()) orelse
                                    functionFirstLoc(context, t, frow, unit.file_id);
                                if (!isThirdPartyUnit(context, unit))
                                    _ = try context.diags.addWarning(anchor2, .unused_param, .{});
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
                                if (t.kind(iid2) == .Alloca) {
                                    const arow = t.instrs.get(.Alloca, iid2);
                                    const hadr = valueBool(&read_allocas0, arow.result);
                                    if (!hadr) {
                                        const loc: Loc = if (!arow.loc.isNone()) context.loc_store.get(arow.loc.unwrap()) else Loc.init(unit.file_id, 0, 0);
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
                                if (t.kind(iid2) == .Load) {
                                    const lr = t.instrs.get(.Load, iid2);
                                    insertValueBool(gpa, &read_map, lr.ptr);
                                }
                            }
                        }
                        // Second pass: general uses (for params)
                        for (blocks) |bid| {
                            const b = t.funcs.Block.get(bid);
                            // Terminators
                            switch (t.kind(b.term)) {
                                .Return => {
                                    const r = t.terms.get(.Return, b.term);
                                    if (!r.value.isNone()) insertValueKey(gpa, &used2, r.value.unwrap());
                                },
                                .CondBr => {
                                    const c = t.terms.get(.CondBr, b.term);
                                    insertValueKey(gpa, &used2, c.cond);
                                },
                                .SwitchInt => {
                                    const s = t.terms.get(.SwitchInt, b.term);
                                    insertValueKey(gpa, &used2, s.scrut);
                                },
                                else => {},
                            }
                            // Instructions
                            const instrs = t.instrs.instr_pool.slice(b.instrs);
                            for (instrs) |iid3| {
                                switch (t.kind(iid3)) {
                                    .Gep => {
                                        const row = t.instrs.get(.Gep, iid3);
                                        insertValueKey(gpa, &used2, row.base);
                                        const idxs = t.instrs.gep_pool.slice(row.indices);
                                        for (idxs) |gid| switch (t.instrs.GepIndex.get(gid)) {
                                            .Const => {},
                                            .Value => |vv| insertValueKey(gpa, &used2, vv),
                                        };
                                    },
                                    .StructMake => {
                                        const row = t.instrs.get(.StructMake, iid3);
                                        const f = t.instrs.sfi_pool.slice(row.fields);
                                        for (f) |sfid| {
                                            const sf = t.instrs.StructFieldInit.get(sfid);
                                            insertValueKey(gpa, &used2, sf.value);
                                        }
                                    },
                                    .TupleMake => {
                                        const row = t.instrs.get(.TupleMake, iid3);
                                        for (t.instrs.value_pool.slice(row.elems)) |v| insertValueKey(gpa, &used2, v);
                                    },
                                    .ArrayMake => {
                                        const row = t.instrs.get(.ArrayMake, iid3);
                                        for (t.instrs.value_pool.slice(row.elems)) |v| insertValueKey(gpa, &used2, v);
                                    },
                                    .Select => {
                                        const row = t.instrs.get(.Select, iid3);
                                        insertValueKey(gpa, &used2, row.cond);
                                        insertValueKey(gpa, &used2, row.then_value);
                                        insertValueKey(gpa, &used2, row.else_value);
                                    },
                                    .Call => {
                                        const row = t.instrs.get(.Call, iid3);
                                        for (t.instrs.val_list_pool.slice(row.args)) |v| insertValueKey(gpa, &used2, v);
                                    },
                                    .IndirectCall => {
                                        const row = t.instrs.get(.IndirectCall, iid3);
                                        insertValueKey(gpa, &used2, row.callee);
                                        for (t.instrs.val_list_pool.slice(row.args)) |v| insertValueKey(gpa, &used2, v);
                                    },
                                    .MlirBlock => {
                                        const row = t.instrs.get(.MlirBlock, iid3);
                                        for (t.instrs.value_pool.slice(row.args)) |v| insertValueKey(gpa, &used2, v);
                                    },
                                    .Load => {
                                        const row = t.instrs.get(.Load, iid3);
                                        insertValueKey(gpa, &used2, row.ptr);
                                    },
                                    .Store => {
                                        const row = t.instrs.get(.Store, iid3);
                                        insertValueKey(gpa, &used2, row.ptr);
                                        insertValueKey(gpa, &used2, row.value);
                                    },
                                    .Index => {
                                        const row = t.instrs.get(.Index, iid3);
                                        insertValueKey(gpa, &used2, row.base);
                                        insertValueKey(gpa, &used2, row.index);
                                    },
                                    .AddressOf => {
                                        const row = t.instrs.get(.AddressOf, iid3);
                                        insertValueKey(gpa, &used2, row.value);
                                    },
                                    .ExtractElem => {
                                        const row = t.instrs.get(.ExtractElem, iid3);
                                        insertValueKey(gpa, &used2, row.agg);
                                    },
                                    .InsertElem => {
                                        const row = t.instrs.get(.InsertElem, iid3);
                                        insertValueKey(gpa, &used2, row.agg);
                                        insertValueKey(gpa, &used2, row.value);
                                    },
                                    .ExtractField => {
                                        const row = t.instrs.get(.ExtractField, iid3);
                                        insertValueKey(gpa, &used2, row.agg);
                                    },
                                    .InsertField => {
                                        const row = t.instrs.get(.InsertField, iid3);
                                        insertValueKey(gpa, &used2, row.agg);
                                        insertValueKey(gpa, &used2, row.value);
                                    },
                                    .VariantMake => {
                                        const row = t.instrs.get(.VariantMake, iid3);
                                        if (!row.payload.isNone()) insertValueKey(gpa, &used2, row.payload.unwrap());
                                    },
                                    .UnionField => {
                                        const row = t.instrs.get(.UnionField, iid3);
                                        insertValueKey(gpa, &used2, row.base);
                                    },
                                    .UnionFieldPtr => {
                                        const row = t.instrs.get(.UnionFieldPtr, iid3);
                                        insertValueKey(gpa, &used2, row.base);
                                    },
                                    .ComplexMake => {
                                        const row = t.instrs.get(.ComplexMake, iid3);
                                        insertValueKey(gpa, &used2, row.re);
                                        insertValueKey(gpa, &used2, row.im);
                                    },
                                    .RangeMake => {
                                        const row = t.instrs.get(.RangeMake, iid3);
                                        insertValueKey(gpa, &used2, row.start);
                                        insertValueKey(gpa, &used2, row.end);
                                        insertValueKey(gpa, &used2, row.inclusive);
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
                                        insertValueKey(gpa, &used2, row.value);
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
                                        insertValueKey(gpa, &used2, row.lhs);
                                        insertValueKey(gpa, &used2, row.rhs);
                                    },
                                    else => {},
                                }
                            }
                        }
                        // Param warnings
                        const params2 = t.funcs.param_pool.slice(frow.params);
                        for (params2) |pid2| {
                            const p2 = t.funcs.Param.get(pid2);
                            if (!containsValueKey(&used2, p2.value)) {
                                const pname_sid2: ?u32 = if (!p2.name.isNone()) p2.name.unwrap().toRaw() else null;
                                const ploc = paramNameLocFromAst(unit, frow.name.toRaw(), pname_sid2) orelse
                                    functionNameLocFromAst(unit, frow.name.toRaw()) orelse
                                    functionFirstLoc(context, t, frow, unit.file_id);
                                if (!isThirdPartyUnit(context, unit))
                                    _ = try context.diags.addWarning(ploc, .unused_param, .{});
                            }
                        }
                        // Simple unused local warning: alloca with no direct load
                        for (blocks) |bid3| {
                            const b3 = t.funcs.Block.get(bid3);
                            const instrs3 = t.instrs.instr_pool.slice(b3.instrs);
                            for (instrs3) |iid4| {
                                if (t.kind(iid4) == .Alloca) {
                                    const arow2 = t.instrs.get(.Alloca, iid4);
                                    const had_read = valueBool(&read_map, arow2.result);
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
                            if (fr2.name.eq(grow.name)) {
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

/// buildDefMap pruning helper.
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
            switch (t.kind(iid)) {
                .MlirBlock => {
                    const row = t.instrs.get(.MlirBlock, iid);
                    insertOptValueInstr(gpa, &defmap, row.result, iid);
                },
                else => {
                    // Most ops have a concrete result field
                    inline for (@typeInfo(tir.OpKind).@"enum".fields) |f| {
                        if (@field(tir.OpKind, f.name) == t.kind(iid)) {
                            const Row = tir.RowT(@field(tir.OpKind, f.name));
                            if (@hasField(Row, "result")) {
                                const row = t.instrs.get(@field(tir.OpKind, f.name), iid);
                                if (@TypeOf(row.result) == tir.ValueId) {
                                    insertValueInstr(gpa, &defmap, row.result, iid);
                                } else insertValueInstr(gpa, &defmap, row.result.unwrap(), iid);
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

/// computeReadAllocas pruning helper.
fn computeReadAllocas(
    gpa: std.mem.Allocator,
    t: *tir.TIR,
    frow: tir.FuncRows.Function,
    defmap: *std.AutoHashMapUnmanaged(u32, tir.InstrId),
) !std.AutoHashMapUnmanaged(u32, bool) {
    var read_allocas: std.AutoHashMapUnmanaged(u32, bool) = .{};
    var visited: std.AutoHashMapUnmanaged(u32, bool) = .{};
    defer visited.deinit(gpa);
    var queue = std.ArrayListUnmanaged(tir.ValueId){};
    defer queue.deinit(gpa);

    const blocks = t.funcs.block_pool.slice(frow.blocks);
    for (blocks) |bid| {
        const b = t.funcs.Block.get(bid);
        const instrs = t.instrs.instr_pool.slice(b.instrs);
        for (instrs) |iid| {
            switch (t.kind(iid)) {
                .Load => {
                    const lr = t.instrs.get(.Load, iid);
                    try queue.append(gpa, lr.ptr);
                },
                .Call => {
                    const cr = t.instrs.get(.Call, iid);
                    for (t.instrs.val_list_pool.slice(cr.args)) |v| try queue.append(gpa, v);
                },
                .IndirectCall => {
                    const icr = t.instrs.get(.IndirectCall, iid);
                    try queue.append(gpa, icr.callee);
                    for (t.instrs.val_list_pool.slice(icr.args)) |v| try queue.append(gpa, v);
                },
                else => {},
            }
        }
    }

    while (queue.pop()) |value| {
        if (valueBool(&visited, value)) continue;
        insertValueBool(gpa, &visited, value);
        if (lookupValueInstr(defmap, value)) |iid| {
            switch (t.kind(iid)) {
                .Alloca => {
                    const ar = t.instrs.get(.Alloca, iid);
                    insertValueBool(gpa, &read_allocas, ar.result);
                },
                .Gep => {
                    const gr = t.instrs.get(.Gep, iid);
                    try queue.append(gpa, gr.base);
                },
                .UnionFieldPtr => {
                    const ur = t.instrs.get(.UnionFieldPtr, iid);
                    try queue.append(gpa, ur.base);
                },
                .VariantPayloadPtr => {
                    const vr = t.instrs.get(.VariantPayloadPtr, iid);
                    try queue.append(gpa, vr.value);
                },
                .AddressOf => {
                    const ar = t.instrs.get(.AddressOf, iid);
                    try queue.append(gpa, ar.value);
                },
                else => {},
            }
        }
    }

    return read_allocas;
}

/// instrOptLoc pruning helper.
fn instrOptLoc(t: *tir.TIR, iid: tir.InstrId) tir.OptLocId {
    return switch (t.kind(iid)) {
        inline else => |kind| t.instrs.get(kind, iid).loc,
    };
}

/// functionFirstLoc pruning helper.
fn functionFirstLoc(context: *compile.Context, t: *tir.TIR, frow: tir.FuncRows.Function, file_id: u32) Loc {
    const blocks = t.funcs.block_pool.slice(frow.blocks);
    for (blocks) |bid| {
        const b = t.funcs.Block.get(bid);
        const instrs = t.instrs.instr_pool.slice(b.instrs);
        for (instrs) |iid| {
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

// =========================
// AST location utilities
// =========================

/// exprLocFromId pruning helper.
inline fn exprLocFromId(ast_unit: *ast.Ast, eid: ast.ExprId) Loc {
    return switch (ast_unit.kind(eid)) {
        inline else => |x| exprLoc(ast_unit, ast_unit.exprs.get(x, eid)),
    };
}
/// exprLoc pruning helper.
inline fn exprLoc(ast_unit: *ast.Ast, expr: anytype) Loc {
    return ast_unit.exprs.locs.get(expr.loc);
}

/// bindingNameOfPattern pruning helper.
fn bindingNameOfPattern(a: *ast.Ast, pid: ast.PatternId) ?ast.StrId {
    return switch (a.kind(pid)) {
        .Binding => a.pats.get(.Binding, pid).name,
        else => null,
    };
}

/// bindingLocOfPattern pruning helper.
fn bindingLocOfPattern(a: *ast.Ast, pid: ast.PatternId) ?Loc {
    return switch (a.kind(pid)) {
        .Binding => blk: {
            const b = a.pats.get(.Binding, pid);
            break :blk a.exprs.locs.get(b.loc);
        },
        else => null,
    };
}

/// findTopFuncDeclByName pruning helper.
fn findTopFuncDeclByName(a: *ast.Ast, name_sid_raw: u32) ?ast.DeclId {
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    for (decls) |did| {
        const d = a.exprs.Decl.get(did);
        // Only consider top-level named function declarations
        if (a.kind(d.value) != .FunctionLit) continue;
        if (!d.pattern.isNone()) {
            if (bindingNameOfPattern(a, d.pattern.unwrap())) |nm| {
                if (nm.eq(ast.StrId.fromRaw(name_sid_raw))) return did;
            }
        }
    }
    return null;
}

/// functionNameLocFromAst pruning helper.
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

/// paramNameLocFromAst pruning helper.
fn paramNameLocFromAst(unit: *package.FileUnit, func_name_sid_raw: u32, param_name_sid_raw: ?u32) ?Loc {
    const a = unit.ast orelse return null;
    const did_opt = findTopFuncDeclByName(a, func_name_sid_raw) orelse return null;
    const d = a.exprs.Decl.get(did_opt);
    if (a.kind(d.value) != .FunctionLit) return null;
    const fnr = a.exprs.get(.FunctionLit, d.value);
    const params = a.exprs.param_pool.slice(fnr.params);
    for (params) |pid| {
        const p = a.exprs.Param.get(pid);
        if (!p.pat.isNone() and param_name_sid_raw != null) {
            if (bindingNameOfPattern(a, p.pat.unwrap())) |nm| {
                if (nm.eq(ast.StrId.fromRaw(param_name_sid_raw.?))) {
                    // Prefer binding loc if available, else use whole param loc
                    if (bindingLocOfPattern(a, p.pat.unwrap())) |loc| return loc;
                    return a.exprs.locs.get(p.loc);
                }
            }
        }
    }
    return null;
}
