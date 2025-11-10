const std = @import("std");
const tir = @import("tir.zig");

const Allocator = std.mem.Allocator;
const DynBitSet = std.bit_set.DynamicBitSet;

pub const Liveness = struct {
    // Per-function liveness dump only; not retained beyond dump() call.
    // This struct is a placeholder in case we want to expose results later.
};

const U32Set = std.AutoHashMapUnmanaged(u32, void);

fn setHas(set: *const U32Set, key: u32) bool {
    return set.get(key) != null;
}
fn setInsert(gpa: Allocator, set: *U32Set, key: u32) !bool {
    if (set.get(key) != null) return false;
    try set.put(gpa, key, {});
    return true;
}
fn setRemove(set: *U32Set, key: u32) void {
    _ = set.remove(key);
}
fn setClearRetainingCapacity(set: *U32Set) void {
    set.clearRetainingCapacity();
}
fn setClone(gpa: Allocator, src: *const U32Set) !U32Set {
    var dst: U32Set = .{};
    if (src.count() == 0) return dst;
    var it = src.iterator();
    while (it.next()) |e| try dst.put(gpa, e.key_ptr.*, {});
    return dst;
}
fn setEqual(a: *const U32Set, b: *const U32Set) bool {
    if (a.count() != b.count()) return false;
    var it = a.iterator();
    while (it.next()) |e| if (b.get(e.key_ptr.*) == null) return false;
    return true;
}
fn setSwap(a: *U32Set, b: *U32Set) void {
    std.mem.swap(U32Set, a, b);
}

const SuccEdge = struct { succ: tir.BlockId, edge: tir.EdgeId };

const UseCtx = struct {
    gpa: Allocator,
    t: *tir.TIR,
    set: *U32Set,
};

fn useAddVal(ctx: *UseCtx, v: tir.ValueId) !void {
    _ = try setInsert(ctx.gpa, ctx.set, v.toRaw());
}
fn useAddOptVal(ctx: *UseCtx, v: tir.OptValueId) !void {
    if (!v.isNone()) _ = try setInsert(ctx.gpa, ctx.set, v.unwrap().toRaw());
}
fn useAddRangeValues(ctx: *UseCtx, r: tir.RangeValue) !void {
    const vals = ctx.t.instrs.value_pool.slice(r);
    for (vals) |v| _ = try setInsert(ctx.gpa, ctx.set, v.toRaw());
}
fn useAddRangeValuesFromValList(ctx: *UseCtx, r: tir.RangeValue) !void {
    const vals = ctx.t.instrs.val_list_pool.slice(r);
    for (vals) |v| _ = try setInsert(ctx.gpa, ctx.set, v.toRaw());
}
fn useAddGepIndices(ctx: *UseCtx, r: tir.RangeGepIndex) !void {
    const idxs = ctx.t.instrs.gep_pool.slice(r);
    for (idxs) |gid| {
        const gi = ctx.t.instrs.GepIndex.get(gid);
        switch (gi) {
            .Const => {},
            .Value => |vv| _ = try setInsert(ctx.gpa, ctx.set, vv.toRaw()),
        }
    }
}
fn useAddStructFieldInits(ctx: *UseCtx, r: tir.RangeStructFieldInit) !void {
    const fields = ctx.t.instrs.sfi_pool.slice(r);
    for (fields) |fid| {
        const frow = ctx.t.instrs.StructFieldInit.get(fid);
        _ = try setInsert(ctx.gpa, ctx.set, frow.value.toRaw());
    }
}

fn collectInstrUses(ctx: *UseCtx, iid: tir.InstrId) !void {
    const k = ctx.t.instrs.index.kinds.items[iid.toRaw()];
    switch (k) {
        .Gep => {
            const row = ctx.t.instrs.get(.Gep, iid);
            try useAddVal(ctx, row.base);
            try useAddGepIndices(ctx, row.indices);
        },
        .StructMake => {
            const row = ctx.t.instrs.get(.StructMake, iid);
            try useAddStructFieldInits(ctx, row.fields);
        },
        .TupleMake => {
            const row = ctx.t.instrs.get(.TupleMake, iid);
            try useAddRangeValues(ctx, row.elems);
        },
        .ArrayMake => {
            const row = ctx.t.instrs.get(.ArrayMake, iid);
            try useAddRangeValues(ctx, row.elems);
        },
        .Select => {
            const row = ctx.t.instrs.get(.Select, iid);
            try useAddVal(ctx, row.cond);
            try useAddVal(ctx, row.then_value);
            try useAddVal(ctx, row.else_value);
        },
        .Call => {
            const row = ctx.t.instrs.get(.Call, iid);
            try useAddRangeValuesFromValList(ctx, row.args);
        },
        .IndirectCall => {
            const row = ctx.t.instrs.get(.IndirectCall, iid);
            try useAddVal(ctx, row.callee);
            try useAddRangeValuesFromValList(ctx, row.args);
        },
        .MlirBlock => {
            const row = ctx.t.instrs.get(.MlirBlock, iid);
            try useAddRangeValues(ctx, row.args);
        },
        .Alloca => {
            const row = ctx.t.instrs.get(.Alloca, iid);
            try useAddOptVal(ctx, row.count);
        },
        .Load => {
            const row = ctx.t.instrs.get(.Load, iid);
            try useAddVal(ctx, row.ptr);
        },
        .Store => {
            const row = ctx.t.instrs.get(.Store, iid);
            try useAddVal(ctx, row.ptr);
            try useAddVal(ctx, row.value);
        },
        .Index => {
            const row = ctx.t.instrs.get(.Index, iid);
            try useAddVal(ctx, row.base);
            try useAddVal(ctx, row.index);
        },
        .AddressOf => {
            const row = ctx.t.instrs.get(.AddressOf, iid);
            try useAddVal(ctx, row.value);
        },
        .ExtractElem => {
            const row = ctx.t.instrs.get(.ExtractElem, iid);
            try useAddVal(ctx, row.agg);
        },
        .InsertElem => {
            const row = ctx.t.instrs.get(.InsertElem, iid);
            try useAddVal(ctx, row.agg);
            try useAddVal(ctx, row.value);
        },
        .ExtractField => {
            const row = ctx.t.instrs.get(.ExtractField, iid);
            try useAddVal(ctx, row.agg);
        },
        .InsertField => {
            const row = ctx.t.instrs.get(.InsertField, iid);
            try useAddVal(ctx, row.agg);
            try useAddVal(ctx, row.value);
        },
        .VariantMake => {
            const row = ctx.t.instrs.get(.VariantMake, iid);
            try useAddOptVal(ctx, row.payload);
        },
        .UnionField => {
            const row = ctx.t.instrs.get(.UnionField, iid);
            try useAddVal(ctx, row.base);
        },
        .UnionFieldPtr => {
            const row = ctx.t.instrs.get(.UnionFieldPtr, iid);
            try useAddVal(ctx, row.base);
        },
        .ComplexMake => {
            const row = ctx.t.instrs.get(.ComplexMake, iid);
            try useAddVal(ctx, row.re);
            try useAddVal(ctx, row.im);
        },
        .RangeMake => {
            const row = ctx.t.instrs.get(.RangeMake, iid);
            try useAddVal(ctx, row.start);
            try useAddVal(ctx, row.end);
            try useAddVal(ctx, row.inclusive);
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
            const row = ctx.t.instrs.get(kind, iid);
            try useAddVal(ctx, row.value);
        },
        // Binary/logic/arithmetic/compare
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
            const row = ctx.t.instrs.get(kind, iid);
            try useAddVal(ctx, row.lhs);
            try useAddVal(ctx, row.rhs);
        },
        // Constants and addresses have no value uses
        .ConstInt, .ConstFloat, .ConstBool, .ConstString, .ConstNull, .ConstUndef, .GlobalAddr => {},
    }
}

fn removeInstrDef(t: *tir.TIR, k: tir.OpKind, iid: tir.InstrId, set: *U32Set) void {
    switch (k) {
        inline else => |kind| setRemove(set, t.instrs.get(kind, iid).result.toRaw()),
        .MlirBlock => {
            const row = t.instrs.get(.MlirBlock, iid);
            if (!row.result.isNone()) setRemove(set, row.result.unwrap().toRaw());
        },
    }
}

pub fn dump(allocator: Allocator, t: *tir.TIR) !void {
    var out_buf: [4096]u8 = undefined;
    var out = std.fs.File.stdout().writer(&out_buf);
    const writer = &out.interface;

    const funcs = t.funcs.func_pool.data.items;
    for (funcs) |fid| {
        const f = t.funcs.Function.get(fid);
        try writer.print("(function {s})\n", .{t.instrs.strs.get(f.name)});

        const blocks = t.funcs.block_pool.slice(f.blocks);

        // Build dense value-index mapping per function for compact bitsets
        var value_to_index = std.AutoHashMapUnmanaged(u32, u32){};
        defer value_to_index.deinit(allocator);
        var index_to_value = std.ArrayListUnmanaged(u32){};
        defer index_to_value.deinit(allocator);

        const ensureIndex = struct {
            fn go(gpa: Allocator, map: *std.AutoHashMapUnmanaged(u32, u32), rev: *std.ArrayListUnmanaged(u32), vraw: u32) !u32 {
                if (map.get(vraw)) |idx| return idx;
                const idx: u32 = @intCast(rev.items.len);
                try rev.append(gpa, vraw);
                try map.put(gpa, vraw, idx);
                return idx;
            }
        }.go;

        // Collect values from params, defs, uses and terminators/edges
        for (blocks) |bid| {
            const b = t.funcs.Block.get(bid);
            // params
            for (t.funcs.param_pool.slice(b.params)) |pid| {
                const v = t.funcs.Param.get(pid).value;
                _ = try ensureIndex(allocator, &value_to_index, &index_to_value, v.toRaw());
            }
            // instr defs and uses
            const instrs = t.instrs.instr_pool.slice(b.instrs);
            for (instrs) |iid| {
                const k = t.instrs.index.kinds.items[iid.toRaw()];
                // defs
                switch (k) {
                    .MlirBlock => {
                        const row = t.instrs.get(.MlirBlock, iid);
                        if (!row.result.isNone()) _ = try ensureIndex(allocator, &value_to_index, &index_to_value, row.result.unwrap().toRaw());
                    },
                    inline else => |kind| {
                        const r = t.instrs.get(kind, iid);
                        if (@hasField(@TypeOf(r), "result")) {
                            _ = try ensureIndex(allocator, &value_to_index, &index_to_value, r.result.toRaw());
                        }
                    },
                }
                // uses via temp set
                var tmp: U32Set = .{};
                defer tmp.deinit(allocator);
                var uctx = UseCtx{ .gpa = allocator, .t = t, .set = &tmp };
                try collectInstrUses(&uctx, iid);
                var it = tmp.iterator();
                while (it.next()) |e| _ = try ensureIndex(allocator, &value_to_index, &index_to_value, e.key_ptr.*);
            }
            // terminator uses
            const term_k = t.terms.index.kinds.items[b.term.toRaw()];
            switch (term_k) {
                .Return => {
                    const r = t.terms.get(.Return, b.term);
                    if (!r.value.isNone()) _ = try ensureIndex(allocator, &value_to_index, &index_to_value, r.value.unwrap().toRaw());
                },
                .CondBr => {
                    const c = t.terms.get(.CondBr, b.term);
                    _ = try ensureIndex(allocator, &value_to_index, &index_to_value, c.cond.toRaw());
                },
                .SwitchInt => {
                    const s = t.terms.get(.SwitchInt, b.term);
                    _ = try ensureIndex(allocator, &value_to_index, &index_to_value, s.scrut.toRaw());
                },
                .Br, .Unreachable => {},
            }
        }

        const bit_len: usize = index_to_value.items.len;

        // Per-block bitsets
        var live_in_bits = try allocator.alloc(DynBitSet, blocks.len);
        defer {
            for (live_in_bits) |*b| b.deinit();
            allocator.free(live_in_bits);
        }
        var live_out_bits = try allocator.alloc(DynBitSet, blocks.len);
        defer {
            for (live_out_bits) |*b| b.deinit();
            allocator.free(live_out_bits);
        }
        var live_param_bits = try allocator.alloc([]bool, blocks.len);
        defer {
            for (live_param_bits) |arr| allocator.free(arr);
            allocator.free(live_param_bits);
        }

        var succs = try allocator.alloc([]SuccEdge, blocks.len);
        defer {
            for (succs) |arr| allocator.free(arr);
            allocator.free(succs);
        }

        // Initialize containers per block
        for (blocks, 0..) |bid, i| {
            live_in_bits[i] = try DynBitSet.initEmpty(allocator, bit_len);
            live_out_bits[i] = try DynBitSet.initEmpty(allocator, bit_len);
            // allocate param bits
            const b = t.funcs.Block.get(bid);
            const params = t.funcs.param_pool.slice(b.params);
            live_param_bits[i] = try allocator.alloc(bool, params.len);
            @memset(live_param_bits[i], false);

            // gather successors (conservative union for multi-succ terms)
            var list = std.ArrayList(SuccEdge){};
            defer list.deinit(allocator);
            const term_kind = t.terms.index.kinds.items[b.term.toRaw()];
            switch (term_kind) {
                .Return => {},
                .Unreachable => {},
                .Br => {
                    const br = t.terms.get(.Br, b.term);
                    const e = t.terms.Edge.get(br.edge);
                    try list.append(allocator, .{ .succ = e.dest, .edge = br.edge });
                },
                .CondBr => {
                    const c = t.terms.get(.CondBr, b.term);
                    const e_then = t.terms.Edge.get(c.then_edge);
                    const e_else = t.terms.Edge.get(c.else_edge);
                    try list.append(allocator, .{ .succ = e_then.dest, .edge = c.then_edge });
                    try list.append(allocator, .{ .succ = e_else.dest, .edge = c.else_edge });
                },
                .SwitchInt => {
                    const sw = t.terms.get(.SwitchInt, b.term);
                    const cases = t.terms.case_pool.slice(sw.cases);
                    for (cases) |cid| {
                        const c = t.terms.Case.get(cid);
                        const e = t.terms.Edge.get(c.edge);
                        try list.append(allocator, .{ .succ = e.dest, .edge = c.edge });
                    }
                    const def_e = t.terms.Edge.get(sw.default_edge);
                    try list.append(allocator, .{ .succ = def_e.dest, .edge = sw.default_edge });
                },
            }
            succs[i] = try list.toOwnedSlice(allocator);
        }

        // Helpers defined at top-level: UseCtx, collectInstrUses, removeInstrDef

        // Dataflow iteration
        var changed = true;
        while (changed) {
            changed = false;
            // Recompute live_out from successors
            for (blocks, 0..) |_, i| {
                var new_out = try DynBitSet.initEmpty(allocator, bit_len);
                const su = succs[i];
                for (su) |se| {
                    // Map successor's live params to our edge args
                    const sb = t.funcs.Block.get(se.succ);
                    const sparams = t.funcs.param_pool.slice(sb.params);
                    const e = t.terms.Edge.get(se.edge);
                    const eargs = t.instrs.value_pool.slice(e.args);
                    const s_idx = indexOfBlock(blocks, se.succ);
                    if (s_idx) |si| {
                        const livep = live_param_bits[si];
                        const limit = @min(livep.len, eargs.len);
                        var p: usize = 0;
                        while (p < limit) : (p += 1) {
                            if (livep[p]) {
                                if (value_to_index.get(eargs[p].toRaw())) |ix| new_out.set(ix);
                            }
                        }
                        _ = sparams; // silence unused in release
                    }
                }
                // Compare and swap if changed
                var equal = true;
                var bi: usize = 0;
                while (bi < bit_len) : (bi += 1) {
                    if (new_out.isSet(bi) != live_out_bits[i].isSet(bi)) { equal = false; break; }
                }
                if (!equal) {
                    live_out_bits[i].deinit();
                    live_out_bits[i] = new_out;
                    changed = true;
                } else new_out.deinit();
            }

            // Recompute live_in per block by scanning backward
            for (blocks, 0..) |bid, i| {
                // Start from live_out
                var live = try live_out_bits[i].clone(allocator);

                // Terminator uses inside block
                const b = t.funcs.Block.get(bid);
                const term_k = t.terms.index.kinds.items[b.term.toRaw()];
                switch (term_k) {
                    .Return => {
                        const r = t.terms.get(.Return, b.term);
                        if (!r.value.isNone()) if (value_to_index.get(r.value.unwrap().toRaw())) |ix| live.set(ix);
                    },
                    .Br => {
                        // no direct value uses; edge args handled via live_out mapping
                    },
                    .CondBr => {
                        const c = t.terms.get(.CondBr, b.term);
                        if (value_to_index.get(c.cond.toRaw())) |ix| live.set(ix);
                    },
                    .SwitchInt => {
                        const s = t.terms.get(.SwitchInt, b.term);
                        if (value_to_index.get(s.scrut.toRaw())) |ix| live.set(ix);
                    },
                    .Unreachable => {},
                }

                // Instructions backward
                const instrs = t.instrs.instr_pool.slice(b.instrs);
                var tmp_uses: U32Set = .{};
                defer tmp_uses.deinit(allocator);
                var use_ctx = UseCtx{ .gpa = allocator, .t = t, .set = &tmp_uses };
                var j: isize = @intCast(instrs.len);
                while (j > 0) {
                    j -= 1;
                    const iid = instrs[@intCast(j)];
                    const k = t.instrs.index.kinds.items[iid.toRaw()];
                    try collectInstrUses(&use_ctx, iid);
                    // set uses
                    var it2 = tmp_uses.iterator();
                    while (it2.next()) |e| if (value_to_index.get(e.key_ptr.*)) |ix| live.set(ix);
                    tmp_uses.clearRetainingCapacity();
                    // remove def
                    switch (k) {
                        .MlirBlock => {
                            const row = t.instrs.get(.MlirBlock, iid);
                            if (!row.result.isNone()) if (value_to_index.get(row.result.unwrap().toRaw())) |ix| live.unset(ix);
                        },
                        inline else => |kind| {
                            const r = t.instrs.get(kind, iid);
                            if (@hasField(@TypeOf(r), "result")) if (value_to_index.get(r.result.toRaw())) |ix| live.unset(ix);
                        },
                    }
                }

                // Partition: block params are defs at entry
                const params = t.funcs.param_pool.slice(b.params);
                var livep_changed = false;
                var pidx: usize = 0;
                while (pidx < params.len) : (pidx += 1) {
                    const pid = params[pidx];
                    const pval = t.funcs.Param.get(pid).value.toRaw();
                    const is_live = if (value_to_index.get(pval)) |ix| live.isSet(ix) else false;
                    if (is_live != live_param_bits[i][pidx]) {
                        live_param_bits[i][pidx] = is_live;
                        livep_changed = true;
                    }
                    if (is_live) if (value_to_index.get(pval)) |ix| live.unset(ix);
                }

                // Compare and swap live_in
                var equal_in = true;
                var bi: usize = 0;
                while (bi < bit_len) : (bi += 1) {
                    if (live.isSet(bi) != live_in_bits[i].isSet(bi)) { equal_in = false; break; }
                }
                if (!equal_in) {
                    live_in_bits[i].deinit();
                    live_in_bits[i] = live;
                    changed = true;
                } else live.deinit();
                if (livep_changed) changed = true;
            }
        }

        // Dump per block
        for (blocks, 0..) |bid, i| {
            try writer.print("  (block block_{})\n", .{bid.toRaw()});
            // live_in values
            try writer.writeAll("    live_in: [");
            var first = true;
            var vi: usize = 0;
            while (vi < bit_len) : (vi += 1) {
                if (live_in_bits[i].isSet(vi)) {
                    if (!first) try writer.writeAll(", ");
                    first = false;
                    try writer.print("v{}", .{index_to_value.items[vi]});
                }
            }
            try writer.writeAll("]\n");

            // live_in params
            if (live_param_bits[i].len > 0) {
                try writer.writeAll("    params_live_in: [");
                var pf = true;
                for (live_param_bits[i], 0..) |b_live, pi| {
                    if (b_live) {
                        if (!pf) try writer.writeAll(", ");
                        pf = false;
                        try writer.print("p{}", .{pi});
                    }
                }
                try writer.writeAll("]\n");
            }

            // live_out values
            try writer.writeAll("    live_out: [");
            first = true;
            vi = 0;
            while (vi < bit_len) : (vi += 1) {
                if (live_out_bits[i].isSet(vi)) {
                    if (!first) try writer.writeAll(", ");
                    first = false;
                    try writer.print("v{}", .{index_to_value.items[vi]});
                }
            }
            try writer.writeAll("]\n");
        }
    }
    try writer.flush();
}

fn indexOfBlock(blocks: []const tir.BlockId, bid: tir.BlockId) ?usize {
    for (blocks, 0..) |b, i| if (b.toRaw() == bid.toRaw()) return i;
    return null;
}
