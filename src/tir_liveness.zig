const std = @import("std");
const tir = @import("tir.zig");

const Allocator = std.mem.Allocator;
const DynBitSet = std.bit_set.DynamicBitSet;

pub const Liveness = struct {};

const SuccEdge = struct { idx: usize, edge_args: []const tir.ValueId };
const BlockSets = struct { gen: DynBitSet, kill: DynBitSet, params: []bool };

/// Helper struct to encapsulate liveness analysis state and logic
const LivenessAnalyzer = struct {
    arena: std.heap.ArenaAllocator,
    alloc: Allocator,
    t: *tir.TIR,
    blocks: []const tir.BlockId,

    // Dense Mapping
    value_to_index: std.AutoHashMap(tir.ValueId, u32),
    index_to_value: std.array_list.Managed(tir.ValueId),

    // Analysis Data
    block_sets: []BlockSets,
    succ_map: []std.array_list.Managed(SuccEdge),
    live_in: []DynBitSet,
    live_out: []DynBitSet,

    fn init(gpa: Allocator, t: *tir.TIR, blocks: []const tir.BlockId) LivenessAnalyzer {
        var arena = std.heap.ArenaAllocator.init(gpa);
        return .{
            .arena = arena,
            .alloc = arena.allocator(),
            .t = t,
            .blocks = blocks,
            .value_to_index = std.AutoHashMap(tir.ValueId, u32).init(arena.allocator()),
            .index_to_value = std.array_list.Managed(tir.ValueId).init(arena.allocator()),
            .block_sets = &.{},
            .succ_map = &.{},
            .live_in = &.{},
            .live_out = &.{},
        };
    }

    fn deinit(self: *LivenessAnalyzer) void {
        self.arena.deinit();
    }

    fn buildValueMap(self: *LivenessAnalyzer) !void {
        var temp_vals = std.array_list.Managed(tir.ValueId).init(self.alloc);
        for (self.blocks) |bid| {
            const b = self.t.funcs.Block.get(bid);
            for (self.t.funcs.param_pool.slice(b.params)) |pid| {
                try temp_vals.append(self.t.funcs.Param.get(pid).value);
            }

            const instrs = self.t.instrs.instr_pool.slice(b.instrs);
            for (instrs) |iid| try scanInstrValues(self.t, iid, &temp_vals);

            // Terminators
            switch (self.t.kind(b.term)) {
                .Return => {
                    const r = self.t.terms.get(.Return, b.term);
                    if (!r.value.isNone()) try temp_vals.append(r.value.unwrap());
                },
                .CondBr => try temp_vals.append(self.t.terms.get(.CondBr, b.term).cond),
                .SwitchInt => try temp_vals.append(self.t.terms.get(.SwitchInt, b.term).scrut),
                else => {},
            }
        }

        for (temp_vals.items) |v| {
            if (!self.value_to_index.contains(v)) {
                try self.value_to_index.put(v, @intCast(self.index_to_value.items.len));
                try self.index_to_value.append(v);
            }
        }
    }

    fn computeGenKill(self: *LivenessAnalyzer) !void {
        const bit_len = self.index_to_value.items.len;
        self.block_sets = try self.alloc.alloc(BlockSets, self.blocks.len);

        var temp_vals = std.array_list.Managed(tir.ValueId).init(self.alloc);

        for (self.blocks, 0..) |bid, i| {
            const b = self.t.funcs.Block.get(bid);
            var gen = try DynBitSet.initEmpty(self.alloc, bit_len);
            var kill = try DynBitSet.initEmpty(self.alloc, bit_len);

            // 1. Block Params -> Kill
            const params = self.t.funcs.param_pool.slice(b.params);
            const live_params = try self.alloc.alloc(bool, params.len);
            @memset(live_params, false);

            for (params) |pid| {
                if (self.value_to_index.get(self.t.funcs.Param.get(pid).value)) |idx| kill.set(idx);
            }

            // 2. Instructions
            const instrs = self.t.instrs.instr_pool.slice(b.instrs);
            for (instrs) |iid| {
                temp_vals.clearRetainingCapacity();
                try scanInstrValues(self.t, iid, &temp_vals);

                // Identify Def
                var def_val: ?tir.ValueId = null;
                switch (self.t.kind(iid)) {
                    .MlirBlock => {
                        const r = self.t.instrs.get(.MlirBlock, iid);
                        if (!r.result.isNone()) def_val = r.result.unwrap();
                    },
                    inline else => |k| {
                        const r = self.t.instrs.get(k, iid);
                        if (@hasField(@TypeOf(r), "result")) {
                            if (@TypeOf(r.result) == tir.ValueId) def_val = r.result else if (!r.result.isNone()) def_val = r.result.unwrap();
                        }
                    },
                }

                // Process Uses (Gen if not Killed)
                for (temp_vals.items) |u| {
                    if (def_val) |d| if (u.eq(d)) continue;
                    if (self.value_to_index.get(u)) |idx| {
                        if (!kill.isSet(idx)) gen.set(idx);
                    }
                }

                // Process Def (Kill)
                if (def_val) |d| {
                    if (self.value_to_index.get(d)) |idx| kill.set(idx);
                }
            }

            // 3. Terminator Uses (Gen)
            temp_vals.clearRetainingCapacity();
            getTerminatorUses(self.t, b.term, &temp_vals) catch {};
            for (temp_vals.items) |u| {
                if (self.value_to_index.get(u)) |idx| if (!kill.isSet(idx)) gen.set(idx);
            }

            self.block_sets[i] = .{ .gen = gen, .kill = kill, .params = live_params };
        }
    }

    fn buildSuccessorMap(self: *LivenessAnalyzer) !void {
        self.succ_map = try self.alloc.alloc(std.array_list.Managed(SuccEdge), self.blocks.len);
        for (self.blocks, 0..) |bid, i| {
            self.succ_map[i] = std.array_list.Managed(SuccEdge).init(self.alloc);
            const b = self.t.funcs.Block.get(bid);
            try self.addTerminatorSuccs(b.term, &self.succ_map[i]);
        }
    }

    fn addTerminatorSuccs(self: *LivenessAnalyzer, term_id: tir.TermId, list: *std.array_list.Managed(SuccEdge)) !void {
        const add = struct {
            fn f(ctx: *LivenessAnalyzer, lst: *std.array_list.Managed(SuccEdge), tgt: tir.BlockId, edge: tir.EdgeId) !void {
                for (ctx.blocks, 0..) |bb, idx| {
                    if (bb.eq(tgt)) {
                        const e = ctx.t.terms.Edge.get(edge);
                        try lst.append(.{ .idx = idx, .edge_args = ctx.t.instrs.value_pool.slice(e.args) });
                        return;
                    }
                }
            }
        }.f;

        switch (self.t.kind(term_id)) {
            .Br => {
                const br = self.t.terms.get(.Br, term_id);
                try add(self, list, self.t.terms.Edge.get(br.edge).dest, br.edge);
            },
            .CondBr => {
                const c = self.t.terms.get(.CondBr, term_id);
                try add(self, list, self.t.terms.Edge.get(c.then_edge).dest, c.then_edge);
                try add(self, list, self.t.terms.Edge.get(c.else_edge).dest, c.else_edge);
            },
            .SwitchInt => {
                const sw = self.t.terms.get(.SwitchInt, term_id);
                for (self.t.terms.case_pool.slice(sw.cases)) |cid| {
                    const c = self.t.terms.Case.get(cid);
                    try add(self, list, self.t.terms.Edge.get(c.edge).dest, c.edge);
                }
                const de = self.t.terms.Edge.get(sw.default_edge);
                try add(self, list, de.dest, sw.default_edge);
            },
            else => {},
        }
    }

    fn solve(self: *LivenessAnalyzer) !void {
        const bit_len = self.index_to_value.items.len;
        self.live_in = try self.alloc.alloc(DynBitSet, self.blocks.len);
        self.live_out = try self.alloc.alloc(DynBitSet, self.blocks.len);

        for (0..self.blocks.len) |i| {
            self.live_in[i] = try DynBitSet.initEmpty(self.alloc, bit_len);
            self.live_out[i] = try DynBitSet.initEmpty(self.alloc, bit_len);
        }

        var changed = true;
        while (changed) {
            changed = false;
            var i = self.blocks.len;
            while (i > 0) {
                i -= 1;
                if (try self.updateBlock(i)) changed = true;
            }
        }
    }

    fn updateBlock(self: *LivenessAnalyzer, i: usize) !bool {
        var new_out = try DynBitSet.initEmpty(self.alloc, self.index_to_value.items.len);

        // 1. Calculate LiveOut = Union(LiveIn(Succs)) + Phi Logic
        for (self.succ_map[i].items) |succ| {
            new_out.setUnion(self.live_in[succ.idx]);

            // Handle Phi args: if succ param is live, our arg is live
            const succ_params = self.block_sets[succ.idx].params;
            if (succ.edge_args.len > 0) {
                const limit = @min(succ_params.len, succ.edge_args.len);
                // We must check if the param *value* is live in the successor
                const sb = self.t.funcs.Block.get(self.blocks[succ.idx]);
                const spids = self.t.funcs.param_pool.slice(sb.params);

                for (0..limit) |p_idx| {
                    const sp_val = self.t.funcs.Param.get(spids[p_idx]).value;
                    if (self.value_to_index.get(sp_val)) |sp_idx| {
                        if (self.live_in[succ.idx].isSet(sp_idx)) {
                            if (self.value_to_index.get(succ.edge_args[p_idx])) |arg_idx| {
                                new_out.set(arg_idx);
                            }
                        }
                    }
                }
            }
        }

        var changed = false;
        if (!new_out.eql(self.live_out[i])) {
            self.live_out[i] = new_out;
            changed = true;
        }

        // 2. Calculate LiveIn = Gen U (Out - Kill)
        var new_in = try self.live_out[i].clone(self.alloc);
        var kill_it = self.block_sets[i].kill.iterator(.{});
        while (kill_it.next()) |idx| new_in.unset(idx);
        new_in.setUnion(self.block_sets[i].gen);

        if (!new_in.eql(self.live_in[i])) {
            self.live_in[i] = new_in;
            changed = true;
        }
        return changed;
    }

    fn dumpResults(self: *LivenessAnalyzer, writer: anytype) !void {
        for (self.blocks, 0..) |bid, i| {
            try writer.print("  (block block_{})\n", .{bid.toRaw()});
            try self.printBitSet(writer, "live_in", &self.live_in[i]);

            // Print live params
            const b = self.t.funcs.Block.get(bid);
            const params = self.t.funcs.param_pool.slice(b.params);
            if (params.len > 0) {
                try writer.writeAll("    params_live_in: [");
                var first = true;
                for (params, 0..) |pid, pi| {
                    const pval = self.t.funcs.Param.get(pid).value;
                    if (self.value_to_index.get(pval)) |vidx| {
                        if (self.live_in[i].isSet(vidx)) {
                            if (!first) try writer.writeAll(", ");
                            try writer.print("p{}", .{pi});
                            first = false;
                        }
                    }
                }
                try writer.writeAll("]\n");
            }

            try self.printBitSet(writer, "live_out", &self.live_out[i]);
        }
    }

    fn printBitSet(self: *LivenessAnalyzer, writer: anytype, label: []const u8, bs: *const DynBitSet) !void {
        try writer.print("    {s}: [", .{label});
        var it = bs.iterator(.{});
        var first = true;
        while (it.next()) |idx| {
            if (!first) try writer.writeAll(", ");
            try writer.print("v{}", .{self.index_to_value.items[idx].toRaw()});
            first = false;
        }
        try writer.writeAll("]\n");
    }
};

// --- Top Level API ---

pub fn dump(gpa: Allocator, t: *tir.TIR) !void {
    var out_buf: [4096]u8 = undefined;
    var out = std.fs.File.stdout().writer(&out_buf);
    const writer = &out.interface;

    const funcs = t.funcs.func_pool.inner.data.items;
    for (funcs) |fid_raw| {
        const fid = tir.FuncId.fromRaw(fid_raw);
        const f = t.funcs.Function.get(fid);
        try writer.print("(function {s})\n", .{t.instrs.strs.get(f.name)});

        const blocks = t.funcs.block_pool.slice(f.blocks);
        if (blocks.len == 0) continue;

        var analyzer = LivenessAnalyzer.init(gpa, t, blocks);
        defer analyzer.deinit();

        try analyzer.buildValueMap();
        if (analyzer.index_to_value.items.len == 0) continue;

        try analyzer.computeGenKill();
        try analyzer.buildSuccessorMap();
        try analyzer.solve();
        try analyzer.dumpResults(writer);
    }
    try writer.flush();
}

// --- Helpers ---

fn getTerminatorUses(t: *tir.TIR, term_id: tir.TermId, list: *std.array_list.Managed(tir.ValueId)) !void {
    switch (t.kind(term_id)) {
        .Return => {
            const r = t.terms.get(.Return, term_id);
            if (!r.value.isNone()) try list.append(r.value.unwrap());
        },
        .CondBr => try list.append(t.terms.get(.CondBr, term_id).cond),
        .SwitchInt => try list.append(t.terms.get(.SwitchInt, term_id).scrut),
        else => {},
    }
}

fn scanInstrValues(t: *tir.TIR, iid: tir.InstrId, list: *std.array_list.Managed(tir.ValueId)) !void {
    @setEvalBranchQuota(10000);
    // Simplified generic scanner using compile-time reflection to avoid huge switches
    switch (t.kind(iid)) {
        .MlirBlock => {
            const row = t.instrs.get(.MlirBlock, iid);
            if (!row.result.isNone()) try list.append(row.result.unwrap());
            try list.appendSlice(t.instrs.value_pool.slice(row.args));
        },
        inline else => |kind| {
            const r = t.instrs.get(kind, iid);
            if (@hasField(@TypeOf(r), "result")) {
                if (@TypeOf(r.result) == tir.ValueId) try list.append(r.result) else if (!r.result.isNone()) try list.append(r.result.unwrap());
            }
            inline for (@typeInfo(@TypeOf(r)).@"struct".fields) |f| {
                if (comptime std.mem.eql(u8, f.name, "result")) continue;
                if (f.type == tir.ValueId) {
                    try list.append(@field(r, f.name));
                } else if (f.type == tir.OptValueId) {
                    if (!@field(r, f.name).isNone()) try list.append(@field(r, f.name).unwrap());
                } else if (f.type == tir.RangeValue) {
                    if (comptime std.mem.eql(u8, f.name, "args") and (kind == .Call or kind == .IndirectCall)) {
                        try list.appendSlice(t.instrs.val_list_pool.slice(@field(r, f.name)));
                    } else {
                        try list.appendSlice(t.instrs.value_pool.slice(@field(r, f.name)));
                    }
                } else if (f.type == tir.RangeGepIndex) {
                    for (t.instrs.gep_pool.slice(@field(r, f.name))) |gid| {
                        if (t.instrs.GepIndex.get(gid) == .Value) try list.append(t.instrs.GepIndex.get(gid).Value);
                    }
                } else if (f.type == tir.RangeStructFieldInit) {
                    for (t.instrs.sfi_pool.slice(@field(r, f.name))) |fid| try list.append(t.instrs.StructFieldInit.get(fid).value);
                }
            }
        },
    }
}
