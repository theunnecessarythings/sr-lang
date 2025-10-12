const std = @import("std");
const testing = std.testing;
const compiler = @import("compiler");

const Lowered = struct {
    tir: compiler.tir.TIR,
    context: compiler.compile.Context,
};

fn expectedMangled(
    alloc: std.mem.Allocator,
    import_path: []const u8,
    field: []const u8,
) ![]u8 {
    var buf = std.ArrayList(u8).init(alloc);
    defer buf.deinit();

    try buf.appendSlice("m$");
    for (import_path) |c| {
        const keep = (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or (c >= '0' and c <= '9');
        try buf.append(if (keep) c else '_');
    }
    try buf.append('_');
    try buf.appendSlice(field);
    return try buf.toOwnedSlice();
}

fn lowerToTir(gpa: std.mem.Allocator, src: []const u8) !Lowered {
    var context = compiler.compile.Context.init(gpa); // Create context

    const src0 = try std.mem.concatWithSentinel(gpa, u8, &.{src}, 0);
    defer gpa.free(src0);
    var parser = compiler.parser.Parser.init(gpa, src0, 0, &context); // Pass file_id and context
    var cst = try parser.parse();
    defer cst.deinit();

    var lower1 = compiler.lower.Lower.init(gpa, &cst, &context); // Pass context
    var hir = try lower1.run();
    defer hir.deinit();

    var type_info = compiler.types.TypeInfo.init(gpa, &context.type_store);
    defer type_info.deinit();
    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context); // Create pipeline
    var chk = compiler.checker.Checker.init(gpa, &hir, &context, &pipeline, &type_info); // Pass context and pipeline
    defer chk.deinit();
    try chk.run();
    if (context.diags.anyErrors()) return error.SemanticErrors; // Use context.diags

    var lt = compiler.lower_tir.LowerTir.init(gpa, &context, &pipeline, &type_info);
    defer lt.deinit();
    const tir_result = try lt.run(&hir);
    return .{ .tir = tir_result, .context = context };
}

test "tir: if expression lowers to condBr + join" {
    const src =
        \\
        \\ f :: fn(x: bool) i32 {
        \\   y :: if x { 1 } else { 2 }
        \\   y
        \\ }
    ;
    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();
    const t = lowered.tir;
    var has_cond = false;
    var has_ret = false;
    const kinds = t.terms.index.kinds.items;
    var i: usize = 0;
    while (i < kinds.len) : (i += 1) {
        if (kinds[i] == .CondBr) has_cond = true;
        if (kinds[i] == .Return) has_ret = true;
    }
    try testing.expect(has_cond);
    try testing.expect(has_ret);
}

// test "tir: match on int emits SwitchInt" {
//     const src =
//         \\
//         \\ f :: fn(b: bool) i64 {
//         \\   return match b { true => { 1 }, false => { 2 }, }
//         \\ }
//     ;
//     var t = try lowerToTir(std.heap.page_allocator, src);
//     defer t.deinit();
//     const kinds = t.terms.index.kinds.items;
//     var has_switch = false;
//     var si: usize = 0;
//     while (si < kinds.len) : (si += 1) {
//         if (kinds[si] == .SwitchInt) {
//             has_switch = true;
//             break;
//         }
//     }
//     try testing.expect(has_switch);
// }

// test "tir: labeled while break carries value to join" {
//     const src =
//         \\
//         \\ f :: fn() i32 {
//         \\   res :: (L: while true { break :L 7 })
//         \\   return res
//         \\ }
//     ;
//     var lowered = try lowerToTir(std.heap.page_allocator, src);
//     defer lowered.tir.deinit();
//     defer lowered.context.deinit();
//     var t = lowered.tir;
//     // Should contain a Return with a value present
//     const kinds = t.terms.index.kinds.items;
//     var has_val_ret = false;
//     var idx: usize = 0;
//     while (idx < kinds.len) : (idx += 1) {
//         if (kinds[idx] == .Return) {
//             const row = t.terms.get(.Return, compiler.tir.TermId.fromRaw(@intCast(idx)));
//             if (!row.value.isNone()) {
//                 has_val_ret = true;
//                 break;
//             }
//         }
//     }
//     try testing.expect(has_val_ret);
// }
//
test "tir: direct call lowers with callee name" {
    const src =
        \\
        \\ add :: fn(a: i32, b: i32) i32 { a + b }
        \\ f :: fn() i32 { add(1, 2) }
    ;
    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();
    var t = lowered.tir;
    const ikinds = t.instrs.index.kinds.items;
    var found = false;
    var i: usize = 0;
    while (i < ikinds.len) : (i += 1) {
        if (ikinds[i] == .Call) {
            const row = t.instrs.get(.Call, compiler.tir.InstrId.fromRaw(@intCast(i)));
            const name = t.instrs.strs.get(row.callee);
            if (std.mem.eql(u8, name, "add")) {
                found = true;
                break;
            }
        }
    }
    try testing.expect(found);
}

test "tir: generic call monomorphizes with mangled callee" {
    const src =
        \\
        \\ max :: fn(comptime T: type, a: T, b: T) T {
        \\   return if a > b { a } else { b };
        \\ }
        \\ useMax :: fn(x: u64, y: u64) u64 {
        \\   return max(u64, x, y);
        \\ }
    ;

    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();
    var t = lowered.tir;

    const expected = "max_u64";

    var has_specialized_fn = false;
    const funcs = t.funcs.func_pool.data.items;
    for (funcs) |fid| {
        const frow = t.funcs.Function.get(fid);
        const fname = t.instrs.strs.get(frow.name);
        if (std.mem.eql(u8, fname, expected)) {
            has_specialized_fn = true;
            break;
        }
    }
    try testing.expect(has_specialized_fn);

    const ikinds = t.instrs.index.kinds.items;
    var saw_specialized_call = false;
    var i: usize = 0;
    while (i < ikinds.len) : (i += 1) {
        if (ikinds[i] != .Call) continue;
        const iid = compiler.tir.InstrId.fromRaw(@intCast(i));
        const call_row = t.instrs.get(.Call, iid);
        const callee_name = t.instrs.strs.get(call_row.callee);
        if (!std.mem.eql(u8, callee_name, expected)) continue;
        const args = t.instrs.val_list_pool.slice(call_row.args);
        try testing.expectEqual(@as(usize, 2), args.len);
        saw_specialized_call = true;
        break;
    }
    try testing.expect(saw_specialized_call);
}

test "tir: match bool fallback carries value to join" {
    const src =
        \\
        \\ f :: fn(b: bool) i64 {
        \\   return match b { true => { 1 }, false => { 2 }, }
        \\ }
    ;
    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();
    var t = lowered.tir;

    // Find the return block (should be the join) and assert it has one param
    const funcs = t.funcs.func_pool.data.items;
    try testing.expect(funcs.len >= 1);
    const f_id = funcs[0];
    const f = t.funcs.Function.get(f_id);
    const blocks = t.funcs.block_pool.slice(f.blocks);
    var join_bid: ?compiler.tir.BlockId = null;
    for (blocks) |bid| {
        const bb = t.funcs.Block.get(bid);
        const term = bb.term;
        if (t.terms.index.kinds.items[term.toRaw()] == .Return) {
            const row = t.terms.get(.Return, term);
            if (!row.value.isNone()) {
                join_bid = bid;
                break;
            }
        }
    }
    try testing.expect(join_bid != null);
    const join_bb = t.funcs.Block.get(join_bid.?);
    const params = t.funcs.param_pool.slice(join_bb.params);
    try testing.expectEqual(@as(usize, 1), params.len);

    // Verify all edges targeting the join carry exactly one argument
    var ok = true;
    for (blocks) |bid| {
        const bb = t.funcs.Block.get(bid);
        const term = bb.term;
        const k = t.terms.index.kinds.items[term.toRaw()];
        switch (k) {
            .Br => {
                const br = t.terms.get(.Br, term);
                const e = t.terms.Edge.get(br.edge);
                if (e.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(e.args);
                    if (args.len != 1) ok = false;
                }
            },
            .CondBr => {
                const cb = t.terms.get(.CondBr, term);
                const te = t.terms.Edge.get(cb.then_edge);
                const ee = t.terms.Edge.get(cb.else_edge);
                if (te.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(te.args);
                    if (args.len != 1) ok = false;
                }
                if (ee.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(ee.args);
                    if (args.len != 1) ok = false;
                }
            },
            .SwitchInt => {
                const sw = t.terms.get(.SwitchInt, term);
                const def = t.terms.Edge.get(sw.default_edge);
                if (def.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(def.args);
                    if (args.len != 1) ok = false;
                }
                const cases = t.terms.case_pool.slice(sw.cases);
                for (cases) |cid| {
                    const c = t.terms.Case.get(cid);
                    const e = t.terms.Edge.get(c.edge);
                    if (e.dest.toRaw() == join_bid.?.toRaw()) {
                        const args = t.instrs.value_pool.slice(e.args);
                        if (args.len != 1) ok = false;
                    }
                }
            },
            else => {},
        }
    }
    try testing.expect(ok);
}

test "tir: if expression carries value to join" {
    const src =
        \\
        \\ f :: fn(x: bool) i64 {
        \\   y :: if x { 1 } else { 2 }
        \\   return y
        \\ }
    ;
    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();
    var t = lowered.tir;

    // Find the return/join block
    const funcs = t.funcs.func_pool.data.items;
    const f_id = funcs[0];
    const f = t.funcs.Function.get(f_id);
    const blocks = t.funcs.block_pool.slice(f.blocks);
    var join_bid: ?compiler.tir.BlockId = null;
    for (blocks) |bid| {
        const bb = t.funcs.Block.get(bid);
        const term = bb.term;
        if (t.terms.index.kinds.items[term.toRaw()] == .Return) {
            const row = t.terms.get(.Return, term);
            if (!row.value.isNone()) {
                join_bid = bid;
                break;
            }
        }
    }
    try testing.expect(join_bid != null);
    const join_bb = t.funcs.Block.get(join_bid.?);
    const params = t.funcs.param_pool.slice(join_bb.params);
    try testing.expectEqual(@as(usize, 1), params.len);

    // Verify all incoming edges to join carry one arg
    var ok = true;
    for (blocks) |bid| {
        const bb = t.funcs.Block.get(bid);
        const term = bb.term;
        const k = t.terms.index.kinds.items[term.toRaw()];
        switch (k) {
            .Br => {
                const br = t.terms.get(.Br, term);
                const e = t.terms.Edge.get(br.edge);
                if (e.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(e.args);
                    if (args.len != 1) ok = false;
                }
            },
            .CondBr => {
                const cb = t.terms.get(.CondBr, term);
                const te = t.terms.Edge.get(cb.then_edge);
                const ee = t.terms.Edge.get(cb.else_edge);
                if (te.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(te.args);
                    if (args.len != 1) ok = false;
                }
                if (ee.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(ee.args);
                    if (args.len != 1) ok = false;
                }
            },
            else => {},
        }
    }
    try testing.expect(ok);
}

test "tir: match with guard carries value to join" {
    const src =
        \\
        \\ f :: fn(b: bool) i32 {
        \\   return match b { true if false => { 1 }, _ => { 2 }, }
        \\ }
    ;
    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();
    var t = lowered.tir;

    const funcs = t.funcs.func_pool.data.items;
    const f_id = funcs[0];
    const f = t.funcs.Function.get(f_id);
    const blocks = t.funcs.block_pool.slice(f.blocks);
    var join_bid: ?compiler.tir.BlockId = null;
    for (blocks) |bid| {
        const bb = t.funcs.Block.get(bid);
        const term = bb.term;
        if (t.terms.index.kinds.items[term.toRaw()] == .Return) {
            const row = t.terms.get(.Return, term);
            if (!row.value.isNone()) {
                join_bid = bid;
                break;
            }
        }
    }
    try testing.expect(join_bid != null);
    const join_bb = t.funcs.Block.get(join_bid.?);
    const params = t.funcs.param_pool.slice(join_bb.params);
    try testing.expectEqual(@as(usize, 1), params.len);

    var ok = true;
    for (blocks) |bid| {
        const bb = t.funcs.Block.get(bid);
        const term = bb.term;
        const k = t.terms.index.kinds.items[term.toRaw()];
        switch (k) {
            .Br => {
                const br = t.terms.get(.Br, term);
                const e = t.terms.Edge.get(br.edge);
                if (e.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(e.args);
                    if (args.len != 1) ok = false;
                }
            },
            .CondBr => {
                const cb = t.terms.get(.CondBr, term);
                const te = t.terms.Edge.get(cb.then_edge);
                const ee = t.terms.Edge.get(cb.else_edge);
                if (te.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(te.args);
                    if (args.len != 1) ok = false;
                }
                if (ee.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(ee.args);
                    if (args.len != 1) ok = false;
                }
            },
            .SwitchInt => {
                const sw = t.terms.get(.SwitchInt, term);
                const def = t.terms.Edge.get(sw.default_edge);
                if (def.dest.toRaw() == join_bid.?.toRaw()) {
                    const args = t.instrs.value_pool.slice(def.args);
                    if (args.len != 1) ok = false;
                }
                const cases = t.terms.case_pool.slice(sw.cases);
                for (cases) |cid| {
                    const c = t.terms.Case.get(cid);
                    const e = t.terms.Edge.get(c.edge);
                    if (e.dest.toRaw() == join_bid.?.toRaw()) {
                        const args = t.instrs.value_pool.slice(e.args);
                        if (args.len != 1) ok = false;
                    }
                }
            },
            else => {},
        }
    }
    try testing.expect(ok);
}

test "tir: imported call uses mangled prefix" {
    const gpa = std.testing.allocator;
    const import_dir = "zig-out/import_prefix_test";
    const main_path = "zig-out/import_prefix_test/main.sr";
    const import_path = "zig-out/import_prefix_test/math.sr";

    _ = std.fs.cwd().deleteTree(import_dir) catch {};
    try std.fs.cwd().makePath(import_dir);
    defer std.fs.cwd().deleteTree(import_dir) catch {};

    var dir = try std.fs.cwd().openDir(import_dir, .{ .access_sub_paths = true });
    defer dir.close();

    const math_src =
        \\
        \\answer :: fn() i32 { return 42 }
    ;
    const main_src =
        \\
        \\math :: import "zig-out/import_prefix_test/math.sr"
        \\call_math :: fn() i32 { return math.answer() }
    ;

    {
        var f = try dir.createFile("math.sr", .{ .truncate = true });
        defer f.close();
        try f.writeAll(math_src);
    }
    {
        var f = try dir.createFile("main.sr", .{ .truncate = true });
        defer f.close();
        try f.writeAll(main_src);
    }

    var context = compiler.compile.Context.init(gpa);
    defer context.deinit();

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);
    var result = try pipeline.runWithImports(main_path, &.{}, .tir);
    defer {
        if (result.tir) |*t| t.deinit();
        if (result.ast) |*a| a.deinit();
        if (result.cst) |*c| c.deinit();
        if (result.type_info) |ti| {
            ti.deinit();
            gpa.destroy(ti);
        }
    }

    const t = blk: {
        if (result.tir) |*ptr| break :blk ptr;
        unreachable;
    };

    const expected = try expectedMangled(gpa, import_path, "answer");
    defer gpa.free(expected);

    const kinds = t.instrs.index.kinds.items;
    var found = false;
    var i: usize = 0;
    while (i < kinds.len) : (i += 1) {
        if (kinds[i] == .Call) {
            const row = t.instrs.get(.Call, compiler.tir.InstrId.fromRaw(@intCast(i)));
            const callee = t.instrs.strs.get(row.callee);
            if (std.mem.eql(u8, callee, expected)) {
                found = true;
                break;
            }
        }
    }
    try testing.expect(found);
}

// test "tir: catch expression carries value to join" {
//     const src =
//         \\
//         \\ g :: fn() i32 ! error{ E } { 1 }
//         \\ f :: fn() i32 { g() catch { 2 } }
//     ;
//     var t = try lowerToTir(std.heap.page_allocator, src);
//     defer t.deinit();
//
//     const funcs = t.funcs.func_pool.data.items;
//     try testing.expect(funcs.len >= 2);
//     const f_id = funcs[1]; // second function is f
//     const f = t.funcs.Function.get(f_id.toRaw());
//     const blocks = t.funcs.block_pool.slice(f.blocks);
//     var join_bid: ?compiler.tir.BlockId = null;
//     for (blocks) |bid| {
//         const bb = t.funcs.Block.get(bid.toRaw());
//         const term = bb.term;
//         if (t.terms.index.kinds.items[term.toRaw()] == .Return) {
//             const row = t.terms.get(.Return, term);
//             if (!row.value.isNone()) { join_bid = bid; break; }
//         }
//     }
//     try testing.expect(join_bid != null);
//     const join_bb = t.funcs.Block.get(join_bid.?.toRaw());
//     const params = t.funcs.param_pool.slice(join_bb.params);
//     try testing.expectEqual(@as(usize, 1), params.len);
//
//     var ok = false;
//     for (blocks) |bid| {
//         const bb = t.funcs.Block.get(bid.toRaw());
//         const term = bb.term;
//         if (t.terms.index.kinds.items[term.toRaw()] == .Br) {
//             const br = t.terms.get(.Br, term);
//             const e = t.terms.Edge.get(br.edge.toRaw());
//             if (e.dest.toRaw() == join_bid.?.toRaw()) {
//                 const args = t.instrs.value_pool.slice(e.args);
//                 if (args.len == 1) ok = true;
//             }
//         }
//     }
//     try testing.expect(ok);
// }
