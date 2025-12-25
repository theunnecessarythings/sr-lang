const std = @import("std");
const testing = std.testing;
const compiler = @import("compiler");
const types = compiler.types;
const diag = compiler.diagnostics;

const Lowered = struct {
    tir: compiler.tir.TIR,
    context: compiler.compile.Context,
};

fn expectedMangled(
    context: *compiler.compile.Context,
    alloc: std.mem.Allocator,
    import_path: []const u8,
    field: []const u8,
) ![]u8 {
    const ns_info = try context.module_graph.namespaceForImport(alloc, import_path);
    defer alloc.free(ns_info.namespace);
    return try std.fmt.allocPrint(alloc, "{s}_{s}", .{ ns_info.namespace, field });
}

fn lowerToTir(gpa: std.mem.Allocator, src: []const u8) !Lowered {
    var context = compiler.compile.Context.init(gpa); // Create context

    const src0 = try std.mem.concatWithSentinel(gpa, u8, &.{src}, 0);
    defer gpa.free(src0);
    var parser = compiler.parser.Parser.init(gpa, src0, 0, &context); // Pass file_id and context
    var cst = try parser.parse();
    defer cst.deinit();

    var lower1 = try compiler.lower_to_ast.Lower.init(gpa, &cst, &context, 0); // Pass context
    defer lower1.deinit();
    const result = try lower1.run();
    defer result.deinit();
    const hir = result.ast_unit;

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context); // Create pipeline
    var chk = compiler.checker.Checker.init(gpa, &context, &pipeline); // Pass context and pipeline
    defer chk.deinit();
    try chk.runAst(hir);
    if (context.diags.anyErrors()) return error.SemanticErrors; // Use context.diags

    var lt = compiler.lower_tir.LowerTir.init(gpa, &context, &pipeline, &chk);
    defer lt.deinit();
    const tir_result = try lt.runAst(hir);
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
        \\ useMax :: fn(x: i32, y: i32) i32 {
        \\   return max(i32, x, y);
        \\ }
        \\ cap :: fn(comptime T: type, comptime Limit: T, value: T) T {
        \\   return if (value > Limit) Limit else value;
        \\ }
        \\ useCap :: fn(value: i32) i32 {
        \\   return cap(i32, 42, value);
        \\ }
    ;

    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();
    var t = lowered.tir;

    const expected = "max_i32";

    var has_specialized_fn = false;
    var has_generic_max = false;
    var max_fn_result_ty: ?types.TypeId = null;
    var max_param_tys: [2]?types.TypeId = .{ null, null };
    var cap_const_found = false;
    const type_store = &lowered.context.type_store;
    const funcs = t.funcs.func_pool.data.items;
    for (funcs) |fid| {
        const frow = t.funcs.Function.get(fid);
        const fname = t.instrs.strs.get(frow.name);
        if (std.mem.eql(u8, fname, "max")) {
            has_generic_max = true;
        }
        if (std.mem.eql(u8, fname, expected)) {
            has_specialized_fn = true;
            max_fn_result_ty = frow.result;
            const params = t.funcs.param_pool.slice(frow.params);
            if (params.len == 2) {
                max_param_tys[0] = t.funcs.Param.get(params[0]).ty;
                max_param_tys[1] = t.funcs.Param.get(params[1]).ty;
            }
        }
        if (std.mem.startsWith(u8, fname, "cap_i32")) {
            const blocks = t.funcs.block_pool.slice(frow.blocks);
            for (blocks) |bid| {
                const block_row = t.funcs.Block.get(bid);
                const instrs = t.instrs.instr_pool.slice(block_row.instrs);
                for (instrs) |iid| {
                    const kind = t.instrs.index.kinds.items[iid.toRaw()];
                    if (kind == .ConstInt) {
                        const row_ci = t.instrs.get(.ConstInt, iid);
                        if (row_ci.value == 42 and row_ci.ty.toRaw() == type_store.tI32().toRaw()) {
                            cap_const_found = true;
                            break;
                        }
                    }
                }
                if (cap_const_found) break;
            }
        }
    }
    try testing.expect(has_specialized_fn);
    try testing.expect(!has_generic_max);
    try testing.expectEqual(type_store.tI32().toRaw(), (max_fn_result_ty orelse type_store.tAny()).toRaw());
    try testing.expectEqual(type_store.tI32().toRaw(), (max_param_tys[0] orelse type_store.tAny()).toRaw());
    try testing.expectEqual(type_store.tI32().toRaw(), (max_param_tys[1] orelse type_store.tAny()).toRaw());
    try testing.expect(cap_const_found);

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

test "tir: any parameters specialize to argument types" {
    const src =
        \\
        \\ max_any :: fn(a: any, b: any) any {
        \\   return if a > b { a } else { b };
        \\ }
        \\ useInt :: fn(x: i32, y: i32) i32 {
        \\   return max_any(x, y);
        \\ }
        \\ useFloat :: fn(x: f64, y: f64) f64 {
        \\   return max_any(x, y);
        \\ }
    ;

    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();

    const t = lowered.tir;
    const type_store = &lowered.context.type_store;

    const expected_i32 = "max_any_i32_i32";
    const expected_f64 = "max_any_f64_f64";

    var found_i32 = false;
    var found_f64 = false;

    const funcs = t.funcs.func_pool.data.items;
    for (funcs) |fid| {
        const frow = t.funcs.Function.get(fid);
        const fname = t.instrs.strs.get(frow.name);
        if (std.mem.eql(u8, fname, expected_i32)) {
            found_i32 = true;
            try testing.expectEqual(type_store.tI32().toRaw(), frow.result.toRaw());
            const params = t.funcs.param_pool.slice(frow.params);
            try testing.expectEqual(@as(usize, 2), params.len);
            try testing.expectEqual(type_store.tI32().toRaw(), t.funcs.Param.get(params[0]).ty.toRaw());
            try testing.expectEqual(type_store.tI32().toRaw(), t.funcs.Param.get(params[1]).ty.toRaw());
        } else if (std.mem.eql(u8, fname, expected_f64)) {
            found_f64 = true;
            try testing.expectEqual(type_store.tF64().toRaw(), frow.result.toRaw());
            const params = t.funcs.param_pool.slice(frow.params);
            try testing.expectEqual(@as(usize, 2), params.len);
            try testing.expectEqual(type_store.tF64().toRaw(), t.funcs.Param.get(params[0]).ty.toRaw());
            try testing.expectEqual(type_store.tF64().toRaw(), t.funcs.Param.get(params[1]).ty.toRaw());
        }
    }

    try testing.expect(found_i32);
    try testing.expect(found_f64);

    const call_kinds = t.instrs.index.kinds.items;
    var call_i32 = false;
    var call_f64 = false;
    var call_generic = false;
    var i: usize = 0;
    while (i < call_kinds.len) : (i += 1) {
        if (call_kinds[i] != .Call) continue;
        const row = t.instrs.get(.Call, compiler.tir.InstrId.fromRaw(@intCast(i)));
        const callee = t.instrs.strs.get(row.callee);
        if (std.mem.eql(u8, callee, expected_i32)) call_i32 = true;
        if (std.mem.eql(u8, callee, expected_f64)) call_f64 = true;
        if (std.mem.eql(u8, callee, "max_any")) call_generic = true;
    }

    try testing.expect(call_i32);
    try testing.expect(call_f64);
    try testing.expect(!call_generic);
}

test "tir: type-returning generic yields concrete struct" {
    const src =
        \\
        \\ Test :: fn(comptime T: type) type {
        \\   return struct { a: T, b: usize };
        \\ }
        \\ TestI64 :: Test(i64)
        \\ make :: fn() TestI64 {
        \\   return TestI64{ .a = 42, .b = 7 };
        \\ }
    ;

    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();

    const t = lowered.tir;
    const type_store = &lowered.context.type_store;

    var make_result: ?types.TypeId = null;
    const funcs = t.funcs.func_pool.data.items;
    for (funcs) |fid| {
        const frow = t.funcs.Function.get(fid);
        const fname = t.instrs.strs.get(frow.name);
        if (std.mem.eql(u8, fname, "make")) {
            make_result = frow.result;
            break;
        }
    }

    try testing.expect(make_result != null);
    const struct_ty = make_result.?;
    try testing.expectEqual(.Struct, type_store.getKind(struct_ty));
    const st = type_store.get(.Struct, struct_ty);
    const fields = type_store.field_pool.slice(st.fields);
    try testing.expectEqual(@as(usize, 2), fields.len);
    const name_a = type_store.strs.get(fields[0].name);
    const name_b = type_store.strs.get(fields[1].name);
    try testing.expect(std.mem.eql(u8, name_a, "a"));
    try testing.expect(std.mem.eql(u8, name_b, "b"));
    try testing.expectEqual(type_store.tI64().toRaw(), fields[0].ty.toRaw());
    try testing.expectEqual(type_store.tUsize().toRaw(), fields[1].ty.toRaw());
}

test "tir: nested generic type propagates specialization" {
    const src =
        \\
        \\ Vec :: fn(comptime T: type, comptime N: usize) type {
        \\   return struct { data: [N]T };
        \\ }
        \\ Matrix :: fn(comptime T: type, comptime R: usize, comptime C: usize) type {
        \\   Row :: Vec(T, C)
        \\   return struct { rows: [R]Row };
        \\ }
        \\ MatrixI32x2x3 :: Matrix(i32, 2, 3)
        \\ make :: fn() MatrixI32x2x3 {
        \\   return MatrixI32x2x3{
        \\     .rows = [
        \\       Vec(i32, 3){ .data = [1, 2, 3] },
        \\       Vec(i32, 3){ .data = [4, 5, 6] },
        \\     ],
        \\   };
        \\ }
    ;

    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();

    const type_store = &lowered.context.type_store;
    const funcs = lowered.tir.funcs.func_pool.data.items;

    var matrix_ty: ?types.TypeId = null;
    for (funcs) |fid| {
        const frow = lowered.tir.funcs.Function.get(fid);
        const fname = lowered.tir.instrs.strs.get(frow.name);
        if (std.mem.eql(u8, fname, "make")) {
            matrix_ty = frow.result;
            break;
        }
    }

    try testing.expect(matrix_ty != null);
    const struct_ty = matrix_ty.?;
    try testing.expectEqual(.Struct, type_store.getKind(struct_ty));
    const matrix_struct = type_store.get(.Struct, struct_ty);
    const matrix_fields = type_store.field_pool.slice(matrix_struct.fields);
    try testing.expectEqual(@as(usize, 1), matrix_fields.len);

    const rows_field = matrix_fields[0];
    try testing.expect(std.mem.eql(u8, type_store.strs.get(rows_field.name), "rows"));
    try testing.expectEqual(.Array, type_store.getKind(rows_field.ty));

    const rows_array = type_store.get(.Array, rows_field.ty);
    try testing.expectEqual(@as(usize, 2), rows_array.len);

    const row_ty = rows_array.elem;
    try testing.expectEqual(.Struct, type_store.getKind(row_ty));
    const row_struct = type_store.get(.Struct, row_ty);
    const row_fields = type_store.field_pool.slice(row_struct.fields);
    try testing.expectEqual(@as(usize, 1), row_fields.len);

    const data_field = row_fields[0];
    try testing.expect(std.mem.eql(u8, type_store.strs.get(data_field.name), "data"));
    try testing.expectEqual(.Array, type_store.getKind(data_field.ty));

    const data_array = type_store.get(.Array, data_field.ty);
    try testing.expectEqual(@as(usize, 3), data_array.len);
    try testing.expectEqual(type_store.tI32().toRaw(), data_array.elem.toRaw());
}

test "tir: recursive generic produces self-referential pointer" {
    const src =
        \\
        \\ List :: fn(comptime T: type) type {
        \\   Type :: struct {
        \\     value: T,
        \\     next: ?*Type,
        \\   }
        \\   return Type;
        \\ }
        \\ use :: fn() List(i32) {
        \\   return List(i32){ .value = 1, .next = null };
        \\ }
    ;

    var lowered = try lowerToTir(std.heap.page_allocator, src);
    defer lowered.tir.deinit();
    defer lowered.context.deinit();

    const type_store = &lowered.context.type_store;
    const funcs = lowered.tir.funcs.func_pool.data.items;

    var list_ty: ?types.TypeId = null;
    for (funcs) |fid| {
        const frow = lowered.tir.funcs.Function.get(fid);
        const fname = lowered.tir.instrs.strs.get(frow.name);
        if (std.mem.eql(u8, fname, "use")) {
            list_ty = frow.result;
            break;
        }
    }

    try testing.expect(list_ty != null);
    const struct_ty = list_ty.?;
    try testing.expectEqual(.Struct, type_store.getKind(struct_ty));

    const list_struct = type_store.get(.Struct, struct_ty);
    const fields = type_store.field_pool.slice(list_struct.fields);
    try testing.expectEqual(@as(usize, 2), fields.len);

    const value_field = fields[0];
    try testing.expect(std.mem.eql(u8, type_store.strs.get(value_field.name), "value"));
    try testing.expectEqual(type_store.tI32().toRaw(), value_field.ty.toRaw());

    const next_field = fields[1];
    try testing.expect(std.mem.eql(u8, type_store.strs.get(next_field.name), "next"));
    try testing.expectEqual(.Optional, type_store.getKind(next_field.ty));

    const opt_ty = type_store.get(.Optional, next_field.ty).elem;
    try testing.expectEqual(.Ptr, type_store.getKind(opt_ty));

    const ptr_info = type_store.get(.Ptr, opt_ty);
    try testing.expect(!ptr_info.is_const);
    try testing.expectEqual(struct_ty.toRaw(), ptr_info.elem.toRaw());
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
    const import_dir = "out/import_prefix_test";
    const main_path = "out/import_prefix_test/main.sr";
    const import_path = "out/import_prefix_test/math.sr";

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
        \\math :: import "out/import_prefix_test/math.sr"
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

    const expected = try expectedMangled(&context, gpa, import_path, "answer");
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

test "tir: runtime any specialization rejects mismatched numeric operands" {
    const gpa = std.heap.page_allocator;
    const src =
        \\ add :: fn(a: any, b: any) any {
        \\     return a + b
        \\ }
        \\ main :: fn() i32 {
        \\     _ = add(1, 2.5)
        \\     return 0
        \\ }
    ;

    var context = compiler.compile.Context.init(gpa);
    defer context.deinit();

    const src0 = try std.mem.concatWithSentinel(gpa, u8, &.{src}, 0);
    defer gpa.free(src0);

    var parser = compiler.parser.Parser.init(gpa, src0, 0, &context);
    var cst = try parser.parse();
    defer cst.deinit();

    var lower1 = try compiler.lower_to_ast.Lower.init(gpa, &cst, &context, 0);
    defer lower1.deinit();
    const result = try lower1.run();
    defer result.deinit();
    const hir = result.ast_unit;

    var pipeline = compiler.pipeline.Pipeline.init(gpa, &context);
    var chk = compiler.checker.Checker.init(gpa, &context, &pipeline);
    defer chk.deinit();
    try chk.runAst(hir);
    try testing.expectEqual(@as(usize, 0), context.diags.count());

    var lt = compiler.lower_tir.LowerTir.init(gpa, &context, &pipeline, &chk);
    defer lt.deinit();

    if (lt.runAst(hir)) |tir_result| {
        defer tir_result.deinit();
    } else |err| {
        switch (err) {
            error.LoweringBug, error.ComptimeExecutionFailed, error.UnsupportedComptimeType => {},
            else => return err,
        }
    }

    try testing.expectEqual(@as(usize, 1), context.diags.count());
    try testing.expectEqual(diag.DiagnosticCode.invalid_binary_op_operands, context.diags.messages.items[0].code);
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
