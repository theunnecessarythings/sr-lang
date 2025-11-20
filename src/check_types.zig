const Checker = @import("checker.zig").Checker;
const types = @import("types.zig");
const ast = @import("ast.zig");
const std = @import("std");
const compile = @import("compile.zig");

const comp = @import("comptime.zig");
const PipelineBinding = @import("pipeline.zig").Pipeline.ComptimeBinding;
const Loc = @import("lexer.zig").Token.Loc;

const Binding = union(enum) {
    Type: struct { name: ast.StrId, ty: types.TypeId },
    Value: struct { name: ast.StrId, value: comp.ComptimeValue, ty: types.TypeId },
};

const PipelineBindingSlice = struct {
    items: []PipelineBinding,
    owns: bool,
};

fn pipelineBindingsFor(self: *Checker, bindings: []const Binding) !PipelineBindingSlice {
    if (bindings.len == 0) return .{ .items = &[_]PipelineBinding{}, .owns = false };

    var out = try self.gpa.alloc(PipelineBinding, bindings.len);
    var i: usize = 0;
    while (i < bindings.len) : (i += 1) {
        const b = bindings[i];
        out[i] = switch (b) {
            .Type => |t| .{ .type_param = .{ .name = t.name, .ty = t.ty } },
            .Value => |v| .{ .value_param = .{ .name = v.name, .ty = v.ty, .value = v.value } },
        };
    }

    return .{ .items = out, .owns = true };
}

fn evalComptimeValueWithBindings(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    expr: ast.ExprId,
    expected_ty: types.TypeId,
    bindings: []const Binding,
) !comp.ComptimeValue {
    const pb = try pipelineBindingsFor(self, bindings);
    defer if (pb.owns) self.gpa.free(pb.items);
    return self.evalComptimeExpr(ctx, ast_unit, expr, expected_ty, pb.items);
}

fn lookupTypeBinding(bindings: []const Binding, name: ast.StrId) ?types.TypeId {
    for (bindings) |binding| {
        switch (binding) {
            .Type => |t| if (t.name.eq(name)) return t.ty,
            else => {},
        }
    }
    return null;
}

fn lookupValueBinding(bindings: []const Binding, name: ast.StrId) ?comp.ComptimeValue {
    for (bindings) |binding| {
        switch (binding) {
            .Value => |v| if (v.name.eq(name)) return v.value,
            else => {},
        }
    }
    return null;
}

// --------- type helpers
pub fn isNumericKind(_: *const Checker, k: types.TypeKind) bool {
    return switch (k) {
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize, .Tensor, .Simd, .Complex => true,
        else => false,
    };
}
pub fn isIntegerKind(_: *const Checker, k: types.TypeKind) bool {
    return switch (k) {
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
        else => false,
    };
}

fn typeAlign(ctx: *const compile.Context, ty_id: types.TypeId) usize {
    const k = ctx.type_store.index.kinds.items[ty_id.toRaw()];
    return switch (k) {
        .Bool, .I8, .U8 => 1,
        .I16, .U16 => 2,
        .I32, .U32, .F32 => 4,
        .I64, .U64, .Usize, .F64, .Ptr, .MlirModule, .MlirAttribute, .MlirType, .Function => 8,
        .Simd => blk: {
            // Assume natural vector alignment (at least 16) on 64-bit targets
            const elem_align = typeAlign(ctx, ctx.type_store.get(.Simd, ty_id).elem);
            break :blk if (elem_align < 16) 16 else elem_align;
        },
        // Conservative defaults for aggregates (will be refined by element alignment)
        .String, .Slice, .DynArray => 8,
        .Array => typeAlign(ctx, ctx.type_store.get(.Array, ty_id).elem),
        .Struct => blk_s: {
            const st = ctx.type_store.get(.Struct, ty_id);
            const fields = ctx.type_store.field_pool.slice(st.fields);
            var max_a: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const a = typeAlign(ctx, f.ty);
                if (a > max_a) max_a = a;
            }
            break :blk_s max_a;
        },
        .Tuple => blk_t: {
            const tp = ctx.type_store.get(.Tuple, ty_id);
            const elems = ctx.type_store.type_pool.slice(tp.elems);
            var max_a: usize = 1;
            for (elems) |eid| {
                const a = typeAlign(ctx, eid);
                if (a > max_a) max_a = a;
            }
            break :blk_t max_a;
        },
        .Variant, .Error => {
            const fields = if (k == .Variant)
                ctx.type_store.field_pool.slice(ctx.type_store.get(.Variant, ty_id).variants)
            else
                ctx.type_store.field_pool.slice(ctx.type_store.get(.Error, ty_id).variants);
            var max_a: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const a = typeAlign(ctx, f.ty);
                if (a > max_a) max_a = a;
            }
            // Struct layout: i32 tag (align 4), then payload (align max_a)
            return if (max_a > 4) max_a else 4;
        },
        .Union => blk_u: {
            const u = ctx.type_store.get(.Union, ty_id);
            const fields = ctx.type_store.field_pool.slice(u.fields);
            var max_a: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const a = typeAlign(ctx, f.ty);
                if (a > max_a) max_a = a;
            }
            break :blk_u max_a;
        },
        .Optional => {
            const o = ctx.type_store.get(.Optional, ty_id);
            const a = typeAlign(ctx, o.elem);
            return if (a > 1) a else 1;
        },
        else => 1,
    };
}

pub fn typeSize(ctx: *const compile.Context, ty_id: types.TypeId) usize {
    const k = ctx.type_store.index.kinds.items[ty_id.toRaw()];
    return switch (k) {
        .I8, .U8, .Bool => 1,
        .I16, .U16 => 2,
        .I32, .U32, .F32 => 4,
        .I64, .U64, .F64, .Usize => 8, // best-effort default for 64-bit targets
        .Ptr => 8, // best-effort default for 64-bit targets
        .MlirModule, .MlirAttribute, .MlirType => 8,
        // Enums lower to their tag type; assume 32-bit by default via tag_type
        .Enum => blk_enum: {
            const en = ctx.type_store.get(.Enum, ty_id);
            break :blk_enum typeSize(ctx, en.tag_type);
        },
        .Simd => blk_simd: {
            const simd = ctx.type_store.get(.Simd, ty_id);
            const elem_size = typeSize(ctx, simd.elem);
            break :blk_simd std.math.mul(usize, elem_size, @as(usize, simd.lanes)) catch unreachable;
        },
        .Void => 0,
        .Any => 0, // Size is not known
        .String => 16, // ptr + len on 64-bit targets
        .Slice => 16, // best-effort: ptr + len on 64-bit
        .DynArray => 24, // ptr + len + cap (3 * usize) on 64-bit
        .Array => blk: {
            const arr = ctx.type_store.get(.Array, ty_id);
            const elem_size = typeSize(ctx, arr.elem);
            break :blk std.math.mul(usize, elem_size, arr.len) catch unreachable;
        },
        .Struct => blk: {
            const st = ctx.type_store.get(.Struct, ty_id);
            const fields = ctx.type_store.field_pool.slice(st.fields);
            var offset: usize = 0;
            var max_a: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const a = typeAlign(ctx, f.ty);
                const sz = typeSize(ctx, f.ty);
                if (a > max_a) max_a = a;
                offset = std.mem.alignForward(usize, offset, a);
                offset = std.math.add(usize, offset, sz) catch unreachable;
            }
            const total = std.mem.alignForward(usize, offset, max_a);
            break :blk total;
        },
        .Tuple => blk_tup: {
            const tp = ctx.type_store.get(.Tuple, ty_id);
            const elems = ctx.type_store.type_pool.slice(tp.elems);
            var total: usize = 0;
            for (elems) |eid| {
                const esz = typeSize(ctx, eid);
                total = std.math.add(usize, total, esz) catch unreachable;
            }
            break :blk_tup total;
        },
        .Variant, .Error => blk_var: {
            // Runtime shape: struct { tag: i32, payload: union {...} }
            const fields = if (k == .Variant)
                ctx.type_store.field_pool.slice(ctx.type_store.get(.Variant, ty_id).variants)
            else
                ctx.type_store.field_pool.slice(ctx.type_store.get(.Error, ty_id).variants);
            var max_payload: usize = 0;
            var max_align: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const sz = typeSize(ctx, f.ty);
                if (sz > max_payload) max_payload = sz;
                const a = typeAlign(ctx, f.ty);
                if (a > max_align) max_align = a;
            }
            const payload_sz = std.mem.alignForward(usize, max_payload, max_align);
            // tag is 4 bytes (i32). We pack payload immediately after tag.
            break :blk_var (4 + payload_sz);
        },
        .ErrorSet => blk_es: {
            const es = ctx.type_store.get(.ErrorSet, ty_id);
            const v_sz = typeSize(ctx, es.value_ty);
            const e_sz = typeSize(ctx, es.error_ty);
            const max_payload = if (v_sz > e_sz) v_sz else e_sz;
            break :blk_es (4 + max_payload);
        },
        .Union => blk_union: {
            const u = ctx.type_store.get(.Union, ty_id);
            const fields = ctx.type_store.field_pool.slice(u.fields);
            var max_sz: usize = 0;
            var max_align: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const sz = typeSize(ctx, f.ty);
                if (sz > max_sz) max_sz = sz;
                const a = typeAlign(ctx, f.ty);
                if (a > max_align) max_align = a;
            }
            break :blk_union std.mem.alignForward(usize, max_sz, max_align);
        },
        .Optional => blk_opt: {
            const o = ctx.type_store.get(.Optional, ty_id);
            const elem_sz = typeSize(ctx, o.elem);
            const elem_align = typeAlign(ctx, o.elem);
            // Runtime shape: struct { is_some: bool, payload } with natural alignment
            const after_flag = std.mem.alignForward(usize, 1, elem_align);
            const total = std.mem.alignForward(usize, after_flag + elem_sz, if (elem_align > 1) elem_align else 1);
            break :blk_opt total;
        },
        .Function => 8,
        .TypeType => blk: {
            const tt = ctx.type_store.get(.TypeType, ty_id);
            break :blk typeSize(ctx, tt.of);
        },
        // Optional/Struct/Tuple/Union/Map/Error/Variant/ErrorSet/Simd/Tensor:
        // ABI/padding/representation are not modeled here yet.
        else => {
            std.debug.print("typeSize: unhandled kind {}\n", .{k});
            unreachable;
        },
    };
}

pub fn isOptional(self: *Checker, id: types.TypeId) ?types.TypeId {
    const k = self.context.type_store.index.kinds.items[id.toRaw()];
    if (k != .Optional) return null;
    return self.context.type_store.get(.Optional, id).elem;
}

pub fn checkTypeOf(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const tr = ast_unit.exprs.get(.TypeOf, id);
    // typeof should accept value expressions; get their type directly.
    const et = try self.checkExpr(ctx, ast_unit, tr.expr);
    if (self.typeKind(et) != .TypeError) {
        return self.context.type_store.mkTypeType(et);
    }
    // As a fallback, allow typeof on a type expression (yielding that type).
    const res = try typeFromTypeExpr(self, ctx, ast_unit, tr.expr);
    if (res[0]) {
        return self.context.type_store.mkTypeType(res[1]);
    }
    try self.context.diags.addError(ast_unit.exprs.locs.get(tr.loc), .could_not_resolve_type, .{});
    return self.context.type_store.tTypeError();
}

// =========================================================
// Type expressions
// =========================================================
fn variantPayloadType(self: *Checker, variant_ty: types.TypeId, tag: ast.StrId) ?types.TypeId {
    const vt = self.context.type_store.get(.Variant, variant_ty);
    const cases = self.context.type_store.field_pool.slice(vt.variants);
    var i: usize = 0;
    while (i < cases.len) : (i += 1) {
        const vc = self.context.type_store.Field.get(cases[i]);
        if (vc.name.eq(tag)) return vc.ty;
    }
    return null;
}

fn evalLiteralToComptime(ast_unit: *ast.Ast, id: ast.ExprId) !?comp.ComptimeValue {
    if (ast_unit.exprs.index.kinds.items[id.toRaw()] != .Literal) return null;
    const lit = ast_unit.exprs.get(.Literal, id);
    return switch (lit.kind) {
        .int => blk: {
            const info = switch (lit.data) {
                .int => |i| i,
                else => return null,
            };
            if (!info.valid) return null;
            break :blk comp.ComptimeValue{ .Int = @as(i128, @intCast(info.value)) };
        },
        else => null,
    };
}

fn typeFromTypeExprWithBindings(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    id: ast.ExprId,
    bindings: []const Binding,
) anyerror!struct { bool, types.TypeId } {
    const kind = ast_unit.exprs.index.kinds.items[id.toRaw()];
    const ts = self.context.type_store;
    var status = true;
    return switch (kind) {
        .Ident => blk_ident: {
            const name = ast_unit.exprs.get(.Ident, id).name;
            if (lookupTypeBinding(bindings, name)) |ty|
                break :blk_ident .{ status, ty };
            break :blk_ident try typeFromTypeExpr(self, ctx, ast_unit, id);
        },
        .StructType => blk_struct: {
            const row = ast_unit.exprs.get(.StructType, id);
            const sfs = ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer ts.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const f = ast_unit.exprs.StructField.get(sfs[i]);
                const gop = try seen.getOrPut(self.gpa, f.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(f.loc), .duplicate_field, .{});
                    status = false;
                }
                const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, f.ty, bindings);
                status = status and res[0];
                buf[i] = .{ .name = f.name, .ty = res[1] };
            }
            break :blk_struct .{ status, ts.mkStruct(buf) };
        },
        .ArrayType => blk_at: {
            const row = ast_unit.exprs.get(.ArrayType, id);
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.elem, bindings);
            status = status and res[0];
            const elem = res[1];
            var size: usize = 0;
            const size_loc = ast_unit.exprs.locs.get(row.loc);
            var size_eval = evalComptimeValueWithBindings(self, ctx, ast_unit, row.size, self.context.type_store.tUsize(), bindings) catch |err| {
                std.debug.print("Size eval error: {}\n", .{err});
                try self.context.diags.addError(size_loc, .array_size_not_integer_literal, .{});
                status = false;
                break :blk_at .{ status, ts.mkArray(elem, size) };
            };
            defer size_eval.destroy(self.gpa);

            switch (size_eval) {
                .Int => |len| {
                    const concrete = std.math.cast(usize, len) orelse {
                        try self.context.diags.addError(size_loc, .array_size_not_integer_literal, .{});
                        status = false;
                        break :blk_at .{ status, ts.mkArray(elem, size) };
                    };
                    size = concrete;
                },
                else => {
                    try self.context.diags.addError(size_loc, .array_size_not_integer_literal, .{});
                    status = false;
                },
            }

            break :blk_at .{ status, ts.mkArray(elem, size) };
        },
        .Call => blk_call: {
            const res = try typeFromTypeExpr(self, ctx, ast_unit, ast_unit.exprs.get(.Call, id).callee);
            status = status and res[0];
            if (try resolveTypeFunctionCall(self, ctx, ast_unit, id, bindings)) |ty_res| {
                status = status and ty_res[0];
                break :blk_call .{ status, ty_res[1] };
            }
            const call_row = ast_unit.exprs.get(.Call, id);
            const callee_kind = ast_unit.exprs.index.kinds.items[call_row.callee.toRaw()];
            if (callee_kind == .FieldAccess or callee_kind == .Ident) {
                const any_type_ty = ts.mkTypeType(ts.tAny());
                var value = evalComptimeValueWithBindings(self, ctx, ast_unit, id, any_type_ty, bindings) catch break :blk_call .{ false, ts.tTypeError() };
                defer value.destroy(self.gpa);
                switch (value) {
                    .Type => |resolved| {
                        const wrapped = self.context.type_store.mkTypeType(resolved);
                        try ast_unit.type_info.ensureExpr(self.gpa, id);
                        ast_unit.type_info.expr_types.items[id.toRaw()] = wrapped;
                        break :blk_call .{ status, resolved };
                    },
                    else => {},
                }
            }
            break :blk_call .{ false, ts.tTypeError() };
        },
        else => try typeFromTypeExpr(self, ctx, ast_unit, id),
    };
}

fn resolveTypeFunctionCall(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    call_id: ast.ExprId,
    existing_bindings: []const Binding,
) anyerror!?struct { bool, types.TypeId } {
    const call = ast_unit.exprs.get(.Call, call_id);
    const callee_kind = ast_unit.exprs.index.kinds.items[call.callee.toRaw()];
    if (callee_kind != .Ident) return null;

    const callee_ident = ast_unit.exprs.get(.Ident, call.callee);
    const sym_id = self.lookup(ctx, callee_ident.name) orelse return null;
    const sym = ctx.symtab.syms.get(sym_id);
    if (sym.origin_decl.isNone()) return null;

    const decl_id = sym.origin_decl.unwrap();
    const decl = ast_unit.exprs.Decl.get(decl_id);
    const value_kind = ast_unit.exprs.index.kinds.items[decl.value.toRaw()];
    if (value_kind != .FunctionLit) return null;

    const fn_lit = ast_unit.exprs.get(.FunctionLit, decl.value);
    const params = ast_unit.exprs.param_pool.slice(fn_lit.params);
    const args = ast_unit.exprs.expr_pool.slice(call.args);
    if (params.len != args.len) return null;

    var bindings_builder: std.ArrayList(Binding) = .empty;
    defer bindings_builder.deinit(self.gpa);
    if (existing_bindings.len > 0) {
        try bindings_builder.appendSlice(self.gpa, existing_bindings);
    }

    var i: usize = 0;
    var status = true;
    while (i < params.len) : (i += 1) {
        const param = ast_unit.exprs.Param.get(params[i]);
        if (!param.is_comptime or param.pat.isNone() or param.ty.isNone()) return null;

        const pat_id = param.pat.unwrap();
        if (ast_unit.pats.index.kinds.items[pat_id.toRaw()] != .Binding) return null;
        const pname = ast_unit.pats.get(.Binding, pat_id).name;

        const res = try typeFromTypeExpr(self, ctx, ast_unit, param.ty.unwrap());
        status = status and res[0];
        const annotated = res[1];
        if (self.typeKind(annotated) == .TypeType) {
            const arg_res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, args[i], bindings_builder.items);
            status = status and arg_res[0];
            try bindings_builder.append(self.gpa, .{ .Type = .{ .name = pname, .ty = arg_res[1] } });
        } else {
            const arg_expr = args[i];
            const arg_kind = ast_unit.exprs.index.kinds.items[arg_expr.toRaw()];

            var have_value = false;
            var value: comp.ComptimeValue = undefined;

            if (arg_kind == .Ident) {
                const ident_name = ast_unit.exprs.get(.Ident, arg_expr).name;
                if (lookupValueBinding(bindings_builder.items, ident_name)) |existing| {
                    value = existing;
                    have_value = true;
                }
            }

            if (!have_value) {
                value = blk: {
                    const computed = evalComptimeValueWithBindings(self, ctx, ast_unit, arg_expr, annotated, bindings_builder.items) catch {
                        if (arg_kind == .Literal) {
                            const literal_val = (try evalLiteralToComptime(ast_unit, arg_expr)) orelse return null;
                            break :blk literal_val;
                        }
                        return null;
                    };
                    break :blk computed;
                };
                have_value = true;
            }

            if (!have_value) return null;
            try bindings_builder.append(self.gpa, .{ .Value = .{ .name = pname, .value = value, .ty = annotated } });
        }
    }

    if (fn_lit.body.isNone()) return null;
    const body_id = fn_lit.body.unwrap();
    if (ast_unit.exprs.index.kinds.items[body_id.toRaw()] != .Block) return null;
    const block = ast_unit.exprs.get(.Block, body_id);
    const stmts = ast_unit.stmts.stmt_pool.slice(block.items);
    for (stmts) |sid| {
        if (ast_unit.stmts.index.kinds.items[sid.toRaw()] != .Return) continue;
        const ret = ast_unit.stmts.get(.Return, sid);
        if (ret.value.isNone()) return null;
        const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, ret.value.unwrap(), bindings_builder.items);
        status = status and res[0];
        const resolved = res[1];
        try ast_unit.type_info.ensureExpr(self.gpa, call_id);
        const type_ty = self.context.type_store.mkTypeType(resolved);
        ast_unit.type_info.expr_types.items[call_id.toRaw()] = type_ty;
        return .{ status, resolved };
    }
    return null;
}

pub fn typeFromTypeExpr(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) anyerror!struct { bool, types.TypeId } {
    const k = ast_unit.exprs.index.kinds.items[id.toRaw()];
    const ts = self.context.type_store;
    var status = true;
    return switch (k) {
        .Ident => blk: {
            const name = ast_unit.exprs.get(.Ident, id).name;
            const s = ast_unit.exprs.strs.get(name);
            if (std.mem.eql(u8, s, "bool")) break :blk .{ true, ts.tBool() };
            if (std.mem.eql(u8, s, "i8")) break :blk .{ true, ts.tI8() };
            if (std.mem.eql(u8, s, "i16")) break :blk .{ true, ts.tI16() };
            if (std.mem.eql(u8, s, "i32")) break :blk .{ true, ts.tI32() };
            if (std.mem.eql(u8, s, "i64")) break :blk .{ true, ts.tI64() };
            if (std.mem.eql(u8, s, "u8")) break :blk .{ true, ts.tU8() };
            if (std.mem.eql(u8, s, "u16")) break :blk .{ true, ts.tU16() };
            if (std.mem.eql(u8, s, "u32")) break :blk .{ true, ts.tU32() };
            if (std.mem.eql(u8, s, "u64")) break :blk .{ true, ts.tU64() };
            if (std.mem.eql(u8, s, "f32")) break :blk .{ true, ts.tF32() };
            if (std.mem.eql(u8, s, "f64")) break :blk .{ true, ts.tF64() };
            if (std.mem.eql(u8, s, "usize")) break :blk .{ true, ts.tUsize() };
            if (std.mem.eql(u8, s, "char")) break :blk .{ true, ts.tU32() };
            if (std.mem.eql(u8, s, "string")) break :blk .{ true, ts.tString() };
            if (std.mem.eql(u8, s, "void")) break :blk .{ true, ts.tVoid() };
            if (std.mem.eql(u8, s, "any")) break :blk .{ true, ts.tAny() };
            if (std.mem.eql(u8, s, "type"))
                break :blk .{ true, ts.mkTypeType(ts.tAny()) };

            if (self.lookup(ctx, name)) |sid| {
                const sym = ctx.symtab.syms.get(sid);
                if (!sym.origin_decl.isNone()) {
                    const did = sym.origin_decl.unwrap();
                    if (ast_unit.type_info.decl_types.items[did.toRaw()]) |ty| {
                        const kind = self.typeKind(ty);
                        if (kind == .TypeType) {
                            const tt = ts.get(.TypeType, ty);
                            if (self.typeKind(tt.of) != .Any) {
                                return .{ true, tt.of };
                            }
                        } else {
                            return .{ true, ty };
                        }
                    }

                    // Recursion guard for lazy type resolution.
                    for (ctx.resolving_type_decls.items) |resolving_did| {
                        if (resolving_did.eq(did)) {
                            // Recursive type definition detected. Return `any` to avoid a crash.
                            // A proper fix requires more advanced type system features (e.g. opaque types).
                            return .{ true, ts.tAny() };
                        }
                    }
                    try ctx.resolving_type_decls.append(self.gpa, did);
                    defer _ = ctx.resolving_type_decls.pop();

                    // Lazy resolve: if the declaration\'s RHS is a type expression, resolve it now.
                    const drow = ast_unit.exprs.Decl.get(did);
                    const rhs_res = try typeFromTypeExpr(self, ctx, ast_unit, drow.value);
                    status = status and rhs_res[0];
                    const rhs_ty = rhs_res[1];
                    if (self.typeKind(rhs_ty) != .TypeError) {
                        // Record as a type constant for future queries
                        const tt = ts.mkTypeType(rhs_ty);
                        ast_unit.type_info.decl_types.items[did.toRaw()] = tt;
                        try ast_unit.type_info.ensureExpr(self.gpa, drow.value);
                        ast_unit.type_info.expr_types.items[drow.value.toRaw()] = tt;
                        return .{ status, rhs_ty };
                    }
                }
                if (!sym.origin_param.isNone()) {
                    const pid = sym.origin_param.unwrap();
                    const param_row = ast_unit.exprs.Param.get(pid);
                    if (!param_row.ty.isNone()) {
                        const res = try typeFromTypeExpr(self, ctx, ast_unit, param_row.ty.unwrap());
                        status = status and res[0];
                        const annotated = res[1];
                        if (param_row.is_comptime) {
                            if (self.typeKind(annotated) == .TypeType) {
                                return .{ status, ts.get(.TypeType, annotated).of };
                            }
                            return .{ status, annotated };
                        }
                        return .{ status, annotated };
                    }
                    return .{ status, ts.tAny() };
                }
            }

            try self.context.diags.addError(ast_unit.exprs.locs.get(ast_unit.exprs.get(.Ident, id).loc), .undefined_identifier, .{});
            break :blk .{ false, ts.tTypeError() };
        },
        .MlirBlock => blk: {
            const row = ast_unit.exprs.get(.MlirBlock, id);
            break :blk switch (row.kind) {
                .Type => .{ true, ts.tMlirType() },
                .Attribute => .{ true, ts.tMlirAttribute() },
                .Module => .{ true, ts.tMlirModule() },
                .Operation => blk_inner: {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .mlir_block_not_a_type, .{});
                    break :blk_inner .{ false, ts.tTypeError() };
                },
            };
        },
        .TupleType => blk_tt: {
            const row = ast_unit.exprs.get(.TupleType, id);
            const ids = ast_unit.exprs.expr_pool.slice(row.elems);
            var buf = try ts.gpa.alloc(types.TypeId, ids.len);
            defer ts.gpa.free(buf);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) {
                const res = try typeFromTypeExpr(self, ctx, ast_unit, ids[i]);
                status = status and res[0];
                buf[i] = res[1];
            }

            break :blk_tt .{ status, ts.mkTuple(buf) };
        },
        .TupleLit => blk_ttl: {
            const row = ast_unit.exprs.get(.TupleLit, id);
            const ids = ast_unit.exprs.expr_pool.slice(row.elems);
            var buf = try ts.gpa.alloc(types.TypeId, ids.len);
            defer ts.gpa.free(buf);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) {
                const res = try typeFromTypeExpr(self, ctx, ast_unit, ids[i]);
                status = status and res[0];
                buf[i] = res[1];
            }
            break :blk_ttl .{ status, ts.mkTuple(buf) };
        },
        .MapType => blk_mt: {
            const row = ast_unit.exprs.get(.MapType, id);
            const key_res = try typeFromTypeExpr(self, ctx, ast_unit, row.key);
            const val_res = try typeFromTypeExpr(self, ctx, ast_unit, row.value);
            status = status and key_res[0] and val_res[0];
            break :blk_mt .{ status, ts.mkMap(key_res[1], val_res[1]) };
        },
        .ArrayType => blk_at: {
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, id, &[_]Binding{});
            break :blk_at res;
        },
        .DynArrayType => blk_dt: {
            const row = ast_unit.exprs.get(.DynArrayType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            break :blk_dt .{ status, ts.mkDynArray(res[1]) };
        },
        .SliceType => blk_st: {
            const row = ast_unit.exprs.get(.SliceType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            break :blk_st .{ status, ts.mkSlice(res[1]) };
        },
        .OptionalType => blk_ot: {
            const row = ast_unit.exprs.get(.OptionalType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            break :blk_ot .{ status, ts.mkOptional(res[1]) };
        },
        .PointerType => blk_pt: {
            const row = ast_unit.exprs.get(.PointerType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            break :blk_pt .{ status, ts.mkPtr(res[1], row.is_const) };
        },
        .SimdType => blk_simd: {
            const row = ast_unit.exprs.get(.SimdType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            const elem_ty = res[1];
            const ek = self.typeKind(elem_ty);
            if (!isNumericKind(self, ek)) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_invalid_element_type, .{});
                status = false;
            }
            const lk = ast_unit.exprs.index.kinds.items[row.lanes.toRaw()];
            if (lk != .Literal) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                status = false;
            }
            const lit = ast_unit.exprs.get(.Literal, row.lanes);
            if (lit.kind != .int) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                status = false;
            }
            const lanes_val = switch (lit.data) {
                .int => |int_info| blk: {
                    if (!int_info.valid) break :blk 0;
                    break :blk std.math.cast(usize, int_info.value) orelse 0;
                },
                else => 0,
            };
            if (lanes_val == 0 or lanes_val > std.math.maxInt(u16)) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                status = false;
            }
            const simd_ty = ts.mkSimd(elem_ty, @intCast(lanes_val));
            break :blk_simd .{ status, simd_ty };
        },
        .TensorType => blk_tensor: {
            const row = ast_unit.exprs.get(.TensorType, id);
            // Validate shape dimensions are integer literals
            const dims = ast_unit.exprs.expr_pool.slice(row.shape);
            if (dims.len > types.max_tensor_rank) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_rank_exceeds_limit, .{});
                status = false;
            }
            var dim_values = [_]usize{0} ** types.max_tensor_rank;
            var i: usize = 0;
            while (i < dims.len) : (i += 1) {
                const dk = ast_unit.exprs.index.kinds.items[dims[i].toRaw()];
                if (dk != .Literal) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    status = false;
                    continue;
                }
                const dl = ast_unit.exprs.get(.Literal, dims[i]);
                if (dl.kind != .int) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    status = false;
                    continue;
                }
                const info = switch (dl.data) {
                    .int => |int_info| int_info,
                    else => ast.LiteralInt{ .text = .{ .index = 0 }, .value = 0, .base = 0, .valid = false },
                };
                if (!info.valid) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    status = false;
                }
                const dim_val = std.math.cast(usize, info.value) orelse val: {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    status = false;
                    break :val 0;
                };
                dim_values[i] = dim_val;
            }
            // Validate element type present and resolvable
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            const ety = res[1];
            if (self.typeKind(ety) == .TypeError) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_missing_element_type, .{});
            }
            const rank = dims.len;
            const tensor_ty = ts.mkTensor(ety, dim_values[0..rank]);
            break :blk_tensor .{ status, tensor_ty };
        },
        .StructType => blk_sty: {
            const row = ast_unit.exprs.get(.StructType, id);
            const sfs = ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer ts.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const f = ast_unit.exprs.StructField.get(sfs[i]);
                const gop = try seen.getOrPut(self.gpa, f.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(f.loc), .duplicate_field, .{});
                    status = false;
                }
                const res = try typeFromTypeExpr(self, ctx, ast_unit, f.ty);
                status = status and res[0];
                buf[i] = .{ .name = f.name, .ty = res[1] };
            }
            break :blk_sty .{ status, ts.mkStruct(buf) };
        },
        .UnionType => blk_un: {
            const row = ast_unit.exprs.get(.UnionType, id);
            const sfs = ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer ts.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const sf = ast_unit.exprs.StructField.get(sfs[i]);
                const gop = try seen.getOrPut(self.gpa, sf.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(sf.loc), .duplicate_field, .{});
                    status = false;
                }
                // Validate field types resolve
                const res = try typeFromTypeExpr(self, ctx, ast_unit, sf.ty);
                status = status and res[0];
                buf[i] = .{ .name = sf.name, .ty = res[1] };
            }
            break :blk_un .{ status, ts.mkUnion(buf) };
        },

        .EnumType => blk_en: {
            const row = ast_unit.exprs.get(.EnumType, id);
            const efs = ast_unit.exprs.efield_pool.slice(row.fields);

            const tag_res = if (row.discriminant.isNone())
                .{ true, ts.tI32() }
            else
                (try typeFromTypeExpr(self, ctx, ast_unit, row.discriminant.unwrap()));
            status = status and tag_res[0];
            const tag_ty = tag_res[1];

            // Ensure the tag type is an integer.
            const tk = self.typeKind(tag_ty);
            if (!isIntegerKind(self, tk)) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .enum_discriminant_not_integer, .{});
                status = false;
            }

            var member_buf = try self.gpa.alloc(types.TypeStore.EnumMemberArg, efs.len);
            defer self.gpa.free(member_buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);
            var enum_value_bindings: std.ArrayList(Binding) = .empty;
            defer enum_value_bindings.deinit(self.gpa);

            var next_value: i128 = 0;
            var i: usize = 0;
            while (i < efs.len) : (i += 1) {
                const enum_field = ast_unit.exprs.EnumField.get(efs[i]);

                const gop = try seen.getOrPut(self.gpa, enum_field.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(enum_field.loc), .duplicate_enum_field, .{});
                    status = false;
                }

                var current_value: i128 = next_value;
                const binding_slice = enum_value_bindings.items[0..enum_value_bindings.items.len];
                if (!enum_field.value.isNone()) {
                    const val_id = enum_field.value.unwrap();
                    var resolved_from_binding = false;
                    if (ast_unit.exprs.index.kinds.items[val_id.toRaw()] == .Ident) {
                        const ident = ast_unit.exprs.get(.Ident, val_id);
                        if (lookupValueBinding(binding_slice, ident.name)) |binding_val| {
                            switch (binding_val) {
                                .Int => |v| {
                                    current_value = v;
                                    resolved_from_binding = true;
                                },
                                else => {},
                            }
                        }
                    }

                    if (!resolved_from_binding) {
                        const comptime_eval_ok = comptime_block: {
                            var comptime_val = evalComptimeValueWithBindings(self, ctx, ast_unit, val_id, tag_ty, binding_slice) catch {
                                break :comptime_block false;
                            };
                            defer comptime_val.destroy(self.gpa);

                            switch (comptime_val) {
                                .Int => |v| current_value = v,
                                else => break :comptime_block false,
                            }
                            break :comptime_block true;
                        };

                        if (!comptime_eval_ok) {
                            try self.context.diags.addError(ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                            status = false;
                        }
                    }
                }

                member_buf[i] = .{ .name = enum_field.name, .value = @intCast(current_value) };
                try enum_value_bindings.append(self.gpa, .{
                    .Value = .{ .name = enum_field.name, .value = comp.ComptimeValue{ .Int = current_value }, .ty = tag_ty },
                });
                next_value = current_value + 1;
            }
            break :blk_en .{ status, ts.mkEnum(member_buf, tag_ty) };
        },
        .ErrorType => blk_err: {
            const row = ast_unit.exprs.get(.ErrorType, id);
            const vfs = ast_unit.exprs.vfield_pool.slice(row.fields);
            var case_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
            defer self.gpa.free(case_buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);

            var i: usize = 0;
            while (i < vfs.len) : (i += 1) {
                const vf = ast_unit.exprs.VariantField.get(vfs[i]);
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vf.loc), .duplicate_error_variant, .{});
                }

                const payload_ty = switch (vf.payload_kind) {
                    .none => ts.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) {
                            break :blk_tuple ts.tVoid();
                        }
                        const elems = ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        var j: usize = 0;
                        while (j < elems.len) : (j += 1) {
                            const res = try typeFromTypeExpr(self, ctx, ast_unit, elems[j]);
                            status = status and res[0];
                            elem_buf[j] = res[1];
                        }

                        break :blk_tuple ts.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) {
                            break :blk_struct ts.tVoid();
                        }
                        const fields = ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        var j: usize = 0;
                        while (j < fields.len) : (j += 1) {
                            const sf = ast_unit.exprs.StructField.get(fields[j]);
                            const res = try typeFromTypeExpr(self, ctx, ast_unit, sf.ty);
                            status = status and res[0];
                            field_buf[j] = .{
                                .name = sf.name,
                                .ty = res[1],
                            };
                        }
                        break :blk_struct ts.mkStruct(field_buf);
                    },
                };
                case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
            }
            break :blk_err .{ status, ts.mkError(case_buf) };
        },
        .ErrorSetType => blk_est: {
            const row = ast_unit.exprs.get(.ErrorSetType, id);
            const val_res = try typeFromTypeExpr(self, ctx, ast_unit, row.value);
            const err_res = try typeFromTypeExpr(self, ctx, ast_unit, row.err);
            status = status and val_res[0] and err_res[0];
            break :blk_est .{ status, ts.mkErrorSet(val_res[1], err_res[1]) };
        },
        .VariantType => blk_var: {
            const row = ast_unit.exprs.get(.VariantType, id);
            const vfs = ast_unit.exprs.vfield_pool.slice(row.fields);
            var case_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
            defer self.gpa.free(case_buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);

            var i: usize = 0;
            while (i < vfs.len) : (i += 1) {
                const vf = ast_unit.exprs.VariantField.get(vfs[i]);
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vf.loc), .duplicate_variant, .{});
                    status = false;
                }

                const payload_ty = switch (vf.payload_kind) {
                    .none => ts.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) {
                            break :blk_tuple ts.tVoid();
                        }
                        const elems = ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        var j: usize = 0;
                        while (j < elems.len) : (j += 1) {
                            const res = try typeFromTypeExpr(self, ctx, ast_unit, elems[j]);
                            status = status and res[0];
                            elem_buf[j] = res[1];
                        }
                        break :blk_tuple ts.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) {
                            break :blk_struct ts.tVoid();
                        }
                        const fields = ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        var j: usize = 0;
                        while (j < fields.len) : (j += 1) {
                            const sf = ast_unit.exprs.StructField.get(fields[j]);
                            const res = try typeFromTypeExpr(self, ctx, ast_unit, sf.ty);
                            status = status and res[0];
                            field_buf[j] = .{ .name = sf.name, .ty = res[1] };
                        }
                        break :blk_struct ts.mkStruct(field_buf);
                    },
                };
                case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
            }
            break :blk_var .{ status, ts.mkVariant(case_buf) };
        },

        .FunctionLit => blk_fn: {
            // function type in type position
            const fnr = ast_unit.exprs.get(.FunctionLit, id);
            const params = ast_unit.exprs.param_pool.slice(fnr.params);
            var pbuf = try self.gpa.alloc(types.TypeId, params.len);
            defer self.gpa.free(pbuf);
            var i: usize = 0;
            while (i < params.len) : (i += 1) {
                const p = ast_unit.exprs.Param.get(params[i]);
                if (p.ty.isNone()) break :blk_fn .{ false, ts.tTypeError() };
                const res = try typeFromTypeExpr(self, ctx, ast_unit, p.ty.unwrap());
                status = status and res[0];
                const pt = res[1];
                if (self.typeKind(pt) == .TypeError) return .{ false, ts.tTypeError() };
                pbuf[i] = pt;
            }
            const res_res = if (!fnr.result_ty.isNone()) (try typeFromTypeExpr(self, ctx, ast_unit, fnr.result_ty.unwrap())) else .{ true, ts.tVoid() };
            status = status and res_res[0];
            const res = res_res[1];
            const is_pure = !fnr.flags.is_proc;
            break :blk_fn .{ status, ts.mkFunction(pbuf, res, fnr.flags.is_variadic, is_pure, fnr.flags.is_extern) };
        },
        .FieldAccess => blk_fa: {
            const fr = ast_unit.exprs.get(.FieldAccess, id);
            const parent_res = try typeFromTypeExpr(self, ctx, ast_unit, fr.parent);
            status = status and parent_res[0];
            const parent_ty = parent_res[1];
            const parent_kind = self.typeKind(parent_ty);
            switch (parent_kind) {
                .Ast => {
                    // Accessing a member from an imported module in type position
                    const ast_ty = ts.get(.Ast, parent_ty);
                    const pkg_name = self.context.interner.get(ast_ty.pkg_name);
                    const filepath = self.context.interner.get(ast_ty.filepath);
                    const pkg = self.context.compilation_unit.packages.getPtr(pkg_name) orelse {
                        try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .import_not_found, .{});
                        break :blk_fa .{ false, ts.tTypeError() };
                    };
                    const parent_unit = pkg.sources.getPtr(filepath) orelse {
                        try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .import_not_found, .{});
                        break :blk_fa .{ false, ts.tTypeError() };
                    };
                    if (parent_unit.ast) |a| {
                        // Re-intern field name in the imported unit's interner for lookup
                        const name_bytes = ast_unit.exprs.strs.get(fr.field);
                        const target_sid = a.exprs.strs.intern(name_bytes);
                        if (a.type_info.getExport(target_sid)) |ex| {
                            var ty = ex.ty;
                            if (self.typeKind(ty) == .TypeType) {
                                ty = ts.get(.TypeType, ty).of;
                            }
                            break :blk_fa .{ status, ty };
                        }
                    }
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_module_field, .{ast_unit.exprs.strs.get(fr.field)});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
                .Struct => {
                    const st = ts.get(.Struct, parent_ty);
                    const fields = ts.field_pool.slice(st.fields);
                    var i: usize = 0;
                    while (i < fields.len) : (i += 1) {
                        const f = fields[i];
                        const field = ts.Field.get(f);
                        if (field.name.toRaw() == fr.field.toRaw()) return .{ status, field.ty };
                    }
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
                .Variant => {
                    if (variantPayloadType(self, parent_ty, fr.field)) |pt| return .{ status, pt };
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_variant_tag, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
                .Enum => {
                    const et = ts.get(.Enum, parent_ty);
                    const members = ts.enum_member_pool.slice(et.members);
                    var i: usize = 0;
                    while (i < members.len) : (i += 1) {
                        const member = ts.EnumMember.get(members[i]);
                        if (member.name.toRaw() == fr.field.toRaw()) {
                            return .{ status, parent_ty };
                        }
                    }
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
                else => {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .field_access_on_non_aggregate, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
            }
        },
        .Import => blk_import: {
            const ir = ast_unit.exprs.get(.Import, id);
            const filepath = ast_unit.exprs.strs.get(ir.path);
            var found = false;
            for (self.context.compilation_unit.packages.values()) |pkg| {
                if (pkg.sources.get(filepath) == null) continue;
                const pkg_name = self.context.interner.intern(pkg.name);
                const ast_ty = ts.mkAst(pkg_name, ir.path);
                // Note: record type directly; no need to stamp expr_types here in type position
                found = true;
                break :blk_import .{ true, ast_ty };
            }
            if (!found) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(ir.loc), .import_not_found, .{});
                break :blk_import .{ false, ts.tTypeError() };
            }
            // Defensive: if control reaches here, return a type error instead of panicking
            break :blk_import .{ false, ts.tTypeError() };
        },
        .Call => blk_call: {
            const res = try typeFromTypeExpr(self, ctx, ast_unit, ast_unit.exprs.get(.Call, id).callee);
            status = status and res[0];
            if (try resolveTypeFunctionCall(self, ctx, ast_unit, id, &[_]Binding{})) |ty_res| {
                status = status and ty_res[0];
                break :blk_call .{ status, ty_res[1] };
            }
            const call_row = ast_unit.exprs.get(.Call, id);
            const callee_kind = ast_unit.exprs.index.kinds.items[call_row.callee.toRaw()];
            if (callee_kind == .FieldAccess or callee_kind == .Ident) {
                const any_type_ty = ts.mkTypeType(ts.tAny());
                var value = evalComptimeValueWithBindings(self, ctx, ast_unit, id, any_type_ty, &[_]Binding{}) catch break :blk_call .{ false, ts.tTypeError() };
                defer value.destroy(self.gpa);
                switch (value) {
                    .Type => |resolved| {
                        const wrapped = ts.mkTypeType(resolved);
                        try ast_unit.type_info.ensureExpr(self.gpa, id);
                        ast_unit.type_info.expr_types.items[id.toRaw()] = wrapped;
                        break :blk_call .{ status, resolved };
                    },
                    else => {},
                }
            }
            break :blk_call .{ false, ts.tTypeError() };
        },
        .AnyType => .{ true, ts.tAny() },
        .TypeType => .{ true, ts.tType() },
        .NoreturnType => .{ true, ts.tNoReturn() },
        else => .{ false, ts.tTypeError() },
    };
}
