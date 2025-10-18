const Checker = @import("checker.zig").Checker;
const types = @import("types.zig");
const ast = @import("ast.zig");
const std = @import("std");

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
    expr: ast.ExprId,
    expected_ty: types.TypeId,
    bindings: []const Binding,
) !comp.ComptimeValue {
    const pb = try pipelineBindingsFor(self, bindings);
    defer if (pb.owns) self.gpa.free(pb.items);
    return self.pipeline.evalComptimeExpr(self, self.ast_unit, expr, expected_ty, pb.items);
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

pub fn typeSize(self: *Checker, ty_id: types.TypeId) ?usize {
    const k = self.context.type_store.index.kinds.items[ty_id.toRaw()];
    return switch (k) {
        .I8, .U8, .Bool => 1,
        .I16, .U16 => 2,
        .I32, .U32, .F32 => 4,
        .I64, .U64, .F64, .Usize => 8, // best-effort default for 64-bit targets
        .Ptr => 8, // best-effort default for 64-bit targets
        .MlirModule, .MlirAttribute, .MlirType => 8,
        .Void => 0,
        .Any => 0, // Size is not known
        .String => 8, // best-effort: pointer-like handle; real impl is more complex
        .Slice => 16, // best-effort: ptr + len on 64-bit
        .Array => blk: {
            const arr = self.context.type_store.get(.Array, ty_id);
            const elem_size = typeSize(self, arr.elem) orelse return null;
            const len = switch (arr.len) {
                .Concrete => |l| l,
                .Unresolved => return null,
            };
            break :blk std.math.mul(usize, elem_size, len) catch return null;
        },
        // Optional/Struct/Tuple/Union/Map/Error/Variant/ErrorSet/Simd/Tensor:
        // ABI/padding/representation are not modeled here yet.
        else => null,
    };
}

pub fn isOptional(self: *Checker, id: types.TypeId) ?types.TypeId {
    const k = self.context.type_store.index.kinds.items[id.toRaw()];
    if (k != .Optional) return null;
    return self.context.type_store.get(.Optional, id).elem;
}

pub fn checkTypeOf(self: *Checker, id: ast.ExprId) !?types.TypeId {
    const tr = self.ast_unit.exprs.get(.TypeOf, id);
    // typeof should accept value expressions; get their type directly.
    if (try self.checkExpr(tr.expr)) |et| {
        return self.context.type_store.mkTypeType(et);
    }
    // As a fallback, allow typeof on a type expression (yielding that type).
    if (try typeFromTypeExpr(self, tr.expr)) |tt| {
        return self.context.type_store.mkTypeType(tt);
    }
    try self.context.diags.addError(self.ast_unit.exprs.locs.get(tr.loc), .could_not_resolve_type, .{});
    return null;
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

fn evalLiteralToComptime(self: *Checker, id: ast.ExprId) !?comp.ComptimeValue {
    if (self.ast_unit.exprs.index.kinds.items[id.toRaw()] != .Literal) return null;
    const lit = self.ast_unit.exprs.get(.Literal, id);
    return switch (lit.kind) {
        .int => blk: {
            const info = switch (lit.data) {
                .int => |i| i,
                else => return null,
            };
            if (!info.valid) return null;
            break :blk comp.ComptimeValue{ .Int = info.value };
        },
        else => null,
    };
}

fn typeFromTypeExprWithBindings(
    self: *Checker,
    id: ast.ExprId,
    bindings: []const Binding,
) anyerror!?types.TypeId {
    const kind = self.ast_unit.exprs.index.kinds.items[id.toRaw()];
    return switch (kind) {
        .Ident => blk_ident: {
            const name = self.ast_unit.exprs.get(.Ident, id).name;
            if (lookupTypeBinding(bindings, name)) |ty|
                break :blk_ident ty;
            break :blk_ident try typeFromTypeExpr(self, id);
        },
        .StructType => blk_struct: {
            const row = self.ast_unit.exprs.get(.StructType, id);
            const sfs = self.ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try self.context.type_store.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer self.context.type_store.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const f = self.ast_unit.exprs.StructField.get(sfs[i]);
                const gop = try seen.getOrPut(self.gpa, f.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(f.loc), .duplicate_field, .{});
                    return null;
                }
                const ft = (try typeFromTypeExprWithBindings(self, f.ty, bindings)) orelse break :blk_struct null;
                buf[i] = .{ .name = f.name, .ty = ft };
            }
            break :blk_struct self.context.type_store.mkStruct(buf);
        },
        .ArrayType => blk_at: {
            const row = self.ast_unit.exprs.get(.ArrayType, id);
            const elem = (try typeFromTypeExprWithBindings(self, row.elem, bindings)) orelse break :blk_at null;
            const size_expr_kind = self.ast_unit.exprs.index.kinds.items[row.size.toRaw()];
            var size: types.ArraySize = .{ .Unresolved = row.size };
            if (size_expr_kind == .Literal) {
                const lit = self.ast_unit.exprs.get(.Literal, row.size);
                if (lit.kind == .int) {
                    const info = switch (lit.data) {
                        .int => |i| i,
                        else => unreachable,
                    };
                    if (info.valid) {
                        const len = std.math.cast(usize, info.value) orelse {
                            try self.context.diags.addError(self.ast_unit.exprs.locs.get(lit.loc), .array_size_not_integer_literal, .{});
                            break :blk_at null;
                        };
                        size = .{ .Concrete = len };
                    }
                }
            }
            break :blk_at self.context.type_store.mkArray(elem, size);
        },
        .Call => try resolveTypeFunctionCall(self, id, bindings),
        else => try typeFromTypeExpr(self, id),
    };
}

fn resolveTypeFunctionCall(
    self: *Checker,
    call_id: ast.ExprId,
    existing_bindings: []const Binding,
) anyerror!?types.TypeId {
    const call = self.ast_unit.exprs.get(.Call, call_id);
    const callee_kind = self.ast_unit.exprs.index.kinds.items[call.callee.toRaw()];
    if (callee_kind != .Ident) return null;

    const callee_ident = self.ast_unit.exprs.get(.Ident, call.callee);
    const sym_id = self.lookup(callee_ident.name) orelse return null;
    const sym = self.symtab.syms.get(sym_id);
    if (sym.origin_decl.isNone()) return null;

    const decl_id = sym.origin_decl.unwrap();
    const decl = self.ast_unit.exprs.Decl.get(decl_id);
    const value_kind = self.ast_unit.exprs.index.kinds.items[decl.value.toRaw()];
    if (value_kind != .FunctionLit) return null;

    const fn_lit = self.ast_unit.exprs.get(.FunctionLit, decl.value);
    const params = self.ast_unit.exprs.param_pool.slice(fn_lit.params);
    const args = self.ast_unit.exprs.expr_pool.slice(call.args);
    if (params.len != args.len) return null;

    var bindings_builder: std.ArrayList(Binding) = .empty;
    defer bindings_builder.deinit(self.gpa);
    if (existing_bindings.len > 0) {
        try bindings_builder.appendSlice(self.gpa, existing_bindings);
    }

    var i: usize = 0;
    while (i < params.len) : (i += 1) {
        const param = self.ast_unit.exprs.Param.get(params[i]);
        if (!param.is_comptime or param.pat.isNone() or param.ty.isNone()) return null;

        const pat_id = param.pat.unwrap();
        if (self.ast_unit.pats.index.kinds.items[pat_id.toRaw()] != .Binding) return null;
        const pname = self.ast_unit.pats.get(.Binding, pat_id).name;

        const annotated = (try typeFromTypeExpr(self, param.ty.unwrap())) orelse return null;
        if (self.context.type_store.getKind(annotated) == .TypeType) {
            const arg_ty = (try typeFromTypeExprWithBindings(self, args[i], bindings_builder.items)) orelse return null;
            try bindings_builder.append(self.gpa, .{ .Type = .{ .name = pname, .ty = arg_ty } });
        } else {
            const arg_expr = args[i];
            const arg_kind = self.ast_unit.exprs.index.kinds.items[arg_expr.toRaw()];

            var have_value = false;
            var value: comp.ComptimeValue = undefined;

            if (arg_kind == .Ident) {
                const ident_name = self.ast_unit.exprs.get(.Ident, arg_expr).name;
                if (lookupValueBinding(bindings_builder.items, ident_name)) |existing| {
                    value = existing;
                    have_value = true;
                }
            }

            if (!have_value) {
                value = blk: {
                    const computed = evalComptimeValueWithBindings(self, arg_expr, annotated, bindings_builder.items) catch {
                        if (arg_kind == .Literal) {
                            const literal_val = (try evalLiteralToComptime(self, arg_expr)) orelse return null;
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
    if (self.ast_unit.exprs.index.kinds.items[body_id.toRaw()] != .Block) return null;
    const block = self.ast_unit.exprs.get(.Block, body_id);
    const stmts = self.ast_unit.stmts.stmt_pool.slice(block.items);
    for (stmts) |sid| {
        if (self.ast_unit.stmts.index.kinds.items[sid.toRaw()] != .Return) continue;
        const ret = self.ast_unit.stmts.get(.Return, sid);
        if (ret.value.isNone()) return null;
        const resolved = try typeFromTypeExprWithBindings(self, ret.value.unwrap(), bindings_builder.items);
        if (resolved) |ty| {
            try self.type_info.ensureExpr(self.gpa, call_id);
            const type_ty = self.context.type_store.mkTypeType(ty);
            self.type_info.expr_types.items[call_id.toRaw()] = type_ty;
            return ty;
        }
        return null;
    }
    return null;
}

pub fn typeFromTypeExpr(self: *Checker, id: ast.ExprId) anyerror!?types.TypeId {
    const k = self.ast_unit.exprs.index.kinds.items[id.toRaw()];
    return switch (k) {
        .Ident => blk_ident: {
            const name = self.ast_unit.exprs.get(.Ident, id).name;
            const s = self.ast_unit.exprs.strs.get(name);
            if (std.mem.eql(u8, s, "bool")) break :blk_ident self.context.type_store.tBool();
            if (std.mem.eql(u8, s, "i8")) break :blk_ident self.context.type_store.tI8();
            if (std.mem.eql(u8, s, "i16")) break :blk_ident self.context.type_store.tI16();
            if (std.mem.eql(u8, s, "i32")) break :blk_ident self.context.type_store.tI32();
            if (std.mem.eql(u8, s, "i64")) break :blk_ident self.context.type_store.tI64();
            if (std.mem.eql(u8, s, "u8")) break :blk_ident self.context.type_store.tU8();
            if (std.mem.eql(u8, s, "u16")) break :blk_ident self.context.type_store.tU16();
            if (std.mem.eql(u8, s, "u32")) break :blk_ident self.context.type_store.tU32();
            if (std.mem.eql(u8, s, "u64")) break :blk_ident self.context.type_store.tU64();
            if (std.mem.eql(u8, s, "f32")) break :blk_ident self.context.type_store.tF32();
            if (std.mem.eql(u8, s, "f64")) break :blk_ident self.context.type_store.tF64();
            if (std.mem.eql(u8, s, "usize")) break :blk_ident self.context.type_store.tUsize();
            if (std.mem.eql(u8, s, "char")) break :blk_ident self.context.type_store.tU32();
            if (std.mem.eql(u8, s, "string")) break :blk_ident self.context.type_store.tString();
            if (std.mem.eql(u8, s, "void")) break :blk_ident self.context.type_store.tVoid();
            if (std.mem.eql(u8, s, "any")) break :blk_ident self.context.type_store.tAny();
            if (std.mem.eql(u8, s, "type"))
                break :blk_ident self.context.type_store.mkTypeType(self.context.type_store.tAny());

            if (self.lookup(name)) |sid| {
                const sym = self.symtab.syms.get(sid);
                if (!sym.origin_decl.isNone()) {
                    const did = sym.origin_decl.unwrap();
                    if (self.type_info.decl_types.items[did.toRaw()]) |ty| {
                        const kind = self.context.type_store.index.kinds.items[ty.toRaw()];
                        if (kind == .TypeType) {
                            const tt = self.context.type_store.get(.TypeType, ty);
                            if (self.context.type_store.getKind(tt.of) != .Any) {
                                return tt.of;
                            }
                        } else {
                            return ty;
                        }
                    }
                    // Lazy resolve: if the declaration's RHS is a type expression, resolve it now.
                    const drow = self.ast_unit.exprs.Decl.get(did);
                    const rhs_ty = try typeFromTypeExpr(self, drow.value);
                    if (rhs_ty) |rt| {
                        // Record as a type constant for future queries
                        const tt = self.context.type_store.mkTypeType(rt);
                        self.type_info.decl_types.items[did.toRaw()] = tt;
                        try self.type_info.ensureExpr(self.gpa, drow.value);
                        self.type_info.expr_types.items[drow.value.toRaw()] = tt;
                        return rt;
                    }
                }
                if (!sym.origin_param.isNone()) {
                    const pid = sym.origin_param.unwrap();
                    const param_row = self.ast_unit.exprs.Param.get(pid);
                    if (!param_row.ty.isNone()) {
                        const annotated = (try typeFromTypeExpr(self, param_row.ty.unwrap())) orelse return null;
                        if (param_row.is_comptime) {
                            if (self.context.type_store.getKind(annotated) == .TypeType) {
                                return self.context.type_store.get(.TypeType, annotated).of;
                            }
                            return annotated;
                        }
                        return annotated;
                    }
                    return self.context.type_store.tAny();
                }
            }

            break :blk_ident null;
        },
        .MlirBlock => blk: {
            const row = self.ast_unit.exprs.get(.MlirBlock, id);
            const ts = &self.context.type_store;
            break :blk switch (row.kind) {
                .Type => ts.tMlirType(),
                .Attribute => ts.tMlirAttribute(),
                .Module => ts.tMlirModule(),
                .Operation => blk_inner: {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .mlir_block_not_a_type, .{});
                    break :blk_inner null;
                },
            };
        },
        .TupleType => blk_tt: {
            const row = self.ast_unit.exprs.get(.TupleType, id);
            const ids = self.ast_unit.exprs.expr_pool.slice(row.elems);
            var buf = try self.context.type_store.gpa.alloc(types.TypeId, ids.len);
            defer self.context.type_store.gpa.free(buf);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) buf[i] = (try typeFromTypeExpr(self, ids[i])) orelse break :blk_tt null;
            break :blk_tt self.context.type_store.mkTuple(buf);
        },
        .TupleLit => blk_ttl: {
            const row = self.ast_unit.exprs.get(.TupleLit, id);
            const ids = self.ast_unit.exprs.expr_pool.slice(row.elems);
            var buf = try self.context.type_store.gpa.alloc(types.TypeId, ids.len);
            defer self.context.type_store.gpa.free(buf);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) buf[i] = (try typeFromTypeExpr(self, ids[i])) orelse break :blk_ttl null;
            break :blk_ttl self.context.type_store.mkTuple(buf);
        },
        .MapType => blk_mt: {
            const row = self.ast_unit.exprs.get(.MapType, id);
            const key = (try typeFromTypeExpr(self, row.key)) orelse break :blk_mt null;
            const val = (try typeFromTypeExpr(self, row.value)) orelse break :blk_mt null;
            break :blk_mt self.context.type_store.mkMap(key, val);
        },
        .ArrayType => blk_at: {
            const row = self.ast_unit.exprs.get(.ArrayType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_at null;
            const size_expr_kind = self.ast_unit.exprs.index.kinds.items[row.size.toRaw()];
            var size: types.ArraySize = .{ .Unresolved = row.size };
            if (size_expr_kind == .Literal) {
                const lit = self.ast_unit.exprs.get(.Literal, row.size);
                if (lit.kind == .int) {
                    const info = switch (lit.data) {
                        .int => |i| i,
                        else => unreachable,
                    };
                    if (info.valid) {
                        const len = std.math.cast(usize, info.value) orelse {
                            try self.context.diags.addError(self.ast_unit.exprs.locs.get(lit.loc), .array_size_not_integer_literal, .{});
                            break :blk_at null;
                        };
                        size = .{ .Concrete = len };
                    }
                }
            }
            break :blk_at self.context.type_store.mkArray(elem, size);
        },
        .DynArrayType => blk_dt: {
            const row = self.ast_unit.exprs.get(.DynArrayType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_dt null;
            break :blk_dt self.context.type_store.mkDynArray(elem);
        },
        .SliceType => blk_st: {
            const row = self.ast_unit.exprs.get(.SliceType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_st null;
            break :blk_st self.context.type_store.mkSlice(elem);
        },
        .OptionalType => blk_ot: {
            const row = self.ast_unit.exprs.get(.OptionalType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_ot null;
            break :blk_ot self.context.type_store.mkOptional(elem);
        },
        .PointerType => blk_pt: {
            const row = self.ast_unit.exprs.get(.PointerType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_pt null;
            break :blk_pt self.context.type_store.mkPtr(elem, row.is_const);
        },
        .SimdType => blk_simd: {
            const row = self.ast_unit.exprs.get(.SimdType, id);
            const elem_ty = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_simd null;
            const ek = self.context.type_store.index.kinds.items[elem_ty.toRaw()];
            if (!isNumericKind(self, ek)) {
                try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_invalid_element_type, .{});
                break :blk_simd null;
            }
            const lk = self.ast_unit.exprs.index.kinds.items[row.lanes.toRaw()];
            if (lk != .Literal) {
                try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                break :blk_simd null;
            }
            const lit = self.ast_unit.exprs.get(.Literal, row.lanes);
            if (lit.kind != .int) {
                try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                break :blk_simd null;
            }
            const lanes_val = switch (lit.data) {
                .int => |int_info| blk: {
                    if (!int_info.valid) break :blk 0;
                    break :blk std.math.cast(usize, int_info.value) orelse 0;
                },
                else => 0,
            };
            if (lanes_val == 0) {
                try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                break :blk_simd null;
            }
            break :blk_simd self.context.type_store.tAny();
        },
        .TensorType => blk_tensor: {
            const row = self.ast_unit.exprs.get(.TensorType, id);
            // Validate shape dimensions are integer literals
            const dims = self.ast_unit.exprs.expr_pool.slice(row.shape);
            if (dims.len > types.max_tensor_rank) {
                try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_rank_exceeds_limit, .{});
                break :blk_tensor null;
            }
            var dim_values = [_]usize{0} ** types.max_tensor_rank;
            var i: usize = 0;
            while (i < dims.len) : (i += 1) {
                const dk = self.ast_unit.exprs.index.kinds.items[dims[i].toRaw()];
                if (dk != .Literal) {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    break :blk_tensor null;
                }
                const dl = self.ast_unit.exprs.get(.Literal, dims[i]);
                if (dl.kind != .int) {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    break :blk_tensor null;
                }
                const info = switch (dl.data) {
                    .int => |int_info| int_info,
                    else => return null,
                };
                if (!info.valid) {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    break :blk_tensor null;
                }
                const dim_val = std.math.cast(usize, info.value) orelse {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    break :blk_tensor null;
                };
                dim_values[i] = dim_val;
            }
            // Validate element type present and resolvable
            const ety = try typeFromTypeExpr(self, row.elem);
            if (ety == null) {
                try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_missing_element_type, .{});
                break :blk_tensor null;
            }
            const rank = dims.len;
            const tensor_ty = self.context.type_store.mkTensor(ety.?, dim_values[0..rank]);
            break :blk_tensor tensor_ty;
        },
        .StructType => blk_sty: {
            const row = self.ast_unit.exprs.get(.StructType, id);
            const sfs = self.ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try self.context.type_store.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer self.context.type_store.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const f = self.ast_unit.exprs.StructField.get(sfs[i]);
                const gop = try seen.getOrPut(self.gpa, f.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(f.loc), .duplicate_field, .{});
                    return null;
                }
                const ft = (try typeFromTypeExpr(self, f.ty)) orelse break :blk_sty null;
                buf[i] = .{ .name = f.name, .ty = ft };
            }
            break :blk_sty self.context.type_store.mkStruct(buf);
        },
        .UnionType => blk_un: {
            const row = self.ast_unit.exprs.get(.UnionType, id);
            const sfs = self.ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try self.context.type_store.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer self.context.type_store.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const sf = self.ast_unit.exprs.StructField.get(sfs[i]);
                const gop = try seen.getOrPut(self.gpa, sf.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(sf.loc), .duplicate_field, .{});
                    return null;
                }
                // Validate field types resolve
                const ft = (try typeFromTypeExpr(self, sf.ty)) orelse break :blk_un null;
                buf[i] = .{ .name = sf.name, .ty = ft };
            }
            break :blk_un self.context.type_store.mkUnion(buf);
        },

        .EnumType => blk_en: {
            const row = self.ast_unit.exprs.get(.EnumType, id);
            const efs = self.ast_unit.exprs.efield_pool.slice(row.fields);

            const tag_ty = if (row.discriminant.isNone())
                self.context.type_store.tI32()
            else
                (try typeFromTypeExpr(self, row.discriminant.unwrap())) orelse return null;

            // Ensure the tag type is an integer.
            const tk = self.context.type_store.index.kinds.items[tag_ty.toRaw()];
            if (!isIntegerKind(self, tk)) {
                try self.context.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .enum_discriminant_not_integer, .{});
                break :blk_en null;
            }

            var member_buf = try self.gpa.alloc(types.TypeStore.EnumMemberArg, efs.len);
            defer self.gpa.free(member_buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);

            var next_value: u64 = 0;
            var i: usize = 0;
            while (i < efs.len) : (i += 1) {
                const enum_field = self.ast_unit.exprs.EnumField.get(efs[i]);

                const gop = try seen.getOrPut(self.gpa, enum_field.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .duplicate_enum_field, .{});
                    return null;
                }

                var current_value: u64 = next_value;
                if (!enum_field.value.isNone()) {
                    const val_id = enum_field.value.unwrap();
                    const val_kind = self.ast_unit.exprs.index.kinds.items[val_id.toRaw()];
                    if (val_kind != .Literal) {
                        try self.context.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                        return null;
                    }
                    const lit = self.ast_unit.exprs.get(.Literal, val_id);
                    if (lit.kind != .int) {
                        try self.context.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                        return null;
                    }
                    const parsed = switch (lit.data) {
                        .int => |int_info| blk: {
                            if (!int_info.valid) {
                                try self.context.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .invalid_integer_literal, .{});
                                break :blk null;
                            }
                            const casted = std.math.cast(u64, int_info.value) orelse {
                                try self.context.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .invalid_integer_literal, .{});
                                break :blk null;
                            };
                            break :blk casted;
                        },
                        else => blk: {
                            try self.context.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                            break :blk null;
                        },
                    };
                    if (parsed == null) return null;
                    current_value = parsed.?;
                }

                member_buf[i] = .{ .name = enum_field.name, .value = current_value };
                next_value = current_value + 1;
            }
            break :blk_en self.context.type_store.mkEnum(member_buf, tag_ty);
        },
        .ErrorType => blk_err: {
            const row = self.ast_unit.exprs.get(.ErrorType, id);
            const vfs = self.ast_unit.exprs.vfield_pool.slice(row.fields);
            var case_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
            defer self.gpa.free(case_buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);

            var i: usize = 0;
            while (i < vfs.len) : (i += 1) {
                const vf = self.ast_unit.exprs.VariantField.get(vfs[i]);
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(vf.loc), .duplicate_error_variant, .{});
                    return null;
                }

                const payload_ty = switch (vf.payload_kind) {
                    .none => self.context.type_store.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) {
                            break :blk_tuple self.context.type_store.tVoid();
                        }
                        const elems = self.ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        var j: usize = 0;
                        while (j < elems.len) : (j += 1) {
                            elem_buf[j] = (try typeFromTypeExpr(self, elems[j])) orelse return null;
                        }
                        break :blk_tuple self.context.type_store.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) {
                            break :blk_struct self.context.type_store.tVoid();
                        }
                        const fields = self.ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        var j: usize = 0;
                        while (j < fields.len) : (j += 1) {
                            const sf = self.ast_unit.exprs.StructField.get(fields[j]);
                            field_buf[j] = .{
                                .name = sf.name,
                                .ty = (try typeFromTypeExpr(self, sf.ty)) orelse return null,
                            };
                        }
                        break :blk_struct self.context.type_store.mkStruct(field_buf);
                    },
                };
                case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
            }
            break :blk_err self.context.type_store.mkError(case_buf);
        },
        .ErrorSetType => blk_est: {
            const row = self.ast_unit.exprs.get(.ErrorSetType, id);
            const val_ty = try typeFromTypeExpr(self, row.value);
            const err_ty = try typeFromTypeExpr(self, row.err);
            if (val_ty == null or err_ty == null) break :blk_est null;
            break :blk_est self.context.type_store.mkErrorSet(val_ty.?, err_ty.?);
        },
        .VariantType => blk_var: {
            const row = self.ast_unit.exprs.get(.VariantType, id);
            const vfs = self.ast_unit.exprs.vfield_pool.slice(row.fields);
            var case_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
            defer self.gpa.free(case_buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);

            var i: usize = 0;
            while (i < vfs.len) : (i += 1) {
                const vf = self.ast_unit.exprs.VariantField.get(vfs[i]);
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(vf.loc), .duplicate_variant, .{});
                    return null;
                }

                const payload_ty = switch (vf.payload_kind) {
                    .none => self.context.type_store.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) {
                            break :blk_tuple self.context.type_store.tVoid();
                        }
                        const elems = self.ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        var j: usize = 0;
                        while (j < elems.len) : (j += 1) {
                            elem_buf[j] = (try typeFromTypeExpr(self, elems[j])) orelse return null;
                        }
                        break :blk_tuple self.context.type_store.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) {
                            break :blk_struct self.context.type_store.tVoid();
                        }
                        const fields = self.ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        var j: usize = 0;
                        while (j < fields.len) : (j += 1) {
                            const sf = self.ast_unit.exprs.StructField.get(fields[j]);
                            field_buf[j] = .{
                                .name = sf.name,
                                .ty = (try typeFromTypeExpr(self, sf.ty)) orelse return null,
                            };
                        }
                        break :blk_struct self.context.type_store.mkStruct(field_buf);
                    },
                };
                case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
            }
            break :blk_var self.context.type_store.mkVariant(case_buf);
        },

        .FunctionLit => blk_fn: {
            // function type in type position
            const fnr = self.ast_unit.exprs.get(.FunctionLit, id);
            const params = self.ast_unit.exprs.param_pool.slice(fnr.params);
            var pbuf = try self.gpa.alloc(types.TypeId, params.len);
            defer self.gpa.free(pbuf);
            var i: usize = 0;
            while (i < params.len) : (i += 1) {
                const p = self.ast_unit.exprs.Param.get(params[i]);
                if (p.ty.isNone()) break :blk_fn null;
                const pt = (try typeFromTypeExpr(self, p.ty.unwrap())) orelse break :blk_fn null;
                pbuf[i] = pt;
            }
            const res = if (!fnr.result_ty.isNone()) (try typeFromTypeExpr(self, fnr.result_ty.unwrap())) else self.context.type_store.tVoid();
            if (res == null) break :blk_fn null;
            const is_pure = !fnr.flags.is_proc;
            break :blk_fn self.context.type_store.mkFunction(pbuf, res.?, fnr.flags.is_variadic, is_pure);
        },
        .FieldAccess => blk_fa: {
            const fr = self.ast_unit.exprs.get(.FieldAccess, id);
            const parent_expr_kind = self.ast_unit.exprs.index.kinds.items[fr.parent.toRaw()];

            if (parent_expr_kind == .Import) {
                if (self.importMemberType(fr.parent, fr.field)) |mt| {
                    const mt_kind = self.context.type_store.index.kinds.items[mt.toRaw()];
                    break :blk_fa if (mt_kind == .TypeType)
                        self.context.type_store.get(.TypeType, mt).of
                    else
                        mt;
                }
                try self.context.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_module_field, .{});
                break :blk_fa null;
            }

            if (parent_expr_kind == .Ident) {
                const idr = self.ast_unit.exprs.get(.Ident, fr.parent);
                if (self.lookup(idr.name)) |sid_sym| {
                    const sym = self.symtab.syms.get(sid_sym);
                    if (!sym.origin_decl.isNone()) {
                        const did = sym.origin_decl.unwrap();
                        const drow = self.ast_unit.exprs.Decl.get(did);
                        if (self.ast_unit.exprs.index.kinds.items[drow.value.toRaw()] == .Import) {
                            if (self.importMemberType(drow.value, fr.field)) |mt| {
                                const mt_kind = self.context.type_store.index.kinds.items[mt.toRaw()];
                                break :blk_fa if (mt_kind == .TypeType)
                                    self.context.type_store.get(.TypeType, mt).of
                                else
                                    mt;
                            }
                            try self.context.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_module_field, .{});
                            break :blk_fa null;
                        }
                    }
                }
            }

            const parent_ty = (try typeFromTypeExpr(self, fr.parent)) orelse break :blk_fa null;
            const parent_kind = self.context.type_store.index.kinds.items[parent_ty.toRaw()];
            switch (parent_kind) {
                .Struct => {
                    const st = self.context.type_store.get(.Struct, parent_ty);
                    const fields = self.context.type_store.field_pool.slice(st.fields);
                    var i: usize = 0;
                    while (i < fields.len) : (i += 1) {
                        const f = fields[i];
                        const field = self.context.type_store.Field.get(f);
                        if (field.name.toRaw() == fr.field.toRaw()) return field.ty;
                    }
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{});
                    break :blk_fa null;
                },
                .Variant => {
                    if (variantPayloadType(self, parent_ty, fr.field)) |pt| return pt;
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_variant_tag, .{});
                    break :blk_fa null;
                },
                .Enum => {
                    const et = self.context.type_store.get(.Enum, parent_ty);
                    const members = self.context.type_store.enum_member_pool.slice(et.members);
                    var i: usize = 0;
                    while (i < members.len) : (i += 1) {
                        const member = self.context.type_store.EnumMember.get(members[i]);
                        if (member.name.toRaw() == fr.field.toRaw()) {
                            return parent_ty;
                        }
                    }
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{});
                    break :blk_fa null;
                },
                else => {
                    try self.context.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .field_access_on_non_aggregate, .{});
                    break :blk_fa null;
                },
            }
        },
        .Call => try resolveTypeFunctionCall(self, id, &[_]Binding{}),
        .AnyType => self.context.type_store.tAny(),
        .TypeType => self.context.type_store.tType(),
        .NoreturnType => self.context.type_store.tNoReturn(),
        else => null,
    };
}
