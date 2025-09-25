const Checker = @import("checker.zig").Checker;
const types = @import("types.zig");
const ast = @import("ast.zig");
const std = @import("std");

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
    const k = self.type_info.store.index.kinds.items[ty_id.toRaw()];
    return switch (k) {
        .I8, .U8 => 1,
        .I16, .U16 => 2,
        .I32, .U32, .F32 => 4,
        .I64, .U64, .F64, .Usize => 8, // Assuming usize is 8 bytes for 64-bit
        .Bool => 1, // Typically 1 byte
        .Ptr => 8, // Assuming 64-bit pointers
        .Void => 0, // No size
        .Any => null, // Unknown size
        .String => 8, // Assuming string is a pointer (8 bytes) for 64-bit (TODO: more complex)
        .Array => {
            const arr = self.type_info.store.Array.get(self.type_info.store.index.rows.items[ty_id.toRaw()]);
            const elem_size = typeSize(self, arr.elem) orelse return null;
            return elem_size * arr.len;
        },
        .Slice => 16, // Pointer + length (assuming 64-bit)
        .Optional => {
            const opt = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[ty_id.toRaw()]);
            const elem_size = typeSize(self, opt.elem) orelse return null;
            return elem_size + 1; // Element size + 1 byte for discriminant
        },
        // TODO: Implement for other aggregate types like Struct, Tuple, Union, etc.
        else => null, // Unknown or complex size
    };
}

pub fn isOptional(self: *Checker, id: types.TypeId) ?types.TypeId {
    const k = self.type_info.store.index.kinds.items[id.toRaw()];
    if (k != .Optional) return null;
    const opt = self.type_info.store.Optional.get(self.type_info.store.index.rows.items[id.toRaw()]);
    return opt.elem;
}

pub fn checkTypeOf(self: *Checker, id: ast.ExprId) !?types.TypeId {
    const tr = self.ast_unit.exprs.get(.TypeOf, id);
    // typeof should accept value expressions; get their type directly.
    if (try self.checkExpr(tr.expr)) |et| {
        return self.type_info.store.mkTypeType(et);
    }
    // As a fallback, allow typeof on a type expression (yielding that type).
    if (try typeFromTypeExpr(self, tr.expr)) |tt| {
        return self.type_info.store.mkTypeType(tt);
    }
    try self.diags.addError(self.ast_unit.exprs.locs.get(tr.loc), .could_not_resolve_type, .{});
    return null;
}

// =========================================================
// Type expressions
// =========================================================
pub fn typeFromTypeExpr(self: *Checker, id: ast.ExprId) anyerror!?types.TypeId {
    const k = self.ast_unit.exprs.index.kinds.items[id.toRaw()];
    return switch (k) {
        .Ident => blk_ident: {
            const name = self.ast_unit.exprs.get(.Ident, id).name;
            const s = self.ast_unit.exprs.strs.get(name);
            if (std.mem.eql(u8, s, "bool")) break :blk_ident self.type_info.store.tBool();
            if (std.mem.eql(u8, s, "i8")) break :blk_ident self.type_info.store.tI8();
            if (std.mem.eql(u8, s, "i16")) break :blk_ident self.type_info.store.tI16();
            if (std.mem.eql(u8, s, "i32")) break :blk_ident self.type_info.store.tI32();
            if (std.mem.eql(u8, s, "i64")) break :blk_ident self.type_info.store.tI64();
            if (std.mem.eql(u8, s, "u8")) break :blk_ident self.type_info.store.tU8();
            if (std.mem.eql(u8, s, "u16")) break :blk_ident self.type_info.store.tU16();
            if (std.mem.eql(u8, s, "u32")) break :blk_ident self.type_info.store.tU32();
            if (std.mem.eql(u8, s, "u64")) break :blk_ident self.type_info.store.tU64();
            if (std.mem.eql(u8, s, "f32")) break :blk_ident self.type_info.store.tF32();
            if (std.mem.eql(u8, s, "f64")) break :blk_ident self.type_info.store.tF64();
            if (std.mem.eql(u8, s, "usize")) break :blk_ident self.type_info.store.tUsize();
            if (std.mem.eql(u8, s, "char")) break :blk_ident self.type_info.store.tU32();
            if (std.mem.eql(u8, s, "string")) break :blk_ident self.type_info.store.tString();
            if (std.mem.eql(u8, s, "void")) break :blk_ident self.type_info.store.tVoid();
            if (std.mem.eql(u8, s, "any")) break :blk_ident self.type_info.store.tAny();

            if (self.lookup(name)) |sid| {
                const sym = self.symtab.syms.get(sid.toRaw());
                if (!sym.origin_decl.isNone()) {
                    const did = sym.origin_decl.unwrap();
                    if (self.type_info.decl_types.items[did.toRaw()]) |ty| {
                        if (self.type_info.store.index.kinds.items[ty.toRaw()] == .TypeType) {
                            const tt = self.type_info.store.TypeType.get(self.type_info.store.index.rows.items[ty.toRaw()]);
                            return tt.of;
                        }
                        return ty;
                    }
                    // Lazy resolve: if the declaration's RHS is a type expression, resolve it now.
                    const drow = self.ast_unit.exprs.Decl.get(did.toRaw());
                    const rhs_ty = try typeFromTypeExpr(self, drow.value);
                    if (rhs_ty) |rt| {
                        // Record as a type constant for future queries
                        const tt = self.type_info.store.mkTypeType(rt);
                        self.type_info.decl_types.items[did.toRaw()] = tt;
                        return rt;
                    }
                }
            }

            break :blk_ident null;
        },
        .TupleType => blk_tt: {
            const row = self.ast_unit.exprs.get(.TupleType, id);
            const ids = self.ast_unit.exprs.expr_pool.slice(row.elems);
            var buf = try self.type_info.store.gpa.alloc(types.TypeId, ids.len);
            defer self.type_info.store.gpa.free(buf);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) buf[i] = (try typeFromTypeExpr(self, ids[i])) orelse break :blk_tt null;
            break :blk_tt self.type_info.store.mkTuple(buf);
        },
        .TupleLit => blk_ttl: {
            const row = self.ast_unit.exprs.get(.TupleLit, id);
            const ids = self.ast_unit.exprs.expr_pool.slice(row.elems);
            var buf = try self.type_info.store.gpa.alloc(types.TypeId, ids.len);
            defer self.type_info.store.gpa.free(buf);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) buf[i] = (try typeFromTypeExpr(self, ids[i])) orelse break :blk_ttl null;
            break :blk_ttl self.type_info.store.mkTuple(buf);
        },
        .MapType => blk_mt: {
            const row = self.ast_unit.exprs.get(.MapType, id);
            const key = (try typeFromTypeExpr(self, row.key)) orelse break :blk_mt null;
            const val = (try typeFromTypeExpr(self, row.value)) orelse break :blk_mt null;
            break :blk_mt self.type_info.store.mkMap(key, val);
        },
        .ArrayType => blk_at: {
            const row = self.ast_unit.exprs.get(.ArrayType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_at null;
            var len_val: usize = 0;
            if (self.ast_unit.exprs.index.kinds.items[row.size.toRaw()] == .Literal) {
                const lit = self.ast_unit.exprs.get(.Literal, row.size);
                if (lit.kind == .int and !lit.value.isNone()) {
                    len_val = std.fmt.parseInt(usize, self.ast_unit.exprs.strs.get(lit.value.unwrap()), 10) catch 0;
                } else {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .array_size_not_integer_literal, .{});
                    return null;
                }
            } else return error.InvalidArraySize;
            break :blk_at self.type_info.store.mkArray(elem, len_val);
        },
        .DynArrayType => blk_dt: {
            const row = self.ast_unit.exprs.get(.DynArrayType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_dt null;
            break :blk_dt self.type_info.store.mkDynArray(elem);
        },
        .SliceType => blk_st: {
            const row = self.ast_unit.exprs.get(.SliceType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_st null;
            break :blk_st self.type_info.store.mkSlice(elem);
        },
        .OptionalType => blk_ot: {
            const row = self.ast_unit.exprs.get(.OptionalType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_ot null;
            break :blk_ot self.type_info.store.mkOptional(elem);
        },
        .PointerType => blk_pt: {
            const row = self.ast_unit.exprs.get(.PointerType, id);
            const elem = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_pt null;
            break :blk_pt self.type_info.store.mkPtr(elem, row.is_const);
        },
        .SimdType => blk_simd: {
            const row = self.ast_unit.exprs.get(.SimdType, id);
            // element type must be numeric (int or float)
            const elem_ty = (try typeFromTypeExpr(self, row.elem)) orelse break :blk_simd null;
            const ek = self.type_info.store.index.kinds.items[elem_ty.toRaw()];
            if (!isNumericKind(self, ek)) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_invalid_element_type, .{});
                break :blk_simd null;
            }
            // lanes must be an integer literal
            const lk = self.ast_unit.exprs.index.kinds.items[row.lanes.toRaw()];
            if (lk != .Literal) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                break :blk_simd null;
            }
            const lit = self.ast_unit.exprs.get(.Literal, row.lanes);
            if (lit.kind != .int) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                break :blk_simd null;
            }
            // Accept the type (we don't model concrete simd in TypeStore yet)
            break :blk_simd self.type_info.store.tAny();
        },
        .TensorType => blk_tensor: {
            const row = self.ast_unit.exprs.get(.TensorType, id);
            // Validate shape dimensions are integer literals
            const dims = self.ast_unit.exprs.expr_pool.slice(row.shape);
            var i: usize = 0;
            while (i < dims.len) : (i += 1) {
                const dk = self.ast_unit.exprs.index.kinds.items[dims[i].toRaw()];
                if (dk != .Literal) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    break :blk_tensor null;
                }
                const dl = self.ast_unit.exprs.get(.Literal, dims[i]);
                if (dl.kind != .int) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    break :blk_tensor null;
                }
            }
            // Validate element type present and resolvable
            const ety = try typeFromTypeExpr(self, row.elem);
            if (ety == null) {
                try self.diags.addError(self.ast_unit.exprs.locs.get(row.loc), .tensor_missing_arguments, .{});
                break :blk_tensor null;
            }
            break :blk_tensor self.type_info.store.tAny();
        },
        .StructType => blk_sty: {
            const row = self.ast_unit.exprs.get(.StructType, id);
            const sfs = self.ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try self.type_info.store.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer self.type_info.store.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const f = self.ast_unit.exprs.StructField.get(sfs[i].toRaw());
                const gop = try seen.getOrPut(self.gpa, f.name.toRaw());
                if (gop.found_existing) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(f.loc), .duplicate_field, .{});
                    return null;
                }
                const ft = (try typeFromTypeExpr(self, f.ty)) orelse break :blk_sty null;
                buf[i] = .{ .name = f.name, .ty = ft };
            }
            break :blk_sty self.type_info.store.mkStruct(buf);
        },
        .UnionType => blk_un: {
            const row = self.ast_unit.exprs.get(.UnionType, id);
            const sfs = self.ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try self.type_info.store.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer self.type_info.store.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const sf = self.ast_unit.exprs.StructField.get(sfs[i].toRaw());
                const gop = try seen.getOrPut(self.gpa, sf.name.toRaw());
                if (gop.found_existing) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(sf.loc), .duplicate_field, .{});
                    return null;
                }
                // Validate field types resolve
                const ft = (try typeFromTypeExpr(self, sf.ty)) orelse break :blk_un null;
                buf[i] = .{ .name = sf.name, .ty = ft };
            }
            break :blk_un self.type_info.store.mkUnion(buf);
        },
        .EnumType => blk_en: {
            const row = self.ast_unit.exprs.get(.EnumType, id);
            const efs = self.ast_unit.exprs.efield_pool.slice(row.fields);

            const tag_ty = if (row.discriminant.isNone())
                self.type_info.store.tI32()
            else
                (try typeFromTypeExpr(self, row.discriminant.unwrap())) orelse return null;

            var member_buf = try self.gpa.alloc(types.TypeStore.EnumMemberArg, efs.len);
            defer self.gpa.free(member_buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, void){};
            defer seen.deinit(self.gpa);

            var next_value: u64 = 0;
            var i: usize = 0;
            while (i < efs.len) : (i += 1) {
                const enum_field = self.ast_unit.exprs.EnumField.get(efs[i].toRaw());
                const name = self.ast_unit.exprs.strs.get(enum_field.name);

                const gop = try seen.getOrPut(self.gpa, enum_field.name.toRaw());
                if (gop.found_existing) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .duplicate_enum_field, .{});
                    return null;
                }

                var current_value: u64 = next_value;
                if (!enum_field.value.isNone()) {
                    const val_id = enum_field.value.unwrap();
                    const val_kind = self.ast_unit.exprs.index.kinds.items[val_id.toRaw()];
                    if (val_kind != .Literal) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                        return null;
                    }
                    const lit = self.ast_unit.exprs.get(.Literal, val_id);
                    if (lit.kind != .int or lit.value.isNone()) {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                        return null;
                    }
                    const val_str = self.ast_unit.exprs.strs.get(lit.value.unwrap());
                    const parsed = std.fmt.parseInt(u64, val_str, 10) catch {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(enum_field.loc), .invalid_integer_literal, .{});
                        return null;
                    };
                    current_value = parsed;
                }

                member_buf[i] = .{ .name = name, .value = current_value };
                next_value = current_value + 1;
            }
            break :blk_en self.type_info.store.mkEnum(member_buf, tag_ty);
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
                const vf = self.ast_unit.exprs.VariantField.get(vfs[i].toRaw());
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(vf.loc), .duplicate_error_variant, .{});
                    return null;
                }

                const payload_ty = switch (vf.payload_kind) {
                    .none => self.type_info.store.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) {
                            break :blk_tuple self.type_info.store.tVoid();
                        }
                        const elems = self.ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        var j: usize = 0;
                        while (j < elems.len) : (j += 1) {
                            elem_buf[j] = (try typeFromTypeExpr(self, elems[j])) orelse return null;
                        }
                        break :blk_tuple self.type_info.store.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) {
                            break :blk_struct self.type_info.store.tVoid();
                        }
                        const fields = self.ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        var j: usize = 0;
                        while (j < fields.len) : (j += 1) {
                            const sf = self.ast_unit.exprs.StructField.get(fields[j].toRaw());
                            field_buf[j] = .{
                                .name = sf.name,
                                .ty = (try typeFromTypeExpr(self, sf.ty)) orelse return null,
                            };
                        }
                        break :blk_struct self.type_info.store.mkStruct(field_buf);
                    },
                };
                case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
            }
            break :blk_err self.type_info.store.mkError(case_buf);
        },
        .ErrorSetType => blk_est: {
            const row = self.ast_unit.exprs.get(.ErrorSetType, id);
            const val_ty = try typeFromTypeExpr(self, row.value);
            const err_ty = try typeFromTypeExpr(self, row.err);
            if (val_ty == null or err_ty == null) break :blk_est null;
            break :blk_est self.type_info.store.mkErrorSet(val_ty.?, err_ty.?);
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
                const vf = self.ast_unit.exprs.VariantField.get(vfs[i].toRaw());
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(vf.loc), .duplicate_variant, .{});
                    return null;
                }

                const payload_ty = switch (vf.payload_kind) {
                    .none => self.type_info.store.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) {
                            break :blk_tuple self.type_info.store.tVoid();
                        }
                        const elems = self.ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        var j: usize = 0;
                        while (j < elems.len) : (j += 1) {
                            elem_buf[j] = (try typeFromTypeExpr(self, elems[j])) orelse return null;
                        }
                        break :blk_tuple self.type_info.store.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) {
                            break :blk_struct self.type_info.store.tVoid();
                        }
                        const fields = self.ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        var j: usize = 0;
                        while (j < fields.len) : (j += 1) {
                            const sf = self.ast_unit.exprs.StructField.get(fields[j].toRaw());
                            field_buf[j] = .{
                                .name = sf.name,
                                .ty = (try typeFromTypeExpr(self, sf.ty)) orelse return null,
                            };
                        }
                        break :blk_struct self.type_info.store.mkStruct(field_buf);
                    },
                };
                case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
            }
            break :blk_var self.type_info.store.mkVariant(case_buf);
        },

        .FunctionLit => blk_fn: {
            // function type in type position
            const fnr = self.ast_unit.exprs.get(.FunctionLit, id);
            const params = self.ast_unit.exprs.param_pool.slice(fnr.params);
            var pbuf = try self.gpa.alloc(types.TypeId, params.len);
            defer self.gpa.free(pbuf);
            var i: usize = 0;
            while (i < params.len) : (i += 1) {
                const p = self.ast_unit.exprs.Param.get(params[i].toRaw());
                if (p.ty.isNone()) break :blk_fn null;
                const pt = (try typeFromTypeExpr(self, p.ty.unwrap())) orelse break :blk_fn null;
                pbuf[i] = pt;
            }
            const res = if (!fnr.result_ty.isNone()) (try typeFromTypeExpr(self, fnr.result_ty.unwrap())) else self.type_info.store.tVoid();
            if (res == null) break :blk_fn null;
            const is_pure = !fnr.flags.is_proc;
            break :blk_fn self.type_info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic, is_pure);
        },
        .FieldAccess => blk_fa: {
            const fr = self.ast_unit.exprs.get(.FieldAccess, id);
            const parent_ty = (try typeFromTypeExpr(self, fr.parent)) orelse break :blk_fa null;
            const parent_kind = self.type_info.store.index.kinds.items[parent_ty.toRaw()];
            switch (parent_kind) {
                .Struct => {
                    const st = self.type_info.store.Struct.get(self.type_info.store.index.rows.items[parent_ty.toRaw()]);
                    const fields = self.type_info.store.field_pool.slice(st.fields);
                    var i: usize = 0;
                    while (i < fields.len) : (i += 1) {
                        const f = fields[i];
                        const field = self.type_info.store.Field.get(f.toRaw());
                        if (field.name.toRaw() == fr.field.toRaw()) return field.ty;
                    }
                    try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{});
                    break :blk_fa null;
                },
                // NEW: handle Variant directly (e.g., V2.C in type position).
                .Variant => {
                    const vt = self.type_info.store.Variant.get(self.type_info.store.index.rows.items[parent_ty.toRaw()]);
                    const cases = self.type_info.store.field_pool.slice(vt.variants);
                    var i: usize = 0;
                    while (i < cases.len) : (i += 1) {
                        const vc = self.type_info.store.Field.get(cases[i].toRaw());
                        if (vc.name.toRaw() == fr.field.toRaw()) {
                            // Return the payload type of the chosen variant (struct/tuple/void).
                            return vc.ty;
                        }
                    }
                    try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_variant_tag, .{});
                    break :blk_fa null;
                },
                .TypeType => {
                    // Back-compat in case a type value ever appears here:
                    const tt = self.type_info.store.TypeType.get(self.type_info.store.index.rows.items[parent_ty.toRaw()]);
                    const inner_kind = self.type_info.store.index.kinds.items[tt.of.toRaw()];
                    if (inner_kind == .Variant) {
                        const vt = self.type_info.store.Variant.get(self.type_info.store.index.rows.items[tt.of.toRaw()]);
                        const cases = self.type_info.store.field_pool.slice(vt.variants);
                        var i: usize = 0;
                        while (i < cases.len) : (i += 1) {
                            const vc = self.type_info.store.Field.get(cases[i].toRaw());
                            if (vc.name.toRaw() == fr.field.toRaw()) return vc.ty;
                        }
                        try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .unknown_variant_tag, .{});
                        break :blk_fa null;
                    } else {
                        try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .field_access_on_non_aggregate, .{});
                        break :blk_fa null;
                    }
                },
                else => {
                    try self.diags.addError(self.ast_unit.exprs.locs.get(fr.loc), .field_access_on_non_aggregate, .{});
                    break :blk_fa null;
                },
            }
        },
        .AnyType => self.type_info.store.tAny(),
        .TypeType => self.type_info.store.tType(),
        .NoreturnType => self.type_info.store.tNoReturn(),
        else => null,
    };
}

pub fn translateType(self: *Checker, src: *types.TypeStore, dst: *types.TypeStore, ty: types.TypeId) types.TypeId {
    const k = src.getKind(ty);
    return switch (k) {
        .Void => dst.tVoid(),
        .Bool => dst.tBool(),
        .I8 => dst.tI8(),
        .I16 => dst.tI16(),
        .I32 => dst.tI32(),
        .I64 => dst.tI64(),
        .U8 => dst.tU8(),
        .U16 => dst.tU16(),
        .U32 => dst.tU32(),
        .U64 => dst.tU64(),
        .F32 => dst.tF32(),
        .F64 => dst.tF64(),
        .Usize => dst.tUsize(),
        .String => dst.tString(),
        .Any => dst.tAny(),
        .Noreturn => dst.tNoReturn(),
        .Struct => blk: {
            const sr = src.get(.Struct, ty);
            const sfields = src.field_pool.slice(sr.fields);
            var buf = dst.gpa.alloc(types.TypeStore.StructFieldArg, sfields.len) catch @panic("OOM");
            defer dst.gpa.free(buf);
            var i: usize = 0;
            while (i < sfields.len) : (i += 1) {
                const f = src.Field.get(sfields[i].toRaw());
                buf[i] = .{ .name = f.name, .ty = translateType(self, src, dst, f.ty) };
            }
            break :blk dst.mkStruct(buf);
        },
        .Ptr => blk: {
            const pr = src.get(.Ptr, ty);
            const et = translateType(self, src, dst, pr.elem);
            break :blk dst.mkPtr(et, pr.is_const);
        },
        .Optional => blk: {
            const opt_row = src.get(.Optional, ty);
            const et = translateType(self, src, dst, opt_row.elem);
            break :blk dst.mkOptional(et);
        },
        .Function => blk: {
            const fr = src.get(.Function, ty);
            const params_src = src.type_pool.slice(fr.params);
            var buf = dst.gpa.alloc(types.TypeId, params_src.len) catch @panic("OOM");
            defer dst.gpa.free(buf);
            var i: usize = 0;
            while (i < params_src.len) : (i += 1) buf[i] = translateType(self, src, dst, params_src[i]);
            const res_t = translateType(self, src, dst, fr.result);
            break :blk dst.mkFunction(buf, res_t, fr.is_variadic, fr.is_pure);
        },
        else => dst.tAny(),
    };
}
