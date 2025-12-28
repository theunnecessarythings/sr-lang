const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const Codegen = @import("codegen_main.zig").Codegen;
const types = @import("types.zig");

// ===== ABI: x86_64 SysV =====

const AbiKind = enum { DirectScalar, DirectPair, IndirectByVal, IndirectSRet };

pub const AbiClass = struct {
    kind: AbiKind,
    scalar0: ?mlir.Type = null,
    scalar1: ?mlir.Type = null,
    alignment: u32 = 1,
    size: usize = 0,
};

const SizeAlign = struct {
    size: usize,
    alignment: usize,
    hasFloat: bool = false,
    allIntsOnly: bool = true,
};

pub fn abiSizeAlign(self: *Codegen, ty: types.TypeId) SizeAlign {
    const ts = self.context.type_store;
    switch (ts.getKind(ty)) {
        .Void => return .{ .size = 0, .alignment = 1 },
        .Bool, .I8, .U8 => return .{ .size = 1, .alignment = 1 },
        .I16, .U16 => return .{ .size = 2, .alignment = 2 },
        .I32, .U32, .F32 => return .{ .size = 4, .alignment = 4, .hasFloat = ts.getKind(ty) == .F32, .allIntsOnly = ts.getKind(ty) != .F32 },
        .I64, .U64, .Usize, .Ptr, .Any, .Code, .Function, .MlirModule, .MlirAttribute, .MlirType, .F64 => return .{ .size = 8, .alignment = 8, .hasFloat = ts.getKind(ty) == .F64, .allIntsOnly = ts.getKind(ty) != .F64 },

        .Simd => {
            const S = ts.get(.Simd, ty);
            const elem = abiSizeAlign(self, S.elem);
            return .{ .size = elem.size * S.lanes, .alignment = @max(16, elem.alignment), .hasFloat = elem.hasFloat, .allIntsOnly = elem.allIntsOnly };
        },
        .Map => return .{ .size = 32, .alignment = 8 },
        .String, .Slice => return .{ .size = 16, .alignment = 8 },
        .DynArray => return .{ .size = 24, .alignment = 8 },
        .Enum => return abiSizeAlign(self, ts.get(.Enum, ty).tag_type),
        .TypeType => {
            const ptr_size = if (@sizeOf(usize) >= 8) 8 else @sizeOf(usize);
            return .{ .size = ptr_size, .alignment = ptr_size };
        },
        .Noreturn => return .{ .size = 0, .alignment = 1 },
        .Array => {
            const A = ts.get(.Array, ty);
            const e = abiSizeAlign(self, A.elem);
            const stride = std.mem.alignForward(usize, e.size, e.alignment);
            return .{ .size = stride * A.len, .alignment = e.alignment, .hasFloat = e.hasFloat, .allIntsOnly = e.allIntsOnly };
        },
        .Variant, .Error, .Union => |k| {
            // Unified logic for union-like types
            const fields = switch (k) {
                .Variant => ts.field_pool.slice(ts.get(.Variant, ty).variants),
                .Error => ts.field_pool.slice(ts.get(.Error, ty).variants),
                .Union => ts.field_pool.slice(ts.get(.Union, ty).fields),
                else => unreachable,
            };
            if (fields.len == 0) return .{ .size = 4, .alignment = 4 };

            var max_sz: usize = 0;
            var max_al: usize = 1;
            var hasF = false;
            var ints = true;

            for (fields) |f| {
                const sa = abiSizeAlign(self, ts.Field.get(f).ty);
                max_sz = @max(max_sz, sa.size);
                max_al = @max(max_al, sa.alignment);
                hasF = hasF or sa.hasFloat;
                ints = ints and sa.allIntsOnly;
            }

            // Variants/Errors have a tag (4 bytes), Unions don't
            const tag_size: usize = if (k == .Union) 0 else 4;
            const min_align: usize = if (k == .Union) 1 else 4;
            const align_final = @max(min_align, max_al);
            return .{ .size = tag_size + max_sz, .alignment = align_final, .hasFloat = hasF, .allIntsOnly = ints };
        },
        .Optional => {
            if (ts.isOptionalPointer(ty)) return abiSizeAlign(self, ts.get(.Optional, ty).elem);
            const tag = SizeAlign{ .size = 1, .alignment = 1 };
            const v = abiSizeAlign(self, ts.get(.Optional, ty).elem);
            var off = std.mem.alignForward(usize, tag.size, v.alignment);
            off += v.size;
            const al = @max(tag.alignment, v.alignment);
            return .{ .size = std.mem.alignForward(usize, off, al), .alignment = al, .hasFloat = v.hasFloat, .allIntsOnly = v.allIntsOnly };
        },
        .ErrorSet => {
            const es = ts.get(.ErrorSet, ty);
            const payload = abiSizeAlign(self, self.context.type_store.mkUnion(&[_]types.TypeStore.StructFieldArg{
                .{ .name = ts.strs.intern("Ok"), .ty = es.value_ty },
                .{ .name = ts.strs.intern("Err"), .ty = es.error_ty },
            }));
            // Payload + 4 byte tag (approximated logic from original)
            var off = std.mem.alignForward(usize, 4, payload.alignment);
            off += payload.size;
            const al = @max(4, payload.alignment);
            return .{ .size = std.mem.alignForward(usize, off, al), .alignment = al, .hasFloat = payload.hasFloat, .allIntsOnly = payload.allIntsOnly };
        },
        .Tuple, .Struct => |k| {
            // Aggregate logic
            var size: usize = 0;
            var alignment: usize = 1;
            var hasF = false;
            var ints = true;

            // Iterator over types
            const elem_types_store = if (k == .Tuple) ts.type_pool.slice(ts.get(.Tuple, ty).elems) else null; // Tuple has types directly
            const field_ids = if (k == .Struct) ts.field_pool.slice(ts.get(.Struct, ty).fields) else null;

            const count = if (k == .Tuple) elem_types_store.?.len else field_ids.?.len;

            for (0..count) |i| {
                const sub_ty = if (k == .Tuple) elem_types_store.?[i] else ts.Field.get(field_ids.?[i]).ty;
                const e = abiSizeAlign(self, sub_ty);
                size = std.mem.alignForward(usize, size, e.alignment);
                size += e.size;
                alignment = @max(alignment, e.alignment);
                hasF = hasF or e.hasFloat;
                ints = ints and e.allIntsOnly;
            }
            return .{ .size = std.mem.alignForward(usize, size, alignment), .alignment = alignment, .hasFloat = hasF, .allIntsOnly = ints };
        },
        else => std.debug.panic("abiSizeAlign: unhandled kind {}", .{ts.getKind(ty)}),
    }
}

// Helpers
fn isFloat(ts: *types.TypeStore, ty: types.TypeId) bool {
    return ts.getKind(ty) == .F32;
}
fn isDouble(ts: *types.TypeStore, ty: types.TypeId) bool {
    return ts.getKind(ty) == .F64;
}

pub fn abiClassifyX64SysV(self: *Codegen, ty: types.TypeId, isReturn: bool) AbiClass {
    const ts = self.context.type_store;
    switch (ts.getKind(ty)) {
        .Noreturn => return .{ .kind = .DirectScalar, .scalar0 = self.void_ty, .size = 0 },
        .Bool => return .{ .kind = .DirectScalar, .scalar0 = self.i1_ty, .size = 1, .alignment = 1 },
        .I8, .U8 => return .{ .kind = .DirectScalar, .scalar0 = self.i8_ty, .size = 1, .alignment = 1 },
        .I16, .U16 => return .{ .kind = .DirectScalar, .scalar0 = mlir.Type.getSignlessIntegerType(self.mlir_ctx, 16), .size = 2, .alignment = 2 },
        .I32, .U32 => return .{ .kind = .DirectScalar, .scalar0 = self.i32_ty, .size = 4, .alignment = 4 },
        .I64, .U64, .Usize => return .{ .kind = .DirectScalar, .scalar0 = self.i64_ty, .size = 8, .alignment = 8 },
        .Ptr, .Any, .Function, .MlirModule, .MlirAttribute, .MlirType => return .{ .kind = .DirectScalar, .scalar0 = self.llvm_ptr_ty, .size = 8, .alignment = 8 },
        .F32 => return .{ .kind = .DirectScalar, .scalar0 = self.f32_ty, .size = 4, .alignment = 4 },
        .F64 => return .{ .kind = .DirectScalar, .scalar0 = self.f64_ty, .size = 8, .alignment = 8 },
        .Optional => if (ts.isOptionalPointer(ty)) {
            const sa = abiSizeAlign(self, ty);
            return .{ .kind = .DirectScalar, .scalar0 = self.llvm_ptr_ty, .size = sa.size, .alignment = @intCast(sa.alignment) };
        },
        .Variant, .Map => { // Force indirect for Map/Variant in this ABI implementation
            const sa = abiSizeAlign(self, ty);
            return if (isReturn) .{ .kind = .IndirectSRet, .alignment = @intCast(sa.alignment), .size = sa.size } else .{ .kind = .IndirectByVal, .alignment = @intCast(sa.alignment), .size = sa.size };
        },
        else => {},
    }

    const sa = abiSizeAlign(self, ty);
    if (sa.size == 0) return .{ .kind = .DirectScalar, .scalar0 = self.i32_ty, .size = 0 };

    if (sa.hasFloat and !sa.allIntsOnly) {
        if (sa.size == 4 and isFloat(ts, ty)) return .{ .kind = .DirectScalar, .scalar0 = self.f32_ty, .size = 4 };
        if (sa.size == 8 and isDouble(ts, ty)) return .{ .kind = .DirectScalar, .scalar0 = self.f64_ty, .size = 8 };
        // 2x float vector check
        var isTwoF = false;
        if (ts.getKind(ty) == .Struct) {
            const S = ts.get(.Struct, ty);
            if (S.fields.len == 2) {
                const fs = ts.field_pool.slice(S.fields);
                if (isFloat(ts, ts.Field.get(fs[0]).ty) and isFloat(ts, ts.Field.get(fs[1]).ty)) isTwoF = true;
            }
        } else if (ts.getKind(ty) == .Tuple) {
            const T = ts.get(.Tuple, ty);
            if (T.elems.len == 2) {
                const es = ts.type_pool.slice(T.elems);
                if (isFloat(ts, es[0]) and isFloat(ts, es[1])) isTwoF = true;
            }
        }
        if (sa.size == 8 and isTwoF) return .{ .kind = .DirectScalar, .scalar0 = mlir.Type.getVectorType(1, &[_]i64{2}, self.f32_ty), .size = 8 };

        return if (isReturn) .{ .kind = .IndirectSRet, .alignment = @intCast(sa.alignment), .size = sa.size } else .{ .kind = .IndirectByVal, .alignment = @intCast(sa.alignment), .size = sa.size };
    }

    if (sa.size > 16)
        return if (isReturn) .{ .kind = .IndirectSRet, .alignment = @intCast(sa.alignment), .size = sa.size } else .{ .kind = .IndirectByVal, .alignment = @intCast(sa.alignment), .size = sa.size };

    if (sa.size <= 8)
        return .{ .kind = .DirectScalar, .scalar0 = mlir.Type.getSignlessIntegerType(self.mlir_ctx, @intCast(sa.size * 8)), .size = sa.size };

    const hiBits: u32 = @intCast(sa.size * 8 - 64);
    return .{ .kind = .DirectPair, .scalar0 = self.i64_ty, .scalar1 = mlir.Type.getSignlessIntegerType(self.mlir_ctx, if (hiBits == 0) 64 else hiBits), .size = sa.size };
}
