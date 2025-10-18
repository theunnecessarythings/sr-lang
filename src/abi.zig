const mlir = @import("mlir_bindings.zig");
const MlirCodegen = @import("mlir_codegen.zig").MlirCodegen;
const types = @import("types.zig");
const std = @import("std");

// ===== ABI: x86_64 SysV  =====
const AbiKind = enum {
    DirectScalar, // coerce to one scalar (i8/i16/i32/i64/i128 or float/double/<2 x float>)
    DirectPair, // split into two integer scalars (lo 64, hi remainder)
    IndirectByVal, // pass pointer with byval(T) align K
    IndirectSRet, // return via sret(T) align K (handled via first arg)
};

pub const AbiClass = struct {
    kind: AbiKind,
    // For DirectScalar: scalar0 used
    // For DirectPair:   scalar0 + scalar1 used
    scalar0: ?mlir.Type = null,
    scalar1: ?mlir.Type = null,
    // For Indirect: alignment
    alignment: u32 = 1,

    // Size in bytes (handy for pack/unpack loads/stores)
    size: usize = 0,
};

fn srIsIntLike(store: *types.TypeStore, ty: types.TypeId) bool {
    return switch (store.getKind(ty)) {
        .I8, .U8, .I16, .U16, .I32, .U32, .I64, .U64, .Usize, .Bool => true,
        .Ptr, .Any, .String, .Function, .MlirModule, .MlirAttribute, .MlirType => true, // treat as pointer-sized
        else => false,
    };
}
fn srIsFloatLike(store: *types.TypeStore, ty: types.TypeId) bool {
    return switch (store.getKind(ty)) {
        .F32, .F64 => true,
        else => false,
    };
}

// Compute size/align for SR type under x86_64 SysV (natural layout, no packed attr).
const SizeAlign = struct {
    size: usize,
    alignment: usize,
    hasFloat: bool,
    allIntsOnly: bool,
};

pub fn abiSizeAlign(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) SizeAlign {
    return switch (store.getKind(ty)) {
        .Void => .{ .size = 0, .alignment = 1, .hasFloat = false, .allIntsOnly = true },
        .Bool => .{ .size = 1, .alignment = 1, .hasFloat = false, .allIntsOnly = true },

        .I8, .U8 => .{ .size = 1, .alignment = 1, .hasFloat = false, .allIntsOnly = true },
        .I16, .U16 => .{ .size = 2, .alignment = 2, .hasFloat = false, .allIntsOnly = true },
        .I32, .U32 => .{ .size = 4, .alignment = 4, .hasFloat = false, .allIntsOnly = true },
        .I64, .U64, .Usize => .{ .size = 8, .alignment = 8, .hasFloat = false, .allIntsOnly = true },

        .F32 => .{ .size = 4, .alignment = 4, .hasFloat = true, .allIntsOnly = false },
        .F64 => .{ .size = 8, .alignment = 8, .hasFloat = true, .allIntsOnly = false },

        .Ptr, .Any, .String, .Function, .MlirModule, .MlirAttribute, .MlirType => .{ .size = 8, .alignment = 8, .hasFloat = false, .allIntsOnly = true },
        .Slice => .{ .size = 16, .alignment = 8, .hasFloat = false, .allIntsOnly = true },
        .Enum => {
            const E = store.get(.Enum, ty);
            // Enums are represented as their discriminant type.
            return abiSizeAlign(self, store, E.tag_type);
        },

        .Array => {
            const A = store.get(.Array, ty);
            const len = switch (A.len) {
                .Concrete => |l| l,
                .Unresolved => std.debug.panic("abiSizeAlign called on array with unresolved size", .{}),
            };
            const e = abiSizeAlign(self, store, A.elem);
            const stride = std.mem.alignForward(usize, e.size, e.alignment);
            return .{ .size = stride * len, .alignment = e.alignment, .hasFloat = e.hasFloat, .allIntsOnly = e.allIntsOnly };
        },
        .Variant => {
            const v_ty = store.get(.Variant, ty);
            const n = v_ty.variants.len;
            if (n == 0) return SizeAlign{ .size = 4, .alignment = 4, .hasFloat = false, .allIntsOnly = true };

            var max_payload_size: usize = 0;
            var max_payload_alignment: usize = 1;
            var has_float = false;
            var all_ints = true;

            const fields = store.field_pool.slice(v_ty.variants);
            for (fields) |f| {
                const field = store.Field.get(f);
                const sa = abiSizeAlign(self, store, field.ty);
                if (sa.size > max_payload_size) {
                    max_payload_size = sa.size;
                }
                if (sa.alignment > max_payload_alignment) {
                    max_payload_alignment = sa.alignment;
                }
                has_float = has_float or sa.hasFloat;
                all_ints = all_ints and sa.allIntsOnly;
            }

            const tag_size = 4;
            const total_size = tag_size + max_payload_size;
            const alignment = @max(4, max_payload_alignment);

            return SizeAlign{ .size = total_size, .alignment = alignment, .hasFloat = has_float, .allIntsOnly = all_ints };
        },
        .Error => {
            const e_ty = store.get(.Error, ty);
            const n = e_ty.variants.len;
            if (n == 0) return SizeAlign{ .size = 4, .alignment = 4, .hasFloat = false, .allIntsOnly = true };

            var max_payload_size: usize = 0;
            var max_payload_alignment: usize = 1;
            var has_float = false;
            var all_ints = true;

            const fields = store.field_pool.slice(e_ty.variants);
            for (fields) |f| {
                const field = store.Field.get(f);
                const sa = abiSizeAlign(self, store, field.ty);
                if (sa.size > max_payload_size) max_payload_size = sa.size;
                if (sa.alignment > max_payload_alignment) max_payload_alignment = sa.alignment;
                has_float = has_float or sa.hasFloat;
                all_ints = all_ints and sa.allIntsOnly;
            }

            const tag_size = 4;
            const total_size = tag_size + max_payload_size;
            const alignment = @max(4, max_payload_alignment);

            return SizeAlign{ .size = total_size, .alignment = alignment, .hasFloat = has_float, .allIntsOnly = all_ints };
        },
        .Optional => { // {i1, T}
            const O = store.get(.Optional, ty);
            const a_tag = SizeAlign{ .size = 1, .alignment = 1, .hasFloat = false, .allIntsOnly = true };
            const v = abiSizeAlign(self, store, O.elem);
            var off: usize = 0;
            var al: usize = a_tag.alignment;
            // field 0 (tag)
            off = std.mem.alignForward(usize, off, a_tag.alignment);
            off += a_tag.size;
            al = @max(al, a_tag.alignment);
            // field 1 (value)
            off = std.mem.alignForward(usize, off, v.alignment);
            off += v.size;
            al = @max(al, v.alignment);
            off = std.mem.alignForward(usize, off, al);
            return .{ .size = off, .alignment = al, .hasFloat = v.hasFloat, .allIntsOnly = a_tag.allIntsOnly and v.allIntsOnly };
        },
        .ErrorSet => {
            const es = store.get(.ErrorSet, ty);
            const ok_name = store.strs.intern("Ok");
            const err_name = store.strs.intern("Err");
            var union_fields = [_]types.TypeStore.StructFieldArg{
                .{ .name = ok_name, .ty = es.value_ty },
                .{ .name = err_name, .ty = es.error_ty },
            };
            const payload_union = store.mkUnion(&union_fields);
            const payload = abiSizeAlign(self, store, payload_union);

            var off: usize = 0;
            var al: usize = 4;
            off = std.mem.alignForward(usize, off, 4);
            off += 4;
            off = std.mem.alignForward(usize, off, payload.alignment);
            off += payload.size;
            al = @max(al, payload.alignment);
            off = std.mem.alignForward(usize, off, al);
            return .{ .size = off, .alignment = al, .hasFloat = payload.hasFloat, .allIntsOnly = payload.allIntsOnly };
        },
        .Tuple => {
            const T = store.get(.Tuple, ty);
            const elems = store.type_pool.slice(T.elems);
            var size: usize = 0;
            var alignment: usize = 1;
            var hasF = false;
            var intsOnly = true;
            for (elems) |eId| {
                const e = abiSizeAlign(self, store, eId);
                size = std.mem.alignForward(usize, size, e.alignment);
                size += e.size;
                alignment = @max(alignment, e.alignment);
                hasF = hasF or e.hasFloat;
                intsOnly = intsOnly and e.allIntsOnly;
            }
            size = std.mem.alignForward(usize, size, alignment);
            return .{ .size = size, .alignment = alignment, .hasFloat = hasF, .allIntsOnly = intsOnly };
        },
        .Struct => {
            const S = store.get(.Struct, ty);
            const fields = store.field_pool.slice(S.fields);
            var size: usize = 0;
            var alignment: usize = 1;
            var hasF = false;
            var intsOnly = true;
            for (fields) |fid| {
                const e = abiSizeAlign(self, store, store.Field.get(fid).ty);
                size = std.mem.alignForward(usize, size, e.alignment);
                size += e.size;
                alignment = @max(alignment, e.alignment);
                hasF = hasF or e.hasFloat;
                intsOnly = intsOnly and e.allIntsOnly;
            }
            size = std.mem.alignForward(usize, size, alignment);
            return .{ .size = size, .alignment = alignment, .hasFloat = hasF, .allIntsOnly = intsOnly };
        },
        .Union => {
            const U = store.get(.Union, ty);
            const fields = store.field_pool.slice(U.fields);
            var size: usize = 0;
            var alignment: usize = 1;
            var hasF = false;
            var intsOnly = true;
            for (fields) |fid| {
                const e = abiSizeAlign(self, store, store.Field.get(fid).ty);
                size = @max(size, e.size);
                alignment = @max(alignment, e.alignment);
                hasF = hasF or e.hasFloat;
                intsOnly = intsOnly and e.allIntsOnly;
            }
            size = std.mem.alignForward(usize, size, alignment);
            return .{ .size = size, .alignment = alignment, .hasFloat = hasF, .allIntsOnly = intsOnly };
        },
        .Noreturn => {
            return .{ .size = 0, .alignment = 1, .hasFloat = false, .allIntsOnly = true };
        },
        else => std.debug.panic("abiSizeAlign: unhandled SR kind {} -> {}", .{ ty, store.getKind(ty) }),
    };
}

// Simple FP pattern recognizers (for MVP SSE cases)
fn srIsExactlyFloat(store: *types.TypeStore, ty: types.TypeId) bool {
    return store.getKind(ty) == .F32;
}
fn srIsExactlyDouble(store: *types.TypeStore, ty: types.TypeId) bool {
    return store.getKind(ty) == .F64;
}
fn srIsTwoFloats(store: *types.TypeStore, ty: types.TypeId) bool {
    if (store.getKind(ty) == .Struct) {
        const S = store.get(.Struct, ty);
        if (S.fields.len != 2) return false;
        const fs = store.field_pool.slice(S.fields);
        return srIsExactlyFloat(store, store.Field.get(fs[0]).ty) and
            srIsExactlyFloat(store, store.Field.get(fs[1]).ty);
    }
    if (store.getKind(ty) == .Tuple) {
        const T = store.get(.Tuple, ty);
        if (T.elems.len != 2) return false;
        const es = store.type_pool.slice(T.elems);
        return srIsExactlyFloat(store, es[0]) and srIsExactlyFloat(store, es[1]);
    }
    return false;
}

// Main classifier for a *parameter* or *return* SR type.
pub fn abiClassifyX64SysV(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId, isReturn: bool) AbiClass {
    // Scalars: map 1:1, don't ABI-mangle
    switch (store.getKind(ty)) {
        .Noreturn => return .{ .kind = .DirectScalar, .scalar0 = self.void_ty, .size = 0 },
        .Bool => return .{ .kind = .DirectScalar, .scalar0 = self.i1_ty, .size = 1, .alignment = 1 },
        .I8, .U8 => return .{ .kind = .DirectScalar, .scalar0 = self.i8_ty, .size = 1, .alignment = 1 },
        .I16, .U16 => return .{ .kind = .DirectScalar, .scalar0 = mlir.Type.getSignlessIntegerType(self.mlir_ctx, 16), .size = 2, .alignment = 2 },
        .I32, .U32 => return .{ .kind = .DirectScalar, .scalar0 = self.i32_ty, .size = 4, .alignment = 4 },
        .I64, .U64, .Usize => return .{ .kind = .DirectScalar, .scalar0 = self.i64_ty, .size = 8, .alignment = 8 },
        .F32 => return .{ .kind = .DirectScalar, .scalar0 = self.f32_ty, .size = 4, .alignment = 4 },
        .F64 => return .{ .kind = .DirectScalar, .scalar0 = self.f64_ty, .size = 8, .alignment = 8 },
        .Ptr, .Any, .Function, .Map, .MlirModule, .MlirAttribute, .MlirType => return .{ .kind = .DirectScalar, .scalar0 = self.llvm_ptr_ty, .size = 8, .alignment = 8 },
        .Variant => {
            const sa = abiSizeAlign(self, store, ty);
            return if (isReturn) .{ .kind = .IndirectSRet, .alignment = @intCast(sa.alignment), .size = sa.size } else .{ .kind = .IndirectByVal, .alignment = @intCast(sa.alignment), .size = sa.size };
        },
        else => {},
    }
    const sa = abiSizeAlign(self, store, ty);

    if (sa.size == 0) {
        return .{ .kind = .DirectScalar, .scalar0 = self.i32_ty, .size = 0 }; // arbitrary; won't be used
    }

    // MVP float handling (common cases)
    if (sa.hasFloat and !sa.allIntsOnly) {
        // 1x float -> float in XMM
        if (sa.size == 4 and srIsExactlyFloat(store, ty)) {
            return .{ .kind = .DirectScalar, .scalar0 = self.f32_ty, .size = 4 };
        }
        // 1x double -> double in XMM
        if (sa.size == 8 and srIsExactlyDouble(store, ty)) {
            return .{ .kind = .DirectScalar, .scalar0 = self.f64_ty, .size = 8 };
        }
        // 2x float -> <2 x float> (one XMM)
        if (sa.size == 8 and srIsTwoFloats(store, ty)) {
            const vty = mlir.Type.getVectorType(1, &[_]i64{2}, self.f32_ty);
            return .{ .kind = .DirectScalar, .scalar0 = vty, .size = 8 };
        }
        // TODO: mixed FP/int or >2 floats: implement full SSE classification.
        // For now, larger/complex FP aggregates go indirect.
        if (isReturn) return .{ .kind = .IndirectSRet, .alignment = @intCast(sa.alignment), .size = sa.size };
        return .{ .kind = .IndirectByVal, .alignment = @intCast(sa.alignment), .size = sa.size };
    }

    // Pure integer/byte/pointer aggregates.
    if (sa.size > 16) {
        if (isReturn) return .{ .kind = .IndirectSRet, .alignment = @intCast(sa.alignment), .size = sa.size };
        return .{ .kind = .IndirectByVal, .alignment = @intCast(sa.alignment), .size = sa.size };
    }
    if (sa.size <= 8) {
        const bits: u32 = @intCast(sa.size * 8);
        const ity = mlir.Type.getSignlessIntegerType(self.mlir_ctx, bits);
        return .{ .kind = .DirectScalar, .scalar0 = ity, .size = sa.size };
    }
    // 8 < size <= 16: DirectPair
    const hiBits: u32 = @intCast(sa.size * 8 - 64);
    const i64t = self.i64_ty;
    const hit = mlir.Type.getSignlessIntegerType(self.mlir_ctx, if (hiBits == 0) 64 else hiBits);
    return .{ .kind = .DirectPair, .scalar0 = i64t, .scalar1 = hit, .size = sa.size };
}
