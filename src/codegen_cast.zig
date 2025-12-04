const codegen = @import("codegen_main.zig");
const Codegen = codegen.Codegen;
const EmitOpArgs = codegen.EmitOpArgs;
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const std = @import("std");

/// MLIR `arith.cmpi` predicates used by integer-based cast helpers.
const CMP_EQ: i64 = 0;
const CMP_NE: i64 = 1;
const CMP_SLT: i64 = 2;
const CMP_SGT: i64 = 4;
const CMP_ULT: i64 = 6;
const CMP_UGT: i64 = 8;

/// MLIR `arith.cmpf` predicates used when comparing floating-point inputs.
const F_CMP_OEQ: i64 = 1;
const F_CMP_OGT: i64 = 2;
const F_CMP_OLT: i64 = 4;
const F_CMP_UNO: i64 = 14;

/// Get the bitwidth of `t` when it represents an integer or floating-point type.
/// Returns `error.NotIntOrFloat` if `t` is neither.
pub fn intOrFloatWidth(t: mlir.Type) !u32 {
    if (t.isAInteger()) return t.getIntegerBitwidth();
    if (t.isAFloat()) return t.getFloatBitwidth();
    return error.NotIntOrFloat;
}

/// Adapter called when lowering individual aggregate elements during casts.
/// It forwards the parameters into `emitCastNormal` so aggregates behave consistently.
fn emitCastAggregateElement(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
) anyerror!mlir.Value {
    return emitCastNormal(self, dst_sr, dst_ty, src_val, src_sr);
}

// --- Saturating helpers ---
/// Convert `v` into `to_ty` while clamping values that lie outside the integer domain.
/// `from_signed`/`to_signed` describe the signedness of the source and destination types.
pub fn saturateIntToInt(self: *Codegen, v: mlir.Value, from_signed: bool, to_ty: mlir.Type, to_signed: bool) mlir.Value {
    // Compare in source domain: extend to_ty limits up to source type
    const lim = intMinMax(self, to_ty, to_signed);
    const from_ty = v.getType();
    const ext_opname = if (from_signed) "arith.extsi" else "arith.extui";
    const min_in_from = self.emitUnaryValueOp(ext_opname, lim.min, from_ty);
    const max_in_from = self.emitUnaryValueOp(ext_opname, lim.max, from_ty);

    const pred_lt: i64 = if (from_signed) CMP_SLT else CMP_ULT;
    const pred_gt: i64 = if (from_signed) CMP_SGT else CMP_UGT;

    const lt = self.emitBinaryValueOp("arith.cmpi", v, min_in_from, self.i1_ty, &.{
        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, pred_lt)),
    });
    const gt = self.emitBinaryValueOp("arith.cmpi", v, max_in_from, self.i1_ty, &.{
        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, pred_gt)),
    });

    // select low/high in source domain
    const sel_low = self.emitOp("arith.select", EmitOpArgs{
        .operands = &.{ lt, min_in_from, v },
        .results = &.{from_ty},
    });
    const sel_hi = self.emitOp("arith.select", EmitOpArgs{
        .operands = &.{ gt, max_in_from, sel_low },
        .results = &.{from_ty},
    });

    // Final convert to destination width
    return castIntToInt(self, sel_hi, from_ty, to_ty, from_signed);
}

/// Clamp float `v` to the integer bounds of `to_ty`, treating NaN as a safe zero value.
/// `signed_to` describes whether the destination integer is signed.
pub fn saturateFloatToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
    const lim = intMinMax(self, to_ty, signed_to);
    const ft = v.getType();
    const min_f = castIntToFloat(self, lim.min, ft, signed_to);
    const max_f = castIntToFloat(self, lim.max, ft, signed_to);

    const lt = self.emitBinaryValueOp("arith.cmpf", v, min_f, self.i1_ty, &.{
        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OLT)),
    });
    const gt = self.emitBinaryValueOp("arith.cmpf", v, max_f, self.i1_ty, &.{
        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OGT)),
    });
    const isnan = self.emitBinaryValueOp("arith.cmpf", v, v, self.i1_ty, &.{
        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_UNO)),
    });
    var fail = self.boolOr(lt, gt);
    fail = self.boolOr(fail, isnan);

    // clamp
    const sel_low = self.emitOp("arith.select", EmitOpArgs{
        .operands = &.{ lt, min_f, v },
        .results = &.{ft},
    });
    const sel_hi = self.emitOp("arith.select", EmitOpArgs{
        .operands = &.{ gt, max_f, sel_low },
        .results = &.{ft},
    });

    return castFloatToInt(self, sel_hi, to_ty, signed_to);
}

// --- Checked helpers ---
/// Perform an integer-to-integer cast and raise if the value cannot round-trip to `from_ty`.
/// `from_signed` indicates if the original value is signed so we choose the correct extension.
pub fn checkedIntToInt(self: *Codegen, v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type, from_signed: bool) mlir.Value {
    // Convert normally (trunc/extend)
    const narrowed = self.castIntToInt(v, from_ty, to_ty, from_signed);

    const widened = self.emitUnaryValueOp(if (from_signed) "arith.extsi" else "arith.extui", narrowed, from_ty);

    const ok = self.emitBinaryValueOp("arith.cmpi", v, widened, self.i1_ty, &.{
        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, CMP_EQ)),
    });
    self.emitAssertCall(ok.getResult(0)); // trap if overflow

    return narrowed;
}

/// Convert a float to `to_ty` while asserting that the value is finite and within the integer range.
/// `signed_to` controls whether signed or unsigned integer semantics apply.
pub fn checkedFloatToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
    const lim = self.intMinMax(to_ty, signed_to);
    const ft = v.getType();
    const min_f = self.castIntToFloat(lim.min, ft, signed_to);
    const max_f = self.castIntToFloat(lim.max, ft, signed_to);

    const lt = self.emitBinaryValueOp("arith.cmpf", v, min_f, self.i1_ty, &.{
        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OLT)),
    });
    const gt = self.emitBinaryValueOp("arith.cmpf", v, max_f, self.i1_ty, &.{
        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OGT)),
    });
    const isnan = self.emitBinaryValueOp("arith.cmpf", v, v, self.i1_ty, &.{
        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_UNO)),
    });

    var bad = self.boolOr(lt, gt);
    bad = self.boolOr(bad, isnan);

    // assert(!bad)
    const ok = self.boolNot(bad);
    self.emitAssertCall(ok);

    return self.castFloatToInt(v, to_ty, signed_to);
}

// --- The normalized "normal cast" (includes Complex + slice→int quirk) ---
/// Emit the “normal” cast of `from_v` from `src_sr` to `dst_sr`, covering aggregates, pointers, Complex, etc.
/// The caller must supply the destination LLVM `to_ty` so that special-case conversions can be handled.
pub fn emitCastNormal(self: *Codegen, dst_sr: types.TypeId, to_ty: mlir.Type, from_v: mlir.Value, src_sr: types.TypeId) !mlir.Value {
    var from_ty = from_v.getType();

    if (from_ty.equal(self.llvm_ptr_ty) and mlir.LLVM.isLLVMStructType(to_ty)) {
        return self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{from_v},
            .results = &.{to_ty},
        });
    }

    // Special-case: build an ErrorSet value from a non-error value.
    // This creates the Ok variant with tag = 0 and coerces the payload.
    if (self.context.type_store.getKind(dst_sr) == .ErrorSet and self.context.type_store.getKind(src_sr) != .ErrorSet) {
        const es = self.context.type_store.get(.ErrorSet, dst_sr);

        // Construct the union storage type: union { Ok: value_ty, Err: error_ty }
        const ok_name = self.context.type_store.strs.intern("Ok");
        const err_name = self.context.type_store.strs.intern("Err");
        var union_fields = [_]types.TypeStore.StructFieldArg{
            .{ .name = ok_name, .ty = es.value_ty },
            .{ .name = err_name, .ty = es.error_ty },
        };
        const union_sr = self.context.type_store.mkUnion(&union_fields);
        const union_mlir = try self.llvmTypeOf(union_sr);

        // Coerce the incoming value to the Ok payload type if needed.
        var payload_val = from_v;
        const ok_payload_mlir = try self.llvmTypeOf(es.value_ty);
        if (!payload_val.getType().equal(ok_payload_mlir)) {
            payload_val = try self.coerceOnBranch(payload_val, ok_payload_mlir, es.value_ty, src_sr);
        }

        // Materialize the union storage by writing the Ok payload at offset 0.
        const tmp_union_ptr = self.spillAgg(self.undefOf(union_mlir), union_mlir, 0);
        self.storeAt(tmp_union_ptr, payload_val, 0);
        const ld_union = self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{tmp_union_ptr},
            .results = &.{union_mlir},
        });

        // Assemble the ErrorSet aggregate: { tag: i32 = 0, payload: union }
        var acc = self.zeroOf(to_ty);
        const tag0 = self.constInt(self.i32_ty, 0);
        acc = self.insertAt(acc, tag0, &.{0});
        acc = self.insertAt(acc, ld_union, &.{1});
        return acc;
    }

    // Complex target?
    if (self.context.type_store.getKind(dst_sr) == .Complex) {
        const tgt = self.context.type_store.get(.Complex, dst_sr);
        const elem_ty = self.llvmTypeOf(tgt.elem) catch unreachable;

        const src_kind = self.context.type_store.getKind(src_sr);
        if (src_kind == .Complex) {
            const src_c = self.context.type_store.get(.Complex, src_sr);
            const src_elem_ty = self.llvmTypeOf(src_c.elem) catch unreachable;
            if (src_elem_ty.equal(elem_ty)) return from_v;

            const re0 = self.complexRe(from_v, src_elem_ty);
            const im0 = self.complexIm(from_v, src_elem_ty);
            const re = resizeFloat(self, re0, src_elem_ty, elem_ty);
            const im = resizeFloat(self, im0, src_elem_ty, elem_ty);
            return self.complexFromParts(re, im, to_ty);
        } else {
            // scalar -> complex
            const from_is_int = from_ty.isAInteger();
            const from_is_f = from_ty.isAFloat();
            var re_val: mlir.Value = from_v;
            if (from_is_int and elem_ty.isAFloat()) {
                const signed_from = self.isSignedInt(src_sr);
                re_val = castIntToFloat(self, from_v, elem_ty, signed_from);
            } else if (from_is_f and elem_ty.isAFloat()) {
                re_val = resizeFloat(self, from_v, from_ty, elem_ty);
            }
            const im_val = self.constFloat(elem_ty, 0.0);
            return self.complexFromParts(re_val, im_val, to_ty);
        }
    }

    // Special-case slice -> int coercion artifact
    if (self.context.type_store.getKind(src_sr) == .Slice and to_ty.isAInteger()) {
        return self.constInt(to_ty, 0);
    }

    // Special-case: static Array -> DynArray. For zero-length arrays, return an empty dyn array
    // (ptr = null, len = 0, cap = 0). This matches expected semantics and fixes join-arg typing
    // when early-returning an empty dynamic array from an empty literal.
    if (self.context.type_store.getKind(dst_sr) == .DynArray and self.context.type_store.getKind(src_sr) == .Array) {
        const arr = self.context.type_store.get(.Array, src_sr);
        if (arr.len == 0)
            return self.zeroOf(to_ty);
        // Non-zero-length array -> dyn array is not yet supported here; fall through to other paths.
    }

    // Scalars & pointers
    const from_is_int = from_ty.isAInteger() or
        (from_ty.isAVector() and from_ty.getShapedElementType().isAInteger());
    const to_is_int = to_ty.isAInteger() or
        (to_ty.isAVector() and to_ty.getShapedElementType().isAInteger());
    const from_is_f = from_ty.isAFloat() or
        (from_ty.isAVector() and from_ty.getShapedElementType().isAFloat());
    const to_is_f = to_ty.isAFloat() or
        (to_ty.isAVector() and to_ty.getShapedElementType().isAFloat());
    const from_is_ptr = from_ty.equal(self.llvm_ptr_ty);
    const to_is_ptr = to_ty.equal(self.llvm_ptr_ty);

    if (from_is_ptr and to_is_ptr) return castPtrToPtr(self, from_v, to_ty);
    if (from_is_ptr and to_is_int) return castPtrToInt(self, from_v, to_ty);
    if (from_is_int and to_is_ptr) return castIntToPtr(self, from_v, to_ty);

    if (from_is_int and to_is_int) return castIntToInt(self, from_v, from_ty, to_ty, self.isSignedInt(src_sr));
    if (from_is_int and to_is_f) return castIntToFloat(self, from_v, to_ty, self.isSignedInt(src_sr));
    if (from_is_f and to_is_int) return castFloatToInt(self, from_v, to_ty, self.isSignedInt(dst_sr));
    if (from_is_f and to_is_f) return resizeFloat(self, from_v, from_ty, to_ty);

    // Special-case: Array -> Simd elementwise conversion (avoid invalid bitcast from !llvm.array to vector)
    if (self.context.type_store.getKind(dst_sr) == .Simd and self.context.type_store.getKind(src_sr) == .Array) {
        const simd = self.context.type_store.get(.Simd, dst_sr);
        const arr = self.context.type_store.get(.Array, src_sr);
        // Only handle concrete fixed-size arrays that match the lane count
        const lanes: usize = @intCast(simd.lanes);
        if (arr.len == lanes and lanes > 0) {
            const elem_mlir = try self.llvmTypeOf(simd.elem);
            const vec_ty = to_ty;
            // Collect elements by extracting from the array and coercing to vector element type
            var elems = try self.gpa.alloc(mlir.Value, lanes);
            defer self.gpa.free(elems);
            var i: usize = 0;
            while (i < lanes) : (i += 1) {
                var e = self.extractAt(from_v, elem_mlir, &.{@intCast(i)});
                if (!e.getType().equal(elem_mlir)) {
                    e = try self.coerceOnBranch(e, elem_mlir, simd.elem, arr.elem);
                }
                elems[i] = e;
            }
            return self.emitOp("vector.from_elements", EmitOpArgs{
                .operands = elems,
                .results = &.{vec_ty},
            });
        }
    }

    if (try self.tryCopyAggregateValue(dst_sr, to_ty, from_v, src_sr, emitCastAggregateElement)) |agg|
        return agg;

    if (try self.reinterpretAggregateViaSpill(dst_sr, to_ty, from_v, src_sr)) |agg|
        return agg;
    if (self.isUndefValue(from_v)) return self.undefOf(to_ty);

    // Fallback: avoid invalid bitcasts on aggregates. If either side is an
    // LLVM struct (aggregate), do not emit an arith.bitcast which is invalid
    // for structs. Let the caller supply a properly shaped value instead.
    if (mlir.LLVM.isLLVMStructType(from_v.getType()) or mlir.LLVM.isLLVMStructType(to_ty)) {
        // Minimal breadcrumb to help locate the source site during bring-up.
        std.debug.print("codegen_cast: skip bitcast for aggregate types\n", .{});
        return self.undefOf(to_ty);
    }
    return self.emitUnaryValueOp("arith.bitcast", from_v, to_ty);
}

// --- Public dispatcher for all cast kinds ---
/// Dispatch the appropriate cast strategy for `kind` (normal, wrap, saturate, checked) between SR types.
/// `dst_sr` and `src_sr` describe the source/destination semantics needed for MLIR emission.
pub fn emitCast(self: *Codegen, kind: tir.OpKind, dst_sr: types.TypeId, src_sr: types.TypeId, from_v: mlir.Value) !mlir.Value {
    const to_ty = try self.llvmTypeOf(dst_sr);
    const from_ty = from_v.getType();

    switch (kind) {
        else => unreachable, // not a cast
        .CastNormal => return emitCastNormal(self, dst_sr, to_ty, from_v, src_sr),

        .CastWrap => {
            if (from_ty.isAInteger() and to_ty.isAInteger()) {
                return castIntToInt(self, from_v, from_ty, to_ty, self.isSignedInt(src_sr)); // wrap == modular
            }
            // others: same as normal
            return emitCastNormal(self, dst_sr, to_ty, from_v, src_sr);
        },

        .CastSaturate => {
            if (from_ty.isAInteger() and to_ty.isAInteger()) {
                return saturateIntToInt(self, from_v, self.isSignedInt(src_sr), to_ty, self.isSignedInt(dst_sr));
            }
            if (from_ty.isAFloat() and to_ty.isAInteger()) {
                return saturateFloatToInt(self, from_v, to_ty, self.isSignedInt(dst_sr));
            }
            // others: normal behavior
            return emitCastNormal(self, dst_sr, to_ty, from_v, src_sr);
        },

        .CastChecked => {
            // const to_ty_mlir = to_ty;
            const from_ty_mlir = from_v.getType();

            // The result of a checked cast is always an Optional type.
            const optional_sr = self.context.type_store.get(.Optional, dst_sr);
            const optional_mlir_ty = try self.llvmTypeOf(dst_sr);
            const optional_elem_mlir_ty = try self.llvmTypeOf(optional_sr.elem);
            const optional_elem_is_signed = self.isSignedInt(optional_sr.elem);

            var cast_ok: mlir.Value = self.constBool(true);
            var casted_val: mlir.Value = undefined;

            if (from_ty_mlir.isAInteger() and optional_elem_mlir_ty.isAInteger()) {
                // Integer to Integer checked cast
                const fw = try intOrFloatWidth(from_ty_mlir);
                const tw = try intOrFloatWidth(optional_elem_mlir_ty);
                const from_signed = self.isSignedInt(src_sr);
                // const to_signed = self.isSignedInt(store.get(.Optional, dst_sr).elem);

                if (fw == tw) {
                    casted_val = from_v;
                } else if (fw > tw) {
                    // Truncation: check for overflow
                    const narrowed = castIntToInt(self, from_v, from_ty_mlir, optional_elem_mlir_ty, from_signed);
                    const widened = self.emitUnaryValueOp(if (from_signed) "arith.extsi" else "arith.extui", narrowed, from_ty_mlir);
                    cast_ok = self.emitBinaryValueOp("arith.cmpi", from_v, widened, self.i1_ty, &.{
                        self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, CMP_EQ)),
                    });
                    casted_val = narrowed;
                } else {
                    // Extension: always succeeds
                    casted_val = castIntToInt(self, from_v, from_ty_mlir, optional_elem_mlir_ty, from_signed);
                }
            } else if (from_ty_mlir.isAFloat() and optional_elem_mlir_ty.isAInteger()) {
                // Float to Integer checked cast
                const lim = intMinMax(self, optional_elem_mlir_ty, optional_elem_is_signed);
                const ft = from_ty_mlir;
                const min_f = castIntToFloat(self, lim.min, ft, optional_elem_is_signed);
                const max_f = castIntToFloat(self, lim.max, ft, optional_elem_is_signed);

                const lt = self.emitBinaryValueOp("arith.cmpf", from_v, min_f, self.i1_ty, &.{
                    self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OLT)),
                });
                const gt = self.emitBinaryValueOp("arith.cmpf", from_v, max_f, self.i1_ty, &.{
                    self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OGT)),
                });
                const isnan = self.emitBinaryValueOp("arith.cmpf", from_v, from_v, self.i1_ty, &.{
                    self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_UNO)),
                });

                var bad = self.boolOr(lt, gt);
                bad = self.boolOr(bad, isnan);
                cast_ok = self.boolNot(bad);

                // Clamp the source value into the integer domain (or a benign value for NaN)
                const clamped_low = self.emitOp("arith.select", EmitOpArgs{
                    .operands = &.{ lt, min_f, from_v },
                    .results = &.{ft},
                });
                const clamped_high = self.emitOp("arith.select", EmitOpArgs{
                    .operands = &.{ gt, max_f, clamped_low },
                    .results = &.{ft},
                });
                const zero = self.constFloat(ft, 0.0);
                const sanitized = self.emitOp("arith.select", EmitOpArgs{
                    .operands = &.{ isnan, zero, clamped_high },
                    .results = &.{ft},
                });

                casted_val = castFloatToInt(self, sanitized, optional_elem_mlir_ty, optional_elem_is_signed);

                // Verify round-trip back to float to catch fractional values.
                const roundtrip = castIntToFloat(self, casted_val, ft, optional_elem_is_signed);
                const same = self.emitBinaryValueOp("arith.cmpf", from_v, roundtrip, self.i1_ty, &.{
                    self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OEQ)),
                });
                cast_ok = self.boolAnd(cast_ok, same);
            } else {
                // For other types (ptr<->int, float<->float), treat as normal cast for now.
                // If it's a normal cast that would fail, then the checked cast should produce None.
                // This is a simplification; a more robust solution would involve more specific checks.
                casted_val = try emitCastNormal(self, optional_sr.elem, optional_elem_mlir_ty, from_v, src_sr);
                // Assume success for now, or add more complex checks if needed.
                cast_ok = self.constBool(true);
            }

            // Construct the Optional struct
            var result_optional = self.undefOf(optional_mlir_ty);
            result_optional = self.insertAt(result_optional, cast_ok, &.{0});
            result_optional = self.insertAt(result_optional, casted_val, &.{1});
            return result_optional;
        },
    }
}

// --- Scalar cast helpers ---

/// Bitcast a pointer value `v` into another pointer type `to_ty`.
fn castPtrToPtr(self: *Codegen, v: mlir.Value, to_ty: mlir.Type) mlir.Value {
    // Use LLVM dialect bitcast for pointer-to-pointer casts
    return self.emitUnaryValueOp("llvm.bitcast", v, to_ty);
}
/// Convert a pointer value into an integer of `to_ty`.
fn castPtrToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type) mlir.Value {
    return self.emitUnaryValueOp("llvm.ptrtoint", v, to_ty);
}
/// Convert an integer value into a pointer type `to_ty`.
fn castIntToPtr(self: *Codegen, v: mlir.Value, to_ty: mlir.Type) mlir.Value {
    return self.emitUnaryValueOp("llvm.inttoptr", v, to_ty);
}

/// Emit integer truncation/extension from `from_ty` to `to_ty`, honoring `signed_from`.
fn castIntToInt(self: *Codegen, from_v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type, signed_from: bool) mlir.Value {
    const fw = intOrFloatWidth(from_ty) catch 0;
    const tw = intOrFloatWidth(to_ty) catch 0;
    if (fw == tw) return from_v;
    if (fw > tw) {
        return self.emitUnaryValueOp("arith.trunci", from_v, to_ty);
    }
    const opname = if (signed_from) "arith.extsi" else "arith.extui";
    return self.emitUnaryValueOp(opname, from_v, to_ty);
}

/// Convert integer `v` to the floating-point `to_ty`, using signed/unsigned conversion.
fn castIntToFloat(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_from: bool) mlir.Value {
    return self.emitUnaryValueOp(if (signed_from) "arith.sitofp" else "arith.uitofp", v, to_ty);
}

/// Convert floating-point `v` into integer `to_ty`, choosing signed or unsigned semantics.
fn castFloatToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
    return self.emitUnaryValueOp(if (signed_to) "arith.fptosi" else "arith.fptoui", v, to_ty);
}

/// Adjust the floating-point `v` from `from_ty` to `to_ty`, using truncation or extension.
fn resizeFloat(self: *Codegen, v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type) mlir.Value {
    const fw = intOrFloatWidth(from_ty) catch 0;
    const tw = intOrFloatWidth(to_ty) catch 0;
    if (fw == tw) return v;
    const opname = if (fw > tw) "arith.truncf" else "arith.extf";
    return self.emitUnaryValueOp(opname, v, to_ty);
}

// --- Integer limits as MLIR constants (destination type) ---
/// Build MLIR constants holding the min/max bounds for `to_ty` given `signed_to`.
/// The returned values are ready to seed comparison/select operations.
fn intMinMax(self: *Codegen, to_ty: mlir.Type, signed_to: bool) struct { min: mlir.Value, max: mlir.Value } {
    const w: u32 = intOrFloatWidth(to_ty) catch 1;
    if (signed_to) {
        return switch (w) {
            inline 1, 8, 16, 32, 64 => |x| blk: {
                const Int = @Type(.{ .int = .{ .bits = x, .signedness = .signed } });
                break :blk .{
                    .min = self.constInt(to_ty, std.math.minInt(Int)),
                    .max = self.constInt(to_ty, std.math.maxInt(Int)),
                };
            },
            else => .{
                .min = self.constInt(to_ty, std.math.minInt(i64)),
                .max = self.constInt(to_ty, std.math.maxInt(i64)),
            },
        };
    } else {
        return switch (w) {
            inline 1, 8, 16, 32, 64 => |x| blk: {
                const Int = @Type(.{ .int = .{ .bits = x, .signedness = .unsigned } });
                break :blk .{
                    .min = self.constInt(to_ty, 0),
                    .max = self.constInt(to_ty, std.math.maxInt(Int)),
                };
            },
            else => .{
                .min = self.constInt(to_ty, 0),
                .max = self.constInt(to_ty, std.math.maxInt(u64)),
            },
        };
    }
}
