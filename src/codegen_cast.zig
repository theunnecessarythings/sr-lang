const codegen = @import("codegen_main.zig");
const Codegen = codegen.Codegen;
const OpBuilder = Codegen.OpBuilder;
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const std = @import("std");

// arith.cmpi predicates (MLIR enum values)
const CMP_EQ: i64 = 0;
const CMP_NE: i64 = 1;
const CMP_SLT: i64 = 2;
const CMP_SGT: i64 = 4;
const CMP_ULT: i64 = 6;
const CMP_UGT: i64 = 8;

// arith.cmpf predicates (MLIR enum values)
const F_CMP_OEQ: i64 = 1;
const F_CMP_OGT: i64 = 2;
const F_CMP_OLT: i64 = 4;
const F_CMP_UNO: i64 = 14;

pub fn intOrFloatWidth(t: mlir.Type) !u32 {
    if (t.isAInteger()) return t.getIntegerBitwidth();
    if (t.isAFloat()) return t.getFloatBitwidth();
    return error.NotIntOrFloat;
}

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
pub fn saturateIntToInt(self: *Codegen, v: mlir.Value, from_signed: bool, to_ty: mlir.Type, to_signed: bool) mlir.Value {
    // Compare in source domain: extend to_ty limits up to source type
    const lim = intMinMax(self, to_ty, to_signed);
    const from_ty = v.getType();
    const ext_opname = if (from_signed) "arith.extsi" else "arith.extui";
    const min_in_from = self.appendIfHasResult(OpBuilder.init(ext_opname, self.loc).builder()
        .operands(&.{lim.min}).results(&.{from_ty}).build());
    const max_in_from = self.appendIfHasResult(OpBuilder.init(ext_opname, self.loc).builder()
        .operands(&.{lim.max}).results(&.{from_ty}).build());

    const pred_lt: i64 = if (from_signed) CMP_SLT else CMP_ULT;
    const pred_gt: i64 = if (from_signed) CMP_SGT else CMP_UGT;

    const lt = OpBuilder.init("arith.cmpi", self.loc).builder()
        .operands(&.{ v, min_in_from })
        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, pred_lt))})
        .results(&.{self.i1_ty}).build();
    const gt = OpBuilder.init("arith.cmpi", self.loc).builder()
        .operands(&.{ v, max_in_from })
        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, pred_gt))})
        .results(&.{self.i1_ty}).build();
    self.append(lt);
    self.append(gt);

    // select low/high in source domain
    const sel_low = OpBuilder.init("arith.select", self.loc).builder()
        .operands(&.{ lt.getResult(0), min_in_from, v }).results(&.{from_ty}).build();
    self.append(sel_low);
    const sel_hi = OpBuilder.init("arith.select", self.loc).builder()
        .operands(&.{ gt.getResult(0), max_in_from, sel_low.getResult(0) }).results(&.{from_ty}).build();
    self.append(sel_hi);

    // Final convert to destination width
    return castIntToInt(self, sel_hi.getResult(0), from_ty, to_ty, from_signed);
}

pub fn saturateFloatToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
    const lim = intMinMax(self, to_ty, signed_to);
    const ft = v.getType();
    const min_f = castIntToFloat(self, lim.min, ft, signed_to);
    const max_f = castIntToFloat(self, lim.max, ft, signed_to);

    const lt = OpBuilder.init("arith.cmpf", self.loc).builder()
        .operands(&.{ v, min_f })
        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OLT))})
        .results(&.{self.i1_ty}).build();
    const gt = OpBuilder.init("arith.cmpf", self.loc).builder()
        .operands(&.{ v, max_f })
        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OGT))})
        .results(&.{self.i1_ty}).build();
    const isnan = OpBuilder.init("arith.cmpf", self.loc).builder()
        .operands(&.{ v, v })
        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_UNO))})
        .results(&.{self.i1_ty}).build();
    self.append(lt);
    self.append(gt);
    self.append(isnan);

    var fail = self.boolOr(lt.getResult(0), gt.getResult(0));
    fail = self.boolOr(fail, isnan.getResult(0));

    // clamp
    const sel_low = OpBuilder.init("arith.select", self.loc).builder()
        .operands(&.{ lt.getResult(0), min_f, v }).results(&.{ft}).build();
    self.append(sel_low);
    const sel_hi = OpBuilder.init("arith.select", self.loc).builder()
        .operands(&.{ gt.getResult(0), max_f, sel_low.getResult(0) }).results(&.{ft}).build();
    self.append(sel_hi);

    return castFloatToInt(self, sel_hi.getResult(0), to_ty, signed_to);
}

// --- Checked helpers ---
pub fn checkedIntToInt(self: *Codegen, v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type, from_signed: bool) mlir.Value {
    // Convert normally (trunc/extend)
    const narrowed = self.castIntToInt(v, from_ty, to_ty, from_signed);

    // Re-extend to source width and compare equality (round-trip check)
    const widened = self.appendIfHasResult(OpBuilder.init(if (from_signed) "arith.extsi" else "arith.extui", self.loc).builder()
        .operands(&.{narrowed}).results(&.{from_ty}).build());

    const ok = OpBuilder.init("arith.cmpi", self.loc).builder()
        .operands(&.{ v, widened })
        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, CMP_EQ))})
        .results(&.{self.i1_ty}).build();
    self.append(ok);
    self.emitAssertCall(ok.getResult(0)); // trap if overflow

    return narrowed;
}

pub fn checkedFloatToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
    const lim = self.intMinMax(to_ty, signed_to);
    const ft = v.getType();
    const min_f = self.castIntToFloat(lim.min, ft, signed_to);
    const max_f = self.castIntToFloat(lim.max, ft, signed_to);

    const lt = OpBuilder.init("arith.cmpf", self.loc).builder()
        .operands(&.{ v, min_f })
        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OLT))})
        .results(&.{self.i1_ty}).build();
    const gt = OpBuilder.init("arith.cmpf", self.loc).builder()
        .operands(&.{ v, max_f })
        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OGT))})
        .results(&.{self.i1_ty}).build();
    const isnan = OpBuilder.init("arith.cmpf", self.loc).builder()
        .operands(&.{ v, v })
        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_UNO))})
        .results(&.{self.i1_ty}).build();
    self.append(lt);
    self.append(gt);
    self.append(isnan);

    var bad = self.boolOr(lt.getResult(0), gt.getResult(0));
    bad = self.boolOr(bad, isnan.getResult(0));

    // assert(!bad)
    const ok = self.boolNot(bad);
    self.emitAssertCall(ok);

    return self.castFloatToInt(v, to_ty, signed_to);
}

// --- The normalized "normal cast" (includes Complex + slice→int quirk) ---
pub fn emitCastNormal(self: *Codegen, dst_sr: types.TypeId, to_ty: mlir.Type, from_v: mlir.Value, src_sr: types.TypeId) !mlir.Value {
    var from_ty = from_v.getType();

    if (from_ty.equal(self.llvm_ptr_ty) and mlir.LLVM.isLLVMStructType(to_ty)) {
        var load = OpBuilder.init("llvm.load", self.loc).builder()
            .operands(&.{from_v})
            .results(&.{to_ty}).build();
        self.append(load);
        return load.getResult(0);
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
        var ld_union = OpBuilder.init("llvm.load", self.loc).builder()
            .operands(&.{tmp_union_ptr})
            .results(&.{union_mlir}).build();
        self.append(ld_union);

        // Assemble the ErrorSet aggregate: { tag: i32 = 0, payload: union }
        var acc = self.zeroOf(to_ty);
        const tag0 = self.constInt(self.i32_ty, 0);
        acc = self.insertAt(acc, tag0, &.{0});
        acc = self.insertAt(acc, ld_union.getResult(0), &.{1});
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
            var op = OpBuilder.init("vector.from_elements", self.loc).builder()
                .operands(elems)
                .results(&.{vec_ty})
                .build();
            self.append(op);
            return op.getResult(0);
        }
    }

    if (try self.tryCopyAggregateValue(dst_sr, to_ty, from_v, src_sr, emitCastAggregateElement)) |agg|
        return agg;

    if (try self.reinterpretAggregateViaSpill(dst_sr, to_ty, from_v, src_sr)) |agg|
        return agg;
    if (self.isUndefValue(from_v)) return self.undefOf(to_ty);

    if (self.isUndefValue(from_v)) return self.undefOf(to_ty);

    // Fallback: avoid invalid bitcasts on aggregates. If either side is an
    // LLVM struct (aggregate), do not emit an arith.bitcast which is invalid
    // for structs. Let the caller supply a properly shaped value instead.
    if (mlir.LLVM.isLLVMStructType(from_v.getType()) or mlir.LLVM.isLLVMStructType(to_ty)) {
        // Minimal breadcrumb to help locate the source site during bring-up.
        std.debug.print("codegen_cast: skip bitcast for aggregate types\n", .{});
        return from_v;
    }
    const op = OpBuilder.init("arith.bitcast", self.loc).builder()
        .operands(&.{from_v}).results(&.{to_ty}).build();
    return self.appendIfHasResult(op);
}

// --- Public dispatcher for all cast kinds ---
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
                    const widened = self.appendIfHasResult(OpBuilder.init(if (from_signed) "arith.extsi" else "arith.extui", self.loc).builder()
                        .operands(&.{narrowed}).results(&.{from_ty_mlir}).build());
                    cast_ok = self.appendIfHasResult(OpBuilder.init("arith.cmpi", self.loc).builder()
                        .operands(&.{ from_v, widened })
                        .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, CMP_EQ))})
                        .results(&.{self.i1_ty}).build());
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

                const lt = self.appendIfHasResult(OpBuilder.init("arith.cmpf", self.loc).builder()
                    .operands(&.{ from_v, min_f })
                    .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OLT))})
                    .results(&.{self.i1_ty}).build());
                const gt = self.appendIfHasResult(OpBuilder.init("arith.cmpf", self.loc).builder()
                    .operands(&.{ from_v, max_f })
                    .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OGT))})
                    .results(&.{self.i1_ty}).build());
                const isnan = self.appendIfHasResult(OpBuilder.init("arith.cmpf", self.loc).builder()
                    .operands(&.{ from_v, from_v })
                    .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_UNO))})
                    .results(&.{self.i1_ty}).build());

                var bad = self.boolOr(lt, gt);
                bad = self.boolOr(bad, isnan);
                cast_ok = self.boolNot(bad);

                // Clamp the source value into the integer domain (or a benign value for NaN)
                const clamped_low = self.appendIfHasResult(OpBuilder.init("arith.select", self.loc).builder()
                    .operands(&.{ lt, min_f, from_v }).results(&.{ft}).build());
                const clamped_high = self.appendIfHasResult(OpBuilder.init("arith.select", self.loc).builder()
                    .operands(&.{ gt, max_f, clamped_low }).results(&.{ft}).build());
                const zero = self.constFloat(ft, 0.0);
                const sanitized = self.appendIfHasResult(OpBuilder.init("arith.select", self.loc).builder()
                    .operands(&.{ isnan, zero, clamped_high }).results(&.{ft}).build());

                casted_val = castFloatToInt(self, sanitized, optional_elem_mlir_ty, optional_elem_is_signed);

                // Verify round-trip back to float to catch fractional values.
                const roundtrip = castIntToFloat(self, casted_val, ft, optional_elem_is_signed);
                const same = self.appendIfHasResult(OpBuilder.init("arith.cmpf", self.loc).builder()
                    .operands(&.{ from_v, roundtrip })
                    .attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OEQ))})
                    .results(&.{self.i1_ty}).build());
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

fn castPtrToPtr(self: *Codegen, v: mlir.Value, to_ty: mlir.Type) mlir.Value {
    // Use LLVM dialect bitcast for pointer-to-pointer casts
    const op = OpBuilder.init("llvm.bitcast", self.loc).builder()
        .operands(&.{v}).results(&.{to_ty}).build();
    return self.appendIfHasResult(op);
}
fn castPtrToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type) mlir.Value {
    const op = OpBuilder.init("llvm.ptrtoint", self.loc).builder()
        .operands(&.{v}).results(&.{to_ty}).build();
    return self.appendIfHasResult(op);
}
fn castIntToPtr(self: *Codegen, v: mlir.Value, to_ty: mlir.Type) mlir.Value {
    const op = OpBuilder.init("llvm.inttoptr", self.loc).builder()
        .operands(&.{v}).results(&.{to_ty}).build();
    return self.appendIfHasResult(op);
}

fn castIntToInt(self: *Codegen, from_v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type, signed_from: bool) mlir.Value {
    const fw = intOrFloatWidth(from_ty) catch 0;
    const tw = intOrFloatWidth(to_ty) catch 0;
    if (fw == tw) return from_v;
    if (fw > tw) {
        const op = OpBuilder.init("arith.trunci", self.loc).builder()
            .operands(&.{from_v}).results(&.{to_ty}).build();
        return self.appendIfHasResult(op);
    }
    const opname = if (signed_from) "arith.extsi" else "arith.extui";
    const op = OpBuilder.init(opname, self.loc).builder()
        .operands(&.{from_v}).results(&.{to_ty}).build();
    return self.appendIfHasResult(op);
}

fn castIntToFloat(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_from: bool) mlir.Value {
    const op = OpBuilder.init(if (signed_from) "arith.sitofp" else "arith.uitofp", self.loc).builder()
        .operands(&.{v}).results(&.{to_ty}).build();
    return self.appendIfHasResult(op);
}

fn castFloatToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
    const op = OpBuilder.init(if (signed_to) "arith.fptosi" else "arith.fptoui", self.loc).builder()
        .operands(&.{v}).results(&.{to_ty}).build();
    return self.appendIfHasResult(op);
}

fn resizeFloat(self: *Codegen, v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type) mlir.Value {
    const fw = intOrFloatWidth(from_ty) catch 0;
    const tw = intOrFloatWidth(to_ty) catch 0;
    if (fw == tw) return v;
    const opname = if (fw > tw) "arith.truncf" else "arith.extf";
    const op = OpBuilder.init(opname, self.loc).builder()
        .operands(&.{v}).results(&.{to_ty}).build();
    return self.appendIfHasResult(op);
}

// --- Integer limits as MLIR constants (destination type) ---
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
