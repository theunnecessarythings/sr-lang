const codegen = @import("codegen_main.zig");
const Codegen = codegen.Codegen;
const EmitOpArgs = codegen.EmitOpArgs;
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const std = @import("std");

// MLIR Predicates
const PRED = struct {
    const EQ: i64 = 0;
    const NE: i64 = 1;
    const SLT: i64 = 2;
    const SLE: i64 = 3;
    const SGT: i64 = 4;
    const SGE: i64 = 5;
    const ULT: i64 = 6;
    const ULE: i64 = 7;
    const UGT: i64 = 8;
    const UGE: i64 = 9;
    const FOEQ: i64 = 1;
    const FOGT: i64 = 2;
    const FOLT: i64 = 4;
    const FUNO: i64 = 14;
};

/// Helper to create a named predicate attribute for cmpi/cmpf ops
inline fn getPred(self: *Codegen, val: i64) mlir.NamedAttribute {
    return self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, val));
}

pub fn intOrFloatWidth(t: mlir.Type) !u32 {
    if (t.isAInteger()) return t.getIntegerBitwidth();
    if (t.isAFloat()) return t.getFloatBitwidth();
    if (t.isAVector() or t.isATensor()) {
        const et = t.getShapedElementType();
        if (et.isAInteger()) return et.getIntegerBitwidth();
        if (et.isAFloat()) return et.getFloatBitwidth();
    }
    return error.NotIntOrFloat;
}

fn emitCastAggregateElement(self: *Codegen, dst_sr: types.TypeId, dst_ty: mlir.Type, src_val: mlir.Value, src_sr: types.TypeId) anyerror!mlir.Value {
    return emitCastNormal(self, dst_sr, dst_ty, src_val, src_sr);
}

// --- Saturating Helpers ---

pub fn saturateIntToInt(self: *Codegen, v: mlir.Value, from_signed: bool, to_ty: mlir.Type, to_signed: bool) mlir.Value {
    const lim = intMinMax(self, to_ty, to_signed);
    const from_ty = v.getType();
    const ext_op = if (from_signed) "arith.extsi" else "arith.extui";

    const min_in = self.emitUnaryValueOp(ext_op, lim.min, from_ty);
    const max_in = self.emitUnaryValueOp(ext_op, lim.max, from_ty);

    const lt = self.emitBinaryValueOp("arith.cmpi", v, min_in, self.i1_ty, &.{getPred(self, if (from_signed) PRED.SLT else PRED.ULT)});
    const gt = self.emitBinaryValueOp("arith.cmpi", v, max_in, self.i1_ty, &.{getPred(self, if (from_signed) PRED.SGT else PRED.UGT)});

    const sel_low = self.emitOp("arith.select", EmitOpArgs{ .operands = &.{ lt, min_in, v }, .results = &.{from_ty} });
    const sel_hi = self.emitOp("arith.select", EmitOpArgs{ .operands = &.{ gt, max_in, sel_low }, .results = &.{from_ty} });

    return castIntToInt(self, sel_hi, from_ty, to_ty, from_signed);
}

pub fn saturateFloatToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
    const lim = intMinMax(self, to_ty, signed_to);
    const ft = v.getType();
    const min_f = castIntToFloat(self, lim.min, ft, signed_to);
    const max_f = castIntToFloat(self, lim.max, ft, signed_to);

    const lt = self.emitBinaryValueOp("arith.cmpf", v, min_f, self.i1_ty, &.{getPred(self, PRED.FOLT)});
    const gt = self.emitBinaryValueOp("arith.cmpf", v, max_f, self.i1_ty, &.{getPred(self, PRED.FOGT)});

    // clamp: select(gt, max, select(lt, min, v))
    const s1 = self.emitOp("arith.select", EmitOpArgs{ .operands = &.{ lt, min_f, v }, .results = &.{ft} });
    const s2 = self.emitOp("arith.select", EmitOpArgs{ .operands = &.{ gt, max_f, s1 }, .results = &.{ft} });

    return castFloatToInt(self, s2, to_ty, signed_to);
}

// --- Checked Helpers ---

pub fn checkedIntToInt(self: *Codegen, v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type, from_signed: bool) mlir.Value {
    const narrowed = castIntToInt(self, v, from_ty, to_ty, from_signed);
    const widened = self.emitUnaryValueOp(if (from_signed) "arith.extsi" else "arith.extui", narrowed, from_ty);
    const ok = self.emitBinaryValueOp("arith.cmpi", v, widened, self.i1_ty, &.{getPred(self, PRED.EQ)});
    self.emitAssertCall(ok.getResult(0));
    return narrowed;
}

pub fn checkedFloatToInt(self: *Codegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
    const lim = intMinMax(self, to_ty, signed_to);
    const ft = v.getType();
    const min_f = castIntToFloat(self, lim.min, ft, signed_to);
    const max_f = castIntToFloat(self, lim.max, ft, signed_to);

    const lt = self.emitBinaryValueOp("arith.cmpf", v, min_f, self.i1_ty, &.{getPred(self, PRED.FOLT)});
    const gt = self.emitBinaryValueOp("arith.cmpf", v, max_f, self.i1_ty, &.{getPred(self, PRED.FOGT)});
    const nan = self.emitBinaryValueOp("arith.cmpf", v, v, self.i1_ty, &.{getPred(self, PRED.FUNO)});

    const ok = self.boolNot(self.boolOr(self.boolOr(lt, gt), nan));
    self.emitAssertCall(ok);
    return castFloatToInt(self, v, to_ty, signed_to);
}

// --- Main Cast Logic ---

pub fn emitCastNormal(self: *Codegen, dst_sr: types.TypeId, to_ty: mlir.Type, from_v: mlir.Value, src_sr: types.TypeId) !mlir.Value {
    const from_ty = from_v.getType();
    if (from_ty.equal(to_ty)) return from_v;

    // 1. Pointer Load (Ptr -> Struct)
    if (from_ty.equal(self.llvm_ptr_ty) and mlir.LLVM.isLLVMStructType(to_ty)) {
        return self.emitOp("llvm.load", EmitOpArgs{ .operands = &.{from_v}, .results = &.{to_ty} });
    }

    const ts = self.context.type_store;
    const dst_kind = ts.getKind(dst_sr);
    const src_kind = ts.getKind(src_sr);

    // 2. ErrorSet Construction
    if (dst_kind == .ErrorSet and src_kind != .ErrorSet) {
        const es = ts.get(.ErrorSet, dst_sr);
        const ok_name = ts.strs.intern("Ok");
        const err_name = ts.strs.intern("Err");
        var fields = [_]types.TypeStore.StructFieldArg{ .{ .name = ok_name, .ty = es.value_ty }, .{ .name = err_name, .ty = es.error_ty } };
        const union_sr = ts.mkUnion(&fields);
        const union_mlir = try self.llvmTypeOf(union_sr);
        const ok_payload_mlir = try self.llvmTypeOf(es.value_ty);

        var payload = from_v;
        if (!payload.getType().equal(ok_payload_mlir)) {
            payload = try self.coerceOnBranch(payload, ok_payload_mlir, es.value_ty, src_sr);
        }

        const ptr = self.spillAgg(self.undefOf(union_mlir), union_mlir, 0);
        self.storeAt(ptr, payload, 0);
        const ld_union = self.emitOp("llvm.load", EmitOpArgs{ .operands = &.{ptr}, .results = &.{union_mlir} });

        const acc = self.insertAt(self.zeroOf(to_ty), self.constInt(self.i32_ty, 0), &.{0});
        return self.insertAt(acc, ld_union, &.{1});
    }

    // 3. Complex Numbers
    if (dst_kind == .Complex) {
        const tgt = ts.get(.Complex, dst_sr);
        const elem_ty = try self.llvmTypeOf(tgt.elem);

        if (src_kind == .Complex) {
            const src_c = ts.get(.Complex, src_sr);
            const src_elem_ty = try self.llvmTypeOf(src_c.elem);
            if (src_elem_ty.equal(elem_ty)) return from_v;
            return self.complexFromParts(resizeFloat(self, self.complexRe(from_v, src_elem_ty), src_elem_ty, elem_ty), resizeFloat(self, self.complexIm(from_v, src_elem_ty), src_elem_ty, elem_ty), to_ty);
        } else {
            // Scalar -> Complex
            var re = from_v;
            if (from_ty.isAInteger() and elem_ty.isAFloat()) {
                re = castIntToFloat(self, from_v, elem_ty, self.isSignedInt(src_sr));
            } else if (from_ty.isAFloat() and elem_ty.isAFloat()) {
                re = resizeFloat(self, from_v, from_ty, elem_ty);
            }
            return self.complexFromParts(re, self.constFloat(elem_ty, 0.0), to_ty);
        }
    }

    // 4. Special Quirks (Slice->Int, Splat, Array->DynArray)
    if (src_kind == .Slice and to_ty.isAInteger()) return self.constInt(to_ty, 0);

    if (dst_kind == .Tensor) {
        const tinfo = ts.get(.Tensor, dst_sr);
        const elem_ty = try self.llvmTypeOf(tinfo.elem);
        if (!from_ty.isATensor() and !from_ty.isAVector()) {
            var scalar = from_v;
            if (!scalar.getType().equal(elem_ty)) scalar = try self.coerceOnBranch(scalar, elem_ty, tinfo.elem, src_sr);
            const op = if (self.emit_only_triton) "tt.splat" else "tensor.splat";
            return self.emitOp(op, EmitOpArgs{ .operands = &.{scalar}, .results = &.{to_ty} });
        }
    }

    if (dst_kind == .DynArray and src_kind == .Array) {
        if (ts.get(.Array, src_sr).len == 0) return self.zeroOf(to_ty);
    }

    // 5. Scalars & Pointers (The hot path)
    const from_ptr = from_ty.equal(self.llvm_ptr_ty);
    const to_ptr = to_ty.equal(self.llvm_ptr_ty);

    if (from_ptr and to_ptr) return castPtrToPtr(self, from_v, to_ty);

    // Check inner types for Vectors/Tensors to treat them as int/float equivalents
    const f_et = if (from_ty.isAVector() or from_ty.isATensor()) from_ty.getShapedElementType() else from_ty;
    const t_et = if (to_ty.isAVector() or to_ty.isATensor()) to_ty.getShapedElementType() else to_ty;
    const f_int = f_et.isAInteger();
    const t_int = t_et.isAInteger();
    const f_flt = f_et.isAFloat();
    const t_flt = t_et.isAFloat();

    if (from_ptr and t_int) return castPtrToInt(self, from_v, to_ty);
    if (f_int and to_ptr) return castIntToPtr(self, from_v, to_ty);
    if (f_int and t_int) return castIntToInt(self, from_v, from_ty, to_ty, self.isSignedInt(src_sr));
    if (f_int and t_flt) return castIntToFloat(self, from_v, to_ty, self.isSignedInt(src_sr));
    if (f_flt and t_int) return castFloatToInt(self, from_v, to_ty, self.isSignedInt(dst_sr));
    if (f_flt and t_flt) return resizeFloat(self, from_v, from_ty, to_ty);

    // 6. Array -> Simd (Vector construction)
    if (dst_kind == .Simd and src_kind == .Array) {
        const simd = ts.get(.Simd, dst_sr);
        const arr = ts.get(.Array, src_sr);
        const lanes: usize = @intCast(simd.lanes);
        if (arr.len == lanes and lanes > 0) {
            const elem_mlir = try self.llvmTypeOf(simd.elem);
            var elems = try self.gpa.alloc(mlir.Value, lanes);
            defer self.gpa.free(elems);
            for (0..lanes) |i| {
                var e = self.extractAt(from_v, elem_mlir, &.{@intCast(i)});
                if (!e.getType().equal(elem_mlir)) e = try self.coerceOnBranch(e, elem_mlir, simd.elem, arr.elem);
                elems[i] = e;
            }
            return self.emitOp("vector.from_elements", EmitOpArgs{ .operands = elems, .results = &.{to_ty} });
        }
    }

    // 7. Aggregates & Fallback
    if (try self.tryCopyAggregateValue(dst_sr, to_ty, from_v, src_sr, emitCastAggregateElement)) |agg| return agg;
    if (try self.reinterpretAggregateViaSpill(dst_sr, to_ty, from_v, src_sr)) |agg| return agg;
    if (self.isUndefValue(from_v)) return self.undefOf(to_ty);

    if (mlir.LLVM.isLLVMStructType(from_ty) or mlir.LLVM.isLLVMStructType(to_ty)) {
        std.debug.print("codegen_cast: skip bitcast for aggregate types\n", .{});
        return self.undefOf(to_ty);
    }
    return self.emitUnaryValueOp("arith.bitcast", from_v, to_ty);
}

pub fn emitCast(self: *Codegen, kind: tir.OpKind, dst_sr: types.TypeId, src_sr: types.TypeId, from_v: mlir.Value) !mlir.Value {
    const to_ty = try self.llvmTypeOf(dst_sr);
    const from_ty = from_v.getType();

    switch (kind) {
        .CastNormal => return emitCastNormal(self, dst_sr, to_ty, from_v, src_sr),
        .CastWrap => {
            if (from_ty.isAInteger() and to_ty.isAInteger()) {
                return castIntToInt(self, from_v, from_ty, to_ty, self.isSignedInt(src_sr));
            }
            return emitCastNormal(self, dst_sr, to_ty, from_v, src_sr);
        },
        .CastSaturate => {
            if (from_ty.isAInteger() and to_ty.isAInteger()) {
                return saturateIntToInt(self, from_v, self.isSignedInt(src_sr), to_ty, self.isSignedInt(dst_sr));
            }
            if (from_ty.isAFloat() and to_ty.isAInteger()) {
                return saturateFloatToInt(self, from_v, to_ty, self.isSignedInt(dst_sr));
            }
            return emitCastNormal(self, dst_sr, to_ty, from_v, src_sr);
        },
        .CastChecked => {
            // Result is always Optional { bool ok, T val }
            const opt_sr = self.context.type_store.get(.Optional, dst_sr);
            const opt_mlir = try self.llvmTypeOf(dst_sr);
            const elem_mlir = try self.llvmTypeOf(opt_sr.elem);
            const elem_signed = self.isSignedInt(opt_sr.elem);

            var cast_ok = self.constBool(true);
            var val: mlir.Value = undefined;

            if (from_ty.isAInteger() and elem_mlir.isAInteger()) {
                const fw = try intOrFloatWidth(from_ty);
                const tw = try intOrFloatWidth(elem_mlir);
                const fs = self.isSignedInt(src_sr);

                val = castIntToInt(self, from_v, from_ty, elem_mlir, fs);

                if (fs and !elem_signed) {
                    // Signed -> Unsigned: source must be >= 0
                    const zero = self.constInt(from_ty, 0);
                    cast_ok = self.emitBinaryValueOp("arith.cmpi", from_v, zero, self.i1_ty, &.{getPred(self, PRED.SGE)});
                } else if (!fs and elem_signed and tw <= fw) {
                    // Unsigned -> Signed: source must fit in positive range of dest
                    const max_s_val: i128 = switch (tw) {
                        1 => 0,
                        8 => @as(i128, std.math.maxInt(i8)),
                        16 => @as(i128, std.math.maxInt(i16)),
                        32 => @as(i128, std.math.maxInt(i32)),
                        64 => @as(i128, std.math.maxInt(i64)),
                        else => @as(i128, std.math.maxInt(i64)),
                    };
                    const max_s = self.constInt(from_ty, max_s_val);
                    cast_ok = self.emitBinaryValueOp("arith.cmpi", from_v, max_s, self.i1_ty, &.{getPred(self, PRED.ULE)});
                }

                if (fw > tw) {
                    // Truncation check
                    const back = self.emitUnaryValueOp(if (fs) "arith.extsi" else "arith.extui", val, from_ty);
                    const trunc_ok = self.emitBinaryValueOp("arith.cmpi", from_v, back, self.i1_ty, &.{getPred(self, PRED.EQ)});
                    cast_ok = self.boolAnd(cast_ok, trunc_ok);
                }
            } else if (from_ty.isAFloat() and elem_mlir.isAInteger()) {
                const lim = intMinMax(self, elem_mlir, elem_signed);
                const ft = from_ty;
                const min_f = castIntToFloat(self, lim.min, ft, elem_signed);
                const max_f = castIntToFloat(self, lim.max, ft, elem_signed);

                const lt = self.emitBinaryValueOp("arith.cmpf", from_v, min_f, self.i1_ty, &.{getPred(self, PRED.FOLT)});
                const gt = self.emitBinaryValueOp("arith.cmpf", from_v, max_f, self.i1_ty, &.{getPred(self, PRED.FOGT)});
                const nan = self.emitBinaryValueOp("arith.cmpf", from_v, from_v, self.i1_ty, &.{getPred(self, PRED.FUNO)});

                cast_ok = self.boolNot(self.boolOr(self.boolOr(lt, gt), nan));

                // Safe conversion logic for Checked cast result
                const s1 = self.emitOp("arith.select", EmitOpArgs{ .operands = &.{ lt, min_f, from_v }, .results = &.{ft} });
                const s2 = self.emitOp("arith.select", EmitOpArgs{ .operands = &.{ gt, max_f, s1 }, .results = &.{ft} });
                const s3 = self.emitOp("arith.select", EmitOpArgs{ .operands = &.{ nan, self.constFloat(ft, 0.0), s2 }, .results = &.{ft} });
                val = castFloatToInt(self, s3, elem_mlir, elem_signed);

                // Roundtrip verification
                const back = castIntToFloat(self, val, ft, elem_signed);
                const same = self.emitBinaryValueOp("arith.cmpf", from_v, back, self.i1_ty, &.{getPred(self, PRED.FOEQ)});
                cast_ok = self.boolAnd(cast_ok, same);
            } else {
                val = try emitCastNormal(self, opt_sr.elem, elem_mlir, from_v, src_sr);
            }

            const res = self.insertAt(self.undefOf(opt_mlir), cast_ok, &.{0});
            return self.insertAt(res, val, &.{1});
        },
        else => unreachable,
    }
}

// --- Inline Helpers ---

inline fn castPtrToPtr(self: *Codegen, v: mlir.Value, t: mlir.Type) mlir.Value {
    return self.emitUnaryValueOp("llvm.bitcast", v, t);
}
inline fn castPtrToInt(self: *Codegen, v: mlir.Value, t: mlir.Type) mlir.Value {
    return self.emitUnaryValueOp("llvm.ptrtoint", v, t);
}
inline fn castIntToPtr(self: *Codegen, v: mlir.Value, t: mlir.Type) mlir.Value {
    return self.emitUnaryValueOp("llvm.inttoptr", v, t);
}
inline fn castIntToInt(self: *Codegen, v: mlir.Value, ft: mlir.Type, tt: mlir.Type, signed: bool) mlir.Value {
    const fw = intOrFloatWidth(ft) catch 0;
    const tw = intOrFloatWidth(tt) catch 0;
    if (fw == tw) return v;
    if (fw > tw) return self.emitUnaryValueOp("arith.trunci", v, tt);
    return self.emitUnaryValueOp(if (signed) "arith.extsi" else "arith.extui", v, tt);
}
inline fn castIntToFloat(self: *Codegen, v: mlir.Value, t: mlir.Type, signed: bool) mlir.Value {
    return self.emitUnaryValueOp(if (signed) "arith.sitofp" else "arith.uitofp", v, t);
}
inline fn castFloatToInt(self: *Codegen, v: mlir.Value, t: mlir.Type, signed: bool) mlir.Value {
    return self.emitUnaryValueOp(if (signed) "arith.fptosi" else "arith.fptoui", v, t);
}
inline fn resizeFloat(self: *Codegen, v: mlir.Value, ft: mlir.Type, tt: mlir.Type) mlir.Value {
    const fw = intOrFloatWidth(ft) catch 0;
    const tw = intOrFloatWidth(tt) catch 0;
    if (fw == tw) return v;
    return self.emitUnaryValueOp(if (fw > tw) "arith.truncf" else "arith.extf", v, tt);
}

fn intMinMax(self: *Codegen, to_ty: mlir.Type, signed: bool) struct { min: mlir.Value, max: mlir.Value } {
    const w = intOrFloatWidth(to_ty) catch 1;
    // Calculate raw limit values based on bitwidth
    if (signed) {
        var min_i: i64 = undefined;
        var max_i: i64 = undefined;
        switch (w) {
            1, 8 => {
                min_i = std.math.minInt(i8);
                max_i = std.math.maxInt(i8);
            },
            16 => {
                min_i = std.math.minInt(i16);
                max_i = std.math.maxInt(i16);
            },
            32 => {
                min_i = std.math.minInt(i32);
                max_i = std.math.maxInt(i32);
            },
            else => {
                min_i = std.math.minInt(i64);
                max_i = std.math.maxInt(i64);
            },
        }
        return .{ .min = self.constInt(to_ty, min_i), .max = self.constInt(to_ty, max_i) };
    } else {
        var max_u: u64 = undefined;
        switch (w) {
            1, 8 => max_u = std.math.maxInt(u8),
            16 => max_u = std.math.maxInt(u16),
            32 => max_u = std.math.maxInt(u32),
            else => max_u = std.math.maxInt(u64),
        }
        return .{ .min = self.constInt(to_ty, 0), .max = self.constInt(to_ty, @intCast(max_u)) };
    }
}
