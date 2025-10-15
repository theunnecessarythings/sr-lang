module attributes {llvm.data_layout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128", llvm.target_triple = "x86_64-unknown-linux-gnu"} {
  llvm.func @printf(i64, ...) -> i32 attributes {sym_visibility = "private"}
  llvm.func @__assert_fail(i64, i64, i32, i64) attributes {sym_visibility = "private"}
  func.func public @assert(%arg0: i1) {
    %0 = llvm.mlir.constant(true) : i1
    %1 = arith.xori %arg0, %0 : i1
    cf.cond_br %1, ^bb1, ^bb2
  ^bb1:  // pred: ^bb0
    %2 = llvm.mlir.addressof @__str_90733134195be8cc : !llvm.ptr
    %3 = llvm.getelementptr %2[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<17 x i8>
    %4 = llvm.mlir.constant(16 : i64) : i64
    %5 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %6 = llvm.insertvalue %3, %5[0] : !llvm.struct<(ptr, i64)> 
    %7 = llvm.insertvalue %4, %6[1] : !llvm.struct<(ptr, i64)> 
    %8 = llvm.mlir.addressof @__str_f9e6e6ef197c2b25 : !llvm.ptr
    %9 = llvm.getelementptr %8[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<5 x i8>
    %10 = llvm.mlir.constant(4 : i64) : i64
    %11 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %12 = llvm.insertvalue %9, %11[0] : !llvm.struct<(ptr, i64)> 
    %13 = llvm.insertvalue %10, %12[1] : !llvm.struct<(ptr, i64)> 
    %14 = llvm.mlir.constant(1 : i64) : i64
    %15 = llvm.mlir.constant(0 : i64) : i64
    %16 = arith.subi %15, %14 : i64
    %17 = llvm.trunc %16 : i64 to i32
    %18 = llvm.mlir.addressof @__str_f89e75bdb43c5a5b : !llvm.ptr
    %19 = llvm.getelementptr %18[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<7 x i8>
    %20 = llvm.mlir.constant(6 : i64) : i64
    %21 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %22 = llvm.insertvalue %19, %21[0] : !llvm.struct<(ptr, i64)> 
    %23 = llvm.insertvalue %20, %22[1] : !llvm.struct<(ptr, i64)> 
    %24 = llvm.mlir.constant(1 : i64) : i64
    %25 = llvm.alloca %24 x !llvm.struct<(ptr, i64)> : (i64) -> !llvm.ptr
    llvm.store %7, %25 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %26 = llvm.load %25 : !llvm.ptr -> i64
    %27 = llvm.mlir.constant(1 : i64) : i64
    %28 = llvm.alloca %27 x !llvm.struct<(ptr, i64)> : (i64) -> !llvm.ptr
    llvm.store %13, %28 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %29 = llvm.load %28 : !llvm.ptr -> i64
    %30 = llvm.mlir.constant(1 : i64) : i64
    %31 = llvm.alloca %30 x !llvm.struct<(ptr, i64)> : (i64) -> !llvm.ptr
    llvm.store %23, %31 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %32 = llvm.load %31 : !llvm.ptr -> i64
    llvm.call @__assert_fail(%26, %29, %17, %32) : (i64, i64, i32, i64) -> ()
    cf.br ^bb3
  ^bb2:  // pred: ^bb0
    cf.br ^bb3
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %33 = llvm.mlir.undef : !llvm.ptr
    return
  }
  func.func public @main() -> i32 {
    %0 = llvm.mlir.constant(-56 : i8) : i8
    %1 = llvm.mlir.constant(1 : i64) : i64
    %2 = llvm.alloca %1 x i8 : (i64) -> !llvm.ptr
    llvm.store %0, %2 : i8, !llvm.ptr
    %3 = llvm.load %2 : !llvm.ptr -> i8
    %4 = llvm.mlir.constant(2 : i64) : i64
    %5 = llvm.trunc %4 : i64 to i8
    %6 = arith.extui %3 : i8 to i16
    %7 = arith.extui %5 : i8 to i16
    %8 = arith.shli %6, %7 : i16
    %9 = llvm.mlir.constant(0 : i8) : i8
    %10 = llvm.mlir.constant(-1 : i8) : i8
    %11 = llvm.zext %9 : i8 to i16
    %12 = llvm.zext %10 : i8 to i16
    %13 = arith.cmpi ult, %8, %11 : i16
    %14 = arith.cmpi ugt, %8, %12 : i16
    %15 = arith.select %13, %11, %8 : i16
    %16 = arith.select %14, %12, %15 : i16
    %17 = llvm.trunc %16 : i16 to i8
    %18 = llvm.mlir.constant(1 : i64) : i64
    %19 = llvm.alloca %18 x i8 : (i64) -> !llvm.ptr
    llvm.store %17, %19 : i8, !llvm.ptr
    %20 = llvm.mlir.addressof @__str_187e97c3ec7c58df : !llvm.ptr
    %21 = llvm.getelementptr %20[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<12 x i8>
    %22 = llvm.mlir.constant(11 : i64) : i64
    %23 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %24 = llvm.insertvalue %21, %23[0] : !llvm.struct<(ptr, i64)> 
    %25 = llvm.insertvalue %22, %24[1] : !llvm.struct<(ptr, i64)> 
    %26 = llvm.load %19 : !llvm.ptr -> i8
    %27 = llvm.mlir.constant(1 : i64) : i64
    %28 = llvm.alloca %27 x !llvm.struct<(ptr, i64)> : (i64) -> !llvm.ptr
    llvm.store %25, %28 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %29 = llvm.load %28 : !llvm.ptr -> i64
    %30 = llvm.call @printf(%29, %26) vararg(!llvm.func<i32 (i64, ...)>) : (i64, i8) -> i32
    %31 = llvm.mlir.constant(0 : i64) : i64
    %32 = llvm.trunc %31 : i64 to i32
    return %32 : i32
  }
  llvm.mlir.global internal constant @__str_90733134195be8cc("Assertion failed\00") {addr_space = 0 : i32}
  llvm.mlir.global internal constant @__str_f9e6e6ef197c2b25("test\00") {addr_space = 0 : i32}
  llvm.mlir.global internal constant @__str_f89e75bdb43c5a5b("assert\00") {addr_space = 0 : i32}
  llvm.mlir.global internal constant @__str_187e97c3ec7c58df("Result: %d\0A\00") {addr_space = 0 : i32}
}
