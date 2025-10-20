module attributes {llvm.data_layout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128", llvm.target_triple = "x86_64-unknown-linux-gnu"} {
  llvm.mlir.global internal @"$__sr_prelude_0"() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.func @ptrcast(...) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @printf(i64, ...) -> i32 attributes {sym_visibility = "private"}
  func.func public @main() -> i32 {
    %0 = llvm.mlir.constant(0 : i64) : i64
    %1 = llvm.mlir.constant(1 : i64) : i64
    %2 = llvm.alloca %1 x i64 : (i64) -> !llvm.ptr
    llvm.store %0, %2 : i64, !llvm.ptr
    %3 = llvm.mlir.constant(0 : i64) : i64
    %4 = llvm.mlir.constant(1 : i64) : i64
    %5 = llvm.alloca %4 x i64 : (i64) -> !llvm.ptr
    llvm.store %3, %5 : i64, !llvm.ptr
    cf.br ^bb1
  ^bb1:  // 2 preds: ^bb0, ^bb6
    %6 = llvm.load %2 : !llvm.ptr -> i64
    %7 = llvm.mlir.constant(2 : i64) : i64
    %8 = arith.cmpi slt, %6, %7 : i64
    cf.cond_br %8, ^bb2, ^bb3
  ^bb2:  // pred: ^bb1
    %9 = llvm.mlir.constant(0 : i64) : i64
    llvm.store %9, %5 : i64, !llvm.ptr
    cf.br ^bb4
  ^bb3:  // pred: ^bb1
    %10 = llvm.mlir.undef : !llvm.ptr
    %11 = llvm.mlir.constant(0 : i64) : i64
    %12 = llvm.trunc %11 : i64 to i32
    cf.br ^bb7(%12 : i32)
  ^bb4:  // 2 preds: ^bb2, ^bb5
    %13 = llvm.load %5 : !llvm.ptr -> i64
    %14 = llvm.mlir.constant(2 : i64) : i64
    %15 = arith.cmpi slt, %13, %14 : i64
    cf.cond_br %15, ^bb5, ^bb6
  ^bb5:  // pred: ^bb4
    %16 = llvm.mlir.addressof @__str_82f56d4f38487990 : !llvm.ptr
    %17 = llvm.getelementptr %16[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<12 x i8>
    %18 = llvm.mlir.constant(11 : i64) : i64
    %19 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %20 = llvm.insertvalue %17, %19[0] : !llvm.struct<(ptr, i64)>
    %21 = llvm.insertvalue %18, %20[1] : !llvm.struct<(ptr, i64)>
    %22 = llvm.load %2 : !llvm.ptr -> i64
    %23 = llvm.load %5 : !llvm.ptr -> i64
    %24 = llvm.mlir.constant(1 : i64) : i64
    %25 = llvm.alloca %24 x !llvm.struct<(ptr, i64)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %21, %25 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %26 = llvm.load %25 : !llvm.ptr -> i64
    %27 = llvm.call @printf(%26, %22, %23) vararg(!llvm.func<i32 (i64, ...)>) : (i64, i64, i64) -> i32
    %28 = llvm.load %5 : !llvm.ptr -> i64
    %29 = llvm.mlir.constant(1 : i64) : i64
    %30 = arith.addi %28, %29 : i64
    llvm.store %30, %5 : i64, !llvm.ptr
    cf.br ^bb4
  ^bb6:  // pred: ^bb4
    %31 = llvm.mlir.undef : !llvm.ptr
    %32 = llvm.load %2 : !llvm.ptr -> i64
    %33 = llvm.mlir.constant(1 : i64) : i64
    %34 = arith.addi %32, %33 : i64
    llvm.store %34, %2 : i64, !llvm.ptr
    cf.br ^bb1
  ^bb7(%35: i32):  // pred: ^bb3
    return %35 : i32
  }
  llvm.mlir.global internal constant @__str_82f56d4f38487990("i=%d, j=%d\0A\00") {addr_space = 0 : i32}
}
