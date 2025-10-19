module attributes {llvm.data_layout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128", llvm.target_triple = "x86_64-unknown-linux-gnu"} {
  llvm.mlir.global internal @"$__sr_prelude_0"() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.func @ptrcast(...) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @printf(i64, ...) -> i32 attributes {sym_visibility = "private"}
  func.func public @main() -> i32 {
    %0 = llvm.mlir.constant(1 : i64) : i64
    %1 = llvm.trunc %0 : i64 to i32
    %2 = llvm.mlir.constant(2 : i64) : i64
    %3 = llvm.trunc %2 : i64 to i32
    %4 = llvm.mlir.constant(3 : i64) : i64
    %5 = llvm.trunc %4 : i64 to i32
    %6 = llvm.mlir.constant(4 : i64) : i64
    %7 = llvm.trunc %6 : i64 to i32
    %from_elements = tensor.from_elements %1, %3, %5, %7 : tensor<2x2xi32>
    %8 = llvm.mlir.constant(0 : i64) : i64
    %9 = llvm.inttoptr %8 : i64 to !llvm.ptr
    %10 = llvm.mlir.constant(5 : i64) : i64
    %11 = llvm.trunc %10 : i64 to i32
    %12 = llvm.mlir.constant(6 : i64) : i64
    %13 = llvm.trunc %12 : i64 to i32
    %14 = llvm.mlir.constant(7 : i64) : i64
    %15 = llvm.trunc %14 : i64 to i32
    %16 = llvm.mlir.constant(8 : i64) : i64
    %17 = llvm.trunc %16 : i64 to i32
    %from_elements_0 = tensor.from_elements %11, %13, %15, %17 : tensor<2x2xi32>
    %18 = llvm.mlir.constant(0 : i64) : i64
    %19 = llvm.inttoptr %18 : i64 to !llvm.ptr
    %20 = arith.addi %from_elements, %from_elements_0 : tensor<2x2xi32>
    %21 = llvm.mlir.constant(0 : i64) : i64
    %22 = llvm.inttoptr %21 : i64 to !llvm.ptr
    %23 = llvm.mlir.addressof @__str_44a786e5b808c007 : !llvm.ptr
    %24 = llvm.getelementptr %23[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<28 x i8>
    %25 = llvm.mlir.constant(27 : i64) : i64
    %26 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %27 = llvm.insertvalue %24, %26[0] : !llvm.struct<(ptr, i64)>
    %28 = llvm.insertvalue %25, %27[1] : !llvm.struct<(ptr, i64)>
    %29 = llvm.mlir.constant(0 : i64) : i64
    %30 = arith.index_cast %29 : i64 to index
    %from_elements_1 = tensor.from_elements %30 : tensor<1xindex>
    %extracted_slice = tensor.extract_slice %20[0, 0] [1, 2] [1, 1] : tensor<2x2xi32> to tensor<1x2xi32>
    %collapsed = tensor.collapse_shape %extracted_slice [[0, 1]] : tensor<1x2xi32> into tensor<2xi32>
    %31 = llvm.mlir.constant(0 : i64) : i64
    %32 = arith.index_cast %31 : i64 to index
    %extracted = tensor.extract %collapsed[%32] : tensor<2xi32>
    %33 = llvm.mlir.constant(1 : i64) : i64
    %34 = arith.index_cast %33 : i64 to index
    %from_elements_2 = tensor.from_elements %34 : tensor<1xindex>
    %extracted_slice_3 = tensor.extract_slice %20[0, 0] [1, 2] [1, 1] : tensor<2x2xi32> to tensor<1x2xi32>
    %collapsed_4 = tensor.collapse_shape %extracted_slice_3 [[0, 1]] : tensor<1x2xi32> into tensor<2xi32>
    %35 = llvm.mlir.constant(1 : i64) : i64
    %36 = arith.index_cast %35 : i64 to index
    %extracted_5 = tensor.extract %collapsed_4[%36] : tensor<2xi32>
    %37 = llvm.mlir.constant(1 : i64) : i64
    %38 = llvm.alloca %37 x !llvm.struct<(ptr, i64)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %28, %38 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %39 = llvm.load %38 : !llvm.ptr -> i64
    %40 = llvm.call @printf(%39, %extracted, %extracted_5) vararg(!llvm.func<i32 (i64, ...)>) : (i64, i32, i32) -> i32
    %41 = llvm.mlir.constant(0 : i64) : i64
    %42 = llvm.trunc %41 : i64 to i32
    cf.br ^bb1(%42 : i32)
  ^bb1(%43: i32):  // pred: ^bb0
    return %43 : i32
  }
  llvm.mlir.global internal constant @__str_44a786e5b808c007("Sum[0][0]=%d, Sum[1][1]=%d\0A\00") {addr_space = 0 : i32}
}
