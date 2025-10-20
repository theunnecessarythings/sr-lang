module attributes {llvm.data_layout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128", llvm.target_triple = "x86_64-unknown-linux-gnu"} {
  llvm.func @malloc(i64) -> !llvm.ptr
  llvm.mlir.global internal @"$__sr_prelude_0"() {addr_space = 0 : i32, sym_visibility = "private"} : !llvm.ptr
  llvm.func @ptrcast(...) -> !llvm.ptr attributes {sym_visibility = "private"}
  llvm.func @printf(i64, ...) -> i32 attributes {sym_visibility = "private"}
  llvm.func @main() -> i32 {
    %0 = llvm.mlir.constant(2 : index) : i64
    %1 = llvm.mlir.constant(1 : index) : i64
    %2 = llvm.mlir.constant(0 : index) : i64
    %3 = llvm.mlir.undef : !llvm.struct<(ptr, i64)>
    %4 = llvm.mlir.constant(27 : i64) : i64
    %5 = llvm.mlir.addressof @__str_44a786e5b808c007 : !llvm.ptr
    %6 = llvm.mlir.constant(8 : i64) : i64
    %7 = llvm.mlir.constant(7 : i64) : i64
    %8 = llvm.mlir.constant(6 : i64) : i64
    %9 = llvm.mlir.constant(5 : i64) : i64
    %10 = llvm.mlir.constant(0 : i64) : i64
    %11 = llvm.mlir.constant(4 : i64) : i64
    %12 = llvm.mlir.constant(3 : i64) : i64
    %13 = llvm.mlir.constant(2 : i64) : i64
    %14 = llvm.mlir.constant(1 : i64) : i64
    %15 = llvm.trunc %14 : i64 to i32
    %16 = llvm.trunc %13 : i64 to i32
    %17 = llvm.trunc %12 : i64 to i32
    %18 = llvm.trunc %11 : i64 to i32
    %19 = llvm.mlir.constant(2 : index) : i64
    %20 = llvm.mlir.constant(2 : index) : i64
    %21 = llvm.mlir.constant(1 : index) : i64
    %22 = llvm.mlir.constant(4 : index) : i64
    %23 = llvm.mlir.zero : !llvm.ptr
    %24 = llvm.getelementptr %23[%22] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %25 = llvm.ptrtoint %24 : !llvm.ptr to i64
    %26 = llvm.mlir.constant(64 : index) : i64
    %27 = llvm.add %25, %26 : i64
    %28 = llvm.call @malloc(%27) : (i64) -> !llvm.ptr
    %29 = llvm.ptrtoint %28 : !llvm.ptr to i64
    %30 = llvm.mlir.constant(1 : index) : i64
    %31 = llvm.sub %26, %30 : i64
    %32 = llvm.add %29, %31 : i64
    %33 = llvm.urem %32, %26 : i64
    %34 = llvm.sub %32, %33 : i64
    %35 = llvm.inttoptr %34 : i64 to !llvm.ptr
    %36 = llvm.mlir.poison : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)>
    %37 = llvm.insertvalue %28, %36[0] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %38 = llvm.insertvalue %35, %37[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %39 = llvm.mlir.constant(0 : index) : i64
    %40 = llvm.insertvalue %39, %38[2] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %41 = llvm.insertvalue %19, %40[3, 0] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %42 = llvm.insertvalue %20, %41[3, 1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %43 = llvm.insertvalue %20, %42[4, 0] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %44 = llvm.insertvalue %21, %43[4, 1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %45 = llvm.extractvalue %44[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %46 = llvm.mlir.constant(2 : index) : i64
    %47 = llvm.mul %2, %46 overflow<nsw, nuw> : i64
    %48 = llvm.add %47, %2 overflow<nsw, nuw> : i64
    %49 = llvm.getelementptr inbounds|nuw %45[%48] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %15, %49 : i32, !llvm.ptr
    %50 = llvm.extractvalue %44[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %51 = llvm.mlir.constant(2 : index) : i64
    %52 = llvm.mul %2, %51 overflow<nsw, nuw> : i64
    %53 = llvm.add %52, %1 overflow<nsw, nuw> : i64
    %54 = llvm.getelementptr inbounds|nuw %50[%53] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %16, %54 : i32, !llvm.ptr
    %55 = llvm.extractvalue %44[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %56 = llvm.mlir.constant(2 : index) : i64
    %57 = llvm.mul %1, %56 overflow<nsw, nuw> : i64
    %58 = llvm.add %57, %2 overflow<nsw, nuw> : i64
    %59 = llvm.getelementptr inbounds|nuw %55[%58] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %17, %59 : i32, !llvm.ptr
    %60 = llvm.extractvalue %44[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %61 = llvm.mlir.constant(2 : index) : i64
    %62 = llvm.mul %1, %61 overflow<nsw, nuw> : i64
    %63 = llvm.add %62, %1 overflow<nsw, nuw> : i64
    %64 = llvm.getelementptr inbounds|nuw %60[%63] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %18, %64 : i32, !llvm.ptr
    %65 = llvm.trunc %9 : i64 to i32
    %66 = llvm.trunc %8 : i64 to i32
    %67 = llvm.trunc %7 : i64 to i32
    %68 = llvm.trunc %6 : i64 to i32
    %69 = llvm.mlir.constant(2 : index) : i64
    %70 = llvm.mlir.constant(2 : index) : i64
    %71 = llvm.mlir.constant(1 : index) : i64
    %72 = llvm.mlir.constant(4 : index) : i64
    %73 = llvm.mlir.zero : !llvm.ptr
    %74 = llvm.getelementptr %73[%72] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %75 = llvm.ptrtoint %74 : !llvm.ptr to i64
    %76 = llvm.mlir.constant(64 : index) : i64
    %77 = llvm.add %75, %76 : i64
    %78 = llvm.call @malloc(%77) : (i64) -> !llvm.ptr
    %79 = llvm.ptrtoint %78 : !llvm.ptr to i64
    %80 = llvm.mlir.constant(1 : index) : i64
    %81 = llvm.sub %76, %80 : i64
    %82 = llvm.add %79, %81 : i64
    %83 = llvm.urem %82, %76 : i64
    %84 = llvm.sub %82, %83 : i64
    %85 = llvm.inttoptr %84 : i64 to !llvm.ptr
    %86 = llvm.mlir.poison : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)>
    %87 = llvm.insertvalue %78, %86[0] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %88 = llvm.insertvalue %85, %87[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %89 = llvm.mlir.constant(0 : index) : i64
    %90 = llvm.insertvalue %89, %88[2] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %91 = llvm.insertvalue %69, %90[3, 0] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %92 = llvm.insertvalue %70, %91[3, 1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %93 = llvm.insertvalue %70, %92[4, 0] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %94 = llvm.insertvalue %71, %93[4, 1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %95 = llvm.extractvalue %94[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %96 = llvm.mlir.constant(2 : index) : i64
    %97 = llvm.mul %2, %96 overflow<nsw, nuw> : i64
    %98 = llvm.add %97, %2 overflow<nsw, nuw> : i64
    %99 = llvm.getelementptr inbounds|nuw %95[%98] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %65, %99 : i32, !llvm.ptr
    %100 = llvm.extractvalue %94[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %101 = llvm.mlir.constant(2 : index) : i64
    %102 = llvm.mul %2, %101 overflow<nsw, nuw> : i64
    %103 = llvm.add %102, %1 overflow<nsw, nuw> : i64
    %104 = llvm.getelementptr inbounds|nuw %100[%103] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %66, %104 : i32, !llvm.ptr
    %105 = llvm.extractvalue %94[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %106 = llvm.mlir.constant(2 : index) : i64
    %107 = llvm.mul %1, %106 overflow<nsw, nuw> : i64
    %108 = llvm.add %107, %2 overflow<nsw, nuw> : i64
    %109 = llvm.getelementptr inbounds|nuw %105[%108] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %67, %109 : i32, !llvm.ptr
    %110 = llvm.extractvalue %94[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %111 = llvm.mlir.constant(2 : index) : i64
    %112 = llvm.mul %1, %111 overflow<nsw, nuw> : i64
    %113 = llvm.add %112, %1 overflow<nsw, nuw> : i64
    %114 = llvm.getelementptr inbounds|nuw %110[%113] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %68, %114 : i32, !llvm.ptr
    llvm.br ^bb1(%2 : i64)
  ^bb1(%115: i64):  // 2 preds: ^bb0, ^bb5
    %116 = llvm.icmp "slt" %115, %0 : i64
    llvm.cond_br %116, ^bb2, ^bb6
  ^bb2:  // pred: ^bb1
    llvm.br ^bb3(%2 : i64)
  ^bb3(%117: i64):  // 2 preds: ^bb2, ^bb4
    %118 = llvm.icmp "slt" %117, %0 : i64
    llvm.cond_br %118, ^bb4, ^bb5
  ^bb4:  // pred: ^bb3
    %119 = llvm.extractvalue %44[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %120 = llvm.mlir.constant(2 : index) : i64
    %121 = llvm.mul %115, %120 overflow<nsw, nuw> : i64
    %122 = llvm.add %121, %117 overflow<nsw, nuw> : i64
    %123 = llvm.getelementptr inbounds|nuw %119[%122] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %124 = llvm.load %123 : !llvm.ptr -> i32
    %125 = llvm.extractvalue %94[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %126 = llvm.mlir.constant(2 : index) : i64
    %127 = llvm.mul %115, %126 overflow<nsw, nuw> : i64
    %128 = llvm.add %127, %117 overflow<nsw, nuw> : i64
    %129 = llvm.getelementptr inbounds|nuw %125[%128] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %130 = llvm.load %129 : !llvm.ptr -> i32
    %131 = llvm.add %124, %130 : i32
    %132 = llvm.extractvalue %44[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %133 = llvm.mlir.constant(2 : index) : i64
    %134 = llvm.mul %115, %133 overflow<nsw, nuw> : i64
    %135 = llvm.add %134, %117 overflow<nsw, nuw> : i64
    %136 = llvm.getelementptr inbounds|nuw %132[%135] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    llvm.store %131, %136 : i32, !llvm.ptr
    %137 = llvm.add %117, %1 : i64
    llvm.br ^bb3(%137 : i64)
  ^bb5:  // pred: ^bb3
    %138 = llvm.add %115, %1 : i64
    llvm.br ^bb1(%138 : i64)
  ^bb6:  // pred: ^bb1
    %139 = llvm.getelementptr %5[0, 0] : (!llvm.ptr) -> !llvm.ptr, !llvm.array<28 x i8>
    %140 = llvm.insertvalue %139, %3[0] : !llvm.struct<(ptr, i64)> 
    %141 = llvm.insertvalue %4, %140[1] : !llvm.struct<(ptr, i64)> 
    %142 = llvm.mlir.poison : !llvm.struct<(ptr, ptr, i64, array<1 x i64>, array<1 x i64>)>
    %143 = llvm.extractvalue %44[0] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %144 = llvm.extractvalue %44[1] : !llvm.struct<(ptr, ptr, i64, array<2 x i64>, array<2 x i64>)> 
    %145 = llvm.insertvalue %143, %142[0] : !llvm.struct<(ptr, ptr, i64, array<1 x i64>, array<1 x i64>)> 
    %146 = llvm.insertvalue %144, %145[1] : !llvm.struct<(ptr, ptr, i64, array<1 x i64>, array<1 x i64>)> 
    %147 = llvm.mlir.constant(0 : index) : i64
    %148 = llvm.insertvalue %147, %146[2] : !llvm.struct<(ptr, ptr, i64, array<1 x i64>, array<1 x i64>)> 
    %149 = llvm.mlir.constant(2 : index) : i64
    %150 = llvm.insertvalue %149, %148[3, 0] : !llvm.struct<(ptr, ptr, i64, array<1 x i64>, array<1 x i64>)> 
    %151 = llvm.mlir.constant(1 : index) : i64
    %152 = llvm.insertvalue %151, %150[4, 0] : !llvm.struct<(ptr, ptr, i64, array<1 x i64>, array<1 x i64>)> 
    %153 = llvm.extractvalue %152[1] : !llvm.struct<(ptr, ptr, i64, array<1 x i64>, array<1 x i64>)> 
    %154 = llvm.getelementptr inbounds|nuw %153[%2] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %155 = llvm.load %154 : !llvm.ptr -> i32
    %156 = llvm.extractvalue %152[1] : !llvm.struct<(ptr, ptr, i64, array<1 x i64>, array<1 x i64>)> 
    %157 = llvm.getelementptr inbounds|nuw %156[%1] : (!llvm.ptr, i64) -> !llvm.ptr, i32
    %158 = llvm.load %157 : !llvm.ptr -> i32
    %159 = llvm.alloca %14 x !llvm.struct<(ptr, i64)> {alignment = 1 : i64} : (i64) -> !llvm.ptr
    llvm.store %141, %159 : !llvm.struct<(ptr, i64)>, !llvm.ptr
    %160 = llvm.load %159 : !llvm.ptr -> i64
    %161 = llvm.call @printf(%160, %155, %158) vararg(!llvm.func<i32 (i64, ...)>) : (i64, i32, i32) -> i32
    %162 = llvm.trunc %10 : i64 to i32
    llvm.return %162 : i32
  }
  llvm.mlir.global internal constant @__str_44a786e5b808c007("Sum[0][0]=%d, Sum[1][1]=%d\0A\00") {addr_space = 0 : i32}
}

