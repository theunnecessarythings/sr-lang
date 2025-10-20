module {
  llvm.mlir.global internal constant @str("Hello, world!\00")

  func.func @main() -> i32 {
    %0 = llvm.mlir.addressof @str : !llvm.ptr
    %1 = llvm.getelementptr %0[0, 0]
       : (!llvm.ptr) -> !llvm.ptr, !llvm.array<13 x i8>
    %width = arith.constant 640 : i32
    %height = arith.constant 480 : i32
    llvm.call @InitWindow(%width, %height, %1) : (i32, i32, !llvm.ptr) -> ()

    %15= arith.constant 15 : i8
    %255 = arith.constant 255 : i8
    %2 = llvm.mlir.undef : !llvm.struct<(i8, i8, i8, i8)>
    %3 = llvm.insertvalue %255, %2[0] : !llvm.struct<(i8, i8, i8, i8)>
    %4 = llvm.insertvalue %255, %3[1] : !llvm.struct<(i8, i8, i8, i8)>
    %5 = llvm.insertvalue %255, %4[2] : !llvm.struct<(i8, i8, i8, i8)>
    %6 = llvm.insertvalue %255, %5[3] : !llvm.struct<(i8, i8, i8, i8)>

    scf.while () : () -> () {
      %close = llvm.call @WindowShouldClose() : () -> i1
      %true = arith.constant 1 : i1
      %cond = arith.cmpi "ne", %close, %true : i1
      scf.condition(%cond) 
    } do {
      llvm.call @BeginDrawing() : () -> ()
      llvm.call @ClearBackground(%6) : (!llvm.struct<(i8, i8, i8, i8)>) -> ()
      llvm.call @EndDrawing() : () -> ()
      scf.yield
    }
    llvm.call @CloseWindow() : () -> ()

    %c0 = arith.constant 0 : i32
    return %c0 : i32
  }

  llvm.func @puts(!llvm.ptr) -> i32
  llvm.func @InitWindow(i32, i32, !llvm.ptr) -> ()
  llvm.func @WindowShouldClose() -> i1
  llvm.func @ClearBackground(!llvm.struct<(i8, i8, i8, i8)>) 
  llvm.func @BeginDrawing() -> ()
  llvm.func @EndDrawing() -> ()
  llvm.func @CloseWindow() -> ()
}
