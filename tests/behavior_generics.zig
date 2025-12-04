const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "generics: simple specialization" {
    const globals =
        \\
        \\ max :: fn(comptime T: type, a: T, b: T) T {
        \\   return if a > b { a } else { b }
        \\ }
        \\ clamp :: fn(comptime T: type, comptime Limit: T, value: T) T {
        \\   return if value > Limit { Limit } else { value }
        \\ }
    ;

    const src =
        \\
        \\ printf("%d\n", max(i32, 10, 7))
        \\ printf("%d\n", clamp(i32, 5, 42))
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "10\n5\n");
}

test "generics: nested type specializations" {
    const globals =
        \\
        \\ Vec :: fn(comptime T: type, comptime N: usize) type {
        \\   return struct { data: [N]T }
        \\ }
        \\ Matrix :: fn(comptime T: type, comptime R: usize, comptime C: usize) type {
        \\   Row :: Vec(T, C)
        \\   return struct { rows: [R]Row }
        \\ }
        \\ MatrixI32x2x3 :: Matrix(i32, 2, 3)
    ;

    const src =
        \\
        \\ row0 := Vec(i32, 3){ data : [1, 2, 3] }
        \\ row1 := Vec(i32, 3){ data : [4, 5, 6] }
        \\ mat := MatrixI32x2x3{ rows : [row0, row1] }
        \\ printf("%d,%d\n", mat.rows[0].data[2], mat.rows[1].data[0])
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "3,4\n");
}

test "generics: struct field uses comptime array length" {
    const globals =
        \\
        \\ Vec :: fn(comptime T: type, comptime N: usize) type {
        \\   return struct { data: [N]T };
        \\ }
    ;

    const src =
        \\
        \\ top := Vec(i32, 3){ data: [1, 2, 3] }
        \\ bottom := Vec(i32, 3){ data: [4, 5, 6] }
        \\ printf("%d,%d,%d|%d,%d,%d\n", top.data[0], top.data[1], top.data[2], bottom.data[0], bottom.data[1], bottom.data[2])
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "1,2,3|4,5,6\n");
}

test "generics: methods" {
    const globals =
        \\ List :: proc(comptime T: type) type {
        \\ Type :: struct {
        \\     data: []const T,
        \\     len: usize,
        \\ }
        \\
        \\ Type.get :: proc(self: *Type, index: usize) T {
        \\     return self.data[index]
        \\ }
        \\
        \\ return Type
        \\ }
    ;
    const src =
        \\  list := List(i64){ data: [1, 2, 3], len: 3 }
        \\  printf("%d\n", list.get(1))
        \\
        \\  list_f64 := List(f64){ data: [1.0, 2.0, 3.0], len: 3 }
        \\  printf("%f\n", list_f64.get(1))
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "2\n2.000000\n");
}

test "generics: nested method specialization per owner" {
    const globals =
        \\    A :: proc(comptime T: type) type {
        \\    Type :: struct { item: T }
        \\    Type.init :: proc(val: T) Type {
        \\        return Type { item: val }
        \\    }
        \\    return Type
        \\}
    ;
    const src =
        \\    TI32 :: A(i32)
        \\    x := TI32.init(5)
        \\    printf("x: %d\n", x.item)
        \\
        \\    TI64 :: A(i64)
        \\    y := TI64.init(7)
        \\    printf("y: %d\n", y.item)
        \\
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "x: 5\ny: 7\n");
}
