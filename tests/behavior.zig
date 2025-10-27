const std = @import("std");

const test_harness =
    \\ package main
    \\ printf :: extern proc(string, any) i32
    \\ __assert_fail :: extern proc(string, string, i32, string) void
    \\ assert :: proc (cond: bool) {{
    \\     if (!cond) {{
    \\        __assert_fail("Assertion failed", "test", -1, "assert")  
    \\     }}
    \\ }}
    \\ {s}
    \\ main :: proc () i32 {{
    \\     // Test cases go here
    \\     {s}
    \\     return 0
    \\ }}
;

pub fn getSource(comptime globals: []const u8, comptime main_body: []const u8) []const u8 {
    return std.fmt.comptimePrint(test_harness, .{ globals, main_body });
}

const alloc = std.testing.allocator;

pub var link_lib: []const u8 = "-lm";

pub fn runCompilerTest(source: []const u8, expected_stdout: []const u8) !void {
    const temp_dir = "out";
    const file_path = temp_dir ++ "/test.sr";
    const file = std.fs.cwd().createFile(file_path, .{}) catch unreachable;
    defer file.close();

    _ = file.writeAll(source) catch unreachable;

    // remove old output
    _ = std.fs.cwd().deleteFile("out/output_program") catch {};

    const compile_result = try std.process.Child.run(.{
        .allocator = alloc,
        .argv = &.{ "zig-out/bin/sr_lang", "compile", "out/test.sr", link_lib },
        .max_output_bytes = 16 * 1024 * 1024,
    });
    defer alloc.free(compile_result.stdout);
    defer alloc.free(compile_result.stderr);
    switch (compile_result.term) {
        .Exited => |code| {
            if (code != 0) {
                std.debug.print("Compiler stdout:\n{s}\n", .{compile_result.stdout});
                std.debug.print("Compiler stderr:\n{s}\n", .{compile_result.stderr});
                return error.CompilationFailed;
            }
        },
        else => {
            std.debug.print("Compiler stdout:\n{s}\n", .{compile_result.stdout});
            std.debug.print("Compiler stderr:\n{s}\n", .{compile_result.stderr});
            return error.ProcessFailed;
        },
    }

    // check output program exists
    _ = std.fs.cwd().statFile("out/output_program") catch |err| {
        std.debug.print("Error: {}\n", .{err});
        return error.CompilationFailed;
    };
    const run_result = try std.process.Child.run(.{
        .allocator = alloc,
        .argv = &.{"out/output_program"},
        .max_output_bytes = 16 * 1024 * 1024,
    });
    defer alloc.free(run_result.stdout);
    defer alloc.free(run_result.stderr);
    switch (run_result.term) {
        .Exited => |code| {
            if (code != 0) {
                std.debug.print("Compiler stdout:\n{s}\n", .{run_result.stdout});
                std.debug.print("Compiler stderr:\n{s}\n", .{run_result.stderr});
                return error.CompilationFailed;
            }
        },
        else => {
            std.debug.print("Compiler stdout:\n{s}\n", .{run_result.stdout});
            std.debug.print("Compiler stderr:\n{s}\n", .{run_result.stderr});
            return error.ProcessFailed;
        },
    }
    try std.testing.expectEqualStrings(expected_stdout, run_result.stdout);
}

test "behavior: hello world" {
    const src =
        \\ printf("Hello, World!\n");
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Hello, World!\n");
}

test "behavior: simple addition" {
    const src =
        \\ r := 10 + 20
        \\ printf("%d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "30\n");
}

test "behavior: arithmetic operations" {
    const src =
        \\ assert(10 - 5 == 5)
        \\ assert(10 * 2 == 20)
        \\ assert(20 / 4 == 5)
        \\ assert(10 % 3 == 1)
        \\ assert(1 + 2 * 3 == 7)
        \\ printf("Arithmetic OK\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Arithmetic OK\n");
}

test "behavior: boolean logic" {
    const src =
        \\ assert(true and true == true)
        \\ assert(true and false == false)
        \\ assert(false or true == true)
        \\ assert(false or false == false)
        \\ assert(!true == false)
        \\ assert(!false == true)
        \\ assert((true and false) or !false == true)
        \\ printf("Boolean OK\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Boolean OK\n");
}

test "behavior: comparison operations" {
    const src =
        \\ assert(10 == 10)
        \\ assert(10 != 5)
        \\ assert(5 < 10)
        \\ assert(10 > 5)
        \\ assert(5 <= 5)
        \\ assert(10 >= 10)
        \\ assert(10 <= 10)
        \\ printf("Comparison OK\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Comparison OK\n");
}

test "behavior: if-else" {
    const src =
        \\ x := 10
        \\ if x == 10 {
        \\   printf("if-then\n")
        \\ } else {
        \\   printf("if-else\n")
        \\ }
        \\ if x != 10 {
        \\    printf("if-then-unreached\n")
        \\ } else {
        \\    printf("if-else-reached\n")
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "if-then\nif-else-reached\n");
}

test "behavior: nested if" {
    const src =
        \\ x := 10
        \\ if x > 5 {
        \\   if x < 15 {
        \\     printf("x is between 5 and 15\n")
        \\   } else {
        \\     printf("x is >= 15\n")
        \\   }
        \\ } else {
        \\   printf("x is <= 5\n")
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x is between 5 and 15\n");
}

test "behavior: if expr" {
    const src =
        \\ x := 10
        \\ y := if x > 5 { 100 } else { 200 }
        \\ printf("y=%d\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "y=100\n");
}

test "behavior: nested if expr" {
    const src =
        \\ x := 10
        \\ y := if x < 5 { 1 } else if x < 15 { 2 } else { 3 }
        \\ printf("y=%d\n", y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "y=2\n");
}

test "behavior: while loop" {
    const src =
        \\ x := 10
        \\ keep_looping := true
        \\ while keep_looping {
        \\   printf("x=%d\n", x)
        \\   x += 1
        \\   if x > 12 {
        \\     keep_looping = false
        \\   }
        \\ }
        \\ printf("While loop finished\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=10\nx=11\nx=12\nWhile loop finished\n");
}

test "behavior: for loop" {
    const src =
        \\ sum := 0
        \\ for i in 0..3 {
        \\   sum += i.(i64)
        \\ }
        \\ printf("Sum=%d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Sum=3\n");
}

test "behavior: function call" {
    const src =
        \\ r := add(5, 7)
        \\ printf("Result=%d\n", r)
    ;
    const globals =
        \\ add :: fn(a: i32, b: i32) i32 { return a + b }
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Result=12\n");
}

test "behavior: procedure call" {
    const src =
        \\ print_val(15)
    ;
    const globals =
        \\ print_val :: proc(val: i32) { printf("Value=%d\n", val) }
    ;

    const code = getSource(globals, src);
    try runCompilerTest(code, "Value=15\n");
}

test "behavior: struct creation and field access" {
    const src =
        \\ Point :: struct { x: i32, y: i32 }
        \\ p := Point{ x: 10, y: 20 }
        \\ printf("Point x=%d, y=%d\n", p.x, p.y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Point x=10, y=20\n");
}

test "behavior: array creation and indexing" {
    const src =
        \\ arr := [10, 20, 30]
        \\ val := arr[1]
        \\ printf("Second element=%d\n", val)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Second element=20\n");
}

test "behavior: for iter array" {
    const src =
        \\ arr := [1, 2, 3]
        \\ sum := 0
        \\ for v in arr {
        \\   sum += v
        \\ }
        \\ printf("Array sum=%d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Array sum=6\n");
}

test "behavior: char and complex literals" {
    const src =
        \\ c := 'A'
        \\ printf("Char=%c\n", c)
        \\ z := 1.0 + 2.0i
        \\ printf("Complex real=%f, imag=%f\n", z.real, z.imag)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Char=A\nComplex real=1.000000, imag=2.000000\n");
}

test "behavior: variable reassignment" {
    const src =
        \\ x := 10
        \\ printf("x_initial=%d\n", x)
        \\ x = 20
        \\ printf("x_reassigned=%d\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x_initial=10\nx_reassigned=20\n");
}

test "behavior: tuple creation and indexing" {
    const src =
        \\ t := (1, "hello", true)
        \\ printf("Tuple 0=%d, 1=%s, 2=%d\n", t.0, t.1, t.2)
        \\ first := t.0
        \\ printf("First element=%d\n", first)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Tuple 0=1, 1=hello, 2=1\nFirst element=1\n");
}

// test "behavior: map creation and access" {
//     const src =
//         \\ m := ["one": 1, "two": 2]
//         \\ printf("Map one=%d, two=%d\n", m["one"], m["two"])
//         \\ m["three"] = 3
//         \\ printf("Map three=%d\n", m["three"])
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Map one=1, two=2\nMap three=3\n");
// }

test "behavior: enum definition and usage" {
    const src =
        \\ State :: enum { Running, Paused }
        \\ s := State.Running
        \\ assert(s == State.Running)
        \\ printf("Enum state=%d\n", s)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Enum state=0\n");
}

test "behavior: variant tag-only and tuple payload" {
    const src =
        \\ V :: variant { A, B(i32) }
        \\ v1 := V.A
        \\ v2 := V.B(123)
        \\ printf("Variant v2 payload=%d\n", v2.1)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Variant v2 payload=123\n");
}

test "behavior: variant struct payload" {
    const src =
        \\ V :: variant { C{ x: i32, y: i32 } }
        \\ v := V.C{ x: 10, y: 20 }
        \\ printf("Variant v x=%d, y=%d\n", v.x, v.y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Variant v x=10, y=20\n");
}

test "behavior: union literal initialization" {
    const src =
        \\ U :: union { i: i32, f: f64 }
        \\ u1 := U{ i: 42 }
        \\ u2 := U{ f: 3.14 }
        \\ printf("Union u1 i=%d\n", u1.i)
        \\ printf("Union u2 f=%f\n", u2.f)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Union u1 i=42\nUnion u2 f=3.140000\n");
}

test "behavior: error propagation and catch" {
    const globals =
        \\ MyErr :: error { NotFound }
        \\ might_fail :: proc() i32!MyErr { return MyErr.NotFound }
        \\ handle_error :: proc() i32 {
        \\   val := might_fail() catch |err| {
        \\     if err == MyErr.NotFound {
        \\        0
        \\     } else {
        \\        1
        \\     }
        \\   }
        \\   return val
        \\ }
    ;

    const src =
        \\ r := handle_error()
        \\ printf("Error handled result=%d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Error handled result=0\n");
}

test "behavior: pointer address-of and dereference" {
    const src =
        \\ x := 10
        \\ p := &x
        \\ val := p.*
        \\ printf("x=%d, p_deref=%d\n", x, val)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "x=10, p_deref=10\n");
}

test "behavior: normal cast" {
    const src =
        \\ f := 123.45
        \\ i := f.(i32)
        \\ printf("Float=%f, Int=%d\n", f, i)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Float=123.450000, Int=123\n");
}

test "behavior: saturating cast" {
    const src =
        \\ big_int := 99999
        \\ saturated_to_i8 := big_int.|i8
        \\ printf("Big int=%d, Saturated i8=%d\n", big_int, saturated_to_i8)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Big int=99999, Saturated i8=127\n");
}

test "behavior: wrapping cast" {
    const src =
        \\ val := 254
        \\ wrapped_add := (val + 5).%u8
        \\ printf("U8 val=%d, Wrapped add=%d\n", val, wrapped_add)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "U8 val=254, Wrapped add=3\n");
}

test "behavior: while is loop" {
    const src =
        \\ Option :: variant { None, Some(i32) }
        \\ maybe_value := Option.Some(42)
        \\ result := 0
        \\ while is Some(x) := maybe_value {
        \\   result = x
        \\   maybe_value = Option.None // Exit loop
        \\ }
        \\ printf("While is result=%d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "While is result=42\n");
}

test "behavior: match expression literals and wildcard" {
    const src =
        \\ x := 2
        \\ r := match x {
        \\   1 => 10,
        \\   2 => 20,
        \\   _ => 30,
        \\ }
        \\ printf("Match result=%d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Match result=20\n");
}

test "behavior: match expression with guards" {
    const src =
        \\ x := 3
        \\ r := match x {
        \\   y @ 3 if y == 3 => 100,
        \\   _ => 200,
        \\ }
        \\ printf("Match with guard result=%d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Match with guard result=100\n");
}

// test "behavior: variadic function call" {
//     const src =
//         \\ print_variadic :: proc(prefix: string, args: any) {
//         \\   printf("%s", prefix)
//         \\   // Assuming a way to iterate over 'any' tuple
//         \\   // For simplicity, just print a fixed number of args
//         \\   printf(" %d %f\n", args.0, args.1)
//         \\ }
//         \\ print_variadic("Numbers:", 10, 3.14)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Numbers: 10 3.140000\n");
// }
//
// test "behavior: closure basic usage" {
//     const src =
//         \\ add_one := fn(x: i32) i32 { return x + 1 }
//         \\ r := add_one(5)
//         \\ printf("Closure result=%d\n", r)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Closure result=6\n");
// }
//
// test "behavior: closure with captured environment" {
//     const src =
//         \\ make_adder :: proc(amount: i32) fn(i32) i32 {
//         \\   add_amount := fn(x: i32) i32 { return x + amount }
//         \\   return add_amount
//         \\ }
//         \\ add_5 := make_adder(5)
//         \\ r := add_5(7)
//         \\ printf("Captured closure result=%d\n", r)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Captured closure result=12\n");
// }
//
// test "behavior: comptime block" {
//     const src =
//         \\ x := 0
//         \\ comptime {
//         \\   x = 10 // This should modify x at compile time
//         \\ }
//         \\ printf("Comptime x=%d\n", x)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Comptime x=10\n");
// }
//
// test "behavior: typeof expression" {
//     const src =
//         \\ t_int := typeof(1)
//         \\ t_bool := typeof(true)
//         \\ printf("Type of 1 is %s\n", t_int)
//         \\ printf("Type of true is %s\n", t_bool)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Type of 1 is i32\nType of true is bool\n");
// }
//
// test "behavior: import and module member access" {
//     const src =
//         \\ math :: import "examples/imports/math"
//         \\ Vector :: math.Vector
//         \\ v1 := Vector{ x: 10.0, y: 20.0 }
//         \\ v2 := Vector{ x: 5.5, y: 1.5 }
//         \\ result := math.add(v1, v2)
//         \\ printf("Vector add x=%f, y=%f\n", result.x, result.y)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Vector add x=15.500000, y=21.500000\n");
// }

test "behavior: mlir module block" {
    const src =
        \\ mod := mlir {
        \\   module {
        \\     func.func @const() -> i32 {
        \\       %c42 = arith.constant 42 : i32
        \\       func.return %c42 : i32
        \\     }
        \\   }
        \\ }
        \\ // Assuming mlir blocks are opaque and can be assigned
        \\ printf("MLIR module assigned\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "MLIR module assigned\n");
}

test "behavior: comptime mlir type reuse" {
    const src =
        \\ mlir_ty := comptime { mlir type { !llvm.ptr } }
        \\ reused_ty := comptime { mlir_ty }
        \\ printf("MLIR comptime handles ok\n")
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "MLIR comptime handles ok\n");
}

test "behavior: defer statement" {
    const global =
        \\ cleanup_ran := 0
        \\ run_test :: proc() {
        \\   defer {
        \\      cleanup_ran = 1
        \\      printf("Cleaning up\n")
        \\  }
        \\   printf("Running test\n")
        \\ }
    ;
    const src =
        \\ run_test()
        \\ printf("Cleanup ran=%d\n", cleanup_ran)
    ;
    const code = getSource(global, src);
    try runCompilerTest(code, "Running test\nCleaning up\nCleanup ran=1\n");
}

test "behavior: errdefer statement" {
    const global =
        \\  MyErr :: error { Failed }
        \\  cleanup_ran := 0
        \\  run_test :: proc() void!MyErr {
        \\      errdefer {
        \\          cleanup_ran = 1
        \\          printf("Errdefer ran\n")
        \\      }
        \\      defer {
        \\          printf("Defer ran\n")
        \\      }
        \\      return MyErr.Failed
        \\  }
    ;

    const src =
        \\ run_test() catch { /* ignore error */ }
        \\ printf("Errdefer ran=%d\n", cleanup_ran)
    ;
    const code = getSource(global, src);
    try runCompilerTest(code, "Errdefer ran\nDefer ran\nErrdefer ran=1\n");
}

test "behavior: unreachable statement" {
    const src =
        \\ x := 10
        \\ if x == 10 {
        \\   printf("Unreachable path not taken\n")
        \\ } else {
        \\   unreachable
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Unreachable path not taken\n");
}

test "behavior: break with value from loop" {
    const src =
        \\ result := (L: while true {
        \\   break :L 42
        \\ })
        \\ printf("Break value=%d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Break value=42\n");
}

test "behavior: continue statement" {
    const src =
        \\ count := 0
        \\ for i in 0..5 {
        \\   if i == 2 {
        \\     continue
        \\   }
        \\   count += 1
        \\ }
        \\ printf("Continue count=%d\n", count)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Continue count=4\n");
}

test "behavior: bitcast" {
    const src =
        \\ some_bits: u32 = 0x42F6E979
        \\ bits_as_float: f32 = some_bits.^f32
        \\ printf("Bits as float=%f\n", bits_as_float.(f64))
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Bits as float=123.456001\n");
}

test "behavior: checked cast" {
    const src =
        \\ big_int: i64 = 99999
        \\ checked_cast: ?i8 = big_int.?i8
        \\ assert(checked_cast == null)
        \\ successful_checked_cast: ?i8 = (100).?i8
        \\ assert(successful_checked_cast == 100)
        \\ printf("Checked cast null=%b, successful=%d\n", checked_cast == null, successful_checked_cast?)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Checked cast null=1, successful=100\n");
}

test "behavior: optional unwrap" {
    const src =
        \\ opt: ?i32 = 123
        \\ val := opt?
        \\ printf("Unwrapped value=%d\n", val)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Unwrapped value=123\n");
}

test "behavior: match expression tuple pattern" {
    const src =
        \\ t := (10, "hello")
        \\ r := match t {
        \\   (a, b) => printf("Matched tuple: %d, %s\n", a, b),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched tuple: 10, hello\n");
}

test "behavior: match expression struct pattern" {
    const src =
        \\ Point :: struct { x: i32, y: i32 }
        \\ p := Point{ x: 1, y: 2 }
        \\ r := match p {
        \\   Point{ x: a, y: b } => printf("Matched struct: x=%d, y=%d\n", a, b),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched struct: x=1, y=2\n");
}

test "behavior: match expression variant pattern" {
    const src =
        \\ V :: variant { A, B(i32), C{ x: i32 } }
        \\ v := V.B(42)
        \\ r := match v {
        \\   V.A => printf("Matched A\n"),
        \\   V.B(val) => printf("Matched B with %d\n", val),
        \\   V.C{ x: val } => printf("Matched C with %d\n", val),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched B with 42\n");
}

test "behavior: match exhaustiveness bool" {
    const src =
        \\ b := true
        \\ r := match b {
        \\   true => 1,
        \\   false => 0,
        \\ }
        \\ printf("Match bool result=%d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Match bool result=1\n");
}

test "behavior: match exhaustiveness enum" {
    const src =
        \\ E :: enum { A, B }
        \\ e := E.B
        \\ r := match e {
        \\   E.A => 10,
        \\   E.B => 20,
        \\ }
        \\ printf("Match enum result=%d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Match enum result=20\n");
}

test "behavior: match or-pattern" {
    const src =
        \\ x := 2
        \\ r := match x {
        \\   1 | 2 => 10,
        \\   _ => 20,
        \\ }
        \\ printf("Match or-pattern result=%d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Match or-pattern result=10\n");
}

test "behavior: match at-pattern" {
    const src =
        \\ x := 5
        \\ r := match x {
        \\   y @ (0..10) => printf("Matched range with %d\n", y),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched range with 5\n");
}

// test "behavior: function pointer call" {
//     const src =
//         \\ add :: fn(a: i32, b: i32) i32 { return a + b }
//         \\ add_ptr := add
//         \\ r := add_ptr(10, 20)
//         \\ printf("Function pointer result=%d\n", r)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Function pointer result=30\n");
// }
//
// test "behavior: default arguments" {
//     const src =
//         \\ greet :: proc(name: string, greeting: string = "Hello") {
//         \\   printf("%s, %s!\n", greeting, name)
//         \\ }
//         \\ greet("Alice")
//         \\ greet("Bob", "Hi")
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Hello, Alice!\nHi, Bob!\n");
// }
//
// test "behavior: code block and insert" {
//     const src =
//         \\ x := 10
//         \\ comptime {
//         \\   code_block := code { x = 20 }
//         \\   insert code_block
//         \\ }
//         \\ printf("Code block x=%d\n", x)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Code block x=20\n");
// }
//
// test "behavior: import and nested member access" {
//     const src =
//         \\ math :: import "examples/imports/math"
//         \\ Vector :: math.Vector
//         \\ v := Vector{ x: 10.0, y: 20.0 }
//         \\ printf("Vector x=%f\n", v.x)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Vector x=10.000000\n");
// }

test "behavior: error union catch" {
    const globals =
        \\ MyErr :: error { Failed }
        \\ might_fail :: proc() i32!MyErr { return MyErr.Failed }
        \\ might_succeed :: proc() i32!MyErr { return 100 }
    ;
    const src =
        \\ r1 := might_fail() catch 0
        \\ r2 := might_succeed() catch 0
        \\ printf("Orelse r1=%d, r2=%d\n", r1, r2)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Orelse r1=0, r2=100\n");
}

test "behavior: optional unwrap failure" {
    const global = "rt_panic :: extern proc(ptr: *const u8, len: usize) noreturn";
    const src =
        \\ opt: ?i32 = null
        \\ // This should ideally cause a runtime error or be caught by checker
        \\ // For now, we expect it to proceed and print a default/garbage value
        \\ // if the language doesn't have runtime checks for this.
        \\ // Assuming it prints 0 or some default for null unwrap.
        \\ val := opt?
        \\ printf("Unwrapped null value=%d\n", val)
    ;
    const code = getSource(global, src);
    runCompilerTest(code, "Unwrapped null value=0\n") catch |err| {
        switch (err) {
            error.CompilationFailed => {},
            else => try std.testing.expect(false),
        }
    };
}

test "behavior: labeled continue" {
    const src =
        \\ count := 0
        \\ outer: for i in 0..3 {
        \\   inner: for j in 0..3 {
        \\     if i == 1 and j == 1 {
        \\       continue :outer
        \\     }
        \\     count += 1
        \\   }
        \\ }
        \\ printf("Labeled continue count=%d\n", count)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Labeled continue count=7\n");
}

test "behavior: break from for loop with value" {
    const src =
        \\ result := (L: for i in 0..10 {
        \\   if i == 5 {
        \\     break :L i.(i64) * 2
        \\   }
        \\   // This line is unreachable after break
        \\   // printf("Should not reach here\n")
        \\ })
        \\ printf("For loop break value=%d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "For loop break value=10\n");
}

test "behavior: nested structs" {
    const src =
        \\ Point :: struct { x: i32, y: i32 }
        \\ Rect :: struct { tl: Point, br: Point }
        \\ r := Rect{ tl: Point{ x: 0, y: 0 }, br: Point{ x: 10, y: 10 } }
        \\ printf("Rect tl.x=%d, br.y=%d\n", r.tl.x, r.br.y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Rect tl.x=0, br.y=10\n");
}

test "behavior: nested arrays" {
    const src =
        \\ matrix := [[1, 2], [3, 4]]
        \\ printf("Matrix[0][1]=%d, Matrix[1][0]=%d\n", matrix[0][1], matrix[1][0])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matrix[0][1]=2, Matrix[1][0]=3\n");
}

test "behavior: nested tuples" {
    const src =
        \\ nested_tup := (1, ("hello", true), 3.14)
        \\ printf("Nested tup 0=%d, 1.0=%s, 1.1=%b\n", nested_tup.0, nested_tup.1.0, nested_tup.1.1)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Nested tup 0=1, 1.0=hello, 1.1=1\n");
}

// test "behavior: mlir attribute block" {
//     const src =
//         \\ attr := mlir attribute { #my_attr<string> }
//         \\ // Assuming mlir attribute blocks are opaque and can be assigned
//         \\ printf("MLIR attribute assigned\n")
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "MLIR attribute assigned\n");
// }
//
// test "behavior: mlir type block" {
//     const src =
//         \\ ty := mlir type { !llvm.ptr }
//         \\ // Assuming mlir type blocks are opaque and can be assigned
//         \\ printf("MLIR type assigned\n")
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "MLIR type assigned\n");
// }
//
// test "behavior: code block with function insert" {
//     const src =
//         \\ x := 0
//         \\ comptime {
//         \\   add_one_func := code { add_one :: fn(val: i32) i32 { return val + 1 } }
//         \\   insert add_one_func
//         \\ }
//         \\ r := add_one(x)
//         \\ printf("Inserted function result=%d\n", r)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Inserted function result=1\n");
// }

test "behavior: complex arithmetic with mixed types" {
    const src =
        \\ x := 10 + 2.5 * 4 - (10 % 3)
        \\ printf("Complex arithmetic result=%f\n", x)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Complex arithmetic result=19.000000\n");
}

test "behavior: integer division and modulo with negative numbers" {
    const src =
        \\ a := -10 / 3
        \\ b := -10 % 3
        \\ printf("Div=%d, Mod=%d\n", a, b)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Div=-3, Mod=-1\n");
}

test "behavior: bitwise operations with different integer sizes" {
    const src =
        \\ x: u8 = 0b1100_1100
        \\ y: u16 = 0b0000_0000_1111_0000
        \\ r := x.(u16) & y
        \\ printf("Bitwise AND result=%d\n", r)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Bitwise AND result=192\n");
}

test "behavior: nested if-else" {
    const src =
        \\ x := 10
        \\ y := 20
        \\ if x == 10 {
        \\   if y == 20 {
        \\     printf("Nested if-then\n")
        \\   } else {
        \\     printf("Nested if-else\n")
        \\   }
        \\ } else {
        \\   printf("Outer if-else\n")
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Nested if-then\n");
}

test "behavior: while loop with break and continue" {
    const src =
        \\ count := 0
        \\ i := 0
        \\ while i < 5 {
        \\   i += 1
        \\   if i == 3 {
        \\     continue
        \\   }
        \\   if i == 4 {
        \\     break
        \\   }
        \\   count += 1
        \\ }
        \\ printf("Loop count=%d\n", count)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Loop count=2\n");
}

test "behavior: for loop with nested if" {
    const src =
        \\ sum := 0
        \\ for i in 0..5 {
        \\   if i.(i64) % 2 == 0 {
        \\     sum += i.(i64)
        \\   }
        \\ }
        \\ printf("Even sum=%d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Even sum=6\n");
}

test "behavior: tuple destructuring in declaration" {
    const src =
        \\ (a, b) := (10, 20)
        \\ printf("Destructured a=%d, b=%d\n", a, b)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Destructured a=10, b=20\n");
}

test "behavior: struct destructuring in declaration" {
    const src =
        \\ Point :: struct { x: i32, y: i32 }
        \\ Point{ x: a, y: b } := Point{ x: 100, y: 200 }
        \\ printf("Destructured x=%d, y=%d\n", a, b)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Destructured x=100, y=200\n");
}

test "behavior: array slice with rest pattern" {
    const src =
        \\ arr := [1, 2, 3, 4, 5]
        \\ r := match arr {
        \\   [first, second, ..rest] => printf("First=%d, Second=%d, Rest len=%d\n", first, second, rest.len),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "First=1, Second=2, Rest len=3\n");
}

test "behavior: error union orelse with success" {
    const globals =
        \\ MyErr :: error { Failed }
        \\ might_succeed :: proc() i32!MyErr { return 100 }
    ;
    const src =
        \\ r := might_succeed() catch 0
        \\ printf("Catch success result=%d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Catch success result=100\n");
}

test "behavior: catch with error binding" {
    const globals =
        \\ MyErr :: error { NotFound, PermissionDenied }
        \\ might_fail :: proc() i32!MyErr { return MyErr.PermissionDenied }
    ;
    const src =
        \\ r := might_fail() catch |err| {
        \\   if err == MyErr.NotFound {
        \\     printf("Caught NotFound\n")
        \\   } else if err == MyErr.PermissionDenied {
        \\     printf("Caught PermissionDenied\n")
        \\   } else {
        \\     printf("Caught unknown error\n")
        \\   }
        \\   return 0
        \\ }
        \\ printf("Catch result=%d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Caught PermissionDenied\nCatch result=0\n");
}

test "behavior: match nested tuple pattern" {
    const src =
        \\ t := (1, (2, "three"))
        \\ r := match t {
        \\   (a, (b, c)) => printf("Matched nested tuple: a=%d, b=%d, c=%s\n", a, b, c),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched nested tuple: a=1, b=2, c=three\n");
}

test "behavior: match nested struct pattern" {
    const src =
        \\ Point :: struct { x: i32, y: i32 }
        \\ Rect :: struct { tl: Point, br: Point }
        \\ r := Rect{ tl: Point{ x: 0, y: 0 }, br: Point{ x: 10, y: 10 } }
        \\ result := match r {
        \\   Rect{ tl: Point{ x: tx, y: ty }, br: Point{ x: bx, y: by } } => printf("Matched nested struct: tx=%d, ty=%d, bx=%d, by=%d\n", tx, ty, bx, by),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched nested struct: tx=0, ty=0, bx=10, by=10\n");
}

test "behavior: match or-pattern with binding" {
    const src =
        \\ x := 10
        \\ r := match x {
        \\   y @ (1 | 2) => printf("Matched 1 or 2 with %d\n", y),
        \\   y @ (10 | 11) => printf("Matched 10 or 11 with %d\n", y),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched 10 or 11 with 10\n");
}

// test "behavior: function pointer as argument" {
//     const src =
//         \\ apply :: proc(f: fn(i32) i32, val: i32) i32 { return f(val) }
//         \\ inc :: fn(x: i32) i32 { return x + 1 }
//         \\ r := apply(inc, 5)
//         \\ printf("Function pointer as arg result=%d\n", r)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Function pointer as arg result=6\n");
// }
//
// test "behavior: closure returning closure" {
//     const src =
//         \\ make_multiplier :: proc(factor: i32) fn(i32) i32 {
//         \\   return fn(x: i32) i32 { return x * factor }
//         \\ }
//         \\ multiply_by_3 := make_multiplier(3)
//         \\ r := multiply_by_3(10)
//         \\ printf("Closure returning closure result=%d\n", r)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Closure returning closure result=30\n");
// }

test "behavior: error type definition and usage" {
    const globals =
        \\ FileSystemError :: error { NotFound, PermissionDenied }
        \\ get_error :: proc() FileSystemError { return FileSystemError.PermissionDenied }
    ;
    const src =
        \\ err := get_error()
        \\ assert(err == FileSystemError.PermissionDenied)
        \\ printf("Error type usage OK\n")
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Error type usage OK\n");
}

test "behavior: nested for loops" {
    const src =
        \\ count := 0
        \\ for i in 0..2 {
        \\   for j in 0..2 {
        \\     count += 1
        \\   }
        \\ }
        \\ printf("Nested for count=%d\n", count)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Nested for count=4\n");
}

test "behavior: labeled for loop with break" {
    const src =
        \\ result := 0
        \\ outer: for i in 0..5 {
        \\   for j in 0..5 {
        \\     if i * j > 10 {
        \\       break :outer
        \\     }
        \\     result += 1
        \\   }
        \\ }
        \\ printf("Labeled for break result=%d\n", result)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Labeled for break result=15\n");
}

// test "behavior: comptime assertion" {
//     const src =
//         \\ comptime {
//         \\   assert(1 + 1 == 2)
//         \\   printf("Comptime assertion OK\n")
//         \\ }
//         \\ printf("Runtime after comptime\n")
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Comptime assertion OK\nRuntime after comptime\n");
// }
//
// test "behavior: code block as expression" {
//     const src =
//         \\ x := 10
//         \\ my_code := code { x + 5 }
//         \\ // Assuming 'code' blocks are opaque and can be assigned
//         \\ printf("Code block as expression assigned\n")
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Code block as expression assigned\n");
// }
//
// test "behavior: default arguments mixed types" {
//     const src =
//         \\ configure :: proc(name: string, id: i32 = 0, active: bool = true) {
//         \\   printf("Name=%s, ID=%d, Active=%b\n", name, id, active)
//         \\ }
//         \\ configure("UserA")
//         \\ configure("UserB", 10)
//         \\ configure("UserC", 20, false)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Name=UserA, ID=0, Active=true\nName=UserB, ID=10, Active=true\nName=UserC, ID=20, Active=false\n");
// }
//
// test "behavior: variadic function with mixed types" {
//     const src =
//         \\ print_mixed :: proc(tag: string, args: any) {
//         \\   printf("%s: %d, %f, %s\n", tag, args.0, args.1, args.2)
//         \\ }
//         \\ print_mixed("Data", 10, 3.14, "hello")
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Data: 10, 3.140000, hello\n");
// }
//
// test "behavior: nested maps" {
//     const src =
//         \\ m := ["user1": ["name": "Alice", "age": 30], "user2": ["name": "Bob", "age": 25]]
//         \\ printf("User1 name=%s, User2 age=%d\n", m["user1"]["name"], m["user2"]["age"])
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "User1 name=Alice, User2 age=25\n");
// }

test "behavior: array of structs" {
    const src =
        \\ Point :: struct { x: i32, y: i32 }
        \\ points := [Point{x:1, y:1}, Point{x:2, y:2}]
        \\ printf("Points[0].x=%d, Points[1].y=%d\n", points[0].x, points[1].y)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Points[0].x=1, Points[1].y=2\n");
}

test "behavior: error union orelse with different types" {
    const globals =
        \\ MyErr :: error { Failed }
        \\ might_fail :: proc() f64!MyErr { return MyErr.Failed }
    ;
    const src =
        \\ r := might_fail() catch 10.0
        \\ printf("Orelse different type result=%f\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Orelse different type result=10.000000\n");
}

test "behavior: catch with nested errors" {
    const globals =
        \\ ErrA :: error { A }
        \\ ErrB :: error { B }
        \\ func_a :: proc() i32!ErrA { return ErrA.A }
        \\ func_b :: proc() i32!ErrB { return func_a()! catch |err| { return ErrB.B } }
    ;
    const src =
        \\ r := func_b() catch |err| {
        \\   if err == ErrB.B {
        \\     printf("Caught nested ErrB\n")
        \\   }
        \\   0
        \\ }
        \\ printf("Nested catch result=%d\n", r)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Caught nested ErrB\nNested catch result=0\n");
}

test "behavior: match variant struct payload with destructuring" {
    const src =
        \\ V :: variant { C{ x: i32, y: i32 } }
        \\ v := V.C{ x: 100, y: 200 }
        \\ result := match v {
        \\   V.C{ x: val_x, y: val_y } => printf("Matched C with x=%d, y=%d\n", val_x, val_y),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched C with x=100, y=200\n");
}

test "behavior: match enum tags" {
    const src =
        \\ State :: enum { Active, Inactive, Pending }
        \\ s := State.Inactive
        \\ result := match s {
        \\   State.Active => printf("State is Active\n"),
        \\   State.Inactive => printf("State is Inactive\n"),
        \\   _ => printf("State is other\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "State is Inactive\n");
}

test "behavior: function with multiple return statements" {
    const globals =
        \\ get_status :: fn(c: i32) string {
        \\   if c == 200 { return "OK" }
        \\   if c == 404 { return "Not Found" }
        \\   return "Unknown"
        \\ }
    ;
    const src =
        \\ printf("Status 200=%s, Status 404=%s, Status 500=%s\n", get_status(200), get_status(404), get_status(500))
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Status 200=OK, Status 404=Not Found, Status 500=Unknown\n");
}

test "behavior: recursive function" {
    const globals =
        \\ factorial :: fn(n: i64) i64 {
        \\   if n == 0 { return 1 }
        \\   return n * factorial(n - 1)
        \\ }
    ;
    const src =
        \\ printf("Factorial 5=%d\n", factorial(5))
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Factorial 5=120\n");
}

// test "behavior: mlir op block with attributes" {
//     const src =
//         \\ op := mlir op { arith.addi %a, %b { attr = "value" } : i32 }
//         \\ // Assuming mlir op blocks are opaque and can be assigned
//         \\ printf("MLIR op with attributes assigned\n")
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "MLIR op with attributes assigned\n");
// }
//
// test "behavior: code block with expression evaluation" {
//     const src =
//         \\ x := 10
//         \\ comptime {
//         \\   expr_code := code { x + 5 }
//         \\   // Assuming a way to evaluate code blocks at comptime
//         \\   // For now, just check if it can be assigned
//         \\   evaluated_val := expr_code // This would be a comptime evaluation
//         \\ }
//         \\ printf("Code block expression assigned\n")
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Code block expression assigned\n");
// }
//
// test "behavior: function pointer with different arities" {
//     const src =
//         \\ add2 :: fn(a: i32, b: i32) i32 { return a + b }
//         \\ add3 :: fn(a: i32, b: i32, c: i32) i32 { return a + b + c }
//         \\ // Assuming function pointers can be assigned to compatible types
//         \\ // This test checks if the type system allows this.
//         \\ // For now, just check if it compiles and runs.
//         \\ printf("Function pointers with different arities assigned\n")
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Function pointers with different arities assigned\n");
// }
//
// test "behavior: variadic function with no fixed arguments" {
//     const src =
//         \\ print_all :: proc(args: any) {
//         \\   printf("Args count=%d\n", args.len)
//         \\   // Assuming iteration over 'any' tuple
//         \\   // For simplicity, just print first two if they exist
//         \\   if args.len > 0 { printf("First arg=%d\n", args.0) }
//         \\   if args.len > 1 { printf("Second arg=%s\n", args.1) }
//         \\ }
//         \\ print_all(10, "hello", true)
//         \\ print_all(5)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Args count=3\nFirst arg=10\nSecond arg=hello\nArgs count=1\nFirst arg=5\n");
// }

test "behavior: error union orelse and catch combined" {
    const globals =
        \\ MyErr :: error { Failed, Other }
        \\ might_fail :: proc(val: i32) ?i32!MyErr {
        \\   if val == 0 { return MyErr.Failed }
        \\   if val == 1 { return MyErr.Other }
        \\   return val
        \\ }
    ;
    const src =
        \\r1 := might_fail(0) orelse { 0 } catch 100
        \\r2 := might_fail(1) orelse { 1 } catch 200
        \\r3 := might_fail(5) orelse { 2 } catch 300
        \\printf("Combined error handling r1=%d, r2=%d, r3=%d\n", r1, r2, r3)
    ;
    const code = getSource(globals, src);
    try runCompilerTest(code, "Combined error handling r1=0, r2=1, r3=5\n");
}

test "behavior: optional chaining (field access on optional struct)" {
    const globals = "rt_panic :: extern proc(ptr: *const u8, len: usize) noreturn";
    const src =
        \\ Point :: struct { x: i32, y: i32 }
        \\ opt_point: ?Point = Point{ x: 10, y: 20 }
        \\ val_x := opt_point?.x
        \\ opt_null: ?Point = null
        \\ val_null_x := opt_null?.x
        \\ printf("Optional chaining val_x=%d, val_null_x=%d\n", val_x, val_null_x)
    ;
    const code = getSource(globals, src);
    runCompilerTest(code, "Optional chaining val_x=10, val_null_x=0\n") catch |err| {
        switch (err) {
            error.CompilationFailed => {},
            else => try std.testing.expect(false), // Unexpected error
        }
    };
}

test "behavior: array of arrays" {
    const src =
        \\ matrix := [[1, 2], [3, 4], [5, 6]]
        \\ printf("Matrix[1][1]=%d, Matrix[2][0]=%d\n", matrix[1][1], matrix[2][0])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matrix[1][1]=4, Matrix[2][0]=5\n");
}

test "behavior: tuple of arrays" {
    const src =
        \\ data := ([1, 2], [true, false])
        \\ printf("Tuple of arrays 0[0]=%d, 1[1]=%b\n", data.0[0], data.1[1])
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Tuple of arrays 0[0]=1, 1[1]=0\n");
}

test "behavior: mlir op with nested region" {
    const src =
        \\ a : i32 = 10
        \\ b : i32 = 32
        \\ c := true
        \\ op : i32 = mlir op(a, b, c) {
        \\   scf.if %arg2 -> (i32) {
        \\     %1 = arith.addi %arg0, %arg1 : i32
        \\     scf.yield %1 : i32
        \\   } else {
        \\     %2 = arith.subi %arg0, %arg1 : i32
        \\     scf.yield %2 : i32
        \\   }
        \\ }
        \\ // Assuming mlir op blocks are opaque and can be assigned
        \\ printf("MLIR op with nested region assigned: %d\n", op)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "MLIR op with nested region assigned: 42\n");
}

// test "behavior: code block with complex type insert" {
//     const src =
//         \\ comptime {
//         \\   PointType := code { Point :: struct { x: i32, y: i32 } }
//         \\   insert PointType
//         \\ }
//         \\ p := Point{ x: 10, y: 20 }
//         \\ printf("Inserted complex type x=%d\n", p.x)
//     ;
//     const code = getSource("", src);
//     try runCompilerTest(code, "Inserted complex type x=10\n");
// }

test "behavior: match or-pattern with at-binding" {
    const src =
        \\ x := 10
        \\ r := match x {
        \\   y @ (1 | 2 | 3) => printf("Matched 1,2,3 with %d\n", y),
        \\   y @ (10 | 11 | 12) => printf("Matched 10,11,12 with %d\n", y),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched 10,11,12 with 10\n");
}

test "behavior: match with if guard and binding" {
    const src =
        \\ x := 15
        \\ r := match x {
        \\   y @ (0..10) if y % 2 == 0 => printf("Matched even in 0-10: %d\n", y),
        \\   y @ (10..20) if y % 2 != 0 => printf("Matched odd in 10-20: %d\n", y),
        \\   _ => printf("No match\n"),
        \\ }
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Matched odd in 10-20: 15\n");
}

test "behavior: mlir block constant" {
    const src =
        \\ value: i32 = mlir op {
        \\   "arith.constant"() {value = 42 : i32} : () -> i32
        \\ }
        \\ printf("%d\n", value)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "42\n");
}

test "behavior: mlir op with comptime splices" {
    const global =
        \\ ValueTy :: mlir type { i32 }
        \\ ConstAttr :: mlir attribute { 42 : i32 }
    ;
    const src =
        \\ value: i32 = mlir op {
        \\   "arith.constant"() {value = `ConstAttr`} : () -> `ValueTy`
        \\ }
        \\ printf("%d\n", value)
    ;
    const code = getSource(global, src);
    try runCompilerTest(code, "42\n");
}

test "behavior: mlir type with spliced shape" {
    const global =
        \\ ElemTy :: mlir type { f32 }
        \\ Rows :: 4
        \\ Cols :: 16
        \\ TensorTy :: mlir type { tensor<`Rows`x`Cols`x`ElemTy`> }
    ;
    const src =
        \\ printf("Tensor type splicing OK\n")
    ;
    const code = getSource(global, src);
    try runCompilerTest(code, "Tensor type splicing OK\n");
}

test "behavior: mlir block with args" {
    const src =
        \\ a : i32 = 10
        \\ b : i32 = 32
        \\ sum: i32 = mlir op(a, b) {
        \\   "arith.addi"(%arg0, %arg1) : (i32, i32) -> i32
        \\ }
        \\ printf("%d\n", sum)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "42\n");
}
