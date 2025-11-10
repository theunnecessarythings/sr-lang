# Generating Executables with Debug Info

The MLIR backend now records source locations for TIR instructions and, when
`enable_debug_info` is `true`, also emits LLVM debug metadata so native
executables can be debugged with tools such as `gdb`. The flag is defined in
`src/mlir_codegen.zig` and defaults to `true`.

## 1. Build the compiler

```bash
zig build
```

The build installs `sr_lang` to `zig-out/bin/` and ensures the runtime library
is available for the compiled program to link against.

## 2. Compile a program with debug info

Use the `compile` subcommand to generate an executable. For example:

```bash
./zig-out/bin/sr_lang compile --output zig-out/bin/hello examples/hello.sr
```

This produces `zig-out/bin/hello` with embedded DWARF debug information. If you
need to disable debug info (for smaller binaries), set
`enable_debug_info = false` in `src/mlir_codegen.zig` and rebuild the compiler.

## 3. Debug the program with gdb

Launch `gdb` (or another DWARF debugger) on the generated binary:

```bash
gdb zig-out/bin/hello
```

Inside `gdb`, you can set breakpoints on source lines or function names, then
run the program:

```gdb
(gdb) break examples/hello.sr:5
(gdb) run
```

Source locations reported in backtraces and breakpoints now correspond to the
original `.sr` files, making interactive debugging substantially easier.
