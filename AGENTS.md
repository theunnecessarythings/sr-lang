# Guidelines

## Project Structure & Module Organization
Core compiler logic and the CLI live in `src/`, with entry points in `src/main.zig` and shared modules exported from `src/root.zig`. The runtime support library is in `runtime/`, standard packages ship under `std/`, and vendored libraries sit in `vendor/`. Language samples live in `examples/`, reference notes sit in `docs/`, and behavioral, parser, and fuzzing harnesses congregate in `tests/`, alongside `test_main.zig`.

## Build, Test, and Development Commands
- `zig build` compiles the `sr_lang` driver and installs artifacts to `zig-out/`.
- `zig build run -- run examples/hello.sr` exercises the compiler via the build runner.
- `zig build run -- ast examples/hello.sr` prints the AST
- `zig build run -- tir examples/hello.sr` prints the checker TIR (typed IR)
- `zig build run -- mlir examples/hello.sr` prints the MLIR generated
- `zig build run -- check examples/hello.sr` runs the checker

- `zig build test` executes module and executable Zig tests; ensure MLIR static libraries exist under `/usr/local/lib`.


## Project Structure
- `src/lexer.zig` - Lexer
- `src/parser.zig` - Parser, and generates CST `src/cst.zig`
- `src/lower.zig` - Takes CST and lowers to AST `src/ast.zig`
- `src/checker.zig` - Takes AST and immutable (produces type information `src/types.zig`)
- `src/lower_tir.zig` - Takes AST and Type Info and produces TIR `src/tir.zig`
- `src/monomorphize.zig` `src/comptime.zig` - Helpers for monomorphization and comptime eval
- `src/mlir_codegen.zig` - Takes TIR and produces MLIR
- `src/mlir_bindings.zig` - MLIR C API bindings
- `src/module_graph.zig` and `src/package/*` - Packages, modules, file imports
- `src/compile.zig` `src/pipeline.zig` - Passes and main pipeline
- `tests/*` - Contains tests

## Testing Guidelines
Place new behavioral cases alongside related suites (e.g., extend `tests/behavior_arrays.zig` for array semantics). Keep the `behavior_*` prefix so `test_main.zig` discovers them. Regression snippets belong in `tests/corpus/` and should be wired into the relevant harness. 


## Environment Notes
MLIR 20+ 
LLVM 20+
Zig 0.15.1
