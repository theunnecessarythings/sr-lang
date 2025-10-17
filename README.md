# sr-lang

![Status](https://img.shields.io/badge/status-alpha-red.svg)
![Built with Zig](https://img.shields.io/badge/built%20with-Zig-blue.svg)
![License](https://img.shields.io/badge/license-GPLv3-green.svg) 

`sr-lang` is a personal, experimental programming language and its compiler, currently in an early alpha stage of development. It aims to explore modern language features, explicit control over system resources, and deep integration with compiler infrastructure like MLIR.

## ✨ Features

The language is designed with a focus on modern language features, explicit control, and compiler extensibility.

### 🚀 Core Language Constructs

*   **Variables & Constants:** Flexible declarations with type inference (`:=`) or explicit typing (`:`), and compile-time constants (`::`).
*   **Literals:** Comprehensive support for integer (decimal, hex, octal, binary), floating-point, character, string (including raw and byte strings), and boolean literals.
*   **Operators:** A full suite of arithmetic, comparison, logical, bitwise, and assignment operators, including specialized wrapping (`+|`, `+%`) and saturating (`+|`, `+%`) arithmetic.
*   **Functions & Procedures:** Define functions (`fn`) with return values or procedures (`proc`) for side effects. Supports default arguments, variadic parameters (`any`), and external function declarations (`extern`).
*   **Control Flow:**
    *   **Conditional Expressions:** `if`/`else` expressions.
    *   **Loops:** `while` loops (boolean, pattern-matching, infinite) and `for` loops for iteration over collections or ranges.
    *   **Labeled Control:** `break` and `continue` statements, including labeled versions for nested loops and `break` with a return value.
    *   **Pattern Matching:** Powerful `match` expressions for exhaustive pattern matching over values.
*   **Error Handling:**
    *   **Error Union Types:** `SuccessType!ErrorType` for handleable errors.
    *   **Propagation:** The `!` operator for concise error propagation.
    *   **Handling:** `catch` for error handling blocks and `orelse` for providing default values on error.
    *   **Cleanup:** `defer` and `errdefer` statements for guaranteed resource cleanup on scope exit (success or error).

### 📦 Data Structures & Types

*   **Basic Types:** Built-in support for various integer widths (`i32`, `u64`), floating-point numbers (`f32`, `f64`), booleans, and strings.
*   **Aggregates:**
    *   **Structs:** Custom data structures with named fields.
    *   **Enums:** Enumerated types, including C-style and integer-backed enums.
    *   **Variants (Sum Types):** Powerful discriminated unions with tuple-like or struct-like payloads, enabling exhaustive pattern matching.
    *   **Unions:** Untagged unions where fields share the same memory.
*   **Collections:**
    *   **Tuples:** Fixed-size, ordered collections of heterogeneous types.
    *   **Arrays:** Fixed-size, homogeneous collections (`[N]T`).
    *   **Slices:** Dynamic views into arrays (`[]T`).
    *   **Dynamic Arrays:** Growable, heap-allocated arrays (`[dyn]T`) with `append`, `len`, and `capacity` operations.
    *   **Maps:** Associative arrays (`[KeyType:ValueType]`).
*   **Pointers & Memory:** Raw pointers (`*T`), constant pointers (`*const T`), address-of operator (`&`), and dereference operator (`.*` or `*`).
*   **Type Casting:** Explicit postfix cast operators for normal (`.()`), bitwise (`.^`), saturating (`.|`), wrapping (`.%`), and checked (`.?`) conversions.

### 🛠️ Advanced & Metaprogramming

*   **Attributes:** Apply metadata to functions, types, and fields using `@[]` syntax.
*   **Closures & Higher-Order Functions:** Define anonymous functions (`|x|`) that can capture their environment, enabling functional programming patterns.
*   **Asynchronous Programming:** `async` procedures and `async` blocks, with the `.await` operator for non-blocking execution.
*   **Compile-Time Execution (`comptime`):** Execute code during compilation for assertions, code generation, and static analysis.
*   **Code as Data (`code` blocks):** Capture Abstract Syntax Trees (ASTs) as first-class values, allowing for programmatic manipulation and `insert`ion into the program.
*   **MLIR Integration:** Embed raw MLIR constructs (`mlir { ... }`) directly into the source code for fine-grained control over the intermediate representation.
*   **Assembly Integration:** Write functions directly in assembly (`asm { ... }`) for performance-critical sections.
*   **Reflection:** Support for both compile-time and runtime reflection to inspect and manipulate types and values.
*   **Compile-Time Polymorphism:** Achieved through static duck typing using the `any` type and compile-time functions as "concepts."

### 🔗 Modularity

*   **Packages:** Every `.sr` file declares a package at the top of the file (`package foo`).
    *   Entry points (`zig build run -- path/to/app.sr`) must declare `package main`, mirroring Go/Odin executables.
    *   When a directory is imported (for example `import "std/io"` or `import "vendor/raylib"`), the compiler loads `main.sr` from that directory and expects the package name to match the directory basename (e.g. `package io`).
*   **Imports:** Organize code into modules and import them using the `import` keyword with fully qualified package paths (e.g. `math :: import "examples/imports/math"`).

## 🚀 Getting Started

To build and run the compiler, you will need:

*   **Zig Compiler:** The project is built using Zig.
*   **LLVM/MLIR Development Libraries:** The compiler links against MLIR for its backend. 

### Building LLVM/MLIR
```bash
git clone https://github.com/llvm/llvm-project
export LLVM_HOME=llvm-project

# Install libc++
sudo apt install libc++-dev libc++abi-dev # For Ubuntu/Debian
cd llvm-project
mkdir build
cd build
CXXFLAGS=-stdlib=libc++ cmake -G Ninja ../llvm    -DLLVM_ENABLE_PROJECTS=mlir     -DLLVM_TARGETS_TO_BUILD="Native;NVPTX;AMDGPU"    -DCMAKE_BUILD_TYPE=Release    -DLLVM_ENABLE_ASSERTIONS=ON  -DCMAKE_C_COMPILER="clang" -DCMAKE_CXX_COMPILER="clang++" -DLLVM_ENABLE_LLD=ON
ninja
cmake --install .
```
```
```
```

```
### Building the Compiler

Navigate to the root of the `sr-lang` repository and run:

```bash
zig build
```

This command will compile the `sr-lang` compiler executable.

### Running Examples

**Please Note:** As of now, only the `examples/hello.sr` example is fully functional and runnable. Other examples demonstrate language features and syntax but may not compile or execute correctly yet.

To run the "hello world" example:

```bash
zig build run -- examples/hello.sr
```

Alternatively, after building, you can directly run the executable:

```bash
./zig-out/bin/sr_lang examples/hello.sr
```

## 🌳 Tree-sitter Grammar

Experimental Tree-sitter support for the language is available in `tools/tree-sitter-sr`.

### Generate & Test the Parser

> **Heads-up:** The commands below require the `tree-sitter` CLI. The CLI is normally
> installed via `npm install`, which downloads packages from the public npm registry.
> The execution environment used for automated checks in this repository does not
> have outbound network access, so `npm install` will fail there. Run these commands
> on a machine with internet access (or with the CLI already installed) when you need
> to regenerate or test the grammar.

```bash
cd tools/tree-sitter-sr
npm install
npx tree-sitter generate
npx tree-sitter test
```

### Parse Sample Code

```bash
npx tree-sitter parse ../../examples/hello.sr
```

### Neovim Integration

The repository ships with a minimal Neovim plugin in `tools/nvim-sr`. To try it out:

```bash
mkdir -p ~/.config/nvim/pack/sr/start
ln -s $(pwd)/tools/nvim-sr ~/.config/nvim/pack/sr/start/sr-lang
```

Then restart Neovim and run:

```vim
:TSInstallFromGrammar sr
```

This will compile and install the grammar, enabling syntax highlighting for `.sr` files.

## 🚧 Current Status

The language is in an **alpha** state. This means:

*   The language syntax and semantics are subject to change.
*   Many features are implemented but may not be fully stable or correctly integrated.
*   Only basic programs (like "hello world") are expected to compile and run successfully.
*   The compiler is under active development, and contributions are welcome (see below).

## 📂 Project Structure

*   `src/`: Contains the core Zig source code for the compiler, including AST definitions, type checking, and MLIR code generation.
*   `grammar/`: Defines the language's lexical analysis (Flex) and parsing (Bison) rules. (Reference only)
*   `examples/`: A collection of `.sr` source files showcasing various language features and syntax.
*   `build.zig`: The Zig build script for the project.

## 🤝 Contributing

Contributions are welcome! Please feel free to open issues or pull requests.

## 📄 License

This project is licensed under the **GNU General Public License v3.0 (GPLv3)**. See the [LICENSE](LICENSE) file for the full text.
