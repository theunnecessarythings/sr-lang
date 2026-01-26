# sr-lang

![Status](https://img.shields.io/badge/status-alpha-red.svg)
![Built with Zig](https://img.shields.io/badge/built%20with-Zig-blue.svg)
![License](https://img.shields.io/badge/license-GPLv3-green.svg)

sr-lang is a personal, experimental programming language and compiler built as a way to learn compiler construction by building something real.

The project started small and gradually accumulated features as I explored parsing, semantic analysis, type systems, and backend design. As a result, some parts are relatively solid while others are experimental, incomplete, or rough around the edges.

This is intentional.

The goal of sr-lang is exploration and learning, not polish or production readiness. Bugs, awkward designs, and missing pieces reflect my learning process at the time they were written, and improving or replacing them is part of the project’s value.

## Project Philosophy

sr-lang is a learning-first project.

It prioritizes:

- Real implementations over toy examples
- Exploration over premature optimization
- Iteration over stability

If you’re looking for a polished or production-ready language, this is probably not it.
If you’re interested in how languages are built — and rebuilt — this project is meant for that.

## ✨ Features

The language is designed with a focus on modern language features, explicit control, and compiler extensibility.

### 🚀 Core Language Constructs

- **Variables & Constants:** Flexible declarations with type inference (`:=`) or explicit typing (`:`), and compile-time constants (`::`).
- **Literals:** Comprehensive support for integer (decimal, hex, octal, binary), floating-point, character, string (including raw and byte strings), and boolean literals.
- **Operators:** A full suite of arithmetic, comparison, logical, bitwise, and assignment operators, including overflow-aware arithmetic (wrapping `+%` and saturating `+|`).
- **Functions & Procedures:** Define functions (`fn`) with return values or procedures (`proc`) for side effects. Supports default arguments, variadic parameters (`any`), and external function declarations (`extern`).
- **Control Flow:**
  - **Conditional Expressions:** `if`/`else` expressions.
  - **Loops:** `while` loops (boolean, pattern-matching, infinite) and `for` loops for iteration over collections or ranges.
  - **Labeled Control:** `break` and `continue` statements, including labeled versions for nested loops and `break` with a return value.
  - **Pattern Matching:** Powerful `match` expressions for exhaustive pattern matching over values.

#### match

`match` is an expression used to branch on the structure or value of data in an exhaustive and explicit way.
It is commonly used with enums and variants to ensure all cases are handled.

```sr
result := match value {
    .ok(x)    => x,
    .error(e) => handle_error(e),
};
```
- **Error Handling:**
  - **Error Union Types:** `SuccessType!ErrorType` for handleable errors.
  - **Propagation:** The `!` operator for concise error propagation.
  - **Handling:** `catch` for error handling blocks and `orelse` for providing default values on error.
  - **Cleanup:** `defer` and `errdefer` statements for guaranteed resource cleanup on scope exit (success or error).

### 📦 Data Structures & Types

- **Basic Types:** Built-in support for various integer widths (`i32`, `u64`), floating-point numbers (`f32`, `f64`), booleans, and strings.
- **Aggregates:**
  - **Structs:** Custom data structures with named fields.
  - **Enums:** Enumerated types, including C-style and integer-backed enums.
  - **Variants (Sum Types):** Powerful discriminated unions with tuple-like or struct-like payloads, enabling exhaustive pattern matching.
  - **Unions:** Untagged unions where fields share the same memory.
- **Collections:**
  - **Tuples:** Fixed-size, ordered collections of heterogeneous types.
  - **Arrays:** Fixed-size, homogeneous collections (`[N]T`).
  - **Slices:** Dynamic views into arrays (`[]T`).
  - **Dynamic Arrays:** Growable, heap-allocated arrays (`[dyn]T`) with `append`, `len`, and `capacity` operations.
  - **Maps:** Associative arrays (`[KeyType:ValueType]`).
- **Pointers & Memory:** Raw pointers (`*T`), constant pointers (`*const T`), address-of operator (`&`), and dereference operator (`.*` or `*`).
- **Type Casting:** Explicit postfix cast operators for normal (`.()`), bitwise (`.^`), saturating (`.|`), wrapping (`.%`), and checked (`.?`) conversions.

### 🛠️ Advanced & Metaprogramming

- **Attributes:** Apply metadata to functions, types, and fields using `@[]` syntax.
- **Closures & Higher-Order Functions:** Define anonymous functions (`|x|`) that can capture their environment, enabling functional programming patterns.
- **Asynchronous Programming:** `async` procedures and `async` blocks, with the `.await` operator for non-blocking execution.
- **Compile-Time Execution (`comptime`):** Execute code during compilation for assertions, code generation, and static analysis.
- **Code as Data (`code` blocks):** Capture Abstract Syntax Trees (ASTs) as first-class values, allowing for programmatic manipulation and `insert`ion into the program.
- **MLIR Integration:** Embed raw MLIR constructs (`mlir { ... }`) directly into the source code for fine-grained control over the intermediate representation.
- **Assembly Integration:** Write functions directly in assembly (`asm { ... }`) for performance-critical sections.
- **Reflection:** Support for both compile-time and runtime reflection to inspect and manipulate types and values.
- **Compile-Time Polymorphism:** Achieved through static duck typing using the `any` type and compile-time functions as "concepts."

### 🔗 Modularity

- **Packages:** Every `.sr` file declares a package at the top of the file (`package foo`).
  - Entry points (`zig build run -- path/to/app.sr`) must declare `package main`, mirroring Go/Odin executables.
  - When a directory is imported (for example `import "std/io"` or `import "vendor/raylib"`), the compiler loads `main.sr` from that directory and expects the package name to match the directory basename (e.g. `package io`).
- **Imports:** Organize code into modules and import them using the `import` keyword with fully qualified package paths (e.g. `math :: import "examples/imports/math"`).

## 🚀 Getting Started

To build and run the compiler, you will need:

- **Zig Compiler:** The project is built using Zig.
- **LLVM/MLIR Development Libraries:** The compiler links against MLIR for its backend.
- **Clang 20:** Required for compiling generated LLVM IR (opaque pointers); ensure `clang`/`clang++` resolve to clang-20.

On Ubuntu 22.04, you can install and map clang-20 like this:

```bash
sudo apt-get update
sudo apt-get install -y lsb-release wget software-properties-common gnupg
curl -fsSL https://apt.llvm.org/llvm.sh -o /tmp/llvm.sh
chmod +x /tmp/llvm.sh
sudo /tmp/llvm.sh 20
sudo ln -sf "$(command -v clang-20)" /usr/local/bin/clang
sudo ln -sf "$(command -v clang++-20)" /usr/local/bin/clang++
```

## 📦 Prebuilt Binaries

If you don’t want to build from source, you can download a prebuilt binary from the GitHub Releases page and run it directly.

- Tested on **Ubuntu 22.04** and **Arch Linux**
- Other Linux distributions may work, but are not guaranteed

### Download

Go to the latest GitHub Release and download the binaries.

### Run

```bash
./bin/src --help # Prints usage
./bin/src run hello.sr # Compiles and runs the program
```

### Required Local Configuration

The build currently assumes system paths that may need adjustment for your machine. Check `build.zig` and update:

- `LLVM_HOME_S` (defaults to `/usr/local/lib`) to your LLVM/MLIR install `lib` directory.
- The hardcoded `libstdc++` path (`/usr/lib/libstdc++.so.6`) if your distro uses a different location.

Optional integrations (Triton, Torch, Skia) are also configured with hardcoded paths; see `build.zig` and the vendor sections below if you want to enable them.

### Building LLVM/MLIR

```bash
git clone https://github.com/llvm/llvm-project
export LLVM_HOME=llvm-project

cd llvm-project
mkdir build
cd build
cmake -G Ninja ../llvm    -DLLVM_ENABLE_PROJECTS=mlir;llvm     -DLLVM_TARGETS_TO_BUILD="Native;NVPTX;AMDGPU"    -DCMAKE_BUILD_TYPE=Release    -DLLVM_ENABLE_ASSERTIONS=ON  -DCMAKE_C_COMPILER="clang" -DCMAKE_CXX_COMPILER="clang++" -DLLVM_ENABLE_LLD=ON
ninja
cmake --install .
```

### Docker Release Build (Ubuntu 22.04)

If you want a portable Linux release without rebuilding LLVM/MLIR every time, use the Docker flow in this repo.

Build the base image once:

```bash
./build_release_image.sh
```

Then build

```bash
./release_docker.sh
```

The release flow requires clang-20. The scripts map `clang` and `clang++` to `clang-20` to avoid opaque-pointers linker errors when compiling generated LLVM IR.

This produces `sr-lang-0.1.0-linux-x86_64.tar.gz` from `zig-out` and caches LLVM/MLIR under `_llvm/build-<commit>/`.

### Building the Compiler

Navigate to the root of the `sr-lang` repository and run:

```bash
zig build
```

Release Build:

```
zig build -Doptimize=ReleaseFast
```

This command will compile the `sr-lang` compiler executable.

### Running Examples

To run the "hello world" example:

```bash
zig build run -- examples/hello.sr
```

Alternatively, after building, you can directly run the executable (debug build name):

```bash
./zig-out/bin/sr_lang examples/hello.sr
```

Release version (Why two different names? Because I can.):

```bash
./zig-out/bin/src examples/hello.sr
```

### Testing & Checks

```bash
zig build test
```

```bash
zig build check
```

### Building Vendor Packages

#### Building Triton

```bash
cd third-party/triton # make sure to pull submodules
python -m venv .venv --prompt triton
source .venv/bin/activate
pip install -r python/requirements.txt # build-time dependencies
export LLVM_BUILD_DIR=$HOME/llvm-project/build
LLVM_INCLUDE_DIRS=$LLVM_BUILD_DIR/include \
         LLVM_LIBRARY_DIR=$LLVM_BUILD_DIR/lib \
         LLVM_SYSPATH=$LLVM_BUILD_DIR \
         pip install -e .

```

### GLFW3, SDL3, Raylib

Install via system package manager.

### Torch

Download LibTorch from PyTorch website and extract to an appropriate location.

```bash
export LIBTORCH=path/to/libtorch
cd vendor/torch/torch-sys/libtch
make
```

To link torch, link `vendor/torch/torch-sys/libtch/libtorch_api.so`.

### Skia

Install Skia using system package manager if available, or build from source.

```bash
cd vendor/skiac
make
```

To link skia, link `vendor/skiac/libskia.so`.

## 🚧 Current Status

The language is in an **alpha** state. This means:

- The language syntax and semantics are subject to change.
- Many features are implemented but may not be fully stable or correctly integrated.
- The compiler is under active development, and contributions are welcome (see below).

## 📂 Project Structure

- `src/`: Contains the core Zig source code for the compiler, including AST definitions, type checking, and MLIR code generation.
- `examples/`: A collection of `.sr` source files showcasing various language features and syntax.
- `tests/`: A collection of `.sr` source files used for testing and validation.
- `std/`: A very basic collection of standard library modules, such as `io`, `math`, and `string`.
- `vendor/`: A collection of external packages that can be imported using the `import` keyword.
- `build.zig`: The Zig build script for the project.

## 📚 Documentation

- `features.md`: Detailed language feature inventory derived from compiler sources.
- `docs/`: In-progress design notes and documentation.
- `BUGS.md`: Known issues and sharp edges.
- `TODO.md`: Short- and long-term work items.

## 🤝 Contributing

Contributions are welcome! Please feel free to open issues or pull requests.

## 🌱 Good First Contributions

This project is intentionally incomplete in many areas, which makes it a good place to learn and experiment without fear of breaking something critical.

If you’re new to compilers, programming languages, or open source in general, here are some concrete ways to get involved:

### 🧩 Standard Library (High Impact, Beginner–Intermediate)

The standard library is currently very minimal. This is a great opportunity to design and implement foundational pieces from scratch, such as:

- Basic data structures (arrays, maps, strings, etc.)
- I/O utilities
- Math and numeric helpers
- Error and result utilities

Ownership of entire modules is encouraged.

### 🧪 Tests & Validation (Beginner Friendly)

Many language features exist but lack thorough testing.

Contributions here include:

- Writing `.sr` test cases for language features
- Adding regression tests for existing bugs
- Improving coverage for edge cases

This is one of the best ways to learn how the language actually behaves.

### 📚 Documentation & Examples (Beginner Friendly)

Documentation is sparse and evolving.

Help is welcome for:

- Writing small language guides or explanations
- Adding annotated examples in the `examples/` directory
- Documenting language features that already exist but aren’t explained yet

Clear docs are just as valuable as code.

### 🛠️ Compiler Internals (Intermediate–Advanced)

For contributors interested in compiler internals:

- Improving diagnostics and error messages
- Refactoring or simplifying parts of the AST or type checker
- Exploring alternative MLIR lowering strategies
- Cleaning up experimental or unused code paths

This is a good place to learn how real compiler codebases evolve.

### 🧭 Finding Your Way Around

If you’re unsure where to start:

- Look for issues labeled `good-first-issue` or `help-wanted`
- Open an issue to ask questions or propose an idea
- Submit a small exploratory PR — imperfect contributions are expected

Learning and iteration matter more than polish here.

## 📄 License

This project is licensed under the **GNU General Public License v3.0 (GPLv3)**. See the [LICENSE](LICENSE) file for the full text.
