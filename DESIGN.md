# sr-lang Compiler Design

This document outlines the architecture and design of the `sr-lang` compiler. It follows a multi-stage pipeline, transforming source code through several Intermediate Representations (IRs) before generating an executable. The design emphasizes modularity, clear separation of concerns between compiler stages, and efficient data representation using a Data-Oriented Design (DOD) approach.

## Compiler Pipeline

The compilation process is a linear sequence of stages, where the output of one stage is the input to the next. The `pipeline.zig` file orchestrates this flow.

```
[Source Text] -> Lexer -> [Tokens] -> Parser -> [CST] -> Lowering -> [AST] -> Checker -> [Typed AST] -> TIR Lowering -> [TIR] -> MLIR Codegen -> [MLIR] -> LLVM IR -> [Object File] -> Linker -> [Executable]
```

1.  **Lexing:** The `lexer.zig` module takes the raw source text and breaks it down into a stream of tokens (e.g., identifiers, keywords, operators, literals).
2.  **Parsing:** The `parser.zig` module, a Pratt parser, consumes the token stream and builds a **Concrete Syntax Tree (CST)**. The CST is a very literal, detailed representation of the source code, including all punctuation and syntactic details.
3.  **CST to AST Lowering:** The `lower.zig` module transforms the CST into an **Abstract Syntax Tree (AST)**. This process desugars complex syntax into simpler, more fundamental nodes and removes purely syntactic information (like grouping parentheses), creating a more abstract representation of the code's semantics.
4.  **Semantic Analysis (Checking):** The `checker.zig` module traverses the AST to perform semantic validation. This is a crucial stage that includes:
    *   **Symbol Resolution:** Using `symbols.zig`, it builds a symbol table to track all declared variables, functions, and types, resolving identifier lookups.
    *   **Type Checking:** It infers and checks the type of every expression, ensuring type safety. It uses a sophisticated `TypeStore` from `types.zig` to manage and intern all types.
    *   **Pattern Match Analysis:** The `check_pattern_matching.zig` submodule ensures that `match` expressions are exhaustive and that their arms are reachable.
5.  **AST to TIR Lowering:** The `lower_tir.zig` module lowers the now-validated and type-annotated AST into a **Typed Intermediate Representation (TIR)**. The TIR is a lower-level, CFG-like (Control Flow Graph) representation. Expressions are broken down into a sequence of simple, three-address-code-like instructions.
6.  **MLIR Code Generation:** The `mlir_codegen.zig` module traverses the TIR and generates **MLIR (Multi-Level Intermediate Representation)** code. It maps TIR instructions to operations in various MLIR dialects, primarily `arith`, `func`, and `llvm` (for LLVM-specific features). This stage also handles the function **Application Binary Interface (ABI)** using `abi.zig` to correctly manage function arguments and return values according to platform conventions (e.g., x86-64 SysV).
7.  **MLIR to LLVM IR:** The `compile.zig` module uses MLIR's built-in pass manager to run a pipeline of transformations that convert the high-level MLIR dialects into the `LLVM` dialect.
8.  **LLVM Backend:** Finally, the LLVM dialect MLIR is translated into LLVM IR, which is then compiled into an object file and linked with the `sr-lang` runtime and any other specified libraries to produce the final executable.

## Data Structures & Intermediate Representations

A key feature of the compiler is its use of a **Data-Oriented Design (DOD)** for its IRs. Instead of creating a tree of heap-allocated objects, it uses a "Structure of Arrays" approach, where nodes of a given type are stored in contiguous arrays (column stores). This is managed by the `Table` and `Pool` data structures in `cst.zig`. An `Index` type (e.g., `ExprId`, `DeclId`) is used to reference nodes, providing a safe and efficient alternative to pointers. This design improves cache locality and reduces memory allocation overhead.

### CST (Concrete Syntax Tree)

-   **Defined in:** `cst.zig`
-   **Purpose:** A direct, one-to-one representation of the parsed source code, including all syntactic details. It is designed to be easily constructed by the parser.
-   **Structure:** Implemented as a DOD `ExprStore` and `PatternStore`. It uses `ExprId` and `PatternId` to reference nodes. The tree structure is encoded by IDs within the node definitions (e.g., an `Infix` node has `left` and `right` `ExprId` fields).

### AST (Abstract Syntax Tree)

-   **Defined in:** `ast.zig`
-   **Purpose:** A simplified, more semantic representation of the code. It abstracts away details like operator precedence (which is encoded in the tree structure) and syntactic sugar.
-   **Structure:** Also implemented using the DOD approach from `cst.zig`. It has a richer and more semantically-grouped set of node kinds (`ExprKind`, `StmtKind`, `PatternKind`) compared to the CST. For example, various assignment operators (`+=`, `-=`) from the CST are desugared into simple `Assign` statements in the AST during the `lower.zig` pass.

### Type System

-   **Defined in:** `types.zig`
-   **Purpose:** To represent and manage all types within the language.
-   **Structure:** The `TypeStore` is another DOD-based store. It interns all types, ensuring that each unique type (e.g., `i32`, `*u8`, `[]string`) is represented by a single, unique `TypeId`. This makes type comparison a simple integer comparison. The `TypeInfo` struct, populated by the checker, acts as a side table mapping AST nodes (`ExprId`, `DeclId`) to their corresponding `TypeId`.

### TIR (Typed Intermediate Representation)

-   **Defined in:** `tir.zig`
-   **Purpose:** To serve as a bridge between the high-level, tree-based AST and the linear, instruction-based MLIR. It makes code generation simpler by making control flow explicit.
-   **Structure:** A TIR program consists of functions, which in turn contain a graph of basic blocks. Each block contains a list of simple, three-address-code-like instructions (`InstrId`) and is terminated by a control-flow instruction (`TermId`, e.g., `br`, `cond_br`, `return`). All operands are `ValueId`s, representing SSA (Static Single Assignment) values.

## Key Compiler Components

### `main.zig` & `pipeline.zig`

-   `main.zig` is the user-facing entry point. It parses command-line arguments to determine which subcommand to run (`compile`, `run`, `ast`, etc.).
-   `pipeline.zig` contains the core logic that drives the compilation process, calling each stage in sequence and passing the resulting IR to the next. It manages the lifecycle of the various data structures.

### `parser.zig`

The parser is a Pratt parser, which is particularly well-suited for handling operator precedence.
-   `nud` (null denotation) methods handle prefix tokens (e.g., literals, identifiers, unary operators).
-   `led` (left denotation) methods handle infix and postfix tokens (e.g., binary operators, function calls, field access).
-   Binding power (`bp`) values determine operator precedence. The parser continues consuming infix operators as long as their left binding power is greater than the current minimum.

### `checker.zig`

This is the heart of the compiler's semantic analysis.
-   It uses a `SymbolStore` (`symbols.zig`) to manage scopes and identifier resolution.
-   It recursively walks the AST, calling `checkExpr` for each expression.
-   It determines the type of each expression and stores it in the `TypeInfo` map.
-   It enforces type rules, such as checking that the operands of a `+` operation are numeric or that the condition of an `if` statement is a boolean.
-   It performs detailed analysis of `match` statements to ensure all possible cases are covered, preventing potential runtime errors.

### `lower_tir.zig`

This pass is responsible for the significant structural transformation from a tree-based AST to a graph-based TIR.
-   It creates basic blocks and manages the flow of control.
-   AST expressions are broken down into sequences of simple TIR instructions. For example, `a + b * c` becomes:
    1.  `%1 = mul %b, %c`
    2.  `%2 = add %a, %1`
-   It makes SSA form explicit, where every new value is assigned a unique `ValueId`.

### `mlir_codegen.zig`

This is the final stage of the frontend.
-   It iterates through the TIR functions, blocks, and instructions.
-   For each TIR instruction, it emits a corresponding MLIR operation. For example, a `tir.Add` instruction becomes an `arith.addi` or `arith.addf` operation.
-   It uses `abi.zig` to determine how to lower function signatures for external calls, handling argument passing (by value, by reference, sret) and return values according to platform conventions.
-   It manages the creation of global constants, particularly for string literals, which are emitted as `llvm.mlir.global` operations.

### `import_resolver.zig`

This component handles the module system.
-   When an `import` statement is encountered, the resolver is invoked to find and compile the imported file.
-   It maintains a cache (`ModuleEntry`) to avoid recompiling the same module multiple times.
-   It runs a separate pipeline for each imported module to generate its TIR and type information.
-   The exported symbols of the imported module are then made available to the checker and MLIR code generator, with names mangled to avoid collisions.

## Language Features

The following sections detail the major features of the `sr-lang` language, as inferred from the example code.

### Types and Data Structures

-   **Primitive Types:** The language includes standard primitives like `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32`, `u64`, `f32`, `f64`, `bool`, `char`, and `string`.
-   **Literals:** Supports integer literals in decimal, hexadecimal (`0x`), octal (`0o`), and binary (`0b`) formats. String literals support standard escape sequences, and raw strings (`r#"..."#`) are available.
-   **Structs:** Composite data types with named fields.
    ```
    Point :: struct { x: i32, y: i32 }
    ```
-   **Enums:** C-style enumerations for simple, named constants. The underlying integer type and values can be specified.
    ```
    State :: enum { Running, Paused }
    HttpCode :: enum(u16) { Ok = 200, NotFound = 404 }
    ```
-   **Variants (Sum Types):** A powerful feature for defining a type that can hold one of several different shapes. Variants can have no payload, a tuple-like payload, or a struct-like payload.
    ```
    Message :: variant {
      Write(string),
      Click { x: i32, y: i32 },
      Nothing,
    }
    ```
-   **Unions:** Similar to C unions, where all fields share the same memory location.
-   **Tuples:** Fixed-size, ordered collections of elements, e.g., `(i32, string)`.
-   **Arrays, Slices, and Dynamic Arrays:**
    -   **Arrays:** Fixed-size collections: `[5]i32`.
    -   **Slices:** A view into a contiguous sequence of elements: `[]i32`.
    -   **Dynamic Arrays:** Growable arrays, similar to vectors: `[dyn]i32`.
-   **Maps:** Key-value hash maps: `[string:i32]`.
-   **Pointers:** `*T` for a mutable pointer and `*const T` for an immutable pointer.
-   **Optional Types:** A type prefixed with `?` can hold either a value of that type or `null`. E.g., `?string`.
-   **Error Types:** The `error` keyword provides a shorthand for defining a simple variant/enum type intended for error handling.

### Functions and Control Flow

-   **Functions vs. Procedures:**
    -   **`fn`:** Defines a pure function that is expected to return a value.
    -   **`proc`:** Defines a procedure that can have side effects and does not need to return a value.
-   **Control Flow:**
    -   Standard `if`/`else if`/`else` expressions.
    -   `while` loops, which can be conditional, infinite (`while {}`), or pattern-based (`while is Some(x) := ...`).
    -   `for` loops for iterating over collections like arrays and ranges (`for item in my_array`).
-   **`defer` and `errdefer`:**
    -   `defer`: Executes a block of code when the current scope is exited, regardless of how it exits.
    -   `errdefer`: Executes a block of code only when the scope is exited due to an error.

### Pattern Matching

Pattern matching is a central feature, used in `match` expressions, variable declarations, and loops.
-   **`match` expression:** Exhaustively matches a value against a set of patterns.
    ```
    match value {
        1 => print("one"),
        2 | 3 => print("two or three"),
        4..=10 => print("range"),
        Point{x, y: 0} => print("on the x-axis"),
        [first, ..rest] => print("array pattern"),
        _ => print("default"),
    }
    ```
-   **Destructuring:** Patterns can be used in `let` bindings to destructure structs, tuples, and arrays.
    ```
    (a, b) := (1, 2)
    Point{x, y} := my_point
    ```
-   **`@` Operator:** Binds a value to a variable while simultaneously matching a more specific sub-pattern.
    ```
    match maybe_point {
        p @ Option.Some(Point{x, y}) => print("Got point:", p),
        _ => {}
    }
    ```

### Error Handling

-   **Error Unions:** Functions that can fail return an error union type, written as `SuccessType!ErrorType`.
-   **`!` Operator:** The postfix `!` operator is used to propagate an error. If the expression it's applied to is an error, the current function immediately returns that error.
-   **`catch` Expression:** Provides a way to handle a potential error.
    ```
    read_file("path")! catch |err| { print("Failed:", err) }
    ```
-   **`orelse`:** Provides a default value if an operation results in an error.
    ```
    content := read_file("path") orelse "default content"
    ```

### Metaprogramming and Advanced Features

-   **`comptime`:** Code inside a `comptime {}` block is executed at compile time.
-   **`code` and `insert`:** The `code {}` block captures a piece of code as an AST value. The `insert` statement splices a `code` value back into the program, allowing for compile-time code generation.
-   **Closures:** Anonymous functions that can capture variables from their enclosing scope.
    ```
    add_amount := |x: i32| { return x + amount }
    ```
-   **Async/Await:** The `async` keyword creates a future, and the `.await` postfix operator suspends execution until the future is resolved.
-   **Inline MLIR and Assembly:** The language allows for embedding low-level code directly.
    -   `mlir { ... }`: A block of MLIR code.
    -   `asm { ... }`: A function body can be replaced with an assembly block.
-   **Postfix Casts:** A convenient syntax for various types of casts:
    -   `.()`: Normal cast (e.g., `my_float.(i32)`).
    -   `.^`: Bitcast.
    -   `.|`: Saturating cast.
    -   `.%`: Wrapping (modular) cast.
    -   `.?`: Checked cast (returns an optional).

### Module System

-   **`package`:** A file can declare which package it belongs to.
-   **`import`:** The `import "path"` expression loads another module. The public symbols of the imported module are accessed through the variable the import result is assigned to.
    ```
    math :: import "std/math"
    result := math.add(v1, v2)
    ```

### Attributes

-   Attributes provide metadata to the compiler about functions, types, or fields. The syntax is `@[name=value, ...]`.
    ```
    @[inline, export_name=my_add]
    add :: fn(a: i32, b: i32) i32 { ... }
    ```

## Error Handling (`diagnostics.zig`)

-   **Diagnostics Engine:** The `diagnostics.zig` file defines a centralized system for collecting and reporting errors, warnings, and notes.
-   **Rich Messages:** It supports structured diagnostic messages with codes, severity levels, and formatted text. It can also attach detailed notes to primary error messages to provide more context or suggest fixes.
-   **Source Location:** Every diagnostic is tied to a specific source location (`Loc`), allowing the engine to print the relevant line of code with a caret `^` pointing to the issue, similar to modern compilers like Rust or Clang.