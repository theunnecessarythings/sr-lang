# Language Construct Test Plan

This document outlines the language constructs to be covered by behavioral tests, based on the existing examples.

## Declarations

- [x] Variable declaration (inferred `:=`, typed `:`)
- [x] Constant declaration (`::`)
- [x] Function declaration (`fn`)
- [x] Procedure declaration (`proc`)
- [x] Extern function/procedure (`extern`)
- [x] Async function/procedure (`async`)
- [x] Assembly function (`asm`)
- [x] Pattern-based declarations
  - [x] Tuple destructuring
  - [x] Struct destructuring
  - [x] Variant destructuring
  - [x] Nested destructuring

## Types & Literals

- [ ] **Primitives**
  - [x] Integer literals (decimal, hex, octal, binary, with `_` separators)
  - [x] Float literals (standard, scientific notation)
  - [x] Boolean literals (`true`, `false`)
  - [x] Character literals (`'c'`)
  - [x] String literals (escapes, raw `r""`, hashed raw `r#""#`)
  - [x] Byte and Byte String literals (`b''`, `b""`, `br""`)
- [ ] **Composite Types**
  - [x] Structs (definition, instantiation, update syntax, nested structs)
  - [x] Enums (C-style, integer-backed)
  - [x] Variants (unit, tuple-like, struct-like, nested)
  - [x] Unions
  - [x] Tuples (definition, access `.0`)
  - [x] Arrays (fixed-size, typed, indexing, nested)
  - [x] Slices (from arrays `[1..3]`)
  - [x] Dynamic Arrays (`[dyn]T`, creation, `.append`, `.len`, `.capacity`)
  - [x] Maps (`[string:i32]`, creation, access, insertion)
- [ ] **Special Types**
  - [x] Pointer types (`*`, `*const`)
  - [x] Optional types (`?T`, `null`)
  - [x] `any` type
  - [x] `noreturn` type
  - [x] `complex(T)` type and literals (`1.0 + 2.0i`)
  - [x] `simd(T, N)` type
  - [x] `tensor(D...)` type
- [ ] **Error Handling Types**
  - [x] Error types via `error` keyword
  - [x] Error union types (`T!E`)

## Control Flow

- [x] `if-else` statements and expressions
- [x] `while` loops (boolean condition)
- [x] `while is` loops (pattern matching)
- [x] `for` loops (range-based `..`, iterator-based)
- [x] `match` expressions (see Patterns section)
- [x] `break` (with and without label, with value)
- [x] `continue` (with and without label)
- [x] `return` from functions
- [x] `unreachable` statement

## Expressions & Operators

- [x] **Arithmetic**: `+`, `-`, `*`, `/`, `%`
- [x] **Comparison**: `==`, `!=`, `<`, `>`, `<=`, `>=`
- [x] **Logical**: `and`, `or`, `!`
- [x] **Bitwise**: `&`, `|`, `^`, `<<`, `>>`
- [x] **Assignment**: `=`, `+=`, `-=`, `*=`, `/=`, `%=`
- [x] **Wrapping/Saturating Arithmetic**: `+|`, `+|=`, `+%`, `*%=`
- [x] **Member Access**: Struct fields (`.`), array elements (`[]`), tuple elements (`.0`)
- [x] **Calls**: Function/Procedure calls
- [x] **Async**: `await` expression
- [ ] **Error Handling**:
  - [x] Propagation (`!`)
  - [x] `orelse` expression
  - [x] `catch` expression (with and without error binding)
- [x] **Optionals**: Optional unwrap (`?`)
- [x] **Pointers**: Address-of (`&`), Dereference (`.*`), auto-deref on fields
- [ ] **Casts**:
  - [x] Normal cast (`.T`)
  - [x] Bitcast (`.^T`)
  - [x] Saturating cast (`.|T`)
  - [x] Wrapping cast (`.%T`)
  - [x] Checked cast (`.?T`)
- [ ] **Misc**:
  - [x] Block expressions (`{ ... }`)
  - [x] Range expressions (`..`, `..=`)

## Patterns

- [x] Literal patterns (numbers, strings)
- [x] Wildcard pattern (`_`)
- [x] Or-patterns (`|`)
- [x] Range patterns (`..`, `..=`)
- [x] Variable binding (`p @ Pattern`)
- [x] Tuple patterns
- [x] Array/Slice patterns (`[head, ..tail]`)
- [x] Struct patterns (full, partial with `..`)
- [x] Variant patterns
- [x] Patterns with `if` guards

## Functions & Closures

- [x] Default arguments
- [x] Variadic functions
- [ ] Closures (`|x| ...`)
- [ ] Higher-order functions (passing functions as arguments)
- [ ] Function pointers (assignment and calls)

## Defer & Error Handling

- [x] `defer` statement
- [x] `errdefer` statement

## Modules & Imports

- [ ] `package` declarations
- [ ] `import "path"` statements
- [ ] Module member access (`module.member`)
- [ ] Public visibility (`pub`)

## Metaprogramming & Low-Level

- [ ] `comptime` blocks
- [x] `code` blocks (capture and `insert`)
- [ ] `asm` blocks and functions
- [ ] `mlir` blocks (`module`, `op`, `type`, `attribute`)
- [ ] Attributes (`@[...]`) on functions, params, structs, fields, etc.
- [ ] Compile-time reflection (`typeof`, hypothetical `comptime_*` functions)
- [ ] Runtime reflection (using `any` and hypothetical `runtime_*` functions)
