
# Proposal: Inline MLIR with Comptime Splicing

- **Author**: Gemini
- **Date**: 2025-10-14
- **Status**: Proposed

## 1. Abstract

This proposal introduces a new syntax for embedding MLIR assembly into the language in a way that is both powerful and practical to implement. It allows developers to write MLIR that is parameterized by compile-time constants and types from the host language. This is achieved by treating `mlir` blocks as string templates processed by the compiler, using a minimal `@` sigil to "splice" compile-time values into the MLIR text. This approach avoids the pitfalls of both brittle string concatenation and an unmaintainable, dialect-aware compiler parser.

## 2. Motivation

The ability to use low-level MLIR constructs is a powerful feature for a systems language. However, the current mechanism is limited. To be truly useful, developers need a way to generate MLIR dynamically, especially in generic, compile-time contexts (e.g., defining a tensor of a generic type and shape).

The primary challenges are:
1.  **Dialect Extensibility**: The MLIR ecosystem is vast and extensible. It is not feasible for the sr-lang compiler to have a built-in parser for every MLIR dialect's custom assembly format. Therefore, the solution must leverage MLIR's own string-based parsers.
2.  **Syntactic Noise**: Simple string interpolation (e.g., `f"tensor<${shape}x${elem}>"`) is often verbose, error-prone, and syntactically noisy.
3.  **Type Safety**: Ad-hoc string construction offers no guarantee that the generated MLIR is valid or that the values being interpolated make sense in their context.

This proposal aims to find a "sweet spot" that provides a clean, "genuinely inline" developer experience while respecting the practical constraint of using MLIR's parsers.

## 3. Proposed Solution

We propose a unified mechanism for all `mlir` blocks (`mlir`, `mlir type`, `mlir attribute`, `mlir op`). These blocks are treated as string templates that are resolved at compile time. Two distinct, clean mechanisms are used to substitute sr-lang values into the template:

#### 1. Runtime Values (for `mlir op`)
Runtime variables are passed as arguments in parentheses to an `mlir op` block. Inside the block, they are referenced positionally using the standard MLIR SSA value syntax (`%arg0`, `%arg1`, etc.).

```sr
a := 10
b := 32
sum := mlir op(a, b) {
    "arith.addi"(%arg0, %arg1) : (i32, i32) -> i32
}
```

#### 2. Compile-Time Values (Splicing)
Compile-time known identifiers (constants defined with `::`, types, or other `comptime` variables) are spliced into the string template using the `@` prefix. The compiler replaces `@identifier` with the string representation of the identifier's value before passing the template to the MLIR parser.

```sr
comptime {
    ElemType :: f32
    Shape :: [4, 16]
    MyTensorType :: mlir type { tensor<@Shape x @ElemType> }
}
```
This provides an unambiguous way for the compiler to substitute values without needing to understand the surrounding dialect syntax. It simply finds and replaces the `@` markers.

## 4. Detailed Design and Examples

This section demonstrates how the proposed syntax applies to each MLIR construct.

#### `mlir type`
Defines an MLIR type. Splicing is used to construct generic types.

```sr
// A static type definition
I32Ptr :: mlir type { !llvm.ptr }

// A generic type definition using comptime splicing
comptime {
    Elem :: f64
    Dims :: [8, 8]
    MyMatrixType :: mlir type { tensor<@Dims x @Elem> }
}
```

#### `mlir attribute`
Defines an MLIR attribute, often using spliced comptime constants.

```sr
comptime {
    AlignmentValue :: 16
    MyAlignAttr :: mlir attribute { #llvm.align<@AlignmentValue> }
}
```

#### `mlir op`
Creates a single MLIR operation. It can take runtime arguments and use spliced comptime values for types or attributes. The block evaluates to the resulting SSA value(s) of the operation.

```sr
comptime {
    I64 :: i64
}
c := mlir op {
    "arith.constant"() {value = 42 : @I64} : () -> @I64
};
```

#### `mlir { ... }` (Module)
Defines a full MLIR module.

```sr
comptime {
    FunctionName :: "my_generated_func"
}
MyModule :: mlir {
    module {
        func.func @@FunctionName() -> i32 {
            %c42 = arith.constant 42 : i32
            func.return %c42 : i32
        }
    }
}
```

## 5. Use Case: A Generic Tensor Type

This example ties all the concepts together to create a generic `Tensor` type, demonstrating the power and cleanliness of the proposed syntax.

```sr
// Generic function to create a Tensor struct type.
// This follows the idiomatic pattern for generics in the language.
Tensor :: fn(comptime Elem: type, comptime Shape: []const i64) type {
    return struct {
        // The underlying data storage.
        data: [prod(Shape)]Elem, // Assumes a comptime `prod` function.
    }
}

// A generic function to add two Tensors of the same type.
add_tensor :: fn(comptime T: type, a: T, b: T) T {
    // At compile time, resolve the generic parameters and define the
    // corresponding MLIR type by splicing them.
    comptime {
        Elem :: comptime_get_generic_arg(T, 0)  // Assumes reflection
        Shape :: comptime_get_generic_arg(T, 1) // Assumes reflection
        MlirType :: mlir type { tensor<@Shape x @Elem> }
    }

    // The `mlir op` block uses runtime arguments for the tensor data
    // and splices in the comptime-resolved MLIR type.
    result_data := mlir op(a.data, b.data) {
        "tensor.add"(%arg0, %arg1) : (@MlirType, @MlirType) -> @MlirType
    }

    return T{ data: result_data }
}

// --- Usage ---
main :: proc() {
    // 1. Instantiate a concrete Tensor type.
    MyTensor :: Tensor(f32, [4, 16])

    // 2. Create instances of this type.
    t1: MyTensor = ...
    t2: MyTensor = ...

    // 3. Use the generic `add_tensor` function. The compiler specializes
    //    this call, generating the correct `tensor.add` operation for
    //    `tensor<4x16xf32>`.
    t3 := add_tensor(MyTensor, t1, t2)
}
```

## 6. Implementation Notes

The compiler would implement this feature as follows:
1.  During parsing, recognize `mlir` blocks.
2.  Inside a block, scan for `@identifier` tokens. For each one, resolve `identifier` as a compile-time constant in the current scope.
3.  Define stringification rules for various sr-lang `comptime` types (e.g., `type`, `string`, integer types, arrays of integers).
4.  At the end of semantic analysis for the scope, construct the final MLIR string by replacing each `@identifier` with its stringified value.
5.  Pass the resulting string to the appropriate MLIR C API function (e.g., `mlirTypeParseGet`, `mlirModuleCreateParse`). For `mlir op`, the runtime arguments are passed separately to the execution mechanism.

## 7. Alternatives Considered

-   **Full DSL Parser**: Rejected because it would require the sr-lang compiler to parse all possible MLIR dialect syntaxes, which is unmaintainable.
-   **Standard String Interpolation**: Rejected because syntax like `${...}` was considered noisy and less "inline" than desired. The proposed `@` splice is more minimal and serves a single, specific purpose.
