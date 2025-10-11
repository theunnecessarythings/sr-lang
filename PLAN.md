# Monomorphization Implementation Plan

This document outlines the incremental plan to implement monomorphization in the sr-lang compiler.

## Goal

The primary goal is to support generic programming, enabling code like the `max` function in `examples/generic.sr` to work.

```sr
// examples/generic.sr
max :: fn(comptime T: type, a: T, b: T) T {
    return if a > b { a } else { b }
}

gimmeTheBiggerInteger :: fn(a: u64, b: u64) u64 {
    return max(u64, a, b)
}
```

## Guiding Principles

*   **Modularity**: New, self-contained logic for monomorphization will be placed in a new file, `src/monomorphize.zig`. The existing `src/lower_tir.zig` will only contain the necessary integration points, keeping it from becoming bloated.
*   **Incrementality**: The implementation will proceed in small, verifiable steps. After each step, we will ensure the compiler builds and functionality is tested with a minimal example before moving to more complex cases.

---

### Step 1: Setup and Basic Plumbing

The first step is to set up the necessary file and data structures and integrate the monomorphization process into the lowering pipeline in a minimal, non-functional way.

1.  **Create `src/monomorphize.zig`**:
    *   Create the new file.
    *   Define an empty `Monomorphizer` struct within it. It will eventually hold the cache, worklist, and a reference to the `LowerTir` instance.
    *   Add `init` and `deinit` functions for the struct.

2.  **Integrate `Monomorphizer` into `LowerTir`**:
    *   In `src/lower_tir.zig`, add a `Monomorphizer` instance to the `LowerTir` struct.
    *   Call the `init` and `deinit` functions in `LowerTir.init` and `LowerTir.deinit`.
    *   Add a call to a new, empty `monomorphizer.run()` function at the end of `LowerTir.run()`.

3.  **Create a Minimal Test Case**:
    *   Use the existing `examples/simple_generic.sr` as our initial, minimal test case. It contains a generic `max` function and a single call `max(i32, 10, 20)`.

**Verification**: The compiler must build successfully. No functional change is expected.

---

### Step 2: Detect Generic Calls and Queue for Monomorphization

Next, we'll make `lowerCall` detect generic calls and add them to a worklist for processing.

1.  **In `src/monomorphize.zig`**:
    *   Define a `MonomorphizationRequest` struct to hold information about a specialization task.
    *   Implement a `requestMonomorphization(call_expr)` function on the `Monomorphizer`. This function will perform a basic check to see if a call is generic, add a corresponding request to its internal worklist, and return a generated mangled name for the specialized function.

2.  **In `src/lower_tir.zig`**:
    *   In `lowerCall`, add logic to detect a call to a generic function.
    *   When detected, it will call `monomorphizer.requestMonomorphization()`.
    *   The `tir.Call` instruction will be updated to use the new mangled name, and the `comptime` arguments will be removed from the call's argument list.

**Verification**: The compiler will build. When compiling the simple test case, the build will fail during linking because the mangled function is referenced but not yet defined. We will add a temporary debug print to `Monomorphizer.run()` to confirm that a request is being correctly queued.

---

### Step 3: Implement the Monomorphization Loop and Basic Instantiation

This is the core step where we first generate the specialized function.

1.  **In `src/monomorphize.zig`**:
    *   Define a `MonomorphizationContext` struct to hold the bindings for `comptime` parameters.
    *   Implement the `Monomorphizer.run()` loop. It will iterate through the worklist and call a new `Monomorphizer.instantiate(request)` function for each item.
    *   `Monomorphizer.instantiate()` will create the `MonomorphizationContext` and then call a new public function on `LowerTir`, e.g., `lowerer.lowerSpecializedFunction(mangled_name, generic_fn_ast, context)`.

2.  **In `src/lower_tir.zig`**:
    *   Implement the new `lowerSpecializedFunction`. This will wrap the existing `lowerFunction`, managing a new `monomorphization_context_stack` to make the substitution context available during lowering.
    *   Adapt `lowerFunction`, `lowerIdent`, and other key functions to be context-aware. This will involve creating a `resolveType` helper that checks the context stack before falling back to the checker's type info.

**Verification**: The `examples/simple_generic.sr` test case should compile and run correctly.

---

### Step 4: Expand `comptime` Argument Handling

With the basic pipeline in place, we will improve the handling of `comptime` arguments.

1.  **In `src/monomorphize.zig`**:
    *   Enhance the logic for evaluating `comptime` arguments. This may involve moving parts of the `comptime` JIT logic out of `lower_tir.zig` and into `src/comptime.zig` so it can be shared.
    *   Refine the cache key generation to robustly handle different kinds and combinations of `comptime` values.

**Verification**: Add more test cases with different argument types (`f32`, `u64`) and simple constant values as `comptime` arguments.

---

### Step 5: Generic Data Structures and Further Testing

Finally, we will tackle more complex generics and edge cases.

1.  **Generic Data Structures**: I will analyze and, if necessary, implement the logic for handling `comptime` function calls that return types, like `List(i32)`. This may require a `jitEvalComptimeCall` mechanism.
2.  **Full Example**: Work towards making the entire `examples/generic.sr` file compile and run.
3.  **Edge Cases**: Add tests for more complex scenarios like nested generic calls and recursive generic functions to ensure the implementation is robust.
