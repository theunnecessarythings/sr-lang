# Comptime Evaluation and Monomorphization Plan

This document outlines the design for implementing arbitrary compile-time code execution (`comptime`) and JIT-powered monomorphization.

The core architecture is a fixed-point evaluation loop within the compiler's `checker` pass. This loop discovers `comptime` work, JIT-compiles it into a native "thunk", executes it, and patches the result back into the compiler's IR. This process repeats until no `comptime` work remains.

## 1. Core Architecture: Fixed-Point Evaluation Loop

The `checker` pass will be modified to operate as a loop:

1.  **Scan for Work:** Traverse the TIR to find the next `ComptimeBlock` node or a call to a generic function that needs monomorphization.
2.  **Exit Condition:** If no work is found, the fixed-point is reached. The loop terminates, and the final, fully-materialized TIR is passed to the MLIR codegen stage.
3.  **Process Work:** If a `comptime` block is found, it is processed as a "thunk" (see section 2).
4.  **Patch IR:** The result from the executed thunk is used to modify the TIR. For example, a `ComptimeBlock` node is replaced with a `Const` node.
5.  **Repeat:** The loop continues from step 1, as patching the IR may have introduced new `comptime` work.

## 2. The Comptime Thunk

A `comptime` block is not interpreted. It is isolated and compiled into a native, executable function called a "thunk".

-   **Standard Signature:** Each thunk will be wrapped in a function with a C ABI, allowing the compiler to call it via a function pointer.
    -   `fn(api_ptr: *ComptimeApi, result_ptr: *ComptimeValue)`
-   **`api_ptr`:** A pointer to a vtable of compiler-provided functions that the `comptime` code can call back into (the Comptime API).
-   **`result_ptr`:** An output pointer to a memory location where the thunk writes its result.

## 3. JIT Compilation Pipeline

For each thunk, a temporary, nested compilation pipeline is invoked:

1.  **Isolate & Wrap:** The TIR for the `comptime` block is extracted and wrapped in the standard thunk function signature.
2.  **Temporary Module:** A new, in-memory MLIR module is created for the thunk.
3.  **Codegen Thunk:** The thunk's TIR is lowered to MLIR within this temporary module. Calls to `comptime` intrinsics become `extern fn` declarations.
4.  **Instantiate JIT Engine:** An `mlir.ExecutionEngine` is created for the temporary module.
5.  **Register API Symbols:** The compiler registers pointers to its internal API functions (e.g., the implementation of `comptime_print`) with the execution engine using `mlirExecutionEngineRegisterSymbol`. This links the JIT'd code back to the compiler.
6.  **Execute:** The thunk is invoked via the execution engine. The compiler passes pointers to its API vtable and the result memory location.
7.  **Retrieve Result:** The compiler reads the `ComptimeValue` from the result memory location.

## 4. The Comptime API & ABI

This is the crucial interface allowing `comptime` code to interact with the compiler. It will be a C-ABI-compatible struct of function pointers.

**Initial API Surface:**
-   `comptime_print(format: *const u8, ...)`: For debugging `comptime` code.
-   `get_type_by_name(name: string) -> TypeId`: For basic reflection.
-   `get_struct_fields(type: TypeId) -> []FieldInfo`: For struct reflection.
-   `add_tir_function(tir_body: ComptimeValue.Code) -> FuncId`: For metaprogramming and generating new functions.

## 5. Monomorphization via Comptime

Generic functions are treated as `comptime` function generators.

1.  **Trigger:** A call to a generic function is detected in the `Checker`.
2.  **JIT Thunk:** The body of the generic function is JIT-compiled as a thunk.
3.  **Pass Types:** The *concrete types* of the call arguments are passed to the thunk as `ComptimeValue.Type` arguments.
4.  **Metaprogramming:** The JIT'd thunk executes. It uses the Comptime API to inspect the types it received and programmatically constructs the TIR for a new, specialized function.
5.  **Return Code:** The thunk returns the new TIR as a `ComptimeValue.Code`.
6.  **Integration:** The main compiler receives this new TIR, adds it to the main module, and replaces the generic call site with a direct call to the newly generated specialized function.

## 6. Incremental Implementation Plan

We will implement this system in small, verifiable steps.

1.  **Step 1: Basic Constant Evaluation (Non-JIT):**
    -   Implement a simple, non-JIT evaluator for `comptime` blocks that only handles constant integer literals and basic arithmetic (`+`, `*`).
    -   Integrate this into the `Checker`'s fixed-point loop.
    -   The goal is to test the infrastructure for finding `comptime` blocks and patching their results back into the TIR.
    -   Create `examples/comptime_const.sr` to test this.

2.  **Step 2: Foundational JIT Infrastructure:**
    -   Implement the JIT pipeline for a thunk that does nothing but return a hardcoded value.
    -   Focus on creating the temporary module, `ExecutionEngine`, and invoking a function.
    -   Replace the simple evaluator from Step 1 with this JIT infrastructure.

3.  **Step 3: The Comptime API & State:**
    -   Define the `ComptimeApi` struct and the `ComptimeValue` union.
    -   Implement the first API function: `comptime_print`.
    -   Pass the API vtable and result pointer to the thunk.
    -   Create a test that calls `comptime_print` from a `comptime` block.

4.  **Step 4: Reflection:**
    -   Expand the Comptime API with basic reflection capabilities (`get_type_by_name`, etc.).
    -   Create tests that inspect types at compile time.

5.  **Step 5: Monomorphization of a Simple Generic Function:**
    -   Implement the full monomorphization workflow for a simple generic function 
    -   This will involve passing types to the JIT'd thunk and generating new TIR.

6.  **Step 6: Advanced Metaprogramming:**
    -   Implement the `add_tir_function` API call.
    -   Create a test where a `comptime` block generates and registers a new function that is then called at runtime.
