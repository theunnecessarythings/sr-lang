# Examples v2

These examples are a fresh, tutorial-style set that favors small, focused files.
Each chapter uses a Socratic style: questions in comments, answers in code.

Run a chapter directly:

- `zig build run -- run examples_v2/00_intro.sr`

Chapters (in order):

- `examples_v2/00_intro.sr` - entry point, imports, basic output
- `examples_v2/01_comments_and_literals.sr` - comments, strings, chars, bools, bytes
- `examples_v2/02_numbers_and_casts.sr` - numbers, complex, cast operators
- `examples_v2/03_bindings_and_scope.sr` - :=, :, ::, shadowing, blocks
- `examples_v2/04_functions_and_procedures.sr` - fn/proc, defaults, variadic, HOFs
- `examples_v2/05_control_flow_if_match.sr` - if/else, match, unreachable
- `examples_v2/06_loops_and_ranges.sr` - for/while, ranges, labeled loops
- `examples_v2/07_structs_and_tuples.sr` - structs, tuples, update syntax
- `examples_v2/08_enums_variants_unions.sr` - enums, variants, unions
- `examples_v2/09_arrays_slices_dyn_arrays.sr` - arrays, slices, dyn arrays
- `examples_v2/10_maps_and_strings.sr` - maps, string slicing basics
- `examples_v2/11_pointers_and_optional.sr` - pointers, optionals, unwrap
- `examples_v2/12_errors_and_defer.sr` - error unions, catch, orelse, defer
- `examples_v2/13_patterns.sr` - match patterns and destructuring
- `examples_v2/14_modules/main.sr` - local modules and pub
- `examples_v2/15_async_and_await.sr` - async and await
- `examples_v2/16_comptime_basics.sr` - comptime blocks
- `examples_v2/17_code_blocks.sr` - code and insert (experimental)
- `examples_v2/18_attributes.sr` - attributes on items
- `examples_v2/19_asm.sr` - asm functions (advanced)
- `examples_v2/20_mlir.sr` - mlir blocks (advanced)
- `examples_v2/21_reflection_and_any.sr` - any, type_of, basic reflection
- `examples_v2/22_special_types.sr` - simd, tensor, noreturn
- `examples_v2/23_operators.sr` - arithmetic, logical, bitwise, wrapping/saturating
- `examples_v2/24_extern_and_ffi.sr` - extern declarations and FFI

Notes:
- Some advanced chapters are experimental and may depend on backend support.
- The old `examples/` directory remains unchanged.
