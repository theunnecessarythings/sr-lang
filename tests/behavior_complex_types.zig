const std = @import("std");
const behavior = @import("behavior.zig");

const getSource = behavior.getSource;
const runCompilerTest = behavior.runCompilerTest;

test "special_types: basic complex literal" {
    const src =
        \\z := 1.0 + 2.0i
        \\printf("Complex: %f + %fi\n", z.real, z.imag)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Complex: 1.000000 + 2.000000i\n");
}

test "special_types: complex addition" {
    const src =
        \\z1 := 1.0 + 2.0i
        \\z2 := 3.0 + 4.0i
        \\sum := z1 + z2
        \\printf("Sum: %f + %fi\n", sum.real, sum.imag)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Sum: 4.000000 + 6.000000i\n");
}

test "special_types: complex multiplication" {
    const src =
        \\z1 := 1.0 + 2.0i
        \\z2 := 3.0 + 4.0i
        \\prod := z1 * z2
        \\printf("Product: %f + %fi\n", prod.real, prod.imag)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Product: -5.000000 + 10.000000i\n");
}

test "special_types: complex with mixed float" {
    const src =
        \\z := 1.0 + 2.0i
        \\r := z + 5.0
        \\printf("Mixed sum: %f + %fi\n", r.real, r.imag)
    ;
    const code = getSource("", src);
    try runCompilerTest(code, "Mixed sum: 6.000000 + 2.000000i\n");
}
