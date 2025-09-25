const std = @import("std");

test "all" {
    _ = @import("lexer.zig");
    _ = @import("parser.zig");
    _ = @import("checker.zig");
    _ = @import("mlir_codegen.zig");
    _ = @import("tir.zig");
}
