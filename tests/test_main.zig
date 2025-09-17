const std = @import("std");

test "all" {
    _ = @import("lexer.zig");
    _ = @import("parser.zig");
    _ = @import("lower_v2.zig");
    _ = @import("checker.zig");
}
