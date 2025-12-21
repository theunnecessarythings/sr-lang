const std = @import("std");

const alloc = std.testing.allocator;

pub var link_lib: []const u8 = "-lm";

pub fn runBehaviorTests() !void {
    // remove old output
    _ = std.fs.cwd().deleteFile("out/output_program") catch {};

    const compile_result = try std.process.Child.run(.{
        .allocator = alloc,
        .argv = &.{ "zig-out/bin/sr_lang", "test", "tests/behavior.sr", link_lib },
        .max_output_bytes = 16 * 1024 * 1024,
    });
    defer alloc.free(compile_result.stdout);
    defer alloc.free(compile_result.stderr);
    switch (compile_result.term) {
        .Exited => |code| {
            if (code != 0) {
                std.debug.print("Compiler stdout:\n{s}\n", .{compile_result.stdout});
                std.debug.print("Compiler stderr:\n{s}\n", .{compile_result.stderr});
                return error.CompilationFailed;
            }
        },
        else => {
            std.debug.print("Compiler stdout:\n{s}\n", .{compile_result.stdout});
            std.debug.print("Compiler stderr:\n{s}\n", .{compile_result.stderr});
            return error.ProcessFailed;
        },
    }

    // check output program exists
    _ = std.fs.cwd().statFile("out/output_program") catch |err| {
        std.debug.print("Error: {}\n", .{err});
        return error.CompilationFailed;
    };
    const run_result = try std.process.Child.run(.{
        .allocator = alloc,
        .argv = &.{"out/output_program"},
        .max_output_bytes = 16 * 1024 * 1024,
    });
    defer alloc.free(run_result.stdout);
    defer alloc.free(run_result.stderr);
    switch (run_result.term) {
        .Exited => |code| {
            if (code != 0) {
                std.debug.print("Compiler stdout:\n{s}\n", .{run_result.stdout});
                std.debug.print("Compiler stderr:\n{s}\n", .{run_result.stderr});
                return error.CompilationFailed;
            }
        },
        else => {
            std.debug.print("Compiler stdout:\n{s}\n", .{run_result.stdout});
            std.debug.print("Compiler stderr:\n{s}\n", .{run_result.stderr});
            return error.ProcessFailed;
        },
    }
}

fn runCrashTest(source_path: []const u8) !void {
    const result = try std.process.Child.run(.{
        .allocator = alloc,
        .argv = &.{ "zig-out/bin/sr_lang", "test", source_path, link_lib },
        .max_output_bytes = 16 * 1024 * 1024,
    });
    defer alloc.free(result.stdout);
    defer alloc.free(result.stderr);

    switch (result.term) {
        .Exited => |code| {
            if (code == 0) {
                std.debug.print("Expected crash for {s}, but it passed!\n", .{source_path});
                std.debug.print("Stdout:\n{s}\n", .{result.stdout});
                std.debug.print("Stderr:\n{s}\n", .{result.stderr});
                return error.TestShouldHaveCrashed;
            }
        },
        else => {}, // Signals etc. count as crashes
    }
}

test "behavior tests" {
    try runBehaviorTests();
}

test "crash tests" {
    try runCrashTest("tests/crash_optional_unwrap.sr");
}

test "all" {
    _ = @import("formatter.zig");
    _ = @import("lexer.zig");
    _ = @import("parser.zig");
    _ = @import("checker.zig");
    _ = @import("mlir_codegen.zig");
    // _ = @import("tir.zig");
    _ = @import("types.zig");
}
