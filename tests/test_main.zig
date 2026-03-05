const std = @import("std");

const alloc = std.testing.allocator;

pub var link_lib: []const u8 = "-lm";

pub fn runBehaviorTests() !void {
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

fn runCommandExpectSuccess(argv: []const []const u8) !std.process.Child.RunResult {
    const result = try std.process.Child.run(.{
        .allocator = alloc,
        .argv = argv,
        .max_output_bytes = 16 * 1024 * 1024,
    });
    errdefer {
        alloc.free(result.stdout);
        alloc.free(result.stderr);
    }

    switch (result.term) {
        .Exited => |code| {
            if (code != 0) {
                std.debug.print("Command failed: ", .{});
                for (argv) |arg| std.debug.print("{s} ", .{arg});
                std.debug.print("\nStdout:\n{s}\nStderr:\n{s}\n", .{ result.stdout, result.stderr });
                return error.CommandFailed;
            }
        },
        else => {
            std.debug.print("Command crashed: ", .{});
            for (argv) |arg| std.debug.print("{s} ", .{arg});
            std.debug.print("\nStdout:\n{s}\nStderr:\n{s}\n", .{ result.stdout, result.stderr });
            return error.CommandCrashed;
        },
    }
    return result;
}

test "behavior tests" {
    try runBehaviorTests();
}

test "crash tests" {
    try runCrashTest("tests/crash_optional_unwrap.sr");
}

test "sr-libc MVP regressions" {
    // bare export_name identifier form must typecheck
    {
        const r = try runCommandExpectSuccess(&.{ "zig-out/bin/sr_lang", "check", "tests/sr_libc/export_name_attr.sr" });
        defer alloc.free(r.stdout);
        defer alloc.free(r.stderr);
    }

    // and must lower to renamed symbol in LLVM IR
    {
        const r = try runCommandExpectSuccess(&.{ "zig-out/bin/sr_lang", "llvm-ir", "tests/sr_libc/export_name_attr.sr" });
        defer alloc.free(r.stdout);
        defer alloc.free(r.stderr);
        const has_my_add =
            std.mem.indexOf(u8, r.stdout, "@my_add") != null or
            std.mem.indexOf(u8, r.stderr, "@my_add") != null;
        try std.testing.expect(has_my_add);
    }

    // plain main wrapper under --sr-libc must compile/run (std/io path)
    {
        const r = try runCommandExpectSuccess(&.{ "zig-out/bin/sr_lang", "run", "tests/sr_libc/plain_main_std_io.sr", "--sr-libc" });
        defer alloc.free(r.stdout);
        defer alloc.free(r.stderr);
        try std.testing.expect(std.mem.indexOf(u8, r.stdout, "std io plain main\n") != null);
    }

    // argc/argv main under --sr-libc must still compile/run
    {
        const r = try runCommandExpectSuccess(&.{ "zig-out/bin/sr_lang", "run", "tests/sr_libc/argc_main_syscall.sr", "--sr-libc" });
        defer alloc.free(r.stdout);
        defer alloc.free(r.stderr);
        try std.testing.expect(std.mem.indexOf(u8, r.stdout, "argc-main sr-libc\n") != null);
    }
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
