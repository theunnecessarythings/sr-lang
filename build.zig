const std = @import("std");

const use_llvm = false;

fn linkMLIR(LLVM_HOME: []const u8, exe: *std.Build.Step.Compile) !void {
    const dir = try std.fs.cwd().openDir(LLVM_HOME, .{ .iterate = true });
    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const name = entry.name;
        if (std.mem.eql(u8, name, "libMLIRFuncMeshShardingExtensions.a")) continue;
        if (std.mem.eql(u8, name, "libllvm_gtest_main.a")) continue;
        if (std.mem.eql(u8, name, "libbenchmark_main.a")) continue;
        if (std.mem.eql(u8, name, "libMLIRMlirOptMain.a")) continue;
        if (std.mem.startsWith(u8, name, "lib") and std.mem.endsWith(u8, name, ".a")) {
            const libname = name[3 .. name.len - 2];
            exe.root_module.linkSystemLibrary(libname, .{ .preferred_link_mode = .static });
        }
    }
    exe.linkSystemLibrary("pthread");
    exe.linkSystemLibrary("dl");
    exe.linkSystemLibrary("m");
    exe.linkSystemLibrary("z");
    exe.linkSystemLibrary("zstd");
    exe.linkLibCpp();
    exe.linkLibC();
}

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const mod = b.addModule("compiler", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });

    const exe = b.addExecutable(.{
        .name = "sr_lang",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "compiler", .module = mod },
            },
        }),
    });
    exe.use_llvm = use_llvm;

    const LLVM_HOME_S = "/usr/local/lib";
    linkMLIR(LLVM_HOME_S, exe) catch |err| {
        std.debug.print("Error linking MLIR: {}\n", .{err});
        @panic("Failed to link MLIR");
    };

    // Build and install the runtime library (C ABI exports for generated programs)
    const runtime_lib = b.addLibrary(.{
        .name = "sr_runtime",
        .root_module = b.createModule(.{
            .root_source_file = b.path("runtime/runtime.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    runtime_lib.root_module.link_libc = true;
    b.installArtifact(runtime_lib);

    b.installArtifact(exe);

    const run_step = b.step("run", "Run the app");
    const run_cmd = b.addRunArtifact(exe);
    run_step.dependOn(&run_cmd.step);

    run_cmd.step.dependOn(b.getInstallStep());
    // Ensure runtime library is built/installed before running compiler (which links against it)
    run_cmd.step.dependOn(&runtime_lib.step);

    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const mod_tests = b.addTest(.{
        .root_module = mod,
    });
    const run_mod_tests = b.addRunArtifact(mod_tests);

    const exe_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/test_main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "compiler", .module = mod },
            },
        }),
    });
    exe_tests.use_llvm = use_llvm;
    linkMLIR(LLVM_HOME_S, exe_tests) catch |err| {
        std.debug.print("Error linking MLIR for tests: {}\n", .{err});
        @panic("Failed to link MLIR for tests");
    };

    const run_exe_tests = b.addRunArtifact(exe_tests);
    b.installArtifact(exe_tests);

    const test_step = b.step("test", "Run tests");
    test_step.dependOn(&run_mod_tests.step);
    test_step.dependOn(&run_exe_tests.step);

    const fuzz_lib = b.addLibrary(.{
        .name = "fuzzer",
        .use_llvm = use_llvm,
        .root_module = b.createModule(.{
            .root_source_file = b.path("tests/fuzzer.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "compiler", .module = mod },
            },
        }),
    });
    linkMLIR(LLVM_HOME_S, fuzz_lib) catch |err| {
        std.debug.print("Error linking MLIR for fuzzer: {}\n", .{err});
        @panic("Failed to link MLIR for fuzzer");
    };
    fuzz_lib.root_module.stack_check = false;
    const fuzz_step = b.step("fuzz", "Build the fuzzer");
    fuzz_step.dependOn(&fuzz_lib.step);
    b.installArtifact(fuzz_lib);
}
