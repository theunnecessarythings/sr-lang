const std = @import("std");

const use_llvm = true;

const skipped_libs = std.StaticStringMap(void).initComptime(.{
    .{"MLIRFuncMeshShardingExtensions"}, .{"llvm_gtest_main"},
    .{"benchmark_main"},                 .{"MLIRMlirOptMain"},
});

fn linkMLIR(LLVM_HOME: []const u8, exe: *std.Build.Step.Compile) !void {
    const dir = try std.fs.cwd().openDir(LLVM_HOME, .{ .iterate = true });
    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        const name = entry.name;
        if (std.mem.startsWith(u8, name, "lib") and std.mem.endsWith(u8, name, ".a")) {
            const libname = name[3 .. name.len - 2];
            if (skipped_libs.get(libname)) |_| continue;
            exe.root_module.linkSystemLibrary(libname, .{ .preferred_link_mode = .static });
        }
    }
    // Ensure runtime can locate the shared libs
    exe.addRPath(.{ .cwd_relative = LLVM_HOME });

    exe.linkSystemLibrary("pthread");
    exe.linkSystemLibrary("dl");
    exe.linkSystemLibrary("m");
    exe.linkSystemLibrary("z");
    exe.linkSystemLibrary("zstd");

    // Force Link to libstdc++
    exe.addObjectFile(.{
        .cwd_relative = "/usr/lib/libstdc++.so.6",
    });

    // If we want to force link it to libc++ abi instead
    // exe.addIncludePath(.{ .cwd_relative = "/usr/include/c++/v1" });
    // exe.addObjectFile(.{ .cwd_relative = "/usr/lib/libc++.so" });
    // exe.addObjectFile(.{ .cwd_relative = "/usr/lib/libc++abi.so" });

    exe.linkSystemLibrary("libunwind");
    exe.linkSystemLibrary("gcc_s");
    exe.linkLibC();
}

fn linkTriton(exe: *std.Build.Step.Compile) !void {
    exe.addObjectFile(.{ .cwd_relative = "/home/sreeraj/Documents/triton/python/triton/_C/libtriton_mlir_plugin.so" });
    exe.addRPath(.{ .cwd_relative = "/home/sreeraj/Documents/triton/python/triton/_C" });
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
        .name = if (optimize != .Debug) "src" else "sr_lang",
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
    const exe_check = b.addExecutable(.{
        .name = "check",
        .root_module = exe.root_module,
    });
    const check = b.step("check", "Check if foo compiles");
    check.dependOn(&exe_check.step);

    // copy std lib and vendor libs to install dir
    var std_lib = std.fs.cwd().openDir("std", .{ .iterate = true }) catch unreachable;
    var iter = std_lib.iterate();
    std.fs.makeDirAbsolute(b.install_path) catch {};
    var install_dir = std.fs.openDirAbsolute(b.install_path, .{}) catch unreachable;
    defer install_dir.close();
    install_dir.makeDir("std") catch |err| switch (err) {
        error.PathAlreadyExists => {},
        else => unreachable,
    };
    install_dir.makeDir("vendor") catch |err| switch (err) {
        error.PathAlreadyExists => {},
        else => unreachable,
    };
    const root_src = std.fs.cwd().realpathAlloc(b.allocator, ".") catch unreachable;
    while (iter.next() catch null) |entry| {
        if (entry.kind != .file) continue;
        const dest = b.pathJoin(&.{ b.install_path, "std", entry.name });
        const src = b.pathJoin(&.{ root_src, "std", entry.name });
        std.fs.copyFileAbsolute(src, dest, .{}) catch unreachable;
    }
    var vendor_lib = std.fs.cwd().openDir("vendor", .{ .iterate = true }) catch unreachable;
    iter = vendor_lib.iterate();
    while (iter.next() catch null) |entry| {
        if (entry.kind != .file) continue;
        const dest = b.pathJoin(&.{ b.install_path, "vendor", entry.name });
        const src = b.pathJoin(&.{ root_src, "vendor", entry.name });
        std.fs.copyFileAbsolute(src, dest, .{}) catch unreachable;
    }

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
    const test_filters = b.option([]const []const u8, "test-filter", "Skip tests that do not match any filter") orelse &[0][]const u8{};
    const exe_tests = b.addTest(.{
        .root_module = b.createModule(
            .{
                .root_source_file = b.path("tests/test_main.zig"),
                .target = target,
                .optimize = optimize,
                .imports = &.{
                    .{ .name = "compiler", .module = mod },
                },
            },
        ),
        .filters = test_filters,
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
