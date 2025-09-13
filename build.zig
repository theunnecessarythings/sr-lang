const std = @import("std");

fn linkMLIR(b: *std.Build, exe: *std.Build.Step.Compile) !void {
    _ = b;
    const MLIR_SRC = "/home/sreeraj/ubuntu/Documents/llvm-project"; // source tree
    const MLIR_BUILD = "/home/sreeraj/ubuntu/Documents/llvm-project/build"; // build tree
    const MLIR_LIB = MLIR_BUILD ++ "/lib";

    // Headers for mlir-c
    exe.root_module.addIncludePath(.{ .cwd_relative = MLIR_SRC ++ "/mlir/include" });
    exe.root_module.addIncludePath(.{ .cwd_relative = MLIR_BUILD ++ "/tools/mlir/include" });
    // Some LLVM headers needed transitively by C API
    exe.root_module.addIncludePath(.{ .cwd_relative = MLIR_SRC ++ "/llvm/include" });
    exe.root_module.addIncludePath(.{ .cwd_relative = MLIR_BUILD ++ "/include" });

    // Library search path
    exe.addLibraryPath(.{ .cwd_relative = MLIR_LIB });

    const PATH = "/home/sreeraj/ubuntu/Documents/llvm-project/build/lib/";
    const dir = try std.fs.cwd().openDir(PATH, .{ .iterate = true });
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

    exe.addRPath(.{ .cwd_relative = MLIR_LIB });
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
    mod.addIncludePath(b.path("grammar/"));

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
    exe.use_llvm = true;
    linkMLIR(b, exe) catch |err| {
        std.debug.print("Error linking MLIR: {}\n", .{err});
        @panic("Failed to link MLIR");
    };

    b.installArtifact(exe);

    const run_step = b.step("run", "Run the app");
    const run_cmd = b.addRunArtifact(exe);
    run_step.dependOn(&run_cmd.step);

    run_cmd.step.dependOn(b.getInstallStep());

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
    exe_tests.use_llvm = true;

    const run_exe_tests = b.addRunArtifact(exe_tests);
    b.installArtifact(exe_tests);

    const test_step = b.step("test", "Run tests");
    test_step.dependOn(&run_mod_tests.step);
    test_step.dependOn(&run_exe_tests.step);
}
