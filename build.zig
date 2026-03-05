const std = @import("std");

const use_llvm = true;

const skipped_libs = std.StaticStringMap(void).initComptime(.{
    .{"MLIRFuncMeshShardingExtensions"}, .{"llvm_gtest_main"},
    .{"benchmark_main"},                 .{"MLIRMlirOptMain"},
});

fn linkMLIR(llvm_scan_dir: []const u8, llvm_link_dir: []const u8, exe: *std.Build.Step.Compile) !void {
    const target = exe.root_module.resolved_target.?.result;
    const is_wasm = target.cpu.arch.isWasm();
    const is_emscripten = target.os.tag == .emscripten;
    const is_wasi = target.os.tag == .wasi;

    if (!is_emscripten) {
        const dir = try std.fs.cwd().openDir(llvm_scan_dir, .{ .iterate = true });
        var iter = dir.iterate();
        while (try iter.next()) |entry| {
            const name = entry.name;
            if (std.mem.startsWith(u8, name, "lib") and std.mem.endsWith(u8, name, ".a")) {
                const libname = name[3 .. name.len - 2];
                if (skipped_libs.get(libname)) |_| continue;
                exe.root_module.linkSystemLibrary(libname, .{ .preferred_link_mode = .static });
            }
        }
    }
    // Ensure runtime can locate the shared libs
    if (!is_wasm) {
        exe.addRPath(.{ .cwd_relative = llvm_link_dir });
    }
    // Ensure linker searches the LLVM/MLIR lib dir
    exe.addLibraryPath(.{ .cwd_relative = llvm_link_dir });
    exe.addIncludePath(.{ .cwd_relative = "/usr/local/include" });

    if (!is_wasm) {
        exe.linkSystemLibrary("pthread");
        exe.linkSystemLibrary("dl");
    }
    if (!is_wasm) {
        exe.linkSystemLibrary("m");
    }

    if (!is_wasm) {
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
    }
    if (!is_wasm or is_wasi) {
        exe.linkLibC();
    }
}

fn linkTriton(exe: *std.Build.Step.Compile) !void {
    exe.addObjectFile(.{ .cwd_relative = "/home/sreeraj/Documents/triton/python/triton/_C/libtriton_mlir_plugin.so" });
    exe.addRPath(.{ .cwd_relative = "/home/sreeraj/Documents/triton/python/triton/_C" });
}

fn copyTree(allocator: std.mem.Allocator, src_root: []const u8, dst_root: []const u8) !void {
    var src_dir = try std.fs.cwd().openDir(src_root, .{ .iterate = true });
    defer src_dir.close();

    var walker = try src_dir.walk(allocator);
    defer walker.deinit();

    while (try walker.next()) |entry| {
        const rel = entry.path;
        const dst_path = try std.fs.path.join(allocator, &.{ dst_root, rel });
        defer allocator.free(dst_path);

        switch (entry.kind) {
            .directory => {
                std.fs.cwd().makePath(dst_path) catch |err| switch (err) {
                    error.PathAlreadyExists => {},
                    else => return err,
                };
            },
            .file => {
                if (std.fs.path.dirname(dst_path)) |parent| {
                    std.fs.cwd().makePath(parent) catch |err| switch (err) {
                        error.PathAlreadyExists => {},
                        else => return err,
                    };
                }
                const src_path = try std.fs.path.join(allocator, &.{ src_root, rel });
                defer allocator.free(src_path);
                std.fs.copyFileAbsolute(src_path, dst_path, .{}) catch return error.FileReadError;
            },
            else => {},
        }
    }
}

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const is_wasm = target.result.cpu.arch.isWasm();
    const is_emscripten = target.result.os.tag == .emscripten;
    const is_wasi = target.result.os.tag == .wasi;
    const optimize = b.standardOptimizeOption(.{});
    const wasm_browser = b.option(bool, "wasm_browser", "Build wasm for browser using emcc") orelse false;
    const sr_lang_src = b.option([]const u8, "sr_lang_src", "Source root for bundling std/lib into wasm");
    const mod = b.addModule("compiler", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = !is_wasm or is_wasi,
    });

    const exe_root = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "compiler", .module = mod },
        },
    });
    const exe = b.addExecutable(.{
        .name = if (optimize != .Debug) "src" else "sr_lang",
        .root_module = exe_root,
    });
    exe.use_llvm = use_llvm;

    const LLVM_HOME_S =
        b.option([]const u8, "llvm_home", "Path to LLVM/MLIR lib directory") orelse
        (std.process.getEnvVarOwned(b.allocator, "LLVM_HOME_S") catch |err| switch (err) {
            error.EnvironmentVariableNotFound => "/usr/local/lib",
            else => "/usr/local/lib",
        });
    const LLVM_LINK_DIR_S =
        b.option([]const u8, "llvm_link_dir", "Path to LLVM/MLIR lib directory for linking") orelse LLVM_HOME_S;
    linkMLIR(LLVM_HOME_S, LLVM_LINK_DIR_S, exe) catch |err| {
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
    runtime_lib.root_module.link_libc = !is_wasm or is_wasi;
    if (is_wasm) runtime_lib.root_module.linkSystemLibrary("c", .{});
    b.installArtifact(runtime_lib);

    // Triton runtime (CUDA launch + caching), only linked for Triton programs
    const triton_runtime_lib = b.addLibrary(.{
        .name = "sr_triton_runtime",
        .root_module = b.createModule(.{
            .root_source_file = b.path("runtime/triton_runtime.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    triton_runtime_lib.root_module.link_libc = !is_wasm or is_wasi;
    if (is_wasm) triton_runtime_lib.root_module.linkSystemLibrary("c", .{});
    b.installArtifact(triton_runtime_lib);

    if (!is_wasm or is_wasi) {
        b.installArtifact(exe);
    }
    if (!is_wasm) {
        const exe_check = b.addExecutable(.{
            .name = "check",
            .root_module = exe.root_module,
        });
        const check = b.step("check", "Check if foo compiles");
        check.dependOn(&exe_check.step);
    }

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
    install_dir.makeDir("std/web") catch |err| switch (err) {
        error.PathAlreadyExists => {},
        else => unreachable,
    };
    install_dir.makeDir("vendor") catch |err| switch (err) {
        error.PathAlreadyExists => {},
        else => unreachable,
    };
    const root_src = std.fs.cwd().realpathAlloc(b.allocator, ".") catch unreachable;

    // Copy std/web files
    {
        var std_web_lib = std.fs.cwd().openDir("std/web", .{ .iterate = true }) catch unreachable;
        var web_iter = std_web_lib.iterate();
        while (web_iter.next() catch null) |entry| {
            if (entry.kind != .file) continue;
            const dest = b.pathJoin(&.{ b.install_path, "std", "web", entry.name });
            const src = b.pathJoin(&.{ root_src, "std", "web", entry.name });
            std.fs.copyFileAbsolute(src, dest, .{}) catch unreachable;
        }
    }

    while (iter.next() catch null) |entry| {
        if (entry.kind != .file) continue;
        const dest = b.pathJoin(&.{ b.install_path, "std", entry.name });
        const src = if (is_wasm and std.mem.eql(u8, entry.name, "io.sr"))
            b.pathJoin(&.{ root_src, "std", "io_wasm.sr" })
        else
            b.pathJoin(&.{ root_src, "std", entry.name });
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

    install_dir.makeDir("libc") catch |err| switch (err) {
        error.PathAlreadyExists => {},
        else => unreachable,
    };
    const libc_src = b.pathJoin(&.{ root_src, "sr-libc" });
    const libc_dst = b.pathJoin(&.{ b.install_path, "libc" });
    copyTree(b.allocator, libc_src, libc_dst) catch unreachable;

    if (!is_wasm) {
        const run_step = b.step("run", "Run the app");
        const run_cmd = b.addRunArtifact(exe);
        run_step.dependOn(&run_cmd.step);

        run_cmd.step.dependOn(b.getInstallStep());
        // Ensure runtime libraries are built/installed before running compiler (which links against them)
        run_cmd.step.dependOn(&runtime_lib.step);
        run_cmd.step.dependOn(&triton_runtime_lib.step);

        if (b.args) |args| {
            run_cmd.addArgs(args);
        }
    }

    if (!is_wasm) {
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
        linkMLIR(LLVM_HOME_S, LLVM_LINK_DIR_S, exe_tests) catch |err| {
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
        linkMLIR(LLVM_HOME_S, LLVM_LINK_DIR_S, fuzz_lib) catch |err| {
            std.debug.print("Error linking MLIR for fuzzer: {}\n", .{err});
            @panic("Failed to link MLIR for fuzzer");
        };
        fuzz_lib.root_module.stack_check = false;
        const fuzz_step = b.step("fuzz", "Build the fuzzer");
        fuzz_step.dependOn(&fuzz_lib.step);
        b.installArtifact(fuzz_lib);
    }

    if (is_wasm and wasm_browser and is_emscripten) {
        const exe_root_wasm = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "compiler", .module = mod },
            },
            .link_libc = true,
        });
        const exe_obj = b.addObject(.{
            .name = "sr_lang_obj",
            .root_module = exe_root_wasm,
            .use_llvm = use_llvm,
        });
        exe_obj.entry = .disabled;
        const emcc = b.addSystemCommand(&.{"emcc"});
        const out_js = b.pathJoin(&.{ b.install_path, "sr_lang.js" });
        emcc.addArg("-o");
        emcc.addArg(out_js);
        emcc.addFileArg(exe_obj.getEmittedBin());

        // Link all LLVM/MLIR static libs into the wasm module.
        const dir = std.fs.cwd().openDir(LLVM_HOME_S, .{ .iterate = true }) catch unreachable;
        var iter_mlir = dir.iterate();
        while (iter_mlir.next() catch null) |entry| {
            const name = entry.name;
            if (std.mem.startsWith(u8, name, "lib") and std.mem.endsWith(u8, name, ".a")) {
                const libname = name[3 .. name.len - 2];
                if (skipped_libs.get(libname)) |_| continue;
                emcc.addFileArg(.{ .cwd_relative = b.pathJoin(&.{ LLVM_HOME_S, name }) });
            }
        }

        emcc.addArgs(&.{
            "-s", "WASM=1",
            "-s", "ENVIRONMENT=web,worker",
            "-s", "USE_PTHREADS=0",
            "-s", "FORCE_FILESYSTEM=1",
            "-s", "EXPORTED_RUNTIME_METHODS=FS,callMain",
            "-s", "INVOKE_RUN=0",
            "-s", "ASSERTIONS=0",
            "-s", "EXIT_RUNTIME=0",
            "-s", "INITIAL_MEMORY=536870912",
            "-s", "MAXIMUM_MEMORY=1073741824",
            "-s", "STACK_SIZE=8388608",
            "-s", "ALLOW_MEMORY_GROWTH=1",
            "-s", "MODULARIZE=1",
            "-s", "EXPORT_ES6=1",
        });
        if (sr_lang_src) |src_root| {
            emcc.addArg("--preload-file");
            emcc.addArg(b.fmt("{s}/std@/std", .{src_root}));
            emcc.addArg("--preload-file");
            emcc.addArg(b.fmt("{s}/sr-libc@/libc", .{src_root}));
        }

        emcc.step.dependOn(&exe_obj.step);
        b.getInstallStep().dependOn(&emcc.step);
    }
}
