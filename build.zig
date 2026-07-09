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
        const b = exe.step.owner;
        var cwd = std.Io.Dir.cwd();
        var dir = try cwd.openDir(b.graph.io, llvm_scan_dir, .{ .iterate = true });
        defer dir.close(b.graph.io);
        var iter = std.Io.Dir.iterate(dir);
        while (try iter.next(b.graph.io)) |entry| {
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
        exe.root_module.addRPath(.{ .cwd_relative = llvm_link_dir });
    }
    // Ensure linker searches the LLVM/MLIR lib dir
    exe.root_module.addLibraryPath(.{ .cwd_relative = llvm_link_dir });
    exe.root_module.addIncludePath(.{ .cwd_relative = "/usr/local/include" });

    if (!is_wasm) {
        exe.root_module.linkSystemLibrary("pthread", .{});
        exe.root_module.linkSystemLibrary("dl", .{});
    }
    if (!is_wasm) {
        exe.root_module.linkSystemLibrary("m", .{});
    }

    if (!is_wasm) {
        exe.root_module.linkSystemLibrary("z", .{});
        exe.root_module.linkSystemLibrary("zstd", .{});

        // Force Link to libstdc++
        exe.root_module.addObjectFile(.{
            .cwd_relative = "/usr/lib/libstdc++.so.6",
        });

        // If we want to force link it to libc++ abi instead
        // exe.root_module.addIncludePath(.{ .cwd_relative = "/usr/include/c++/v1" });
        // exe.root_module.addObjectFile(.{ .cwd_relative = "/usr/lib/libc++.so" });
        // exe.root_module.addObjectFile(.{ .cwd_relative = "/usr/lib/libc++abi.so" });

        exe.root_module.linkSystemLibrary("libunwind", .{});
        exe.root_module.linkSystemLibrary("gcc_s", .{});
    }
    if (!is_wasm or is_wasi) {
        exe.root_module.link_libc = true;
    }
}

fn linkTriton(exe: *std.Build.Step.Compile) !void {
    exe.root_module.addObjectFile(.{ .cwd_relative = "/home/sreeraj/Documents/triton/python/triton/_C/libtriton_mlir_plugin.so" });
    exe.root_module.addRPath(.{ .cwd_relative = "/home/sreeraj/Documents/triton/python/triton/_C" });
}

fn copyTree(io: std.Io, allocator: std.mem.Allocator, src_root: []const u8, dst_root: []const u8) !void {
    var cwd = std.Io.Dir.cwd();
    var src_dir = try cwd.openDir(io, src_root, .{ .iterate = true });
    defer src_dir.close(io);

    var walker = try src_dir.walk(allocator);
    defer walker.deinit();

    while (try walker.next(io)) |entry| {
        const rel = entry.path;
        const dst_path = try std.fs.path.join(allocator, &.{ dst_root, rel });
        defer allocator.free(dst_path);

        switch (entry.kind) {
            .directory => {
                cwd.createDirPath(io, dst_path) catch |err| switch (err) {
                    error.PathAlreadyExists => {},
                    else => return err,
                };
            },
            .file => {
                if (std.fs.path.dirname(dst_path)) |parent| {
                    cwd.createDirPath(io, parent) catch |err| switch (err) {
                        error.PathAlreadyExists => {},
                        else => return err,
                    };
                }
                try src_dir.copyFile(rel, cwd, dst_path, io, .{});
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
        b.graph.environ_map.get("LLVM_HOME_S") orelse
        "/usr/local/lib";
    const LLVM_LINK_DIR_S =
        b.option([]const u8, "llvm_link_dir", "Path to LLVM/MLIR lib directory for linking") orelse LLVM_HOME_S;
    linkMLIR(LLVM_HOME_S, LLVM_LINK_DIR_S, exe) catch |err| {
        std.debug.print("Error linking MLIR: {}\n", .{err});
        @panic("Failed to link MLIR");
    };

    // Build and install the runtime object (C ABI exports for generated programs)
    const runtime_obj = b.addObject(.{
        .name = "libsr_runtime",
        .root_module = b.createModule(.{
            .root_source_file = b.path("runtime/runtime.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    runtime_obj.root_module.link_libc = !is_wasm or is_wasi;
    if (is_wasm) runtime_obj.root_module.linkSystemLibrary("c", .{});
    b.getInstallStep().dependOn(&b.addInstallFile(runtime_obj.getEmittedBin(), "lib/libsr_runtime.o").step);

    // Triton runtime object (CUDA launch + caching), only linked for Triton programs
    const triton_runtime_obj = b.addObject(.{
        .name = "libsr_triton_runtime",
        .root_module = b.createModule(.{
            .root_source_file = b.path("runtime/triton_runtime.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    triton_runtime_obj.root_module.link_libc = !is_wasm or is_wasi;
    if (is_wasm) triton_runtime_obj.root_module.linkSystemLibrary("c", .{});
    b.getInstallStep().dependOn(&b.addInstallFile(triton_runtime_obj.getEmittedBin(), "lib/libsr_triton_runtime.o").step);

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
    var cwd = std.Io.Dir.cwd();
    const io = b.graph.io;

    var std_lib = cwd.openDir(io, "std", .{ .iterate = true }) catch unreachable;
    defer std_lib.close(io);

    cwd.createDirPath(io, b.install_path) catch {};
    var install_dir = cwd.openDir(io, b.install_path, .{}) catch unreachable;
    defer install_dir.close(io);

    install_dir.createDirPath(io, "std") catch {};
    install_dir.createDirPath(io, "std/web") catch {};
    install_dir.createDirPath(io, "vendor") catch {};

    const root_src = b.build_root.path.?;

    // Copy std/web files
    {
        var std_web_lib = cwd.openDir(io, "std/web", .{ .iterate = true }) catch unreachable;
        defer std_web_lib.close(io);
        var web_iter = std.Io.Dir.iterate(std_web_lib);
        while (web_iter.next(io) catch null) |entry| {
            if (entry.kind != .file) continue;
            const dest = b.pathJoin(&.{ b.install_path, "std", "web", entry.name });
            const src = b.pathJoin(&.{ root_src, "std", "web", entry.name });
            cwd.copyFile(src, cwd, dest, io, .{}) catch unreachable;
        }
    }

    var iter = std.Io.Dir.iterate(std_lib);
    while (iter.next(io) catch null) |entry| {
        if (entry.kind != .file) continue;
        const dest = b.pathJoin(&.{ b.install_path, "std", entry.name });
        const src = if (is_wasm and std.mem.eql(u8, entry.name, "io.sr"))
            b.pathJoin(&.{ root_src, "std", "io_wasm.sr" })
        else
            b.pathJoin(&.{ root_src, "std", entry.name });
        cwd.copyFile(src, cwd, dest, io, .{}) catch unreachable;
    }

    var vendor_lib = cwd.openDir(io, "vendor", .{ .iterate = true }) catch unreachable;
    defer vendor_lib.close(io);
    var vendor_iter = std.Io.Dir.iterate(vendor_lib);
    while (vendor_iter.next(io) catch null) |entry| {
        if (entry.kind != .file) continue;
        const dest = b.pathJoin(&.{ b.install_path, "vendor", entry.name });
        const src = b.pathJoin(&.{ root_src, "vendor", entry.name });
        cwd.copyFile(src, cwd, dest, io, .{}) catch unreachable;
    }

    install_dir.createDirPath(io, "libc") catch {};
    const libc_src = b.pathJoin(&.{ root_src, "sr-libc" });
    const libc_dst = b.pathJoin(&.{ b.install_path, "libc" });
    copyTree(io, b.allocator, libc_src, libc_dst) catch unreachable;

    if (!is_wasm) {
        const run_step = b.step("run", "Run the app");
        const run_cmd = b.addRunArtifact(exe);
        run_step.dependOn(&run_cmd.step);

        run_cmd.step.dependOn(b.getInstallStep());
        // Ensure runtime libraries are built/installed before running compiler (which links against them)
        run_cmd.step.dependOn(&runtime_obj.step);
        run_cmd.step.dependOn(&triton_runtime_obj.step);

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
        var dir = cwd.openDir(io, LLVM_HOME_S, .{ .iterate = true }) catch unreachable;
        defer dir.close(io);
        var iter_mlir = std.Io.Dir.iterate(dir);
        while (iter_mlir.next(io) catch null) |entry| {
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
