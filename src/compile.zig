const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const cst = @import("cst.zig");
const package = @import("package.zig");
const CompilationUnit = package.CompilationUnit;
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const TypeInfo = @import("types.zig").TypeInfo;
const TypeStore = @import("types.zig").TypeStore;
const Parser = @import("parser.zig").Parser;

var g_passes_registered: bool = false;

pub const SourceManager = struct {
    gpa: std.mem.Allocator,
    files: std.ArrayList(Entry) = .empty,

    const Entry = struct {
        path: []u8,
        virtual_source: ?[]u8 = null,
    };

    pub fn deinit(self: *SourceManager) void {
        for (self.files.items) |*entry| {
            self.gpa.free(entry.path);
            if (entry.virtual_source) |src| {
                self.gpa.free(src);
            }
        }
        self.files.deinit(self.gpa);
    }

    pub fn add(self: *SourceManager, file_path: []const u8) !u32 {
        if (self.findIndex(file_path)) |idx| {
            return @intCast(idx);
        }
        const copy = try self.gpa.dupe(u8, file_path);
        errdefer self.gpa.free(copy);
        try self.files.append(self.gpa, .{ .path = copy });
        return @intCast(self.files.items.len - 1);
    }

    pub fn find(self: *SourceManager, file_path: []const u8) ?u32 {
        const idx = self.findIndex(file_path) orelse return null;
        return @intCast(idx);
    }

    pub fn read(self: *SourceManager, index: u32) ![]const u8 {
        if (index >= self.files.items.len) return error.FileNotFound;
        const entry = self.files.items[index];
        if (entry.virtual_source) |src| {
            return try self.gpa.dupe(u8, src);
        }
        var file = std.fs.cwd().openFile(entry.path, .{}) catch |err| {
            std.debug.print("error: {s}\n", .{entry.path});
            return err;
        };

        defer file.close();
        const file_size = try file.getEndPos();
        const buffer = try self.gpa.alloc(u8, file_size);
        const read_bytes = try file.readAll(buffer);
        if (read_bytes != file_size) {
            self.gpa.free(buffer);
            return error.FileReadError;
        }
        return buffer;
    }

    pub fn get(self: *const SourceManager, index: u32) ?[]const u8 {
        if (index < self.files.items.len) {
            return self.files.items[index].path;
        }
        return null;
    }

    pub fn setVirtualSource(self: *SourceManager, index: u32, contents: []const u8) !void {
        if (index >= self.files.items.len) return error.FileNotFound;
        var entry = &self.files.items[index];
        if (entry.virtual_source) |src| {
            self.gpa.free(src);
        }
        entry.virtual_source = try self.gpa.dupe(u8, contents);
    }

    pub fn clearVirtualSource(self: *SourceManager, index: u32) void {
        if (index >= self.files.items.len) return;
        var entry = &self.files.items[index];
        if (entry.virtual_source) |src| {
            self.gpa.free(src);
            entry.virtual_source = null;
        }
    }

    pub fn setVirtualSourceByPath(self: *SourceManager, file_path: []const u8, contents: []const u8) !u32 {
        const idx = try self.add(file_path);
        try self.setVirtualSource(idx, contents);
        return idx;
    }

    fn findIndex(self: *SourceManager, file_path: []const u8) ?usize {
        for (self.files.items, 0..) |entry, idx| {
            if (std.mem.eql(u8, entry.path, file_path)) {
                return idx;
            }
        }
        return null;
    }
};

pub const Context = struct {
    gpa: std.mem.Allocator,
    source_manager: *SourceManager,
    diags: *Diagnostics,
    interner: *cst.StringInterner,
    loc_store: *cst.LocStore,
    type_store: *TypeStore,
    compilation_unit: CompilationUnit,
    mutex: std.Thread.Mutex = .{},

    parse_worklist: std.ArrayList(ParseRequest) = .{},

    const ParseRequest = struct {
        path: []const u8,
        file_id: u32,
        thread: std.Thread,
        diags: *Diagnostics,
        parser: *Parser,
    };

    pub fn init(gpa: std.mem.Allocator) Context {
        const interner = gpa.create(cst.StringInterner) catch unreachable;
        interner.* = cst.StringInterner.init(gpa);
        const diags = gpa.create(Diagnostics) catch unreachable;
        diags.* = Diagnostics.init(gpa);
        const source_manager = gpa.create(SourceManager) catch unreachable;
        source_manager.* = SourceManager{ .gpa = gpa };
        const loc_store = gpa.create(cst.LocStore) catch unreachable;
        loc_store.* = cst.LocStore{};
        const type_store = gpa.create(TypeStore) catch unreachable;
        type_store.* = TypeStore.init(gpa, interner);
        return .{
            .diags = diags,
            .interner = interner,
            .loc_store = loc_store,
            .gpa = gpa,
            .source_manager = source_manager,
            .type_store = type_store,
            .compilation_unit = CompilationUnit.init(gpa),
        };
    }

    pub fn deinit(self: *Context) void {
        self.compilation_unit.deinit();
        self.source_manager.deinit();
        self.diags.deinit();
        self.interner.deinit();
        self.loc_store.deinit(self.gpa);
        self.type_store.deinit();
        self.gpa.destroy(self.interner);
        self.gpa.destroy(self.diags);
        self.gpa.destroy(self.source_manager);
        self.gpa.destroy(self.loc_store);
        self.gpa.destroy(self.type_store);
    }
};

pub const DependencyLevels = struct {
    allocator: std.mem.Allocator,
    levels: std.ArrayList(std.ArrayList(u32)),

    pub fn init(allocator: std.mem.Allocator) DependencyLevels {
        return .{ .allocator = allocator, .levels = .{} };
    }

    pub fn deinit(self: *DependencyLevels) void {
        for (self.levels.items) |*level| {
            level.deinit(self.allocator);
        }
        self.levels.deinit(self.allocator);
    }
};

pub fn computeDependencyLevels(
    allocator: std.mem.Allocator,
    unit: *CompilationUnit,
    interner: *cst.StringInterner,
    source_manager: *SourceManager,
) !DependencyLevels {
    var result = DependencyLevels.init(allocator);
    errdefer result.deinit();

    var indegree = std.AutoHashMap(u32, usize).init(allocator);
    defer indegree.deinit();

    var adjacency = std.AutoHashMap(u32, std.ArrayList(u32)).init(allocator);
    defer {
        var adj_iter = adjacency.iterator();
        while (adj_iter.next()) |entry| {
            entry.value_ptr.deinit(allocator);
        }
        adjacency.deinit();
    }

    var ordered_nodes = std.ArrayList(u32){};
    defer ordered_nodes.deinit(allocator);

    var remaining = std.AutoHashMap(u32, void).init(allocator);
    defer remaining.deinit();

    var pkg_iter = unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var source_iter = pkg.value_ptr.sources.iterator();
        while (source_iter.next()) |entry| {
            const file_id = entry.value_ptr.file_id;
            if (indegree.getPtr(file_id) == null) {
                try indegree.put(file_id, 0);
            }
            if (!remaining.contains(file_id)) {
                try remaining.put(file_id, {});
                try ordered_nodes.append(allocator, file_id);
            }
        }
    }

    var dep_iter = unit.dependencies.iterator();
    while (dep_iter.next()) |entry| {
        const file_id = entry.key_ptr.*;
        if (indegree.getPtr(file_id) == null) {
            try indegree.put(file_id, 0);
        }
        if (!remaining.contains(file_id)) {
            try remaining.put(file_id, {});
            try ordered_nodes.append(allocator, file_id);
        }

        var set_iter = entry.value_ptr.iterator();
        while (set_iter.next()) |dep_entry| {
            const dep_str = interner.get(dep_entry.key_ptr.*);
            const dep_file_id = source_manager.find(dep_str) orelse continue;
            if (dep_file_id == file_id) continue;

            const indegree_ptr = indegree.getPtr(file_id) orelse blk: {
                try indegree.put(file_id, 0);
                break :blk indegree.getPtr(file_id).?;
            };
            indegree_ptr.* += 1;

            var adj_ptr = adjacency.getPtr(dep_file_id) orelse blk: {
                const list = std.ArrayList(u32){};
                try adjacency.put(dep_file_id, list);
                break :blk adjacency.getPtr(dep_file_id).?;
            };
            try adj_ptr.append(allocator, file_id);

            if (indegree.getPtr(dep_file_id) == null) {
                try indegree.put(dep_file_id, 0);
            }
            if (!remaining.contains(dep_file_id)) {
                try remaining.put(dep_file_id, {});
                try ordered_nodes.append(allocator, dep_file_id);
            }
        }
    }

    var queue = std.ArrayList(u32){};
    defer queue.deinit(allocator);
    var next_queue = std.ArrayList(u32){};
    defer next_queue.deinit(allocator);

    var indegree_iter = indegree.iterator();
    while (indegree_iter.next()) |entry| {
        if (entry.value_ptr.* == 0) {
            try queue.append(allocator, entry.key_ptr.*);
        }
    }

    while (queue.items.len > 0) {
        var level = std.ArrayList(u32){};
        try level.appendSlice(allocator, queue.items);
        for (queue.items) |node| {
            _ = remaining.remove(node);
        }
        try result.levels.append(allocator, level);

        next_queue.clearRetainingCapacity();
        for (queue.items) |node| {
            if (adjacency.getPtr(node)) |neighbors| {
                for (neighbors.items) |neighbor| {
                    const indegree_ptr = indegree.getPtr(neighbor) orelse continue;
                    if (indegree_ptr.* == 0) continue;
                    indegree_ptr.* -= 1;
                    if (indegree_ptr.* == 0) {
                        try next_queue.append(allocator, neighbor);
                    }
                }
            }
        }

        queue.clearRetainingCapacity();
        std.mem.swap(std.ArrayList(u32), &queue, &next_queue);
    }

    if (remaining.count() > 0) {
        var cycle_level = std.ArrayList(u32){};
        for (ordered_nodes.items) |node| {
            if (remaining.contains(node)) {
                _ = remaining.remove(node);
                try cycle_level.append(allocator, node);
            }
        }
        if (cycle_level.items.len > 0) {
            try result.levels.append(allocator, cycle_level);
        } else {
            cycle_level.deinit(allocator);
        }
    }

    return result;
}

pub fn initMLIR(alloc: std.mem.Allocator) mlir.Context {
    mlir.setGlobalAlloc(alloc);
    var mlir_context = mlir.Context.create();
    const registry = mlir.DialectRegistry.create();
    mlir.registerAllDialects(registry);
    if (!g_passes_registered) {
        mlir.registerAllPasses();
        g_passes_registered = true;
    }
    mlir.registerAllLLVMTranslations(mlir_context);

    mlir_context.appendDialectRegistry(registry);
    mlir_context.loadAllAvailableDialects();
    return mlir_context;
}

pub fn run_passes(context: *mlir.Context, module: *mlir.Module) !void {
    const pm = mlir.c.mlirPassManagerCreate(context.handle);
    defer mlir.c.mlirPassManagerDestroy(pm);
    const pipeline =
        "canonicalize,cse," ++
        "empty-tensor-to-alloc-tensor," ++
        "convert-elementwise-to-linalg," ++
        "one-shot-bufferize{bufferize-function-boundaries=true allow-unknown-ops=true}," ++
        // "lift-cf-to-scf," ++
        // "buffer-deallocation-pipeline," ++
        "canonicalize,cse," ++
        "convert-bufferization-to-memref," ++
        "convert-linalg-to-loops," ++
        "loop-invariant-code-motion," ++
        "lower-affine," ++
        "convert-vector-to-llvm," ++

        // Control flow & math
        "convert-scf-to-cf," ++
        "arith-expand," ++ //                  # (if wide-int/index/mulhs etc. show up)
        "convert-math-to-llvm," ++ //          # (if math dialect is present)

        "expand-strided-metadata," ++
        "fold-memref-alias-ops," ++

        // To LLVM
        "finalize-memref-to-llvm," ++
        "convert-complex-to-llvm," ++
        "convert-arith-to-llvm," ++
        "convert-func-to-llvm," ++
        "convert-cf-to-llvm," ++
        // "convert-ub-to-llvm," ++
        "reconcile-unrealized-casts," ++
        "llvm-legalize-for-export";
    const op_pm = mlir.c.mlirPassManagerGetAsOpPassManager(pm);
    var result = mlir.c.mlirOpPassManagerAddPipeline(op_pm, mlir.c.mlirStringRefCreateFromCString(@ptrCast(pipeline)), callback, null);

    if (mlir.c.mlirLogicalResultIsFailure(result)) {
        std.debug.print("Failed to create pass pipeline\n", .{});
        return error.PassPipelineCreationFailed;
    }

    // Run the pass manager on the module
    const c_module = module.getOperation().clone();
    result = mlir.c.mlirPassManagerRunOnOp(pm, module.getOperation().handle);

    if (mlir.c.mlirLogicalResultIsFailure(result)) {
        std.debug.print("Pass manager failed\n", .{});
        c_module.dump();
        return error.PassManagerFailed;
    }
}

fn callback(msg: mlir.c.MlirStringRef, data: ?*anyopaque) callconv(.c) void {
    const message = std.mem.sliceAsBytes(msg.data[0..msg.length]);
    std.debug.print("{s}", .{message});
    _ = data;
}

pub fn runJit(module: mlir.c.MlirModule) void {
    _ = mlir.c.LLVMInitializeNativeTarget();
    _ = mlir.c.LLVMInitializeNativeAsmPrinter();

    const engine = mlir.c.mlirExecutionEngineCreate(module, 3, 0, null, false);
    if (mlir.c.mlirExecutionEngineIsNull(engine)) {
        std.debug.print("Failed to create execution engine\n", .{});
        return;
    }

    const result = mlir.c.mlirExecutionEngineInvokePacked(engine, mlir.c.mlirStringRefCreateFromCString("main"), null);
    if (mlir.c.mlirLogicalResultIsFailure(result)) {
        std.debug.print("Failed to invoke main function\n", .{});
        return;
    }
}

const Mode = enum {
    llvm_ir,
    llvm_passes,
    compile,
};

pub fn convert_to_llvm_ir(module: mlir.c.MlirModule, print_ir: bool, link_args: []const []const u8, mode: Mode) !void {
    _ = mlir.c.LLVMInitializeNativeTarget();
    _ = mlir.c.LLVMInitializeNativeAsmPrinter();
    _ = mlir.c.LLVMInitializeNativeAsmParser();

    const llvmContext = mlir.c.LLVMContextCreate();
    const llvmIR = mlir.c.mlirTranslateModuleToLLVMIR(mlir.c.mlirModuleGetOperation(module), llvmContext);
    if (llvmIR == null) return error.CompilationFailed;

    if (print_ir)
        mlir.c.LLVMDumpModule(llvmIR);
    if (mode == .llvm_ir) return;

    const targetTriple = mlir.c.LLVMGetDefaultTargetTriple();
    const features = "";
    const cpu = "";

    // Get target from triple BEFORE creating target machine
    var target: mlir.c.LLVMTargetRef = undefined;
    var err: [*c]u8 = undefined;
    if (mlir.c.LLVMGetTargetFromTriple(targetTriple[0..], &target, &err) != 0) {
        std.debug.print("Error finding target: {s}\n", .{err});
        mlir.c.LLVMDisposeMessage(err);
        return error.TargetNotFound;
    }

    const targetMachine = mlir.c.LLVMCreateTargetMachine(target, targetTriple, cpu, features, mlir.c.LLVMCodeGenLevelNone, mlir.c.LLVMRelocPIC, mlir.c.LLVMCodeModelDefault);

    defer {
        mlir.c.LLVMDisposeTargetMachine(targetMachine);
        mlir.c.LLVMContextDispose(llvmContext);
    }
    // Create the pass manager
    const pass_manager = mlir.c.LLVMCreatePassManager();
    defer mlir.c.LLVMDisposePassManager(pass_manager);
    // Set up the pass builder options
    const passBuilderOptions = mlir.c.LLVMCreatePassBuilderOptions();
    defer mlir.c.LLVMDisposePassBuilderOptions(passBuilderOptions);

    // Run the default O2 optimization pipeline
    const passes = "default<O0>";
    const pass_err = mlir.c.LLVMRunPasses(llvmIR, passes, targetMachine, passBuilderOptions);
    _ = pass_err;
    _ = mlir.c.LLVMRunPassManager(pass_manager, llvmIR);
    if (mlir.c.LLVMGetTargetFromTriple(mlir.c.LLVMGetDefaultTargetTriple(), &target, &err) != 0) {
        std.debug.print("Error finding target: {s}\n", .{err});
        mlir.c.LLVMDisposeMessage(err);
        return error.TargetNotFound;
    }
    if (print_ir) {
        std.debug.print("Optimized LLVM IR:\n", .{});
        mlir.c.LLVMDumpModule(llvmIR);
    }
    if (mode == .llvm_passes) return;

    // make output dir
    if (std.fs.cwd().access("out", .{})) |_| {} else |_| try std.fs.cwd().makeDir("out");

    const objectFileName = "out/output.o";
    if (mlir.c.LLVMTargetMachineEmitToFile(targetMachine, llvmIR, objectFileName, mlir.c.LLVMObjectFile, &err) != 0) {
        std.debug.print("Error emitting object file: {s}\n", .{err});
        mlir.c.LLVMDisposeMessage(err);
        return error.ObjectFileEmissionFailed;
    }

    // Link object file and run executable
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var args: std.ArrayList([]const u8) = .empty;
    defer args.deinit(allocator);
    try args.append(allocator, "clang");
    try args.append(allocator, "-O0");
    try args.append(allocator, "-g");
    try args.append(allocator, "-o");
    try args.append(allocator, "out/output_program");
    try args.append(allocator, "out/output.o");
    // Link the language runtime (static)
    const exe_path = try std.fs.selfExeDirPathAlloc(allocator);
    defer allocator.free(exe_path);
    const runtime_path = try std.fs.path.join(
        allocator,
        &.{ exe_path[0 .. exe_path.len - 4], "lib/libsr_runtime.a" },
    );
    defer allocator.free(runtime_path);
    try args.append(allocator, runtime_path);
    // Ensure local out dir is searched at link and runtime for shared libs
    try args.append(allocator, "-Wl,-rpath,./out");
    try args.append(allocator, "-Lout");

    // Append user-provided link args (e.g., -L/usr/local/lib, -lraylib, ./out/mylib.so)
    for (link_args) |la| {
        try args.append(allocator, la);
    }

    var child = std.process.Child.init(args.items, allocator);
    child.spawn() catch {
        return error.LinkFailed;
    };
    const term = child.wait() catch {
        return error.LinkFailed;
    };
    switch (term) {
        .Exited => |code| {
            if (code != 0) {
                return error.LinkFailed;
            }
        },
        else => return error.LinkFailed,
    }
}

pub fn run() void {
    const argv = &[_][]const u8{"out/output_program"};
    var child = std.process.Child.init(argv, std.heap.page_allocator);
    child.spawn() catch unreachable;
    _ = child.wait() catch unreachable;
}
