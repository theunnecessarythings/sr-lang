const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const cst = @import("cst.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const ModuleGraph = @import("module_graph.zig").ModuleGraph;
const TypeInfo = @import("types.zig").TypeInfo;
const TypeStore = @import("types.zig").TypeStore;

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

    pub fn read(self: *SourceManager, index: u32) ![]const u8 {
        if (index >= self.files.items.len) return error.FileNotFound;
        const entry = self.files.items[index];
        if (entry.virtual_source) |src| {
            return try self.gpa.dupe(u8, src);
        }
        var file = try std.fs.cwd().openFile(entry.path, .{});
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
    module_graph: ModuleGraph,
    type_store: TypeStore,

    pub fn init(gpa: std.mem.Allocator) Context {
        const interner = gpa.create(cst.StringInterner) catch unreachable;
        interner.* = cst.StringInterner.init(gpa);
        const diags = gpa.create(Diagnostics) catch unreachable;
        diags.* = Diagnostics.init(gpa);
        const source_manager = gpa.create(SourceManager) catch unreachable;
        source_manager.* = SourceManager{ .gpa = gpa };
        const loc_store = gpa.create(cst.LocStore) catch unreachable;
        loc_store.* = cst.LocStore{};
        return .{
            .diags = diags,
            .interner = interner,
            .loc_store = loc_store,
            .gpa = gpa,
            .source_manager = source_manager,
            .module_graph = ModuleGraph.init(gpa),
            .type_store = TypeStore.init(gpa, interner),
        };
    }

    pub fn deinit(self: *Context) void {
        self.source_manager.deinit();
        self.diags.deinit();
        self.interner.deinit();
        self.loc_store.deinit(self.gpa);
        self.type_store.deinit();
        self.module_graph.deinit();
        self.gpa.destroy(self.interner);
        self.gpa.destroy(self.diags);
        self.gpa.destroy(self.source_manager);
    }
};

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

    const pipeline = "convert-scf-to-cf,convert-arith-to-llvm,convert-complex-to-llvm,convert-func-to-llvm,convert-cf-to-llvm,inline,canonicalize,cse";
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
    // Append user-provided link args (e.g., -L/usr/local/lib, -lraylib)
    for (link_args) |la| try args.append(allocator, la);

    var child = std.process.Child.init(args.items, allocator);
    child.spawn() catch unreachable;
    _ = child.wait() catch unreachable;
}

pub fn run() void {
    const argv = &[_][]const u8{"out/output_program"};
    var child = std.process.Child.init(argv, std.heap.page_allocator);
    child.spawn() catch unreachable;
    _ = child.wait() catch unreachable;
}
