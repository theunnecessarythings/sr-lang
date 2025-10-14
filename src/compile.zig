const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const cst = @import("cst.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const ImportResolver = @import("import_resolver.zig").ImportResolver;
const TypeInfo = @import("types.zig").TypeInfo;
const TypeStore = @import("types.zig").TypeStore;

var g_passes_registered: bool = false;

pub const SourceManager = struct {
    gpa: std.mem.Allocator,
    files: std.ArrayList([]const u8) = .empty,

    pub fn deinit(self: *SourceManager) void {
        for (self.files.items) |file_path| {
            self.gpa.free(file_path);
        }
        self.files.deinit(self.gpa);
    }

    pub fn add(self: *SourceManager, file_path: []const u8) !u32 {
        try self.files.append(self.gpa, try self.gpa.dupe(u8, file_path));
        return @intCast(self.files.items.len - 1);
    }

    pub fn read(self: *SourceManager, index: u32) ![]const u8 {
        const file_path = self.get(index) orelse return error.FileNotFound;
        var file = try std.fs.cwd().openFile(file_path, .{});
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
            return self.files.items[index];
        }
        return null;
    }
};

pub const Context = struct {
    gpa: std.mem.Allocator,
    source_manager: *SourceManager,
    diags: *Diagnostics,
    interner: *cst.StringInterner,
    resolver: ImportResolver,
    type_store: TypeStore,

    pub fn init(gpa: std.mem.Allocator) Context {
        const interner = gpa.create(cst.StringInterner) catch unreachable;
        interner.* = cst.StringInterner.init(gpa);
        const diags = gpa.create(Diagnostics) catch unreachable;
        diags.* = Diagnostics.init(gpa);
        const source_manager = gpa.create(SourceManager) catch unreachable;
        source_manager.* = SourceManager{ .gpa = gpa };
        return .{
            .diags = diags,
            .interner = interner,
            .gpa = gpa,
            .source_manager = source_manager,
            .resolver = ImportResolver.init(gpa),
            .type_store = TypeStore.init(gpa, interner),
        };
    }

    pub fn deinit(self: *Context) void {
        self.source_manager.deinit();
        self.diags.deinit();
        self.interner.deinit();
        self.type_store.deinit();
        self.resolver.deinit();
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
    result = mlir.c.mlirPassManagerRunOnOp(pm, module.getOperation().handle);

    if (mlir.c.mlirLogicalResultIsFailure(result)) {
        std.debug.print("Pass manager failed\n", .{});
        module.getOperation().dump();
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

    const objectFileName = "zig-out/output.o";
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
    try args.append(allocator, "zig-out/output_program");
    try args.append(allocator, "zig-out/output.o");
    // Link the language runtime (static)
    try args.append(allocator, "zig-out/lib/libsr_runtime.a");
    // Append user-provided link args (e.g., -L/usr/local/lib, -lraylib)
    for (link_args) |la| try args.append(allocator, la);

    var child = std.process.Child.init(args.items, allocator);
    child.spawn() catch unreachable;
    _ = child.wait() catch unreachable;
}

pub fn run() void {
    const argv = &[_][]const u8{"zig-out/output_program"};
    var child = std.process.Child.init(argv, std.heap.page_allocator);
    child.spawn() catch unreachable;
    _ = child.wait() catch unreachable;
}
