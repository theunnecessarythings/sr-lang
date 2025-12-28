const std = @import("std");
const ast = @import("ast.zig");
const cst = @import("cst.zig");
const tir = @import("tir.zig");
const package = @import("package.zig");
const CompilationUnit = package.CompilationUnit;
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const TypeInfo = @import("types.zig").TypeInfo;
const TypeStore = @import("types.zig").TypeStore;
const Parser = @import("parser.zig").Parser;
const mlir = @import("mlir_bindings.zig");

/// Tracks whether MLIR passes have already been registered globally.
var g_passes_registered: bool = false;

/// Manages file paths, cached contents, and virtual overrides used across compilation.
pub const SourceManager = struct {
    gpa: std.mem.Allocator,
    files: std.ArrayList(Entry) = .empty,
    /// Maps file path string to index for O(1) lookup.
    lookup_cache: std.StringHashMap(u32),

    const Entry = struct {
        path: []u8,
        virtual_source: ?[]u8 = null,
    };

    pub fn init(gpa: std.mem.Allocator) SourceManager {
        return .{
            .gpa = gpa,
            .lookup_cache = std.StringHashMap(u32).init(gpa),
        };
    }

    pub fn deinit(self: *SourceManager) void {
        for (self.files.items) |*entry| {
            self.gpa.free(entry.path);
            if (entry.virtual_source) |src| self.gpa.free(src);
        }
        self.files.deinit(self.gpa);
        self.lookup_cache.deinit();
    }

    /// Register `file_path` and return its managed index (avoids duplicates).
    pub fn add(self: *SourceManager, file_path: []const u8) !u32 {
        if (self.lookup_cache.get(file_path)) |idx| return idx;

        const copy = try self.gpa.dupe(u8, file_path);
        errdefer self.gpa.free(copy);

        const idx: u32 = @intCast(self.files.items.len);
        try self.files.append(self.gpa, .{ .path = copy });
        try self.lookup_cache.put(copy, idx);
        return idx;
    }

    pub fn find(self: *SourceManager, file_path: []const u8) ?u32 {
        return self.lookup_cache.get(file_path);
    }

    pub fn read(self: *SourceManager, index: u32) ![]const u8 {
        if (index >= self.files.items.len) return error.FileNotFound;
        const entry = self.files.items[index];
        if (entry.virtual_source) |src| return try self.gpa.dupe(u8, src);

        var file = std.fs.cwd().openFile(entry.path, .{}) catch |err| {
            std.debug.print("error opening: {s}\n", .{entry.path});
            return err;
        };
        defer file.close();

        const size = try file.getEndPos();
        const buffer = try self.gpa.alloc(u8, size);
        errdefer self.gpa.free(buffer);

        if (try file.readAll(buffer) != size) return error.FileReadError;
        return buffer;
    }

    pub fn get(self: *const SourceManager, index: u32) ?[]const u8 {
        if (index < self.files.items.len) return self.files.items[index].path;
        return null;
    }

    pub fn setVirtualSource(self: *SourceManager, index: u32, contents: []const u8) !void {
        if (index >= self.files.items.len) return error.FileNotFound;
        var entry = &self.files.items[index];
        if (entry.virtual_source) |src| self.gpa.free(src);
        entry.virtual_source = try self.gpa.dupe(u8, contents);
    }

    pub fn setVirtualSourceByPath(self: *SourceManager, file_path: []const u8, contents: []const u8) !u32 {
        const idx = try self.add(file_path);
        try self.setVirtualSource(idx, contents);
        return idx;
    }

    pub fn clearVirtualSource(self: *SourceManager, index: u32) void {
        if (index >= self.files.items.len) return;
        var entry = &self.files.items[index];
        if (entry.virtual_source) |src| {
            self.gpa.free(src);
            entry.virtual_source = null;
        }
    }
};

/// Resolves a raw import string into an absolute path on disk.
pub fn resolveImportPath(allocator: std.mem.Allocator, source_manager: *SourceManager, current_file_id: u32, import_name: []const u8) ![]const u8 {
    const current_file_path = source_manager.get(current_file_id) orelse return error.FileNotFound;
    const current_dir = std.fs.path.dirname(current_file_path) orelse ".";
    const ext = if (std.fs.path.extension(import_name).len == 0) ".sr" else "";
    const filename = try std.fmt.allocPrint(allocator, "{s}{s}", .{ import_name, ext });
    defer allocator.free(filename);

    const paths_to_try = [_][]const u8{
        current_dir,
        try std.fs.path.join(allocator, &.{ current_dir, "imports" }),
        try std.fs.path.join(allocator, &.{ try std.fs.selfExeDirPathAlloc(allocator), ".." }),
    };
    defer {
        allocator.free(paths_to_try[1]);
        allocator.free(paths_to_try[2]); // exe_dir path join result
    }

    for (paths_to_try) |base| {
        const joined = try std.fs.path.join(allocator, &.{ base, filename });
        defer allocator.free(joined);
        if (std.fs.cwd().access(joined, .{})) |_| {
            return std.fs.realpathAlloc(allocator, joined);
        } else |err| {
            if (err != error.FileNotFound) return err;
        }
    }
    return error.ImportNotFound;
}

pub const Context = struct {
    gpa: std.mem.Allocator,
    source_manager: *SourceManager,
    diags: *Diagnostics,
    interner: *cst.StringInterner,
    loc_store: *cst.LocStore,
    type_store: *TypeStore,
    compilation_unit: CompilationUnit,
    global_func_map: std.AutoHashMap(tir.StrId, struct { tir.FuncId, *tir.FuncStore }),
    load_imports: bool = true,
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
        const type_store = gpa.create(TypeStore) catch unreachable;
        type_store.* = TypeStore.init(gpa, interner);
        const diags = gpa.create(Diagnostics) catch unreachable;
        diags.* = Diagnostics.init(gpa, type_store, interner);
        const sm = gpa.create(SourceManager) catch unreachable;
        sm.* = SourceManager.init(gpa);
        const loc_store = gpa.create(cst.LocStore) catch unreachable;
        loc_store.* = cst.LocStore{};

        return .{
            .diags = diags,
            .interner = interner,
            .loc_store = loc_store,
            .gpa = gpa,
            .source_manager = sm,
            .type_store = type_store,
            .compilation_unit = .init(gpa),
            .global_func_map = .init(gpa),
        };
    }

    pub fn deinit(self: *Context) void {
        self.compilation_unit.deinit();
        self.global_func_map.deinit();
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
        for (self.levels.items) |*l| l.deinit(self.allocator);
        self.levels.deinit(self.allocator);
    }
};

/// Helper struct for graph algorithms
const GraphData = struct {
    indegree: std.AutoHashMap(u32, usize),
    adjacency: std.AutoHashMap(u32, std.ArrayList(u32)),
    all_nodes: std.AutoHashMap(u32, void),

    fn deinit(self: *GraphData, allocator: std.mem.Allocator) void {
        self.indegree.deinit();
        var it = self.adjacency.iterator();
        while (it.next()) |kv| kv.value_ptr.deinit(allocator);
        self.adjacency.deinit();
        self.all_nodes.deinit();
    }
};

fn buildAdjacencyGraph(allocator: std.mem.Allocator, unit: *CompilationUnit, interner: *cst.StringInterner, sm: *SourceManager) !GraphData {
    var data = GraphData{
        .indegree = .init(allocator),
        .adjacency = .init(allocator),
        .all_nodes = .init(allocator),
    };

    // Register all nodes first
    var pkg_iter = unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var src_iter = pkg.value_ptr.sources.iterator();
        while (src_iter.next()) |e| {
            const fid = e.value_ptr.file_id;
            try data.all_nodes.put(fid, {});
            if (!data.indegree.contains(fid)) try data.indegree.put(fid, 0);
        }
    }

    // Build edges
    var dep_iter = unit.dependencies.iterator();
    while (dep_iter.next()) |e| {
        const fid = e.key_ptr.*;
        if (!data.indegree.contains(fid)) try data.indegree.put(fid, 0);
        try data.all_nodes.put(fid, {});

        var set_iter = e.value_ptr.iterator();
        while (set_iter.next()) |dep| {
            const dep_fid = sm.find(interner.get(dep.key_ptr.*)) orelse continue;
            if (dep_fid == fid) continue;

            const d_deg = try data.indegree.getOrPutValue(dep_fid, 0);
            _ = d_deg; // unused, just ensuring existence
            if (!data.all_nodes.contains(dep_fid)) try data.all_nodes.put(dep_fid, {});

            // Add edge: dep_fid -> fid (dep must be processed before fid)
            // Note: Indegree is count of dependencies needed by 'fid', so we increment fid's indegree
            // and add fid to dep_fid's adjacency list.

            // Correction: Standard dep graph: A imports B. B must be compiled before A.
            // Edge: B -> A.
            // B's adjacency list contains A.
            // A's indegree increments.

            const tgt_deg = data.indegree.getPtr(fid).?;
            tgt_deg.* += 1;

            const adj = try data.adjacency.getOrPut(dep_fid);
            if (!adj.found_existing) adj.value_ptr.* = .empty;
            try adj.value_ptr.append(allocator, fid);
        }
    }
    return data;
}

pub fn computeDependencyLevels(allocator: std.mem.Allocator, unit: *CompilationUnit, interner: *cst.StringInterner, sm: *SourceManager) !DependencyLevels {
    var graph = try buildAdjacencyGraph(allocator, unit, interner, sm);
    defer graph.deinit(allocator);

    var res = DependencyLevels.init(allocator);
    errdefer res.deinit();

    var queue = std.ArrayList(u32){};
    defer queue.deinit(allocator);
    var next_queue = std.ArrayList(u32){};
    defer next_queue.deinit(allocator);

    // Kahn's Algorithm
    var it = graph.indegree.iterator();
    while (it.next()) |e| {
        if (e.value_ptr.* == 0) try queue.append(allocator, e.key_ptr.*);
    }

    var processed_count: usize = 0;

    while (queue.items.len > 0) {
        var level = std.ArrayList(u32){};
        try level.appendSlice(allocator, queue.items);
        try res.levels.append(allocator, level);
        processed_count += queue.items.len;

        for (queue.items) |u| {
            if (graph.adjacency.getPtr(u)) |vs| {
                for (vs.items) |v| {
                    const deg = graph.indegree.getPtr(v).?;
                    deg.* -= 1;
                    if (deg.* == 0) try next_queue.append(allocator, v);
                }
            }
        }
        queue.clearRetainingCapacity();
        std.mem.swap(std.ArrayList(u32), &queue, &next_queue);
    }

    // Nodes in cycles are leftover
    if (processed_count < graph.all_nodes.count()) {
        var cycle_level = std.ArrayList(u32){};
        var nit = graph.all_nodes.iterator();
        while (nit.next()) |e| {
            if (graph.indegree.get(e.key_ptr.*).? > 0) try cycle_level.append(allocator, e.key_ptr.*);
        }
        if (cycle_level.items.len > 0) try res.levels.append(allocator, cycle_level);
    }

    return res;
}

pub const CycleReport = struct {
    allocator: std.mem.Allocator,
    cycles: std.ArrayList(std.ArrayList(u32)),
    blocked: std.ArrayList(u32),

    pub fn init(allocator: std.mem.Allocator) CycleReport {
        return .{ .allocator = allocator, .cycles = .{}, .blocked = .{} };
    }
    pub fn deinit(self: *CycleReport) void {
        for (self.cycles.items) |*c| c.deinit(self.allocator);
        self.cycles.deinit(self.allocator);
        self.blocked.deinit(self.allocator);
    }
};

pub fn detectImportCycles(allocator: std.mem.Allocator, unit: *CompilationUnit, interner: *cst.StringInterner, sm: *SourceManager) !CycleReport {
    var graph = try buildAdjacencyGraph(allocator, unit, interner, sm);
    defer graph.deinit(allocator);
    var report = CycleReport.init(allocator);
    errdefer report.deinit();

    // Re-run Kahn's partially to strip acyclic nodes
    var queue = std.ArrayList(u32){};
    defer queue.deinit(allocator);
    var it = graph.indegree.iterator();
    while (it.next()) |e| if (e.value_ptr.* == 0) try queue.append(allocator, e.key_ptr.*);

    while (queue.items.len > 0) {
        const u = queue.pop().?;
        _ = graph.all_nodes.remove(u); // Remove from 'remaining' set
        if (graph.adjacency.getPtr(u)) |vs| {
            for (vs.items) |v| {
                const deg = graph.indegree.getPtr(v).?;
                deg.* -= 1;
                if (deg.* == 0) try queue.append(allocator, v);
            }
        }
    }

    if (graph.all_nodes.count() == 0) return report;

    // DFS for cycles on remaining subgraph
    var visited = std.AutoHashMap(u32, bool).init(allocator);
    defer visited.deinit();
    var onstack = std.AutoHashMap(u32, bool).init(allocator);
    defer onstack.deinit();
    var stack = std.ArrayList(u32){};
    defer stack.deinit(allocator);
    var in_cycle = std.AutoHashMap(u32, void).init(allocator);
    defer in_cycle.deinit();

    // Recursive closure for DFS
    const DfsCtx = struct {
        g: *GraphData,
        r: *CycleReport,
        v: *std.AutoHashMap(u32, bool),
        os: *std.AutoHashMap(u32, bool),
        st: *std.ArrayList(u32),
        ic: *std.AutoHashMap(u32, void),
        alloc: std.mem.Allocator,

        fn run(ctx: @This(), u: u32) !void {
            try ctx.v.put(u, true);
            try ctx.os.put(u, true);
            try ctx.st.append(ctx.alloc, u);

            if (ctx.g.adjacency.getPtr(u)) |vs| {
                for (vs.items) |v| {
                    if (!ctx.g.all_nodes.contains(v)) continue;
                    if (!ctx.v.contains(v)) {
                        try ctx.run(v);
                    } else if (ctx.os.contains(v)) {
                        // Cycle found
                        var cyc = std.ArrayList(u32){};
                        var idx: usize = 0;
                        while (idx < ctx.st.items.len and ctx.st.items[idx] != v) : (idx += 1) {}
                        if (idx < ctx.st.items.len) {
                            try cyc.appendSlice(ctx.alloc, ctx.st.items[idx..]);
                            try cyc.append(ctx.alloc, ctx.st.items[idx]); // Close loop
                            for (cyc.items) |n| try ctx.ic.put(n, {});
                            try ctx.r.cycles.append(ctx.alloc, cyc);
                        } else {
                            cyc.deinit(ctx.alloc);
                        }
                    }
                }
            }
            _ = ctx.os.remove(u);
            _ = ctx.st.pop();
        }
    };

    var nit = graph.all_nodes.iterator();
    while (nit.next()) |e| {
        if (!visited.contains(e.key_ptr.*)) {
            try DfsCtx.run(.{ .g = &graph, .r = &report, .v = &visited, .os = &onstack, .st = &stack, .ic = &in_cycle, .alloc = allocator }, e.key_ptr.*);
        }
    }

    // Populate blocked
    nit = graph.all_nodes.iterator();
    while (nit.next()) |e| {
        if (!in_cycle.contains(e.key_ptr.*)) try report.blocked.append(allocator, e.key_ptr.*);
    }

    return report;
}

pub fn initMLIR(alloc: std.mem.Allocator) mlir.Context {
    mlir.setGlobalAlloc(alloc);
    var ctx = mlir.Context.create();
    const reg = mlir.DialectRegistry.create();
    mlir.registerAllDialects(reg);
    if (!g_passes_registered) {
        mlir.registerAllPasses();
        g_passes_registered = true;
    }
    mlir.registerAllLLVMTranslations(ctx);
    ctx.appendDialectRegistry(reg);
    ctx.loadAllAvailableDialects();
    ctx.setAllowUnregisteredDialects(true);
    return ctx;
}

pub fn run_passes(context: *mlir.Context, module: *mlir.Module) !void {
    const pm = mlir.c.mlirPassManagerCreate(context.handle);
    defer mlir.c.mlirPassManagerDestroy(pm);

    // Canonicalization pipeline
    const pipeline = "canonicalize,cse,symbol-dce,empty-tensor-to-alloc-tensor,convert-elementwise-to-linalg,one-shot-bufferize{bufferize-function-boundaries=true allow-unknown-ops=true},canonicalize,cse,async-to-async-runtime,async-runtime-ref-counting,async-runtime-ref-counting-opt,convert-bufferization-to-memref,convert-linalg-to-loops,loop-invariant-code-motion,lower-affine,convert-vector-to-llvm,convert-scf-to-cf,arith-expand,convert-math-to-llvm,expand-strided-metadata,fold-memref-alias-ops,finalize-memref-to-llvm,convert-async-to-llvm,convert-complex-to-llvm,convert-arith-to-llvm,convert-func-to-llvm,convert-cf-to-llvm,reconcile-unrealized-casts,llvm-legalize-for-export";

    const op_pm = mlir.c.mlirPassManagerGetAsOpPassManager(pm);
    const pipe_str = mlir.c.mlirStringRefCreateFromCString(@ptrCast(pipeline));
    if (mlir.c.mlirLogicalResultIsFailure(mlir.c.mlirOpPassManagerAddPipeline(op_pm, pipe_str, callback, null))) {
        return error.PassPipelineCreationFailed;
    }

    if (mlir.c.mlirLogicalResultIsFailure(mlir.c.mlirPassManagerRunOnOp(pm, module.getOperation().handle))) {
        module.getOperation().clone().dump();
        return error.PassManagerFailed;
    }
}

fn callback(msg: mlir.c.MlirStringRef, _: ?*anyopaque) callconv(.c) void {
    std.debug.print("{s}", .{std.mem.sliceAsBytes(msg.data[0..msg.length])});
}

pub fn runJit(module: mlir.c.MlirModule) void {
    _ = mlir.c.LLVMInitializeNativeTarget();
    _ = mlir.c.LLVMInitializeNativeAsmPrinter();
    const eng = mlir.c.mlirExecutionEngineCreate(module, 3, 0, null, false);
    if (mlir.c.mlirExecutionEngineIsNull(eng)) {
        std.debug.print("JIT Engine creation failed\n", .{});
        return;
    }
    if (mlir.c.mlirLogicalResultIsFailure(mlir.c.mlirExecutionEngineInvokePacked(eng, mlir.c.mlirStringRefCreateFromCString("main"), null))) {
        std.debug.print("JIT invoke main failed\n", .{});
    }
}

pub const Mode = enum { llvm_ir, llvm_passes, compile };

pub fn convert_to_llvm_ir(module: mlir.c.MlirModule, link_args: []const []const u8, mode: Mode, opt_lvl: ?[]const u8, debug: bool) !void {
    _ = mlir.c.LLVMInitializeNativeTarget();
    _ = mlir.c.LLVMInitializeNativeAsmPrinter();
    _ = mlir.c.LLVMInitializeNativeAsmParser();

    const ctx = mlir.c.LLVMContextCreate();
    defer mlir.c.LLVMContextDispose(ctx);
    const ir = mlir.c.mlirTranslateModuleToLLVMIR(mlir.c.mlirModuleGetOperation(module), ctx);
    if (ir == null) return error.CompilationFailed;

    if (mode != .compile) mlir.c.LLVMDumpModule(ir);
    if (mode == .llvm_ir) return;

    var target: mlir.c.LLVMTargetRef = undefined;
    var err: [*c]u8 = undefined;
    const triple = mlir.c.LLVMGetDefaultTargetTriple();
    if (mlir.c.LLVMGetTargetFromTriple(triple, &target, &err) != 0) {
        std.debug.print("Target Error: {s}\n", .{err});
        mlir.c.LLVMDisposeMessage(err);
        return error.TargetNotFound;
    }

    const tm = mlir.c.LLVMCreateTargetMachine(target, triple, "", "", mlir.c.LLVMCodeGenLevelNone, mlir.c.LLVMRelocPIC, mlir.c.LLVMCodeModelDefault);
    defer mlir.c.LLVMDisposeTargetMachine(tm);

    const builder_opts = mlir.c.LLVMCreatePassBuilderOptions();
    defer mlir.c.LLVMDisposePassBuilderOptions(builder_opts);

    var pass_buf: [32]u8 = undefined;
    const passes = try std.fmt.bufPrintZ(&pass_buf, "default<O{s}>", .{opt_lvl orelse "0"});

    if (mlir.c.LLVMRunPasses(ir, passes, tm, builder_opts) != null) return error.PassManagerFailed;
    if (mode != .compile) mlir.c.LLVMDumpModule(ir);
    if (mode == .llvm_passes) return;

    std.fs.cwd().makeDir("out") catch |e| if (e != error.PathAlreadyExists) return e;
    if (mlir.c.LLVMPrintModuleToFile(ir, "out/output.ll", &err) != 0) {
        std.debug.print("Emit Error: {s}\n", .{err});
        mlir.c.LLVMDisposeMessage(err);
        return error.ObjectFileEmissionFailed;
    }

    // Link
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var cmd = std.ArrayList([]const u8){};
    try cmd.appendSlice(alloc, &[_][]const u8{ "clang", try std.fmt.allocPrint(alloc, "-O{s}", .{opt_lvl orelse "0"}), "-w" });
    if (debug) try cmd.append(alloc, "-g");
    try cmd.appendSlice(alloc, &[_][]const u8{ "-o", "out/output_program", "out/output.ll" });

    const exe_dir = try std.fs.selfExeDirPathAlloc(alloc);
    const rt_path = try std.fs.path.join(alloc, &.{ exe_dir[0 .. exe_dir.len - 4], "lib/libsr_runtime.a" });
    try cmd.append(alloc, rt_path);
    try cmd.appendSlice(alloc, &[_][]const u8{ "-Wl,-rpath,./out", "-Lout" });

    var op = mlir.Operation{ .handle = mlir.c.mlirModuleGetOperation(module) };
    if (!op.getDiscardableAttributeByName(mlir.StringRef.from("sr.has_async")).isNull()) {
        try cmd.appendSlice(alloc, &[_][]const u8{ "-L/usr/local/lib", "-Wl,-rpath,/usr/local/lib", "-lmlir_async_runtime" });
    }
    try cmd.appendSlice(alloc, link_args);

    var child = std.process.Child.init(cmd.items, alloc);
    const term = child.spawnAndWait() catch return error.LinkFailed;
    if (term != .Exited or term.Exited != 0) return error.LinkFailed;
}

pub fn runWithStatus() !u8 {
    var child = std.process.Child.init(&[_][]const u8{"out/output_program"}, std.heap.page_allocator);
    const term = try child.spawnAndWait();
    return switch (term) {
        .Exited => |c| @intCast(c),
        else => error.ProgramFailed,
    };
}

pub fn run() void {
    _ = runWithStatus() catch {};
}
