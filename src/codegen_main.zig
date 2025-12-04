const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const compile = @import("compile.zig");
const types = @import("types.zig");
const abi = @import("abi.zig");
const cst = @import("cst.zig");
const comp = @import("comptime.zig");
const cast = @import("codegen_cast.zig");
const debug = @import("codegen_debug.zig");
const package = @import("package.zig");

/// Operation kinds for binary arithmetic lowering helpers.
const BinArithOp = enum {
    /// Addition between SSA values.
    add,
    /// Subtraction between SSA values.
    sub,
    /// Multiplication between SSA values.
    mul,
};
/// Binary bitwise/logical helpers emitted during lowering.
const BinBitOp = enum {
    /// Logical AND operation.
    @"and",
    /// Logical OR operation.
    @"or",
    /// Bitwise XOR operation.
    xor,
};

const Allocator = std.mem.Allocator;
const ArrayList = std.array_list.Managed;

pub var enable_debug_info: bool = false;

/// Recorded line and column numbers computed from a source index.
const LineInfo = struct {
    /// 0-based line number.
    line: usize,
    /// 0-based column offset from start of the line.
    col: usize,
};

/// Thin wrapper used by `mlir.Module.dump` callbacks to capture output as bytes.
pub const PrintBuffer = struct {
    /// Destination byte buffer where MLIR output is appended.
    list: *ArrayList(u8),
    /// Flag set when writing to `list` fails.
    had_error: *bool,
};

/// Callback invoked by MLIR printing helpers to stream characters into a buffer.
pub fn printCallback(str: mlir.c.MlirStringRef, user_data: ?*anyopaque) callconv(.c) void {
    const buf: *PrintBuffer = @ptrCast(@alignCast(user_data));
    const bytes = str.data[0..str.length];
    buf.list.appendSlice(bytes) catch {
        buf.had_error.* = true;
    };
}

fn computeLineIndex(line_starts: []const usize, offset: usize) usize {
    var lo: usize = 0;
    var hi: usize = line_starts.len - 1;
    while (lo < hi) {
        const mid = lo + ((hi - lo + 1) / 2);
        if (line_starts[mid] <= offset) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    return lo;
}

fn computeLineColFallback(src: []const u8, offset: usize) LineInfo {
    var i: usize = 0;
    var line: usize = 0;
    var last_nl: usize = 0;
    while (i < offset) : (i += 1) {
        if (src[i] == '\n') {
            line += 1;
            last_nl = i + 1;
        }
    }
    const col = if (offset >= last_nl) offset - last_nl else 0;
    return .{ .line = line, .col = col };
}

fn ensureLineStarts(self: *Codegen, file_id: u32, src: []const u8) ![]usize {
    if (self.line_index_cache.get(file_id)) |cached| return cached;
    var count: usize = 1;
    for (src) |c| {
        if (c == '\n') count += 1;
    }

    var buf = try self.gpa.alloc(usize, count);
    buf[0] = 0;
    var line_idx: usize = 1;
    var i: usize = 0;
    while (i < src.len) : (i += 1) {
        if (src[i] == '\n') {
            if (line_idx < count) {
                buf[line_idx] = i + 1;
                line_idx += 1;
            }
        }
    }
    try self.line_index_cache.put(file_id, buf);
    return buf;
}

/// Convert a byte index into a `LineInfo` so diagnostics can report (line,col).
fn computeLineCol(self: *Codegen, src: []const u8, index: usize, file_id: u32) LineInfo {
    const limit = if (index > src.len) src.len else index;
    const lines = self.ensureLineStarts(file_id, src) catch return computeLineColFallback(src, limit);
    const line = computeLineIndex(lines, limit);
    const col = limit - lines[line];
    return .{ .line = line, .col = col };
}

/// Primary code generation driver that lowers TIR to MLIR/LLVM IR.
pub const Codegen = @This();

/// Arena allocator driving MLIR metadata/temp storage.
gpa: Allocator,
/// Primary compilation context shared across pipeline phases.
context: *compile.Context,
/// MLIR context containing dialect registrations.
mlir_ctx: mlir.Context,
/// Current source location recorded during lowering.
loc: mlir.Location,
/// MLIR module under construction.
module: mlir.Module,

/// Cached mapping from SR location IDs to MLIR location objects.
loc_cache: std.AutoHashMap(cst.LocId, mlir.Location),
/// Cache for original source files looked up via IDs.
file_cache: std.AutoHashMap(u32, []const u8),
/// Line-start tables per file used to convert offsets to (line,col) faster.
line_index_cache: std.AutoHashMap(u32, []usize),
/// Debug file metadata entries stored per file ID.
di_files: std.AutoHashMap(u32, debug.DebugFileInfo),
/// Cached subprogram metadata keyed by function ID.
di_subprograms: std.AutoHashMap(tir.FuncId, debug.DebugSubprogramInfo),

/// Cached `llvm.null.di.type` attribute used for empty slots.
di_null_type_attr: mlir.Attribute,
/// Cached `llvm.null.di.subroutineType` attribute for optional entries.
di_subroutine_null_type_attr: mlir.Attribute,
/// Cached empty DI expression attribute.
di_empty_expr_attr: mlir.Attribute,
/// DI type cache for SR type IDs.
di_type_cache: std.AutoHashMap(types.TypeId, mlir.Attribute),
/// Counter used when generating unique DI node names.
next_di_id: usize = 0,
/// Whether module-level debug attributes were already emitted.
debug_module_attrs_initialized: bool = false,

// common LLVM/arith types (opaque pointers on master)
/// Void MLIR type reference.
void_ty: mlir.Type,
/// 1-bit boolean type.
i1_ty: mlir.Type,
/// 8-bit integer type.
i8_ty: mlir.Type,
/// 32-bit integer type.
i32_ty: mlir.Type,
/// 64-bit integer type.
i64_ty: mlir.Type,
/// 32-bit float type.
f32_ty: mlir.Type,
/// 64-bit float type.
f64_ty: mlir.Type,
/// Opaque pointer type used for raw pointer casting.
llvm_ptr_ty: mlir.Type, // !llvm.ptr (opaque)

// per-module caches
/// Map from function StrId to emitted MLIR FuncOp info.
func_syms: std.AutoHashMap(tir.StrId, FuncInfo),
/// Global symbol table for functions/globals requiring linker visibility.
global_syms: std.StringHashMap(void),
/// Cache from string literals to the `llvm.mlir.global` operations.
str_pool: std.StringHashMap(mlir.Operation), // text -> llvm.mlir.global op

// per-function state (reset each function)
/// Current MLIR region used for lowering the active function.
cur_region: ?mlir.Region = null,
/// Current block being emitted.
cur_block: ?mlir.Block = null,
/// Entry block for the active function.
func_entry_block: ?mlir.Block = null,
/// Cached constant `1` used when constructing branch arguments.
i64_one_in_entry: ?mlir.Value = null,
/// Join block that receives the control flow when returning from multiple sites.
ret_join_block: ?mlir.Block = null,
/// Tracks whether the current function returns a value.
ret_has_value: bool = false,
/// Cached return type for the function being lowered.
ret_type_cache: ?mlir.Type = null,
/// Tracks the current lexical scope/DI attribute.
current_scope: ?mlir.Attribute = null,
/// Mapping from TIR blocks to MLIR blocks.
block_map: std.AutoHashMap(tir.BlockId, mlir.Block),
/// SSA value to MLIR value mapping.
value_map: std.AutoHashMap(tir.ValueId, mlir.Value),
/// Storage assigned to spilled tensor values.
tensor_slots: std.AutoHashMap(tir.ValueId, mlir.Value),
/// Tensor element pointer metadata for multi-index stores.
tensor_elem_ptrs: std.AutoHashMap(tir.ValueId, TensorElemPtrInfo),

/// SR type of each SSA value – used for signedness/casting decisions.
val_types: std.AutoHashMap(tir.ValueId, types.TypeId), // SR types of SSA values
/// Tracks the defining instruction for each value to facilitate diagnostics.
def_instr: std.AutoHashMap(tir.ValueId, tir.InstrId), // SSA def site
/// Counter used when emitting and naming inline helper operations.
inline_mlir_counter: u32 = 0,

/// Cache for LLVM values that represent constant addresses.
global_addr_cache: std.StringHashMap(mlir.Value),
/// Functions that must remain as `llvm.func` due to taking addresses.
force_llvm_func_syms: std.AutoHashMap(tir.StrId, void),

/// MLIR diagnostic handler ID configured during module emission.
diagnostic_handler: mlir.c.MlirDiagnosticHandlerID,
/// Optional pointer to the active diagnostic data.
diagnostic_data: *DiagnosticData,
/// Tracks the type info context currently active during lowering.
active_type_info: ?*types.TypeInfo = null,

/// Metadata cached per emitted function so we can re-enter or reference it.
pub const FuncInfo = struct {
    /// MLIR operation representing the function (FuncOp or llvm.func).
    op: mlir.Operation,
    /// Whether the function accepts varargs.
    is_variadic: bool,
    /// Number of formal parameters visible in MLIR after stripping trailing `Any`.
    n_formals: usize,
    /// Return type of the lowered function.
    ret_type: mlir.Type,
    /// Parameter MLIR types, either borrowed or owned.
    param_types: []mlir.Type = @constCast((&[_]mlir.Type{})[0..]),
    /// Whether `param_types` slices own heap storage.
    owns_param_types: bool = false,
    /// Optional debug subprogram attribute for this function.
    dbg_subprogram: ?mlir.Attribute = null,
};

/// Describes how to index into a tensor: constant offset or SSA value.
const TensorIndex = union(enum) {
    /// Fixed element index.
    constant: i64,
    /// SSA-defined index value.
    value: tir.ValueId,
};

/// Tracks tensor-related SSA metadata needed for pointer arithmetic helpers.
const TensorElemPtrInfo = struct {
    /// SSA value pointing to the root tensor storage.
    root_ptr: tir.ValueId,
    /// Element type carried by the tensor.
    elem_ty: types.TypeId,
    /// Indices used for nested element access.
    indices: []TensorIndex,
};

/// Release the index buffer owned by `info` when it’s no longer needed.
fn freeTensorElemPtrInfo(self: *Codegen, info: *TensorElemPtrInfo) void {
    if (info.indices.len != 0) {
        self.gpa.free(info.indices);
        info.indices = &[_]TensorIndex{};
    }
}

/// Clear the per-function tensor element pointer cache without freeing capacity.
fn clearTensorElemPtrs(self: *Codegen) void {
    var it = self.tensor_elem_ptrs.valueIterator();
    while (it.next()) |info| self.freeTensorElemPtrInfo(info);
    self.tensor_elem_ptrs.clearRetainingCapacity();
}

/// Free all tensor element pointer entries and release their buffers.
fn releaseTensorElemPtrs(self: *Codegen) void {
    var it = self.tensor_elem_ptrs.valueIterator();
    while (it.next()) |info| self.freeTensorElemPtrInfo(info);
    self.tensor_elem_ptrs.clearRetainingCapacity();
}

// ----------------------------------------------------------------
// Op builder
// ----------------------------------------------------------------
/// Helper builder that accumulates operands/results/regions before creating an MLIR operation.
pub const OpBuilder = struct {
    /// Optional operands used when building the operation.
    ops: ?[]const mlir.Value = null,
    /// Optional result types for the new op.
    tys: ?[]const mlir.Type = null,
    /// Optional attributes attached to the op.
    attrs: ?[]const mlir.NamedAttribute = null,
    /// Owned regions to move into the operation.
    regs: ?[]const mlir.Region = null,
    /// Successor blocks for branch-style ops.
    succs: ?[]const mlir.Block = null,
    /// Operation name (e.g., "arith.add").
    name: []const u8,
    /// Location to attribute to `name`.
    loc: mlir.Location,

    /// Initialize an `OpBuilder` for `name` at `loc`.
    pub fn init(name: []const u8, loc: mlir.Location) OpBuilder {
        return .{ .name = name, .loc = loc };
    }
    /// Cast away const so callers can mutate the builder API fluently.
    pub fn builder(self: *const OpBuilder) *OpBuilder {
        return @constCast(self);
    }
    /// Set the operand list used when building the op.
    pub fn operands(self: *OpBuilder, ops: []const mlir.Value) *OpBuilder {
        self.ops = ops;
        return self;
    }
    /// Set the expected result types on the new operation.
    pub fn results(self: *OpBuilder, tys: []const mlir.Type) *OpBuilder {
        self.tys = tys;
        return self;
    }
    /// Set attributes that should attach to the operation.
    pub fn attributes(self: *OpBuilder, attrs: []const mlir.NamedAttribute) *OpBuilder {
        self.attrs = attrs;
        return self;
    }
    /// Provide regions that the new operation should own.
    pub fn regions(self: *OpBuilder, regs: []const mlir.Region) *OpBuilder {
        self.regs = regs;
        return self;
    }
    /// Provide successor blocks for ops that branch.
    pub fn successors(self: *OpBuilder, succs: []const mlir.Block) *OpBuilder {
        self.succs = succs;
        return self;
    }
    /// Emit the MLIR operation by populating `OperationState` and instantiating it.
    pub fn build(self: *OpBuilder) mlir.Operation {
        var st = mlir.OperationState.get(mlir.StringRef.from(self.name), self.loc);
        if (self.tys) |r| st.addResults(r);
        if (self.ops) |o| st.addOperands(o);
        if (self.attrs) |a| st.addAttributes(a);
        if (self.regs) |rg| st.addOwnedRegions(rg);
        if (self.succs) |s| st.addSuccessors(s);
        return mlir.Operation.create(&st);
    }
};

/// Capture the printed form of `attr` into an owned byte slice.
pub fn ownedAttributeText(self: *Codegen, attr: mlir.Attribute) ![]u8 {
    var list = ArrayList(u8).init(self.gpa);
    errdefer list.deinit();

    var had_error = false;
    var sink = PrintBuffer{ .list = &list, .had_error = &had_error };
    attr.print(printCallback, &sink);
    if (had_error) return error.OutOfMemory;

    return try list.toOwnedSlice();
}

/// Append the text representation of `ty` into `buf`.
fn appendMlirTypeText(self: *Codegen, buf: *ArrayList(u8), ty: mlir.Type) !void {
    var tmp = ArrayList(u8).init(self.gpa);
    defer tmp.deinit();
    var had_error = false;
    var sink = PrintBuffer{ .list = &tmp, .had_error = &had_error };
    ty.print(printCallback, &sink);
    if (had_error) return error.OutOfMemory;
    try buf.appendSlice(tmp.items);
}

/// Append the textual dump of `attr` into `buf`.
fn appendMlirAttributeText(self: *Codegen, buf: *ArrayList(u8), attr: mlir.Attribute) !void {
    var tmp = ArrayList(u8).init(self.gpa);
    defer tmp.deinit();
    var had_error = false;
    var sink = PrintBuffer{ .list = &tmp, .had_error = &had_error };
    attr.print(printCallback, &sink);
    if (had_error) return error.OutOfMemory;
    try buf.appendSlice(tmp.items);
}

/// Append the `module` textual dump to `buf`.
fn appendMlirModuleText(self: *Codegen, buf: *ArrayList(u8), module: mlir.Module) !void {
    var tmp = ArrayList(u8).init(self.gpa);
    defer tmp.deinit();
    var had_error = false;
    var sink = PrintBuffer{ .list = &tmp, .had_error = &had_error };
    module.getOperation().print(printCallback, &sink);
    if (had_error) return error.OutOfMemory;
    try buf.appendSlice(tmp.items);
}

/// Convert a comptime splice value into its textual form appended to `buf`.
fn appendMlirSpliceValue(
    self: *Codegen,
    buf: *ArrayList(u8),
    value: comp.ComptimeValue,
) !void {
    switch (value) {
        .Void => return error.MlirSpliceMissingValue,
        .Int => |v| {
            var writer = buf.writer();
            try writer.print("{}", .{v});
        },
        .Float => |v| {
            var writer = buf.writer();
            try writer.print("{}", .{v});
        },
        .Bool => |b| {
            try buf.appendSlice(if (b) "true" else "false");
        },
        .String => |s| {
            try buf.appendSlice(s);
        },
        .Sequence => |seq| {
            var writer = buf.writer();
            try writer.print("[sequence len={d}]", .{seq.values.items.len});
        },
        .Struct => |sv| {
            var writer = buf.writer();
            try writer.print("<struct len={d}>", .{sv.fields.items.len});
        },
        .Map => |mp| {
            var writer = buf.writer();
            try writer.print("<map len={d}>", .{mp.entries.items.len});
        },
        .Range => |rg| {
            var writer = buf.writer();
            try writer.print("range({d}..{d}{s})", .{ rg.start, rg.end, if (rg.inclusive) "=" else "" });
        },
        .Type => |ty| {
            const writer = buf.writer();
            try self.context.type_store.fmt(ty, writer);
        },
        .MlirType => |ty| try self.appendMlirTypeText(buf, ty),
        .MlirAttribute => |attr| try self.appendMlirAttributeText(buf, attr),
        .MlirModule => |module| try self.appendMlirModuleText(buf, module),
        .Pointer => |_| try buf.appendSlice("<pointer>"),
        .Function => |_| return error.MlirSpliceMissingValue,
    }
}

/// Evaluate the MLIR template pieces for a function and return the concatenated text.
fn renderMlirTemplate(
    self: *Codegen,
    t: *tir.TIR,
    pieces: []const tir.MlirPieceId,
) ![]u8 {
    var buf = ArrayList(u8).init(self.gpa);
    errdefer buf.deinit();

    for (pieces) |pid| {
        const piece = t.instrs.MlirPiece.get(pid);
        switch (piece.kind) {
            .literal => {
                const text = t.instrs.strs.get(piece.text);
                try buf.appendSlice(text);
            },
            .splice => try self.appendMlirSpliceValue(&buf, piece.value),
        }
    }

    return try buf.toOwnedSlice();
}

/// Diagnostic data passed into the MLIR diagnostic callback.
const DiagnosticData = struct {
    /// Compilation context for ownership and message formatting.
    context: *compile.Context,
    /// Captured diagnostic payload as text.
    msg: ?[]const u8 = null,
    /// Byte range/span for the diagnostic message.
    span: ?struct { start: u32, end: u32 } = null,
};

/// MLIR diagnostic callback that captures the error message and location span.
fn diagnosticHandler(diag: mlir.c.MlirDiagnostic, userdata: ?*anyopaque) callconv(.c) mlir.c.MlirLogicalResult {
    const data: *DiagnosticData = @ptrCast(@alignCast(userdata));
    var buf = ArrayList(u8).init(data.context.gpa);
    defer buf.deinit();
    var had_error = false;
    var sink = PrintBuffer{ .list = &buf, .had_error = &had_error };
    mlir.c.mlirDiagnosticPrint(diag, printCallback, &sink);
    const loc = mlir.c.mlirDiagnosticGetLocation(diag);
    var start = mlir.c.mlirLocationFileLineColRangeGetStartColumn(loc);
    var end = mlir.c.mlirLocationFileLineColRangeGetEndColumn(loc);
    if (start == -1) start = 0;
    if (end == -1) end = 0;
    data.msg = buf.toOwnedSlice() catch unreachable;
    data.span = .{ .start = @intCast(start), .end = @intCast(end) };

    return .{ .value = 1 };
}

// ----------------------------------------------------------------
// Init / Deinit
// ----------------------------------------------------------------
/// Create a fresh `Codegen` driver with initialized caches and DI metadata.
pub fn init(gpa: Allocator, context: *compile.Context, ctx: mlir.Context) Codegen {
    const loc = mlir.Location.unknownGet(ctx);
    const module = mlir.Module.createEmpty(loc);
    const void_ty = mlir.Type{ .handle = mlir.c.mlirLLVMVoidTypeGet(ctx.handle) };
    const diag_data = gpa.create(DiagnosticData) catch unreachable;
    diag_data.* = DiagnosticData{ .context = context };
    return .{
        .gpa = gpa,
        .context = context,
        .mlir_ctx = ctx,
        .loc = loc,
        .module = module,
        .loc_cache = std.AutoHashMap(cst.LocId, mlir.Location).init(gpa),
        .file_cache = std.AutoHashMap(u32, []const u8).init(gpa),
        .line_index_cache = std.AutoHashMap(u32, []usize).init(gpa),
        .di_files = std.AutoHashMap(u32, debug.DebugFileInfo).init(gpa),
        .di_subprograms = std.AutoHashMap(tir.FuncId, debug.DebugSubprogramInfo).init(gpa),
        .di_null_type_attr = mlir.Attribute.empty(),
        .di_subroutine_null_type_attr = mlir.Attribute.empty(),
        .di_empty_expr_attr = mlir.Attribute.empty(),
        .di_type_cache = std.AutoHashMap(types.TypeId, mlir.Attribute).init(gpa),
        .next_di_id = 0,
        .void_ty = void_ty,
        .i1_ty = mlir.Type.getSignlessIntegerType(ctx, 1),
        .i8_ty = mlir.Type.getSignlessIntegerType(ctx, 8),
        .i32_ty = mlir.Type.getSignlessIntegerType(ctx, 32),
        .i64_ty = mlir.Type.getSignlessIntegerType(ctx, 64),
        .f32_ty = mlir.Type.getFloat32Type(ctx),
        .f64_ty = mlir.Type.getFloat64Type(ctx),
        .llvm_ptr_ty = mlir.LLVM.getPointerType(ctx, 0),
        .func_syms = std.AutoHashMap(tir.StrId, FuncInfo).init(gpa),
        .global_syms = std.StringHashMap(void).init(gpa),
        .str_pool = std.StringHashMap(mlir.Operation).init(gpa),
        .block_map = std.AutoHashMap(tir.BlockId, mlir.Block).init(gpa),
        .value_map = std.AutoHashMap(tir.ValueId, mlir.Value).init(gpa),
        .tensor_slots = std.AutoHashMap(tir.ValueId, mlir.Value).init(gpa),
        .tensor_elem_ptrs = std.AutoHashMap(tir.ValueId, TensorElemPtrInfo).init(gpa),
        .val_types = std.AutoHashMap(tir.ValueId, types.TypeId).init(gpa),
        .def_instr = std.AutoHashMap(tir.ValueId, tir.InstrId).init(gpa),
        .global_addr_cache = std.StringHashMap(mlir.Value).init(gpa),
        .force_llvm_func_syms = std.AutoHashMap(tir.StrId, void).init(gpa),
        .diagnostic_handler = mlir.c.mlirContextAttachDiagnosticHandler(ctx.handle, diagnosticHandler, @ptrCast(diag_data), null),
        .diagnostic_data = diag_data,
        .active_type_info = null,
    };
}

/// Tear down `Codegen`, releasing all MLIR/diagnostic caches and allocator ownership.
pub fn deinit(self: *Codegen) void {
    self.resetDebugCaches();
    self.di_subprograms.deinit();
    self.di_files.deinit();
    self.di_type_cache.deinit();
    var fit = self.func_syms.valueIterator();
    while (fit.next()) |info| {
        if (info.owns_param_types) {
            self.gpa.free(info.param_types);
        }
    }
    self.func_syms.deinit();
    self.global_syms.deinit();
    self.str_pool.deinit();
    self.block_map.deinit();
    self.value_map.deinit();
    self.releaseTensorElemPtrs();
    self.tensor_elem_ptrs.deinit();
    self.tensor_slots.deinit();
    self.val_types.deinit();
    self.def_instr.deinit();
    self.global_addr_cache.deinit();
    self.force_llvm_func_syms.deinit();
    var li_it = self.line_index_cache.valueIterator();
    while (li_it.next()) |lines| self.gpa.free(lines);
    self.line_index_cache.deinit();
    var it = self.file_cache.valueIterator();
    while (it.next()) |src| {
        self.context.source_manager.gpa.free(@constCast(src.*));
    }
    self.file_cache.deinit();
    self.loc_cache.deinit();
    if (self.diagnostic_data.msg) |msg| {
        self.gpa.free(msg);
    }
    self.gpa.destroy(self.diagnostic_data);
    mlir.c.mlirContextDetachDiagnosticHandler(self.mlir_ctx.handle, self.diagnostic_handler);
    self.module.destroy();
}

/// Empty cached debug metadata so future functions regenerate DI entries.
pub fn resetDebugCaches(self: *Codegen) void {
    debug.resetDebugCaches(self);
}

/// Fetch and cache the source buffer for `file_id`, reusing previous reads.
fn getFileSource(self: *Codegen, file_id: u32) ![]const u8 {
    if (self.file_cache.get(file_id)) |buf| return buf;
    const data = try self.context.source_manager.read(file_id);
    var owned = true;
    defer if (owned) self.context.source_manager.gpa.free(@constCast(data));
    try self.file_cache.put(file_id, data);
    owned = false;
    return data;
}

/// Read the optional source location attached to `ins_id` inside `t`.
fn instrOptLoc(_: *Codegen, t: *tir.TIR, ins_id: tir.InstrId) tir.OptLocId {
    const kind = t.kind(ins_id);
    return switch (kind) {
        inline else => |k| t.instrs.get(k, ins_id).loc,
    };
}

/// Return the optional location stored on terminator `term_id` within `t`.
fn termOptLoc(_: *Codegen, t: *tir.TIR, term_id: tir.TermId) tir.OptLocId {
    return switch (t.kind(term_id)) {
        inline else => |k| t.terms.get(k, term_id).loc,
    };
}

/// Scan `block_id` for any instruction/terminator location and return the first one.
fn blockOptLoc(self: *Codegen, block_id: tir.BlockId, t: *tir.TIR) tir.OptLocId {
    const block = t.funcs.Block.get(block_id);
    const instrs = t.instrs.instr_pool.slice(block.instrs);
    for (instrs) |ins_id| {
        const loc = self.instrOptLoc(t, ins_id);
        if (!loc.isNone()) return loc;
    }
    return self.termOptLoc(t, block.term);
}

/// Populate a list of functions whose LLVM symbols must be emitted because addresses are taken.
fn collectForceLlvmFuncSyms(self: *Codegen, t: *tir.TIR) !void {
    self.force_llvm_func_syms.clearRetainingCapacity();

    const type_store = self.context.type_store;
    const funcs = t.funcs.func_pool.data.items;
    for (funcs) |fid| {
        const f = t.funcs.Function.get(fid);
        const blocks = t.funcs.block_pool.slice(f.blocks);
        for (blocks) |bid| {
            const b = t.funcs.Block.get(bid);
            const instrs = t.instrs.instr_pool.slice(b.instrs);
            for (instrs) |iid| {
                if (t.kind(iid) != .GlobalAddr) continue;
                const row = t.instrs.get(.GlobalAddr, iid);
                if (type_store.getKind(row.ty) != .Ptr) continue;
                const ptr = type_store.get(.Ptr, row.ty);
                if (type_store.getKind(ptr.elem) != .Function) continue;
                _ = try self.force_llvm_func_syms.put(row.name, {});
            }
        }
    }
}

/// Return the first non-empty location associated with function `f_id`.
fn functionOptLoc(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR) tir.OptLocId {
    const f = t.funcs.Function.get(f_id);
    const blocks = t.funcs.block_pool.slice(f.blocks);
    for (blocks) |block_id| {
        const loc = self.blockOptLoc(block_id, t);
        if (!loc.isNone()) return loc;
    }
    // No block carried a concrete span. Leave the function location unknown so
    // downstream consumers treat it as compiler-synthesized.
    return tir.OptLocId.none();
}

// ----------------------------------------------------------------
// Public entry
// ----------------------------------------------------------------

/// Lower all dependency levels into MLIR by iterating through TIR units.
pub fn emit(self: *Codegen, levels: *const compile.DependencyLevels) !mlir.Module {
    var unit_by_file = std.AutoHashMap(u32, *package.FileUnit).init(self.gpa);
    defer unit_by_file.deinit();

    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var source_iter = pkg.value_ptr.sources.iterator();
        while (source_iter.next()) |unit| {
            try unit_by_file.put(unit.value_ptr.file_id, unit.value_ptr);
        }
    }

    for (levels.levels.items) |level| {
        if (level.items.len == 0) continue;

        for (level.items) |file_id| {
            const unit = unit_by_file.get(file_id) orelse continue;
            if (unit.tir == null) continue;
            _ = try self.emitModule(unit.tir.?);
        }
    }
    return self.module;
}

/// Lower a single TIR unit into MLIR, emitting functions and debug info.
pub fn emitModule(
    self: *Codegen,
    t: *tir.TIR,
) !mlir.Module {
    const prev_loc = self.loc;
    defer self.loc = prev_loc;

    // const prev_type_info = self.active_type_info;
    // self.active_type_info = type_info;
    // defer self.active_type_info = prev_type_info;

    self.loc_cache.clearRetainingCapacity();
    try self.collectForceLlvmFuncSyms(t);
    try debug.attachTargetInfo(self);
    try debug.ensureDebugModuleAttrs(self);
    try self.emitExternDecls(t);

    const func_ids = t.funcs.func_pool.data.items;
    for (func_ids) |fid| try self.emitFunctionHeader(fid, t);
    for (func_ids) |fid| {
        const row = t.funcs.Function.get(fid);
        const blocks = t.funcs.block_pool.slice(row.blocks);
        if (blocks.len > 0) try self.emitFunctionBody(fid, t);
    }
    return self.module;
}

/// Map `opt_loc` to an MLIR `Location`, caching repeated lookups.
fn mlirFileLineColLocation(self: *Codegen, opt_loc: tir.OptLocId) mlir.Location {
    if (opt_loc.isNone())
        // Preserve the current ambient location so callers can deliberately
        // keep emitting with whatever scope was active.
        return self.loc;
    const loc_id = opt_loc.unwrap();
    if (self.loc_cache.get(loc_id)) |cached| return cached;

    const loc_record = self.context.loc_store.get(loc_id);
    const src = self.getFileSource(loc_record.file_id) catch {
        return self.loc;
    };
    const lc = self.computeLineCol(src, loc_record.start, loc_record.file_id);
    const filename = self.context.source_manager.get(loc_record.file_id) orelse "unknown";
    const mlir_loc = mlir.Location.fileLineColGet(
        self.mlir_ctx,
        mlir.StringRef.from(filename),
        @as(u32, @intCast(lc.line + 1)),
        @as(u32, @intCast(lc.col + 1)),
    );
    _ = self.loc_cache.put(loc_id, mlir_loc) catch {};
    return mlir_loc;
}

/// Update the current MLIR location to `opt_loc` and return the previous location.
pub fn pushLocation(self: *Codegen, opt_loc: tir.OptLocId) mlir.Location {
    const prev = self.loc;
    const file_loc = self.mlirFileLineColLocation(opt_loc);
    if (self.current_scope) |s| {
        if (s.isNull()) {
            self.loc = file_loc;
        } else {
            self.loc = mlir.Location.fusedGet(self.mlir_ctx, &.{file_loc}, s);
        }
    } else {
        self.loc = file_loc;
    }
    return prev;
}

/// Convert a TIR constant initializer into an MLIR attribute of type `ty`.
fn attributeFromConstInit(self: *Codegen, ci: tir.ConstInit, ty: mlir.Type) !mlir.Attribute {
    return switch (ci) {
        .int => |val| mlir.Attribute.integerAttrGet(ty, val),
        .bool => |val| mlir.Attribute.integerAttrGet(ty, if (val) 1 else 0),
        .float => |val| mlir.Attribute.floatAttrDoubleGet(self.mlir_ctx, ty, val),
        .aggregate => |fields| {
            if (!mlir.LLVM.isLLVMStructType(ty)) return error.Unexpected;
            const num_elem_types = mlir.LLVM.getLLVMStructTypeNumElementTypes(ty);
            if (num_elem_types != fields.len) return error.Unexpected;

            var field_attrs = try self.gpa.alloc(mlir.Attribute, fields.len);
            defer self.gpa.free(field_attrs);

            for (fields, 0..) |field_init, i| {
                const elem_ty = mlir.LLVM.getLLVMStructTypeElementType(ty, i);
                field_attrs[i] = try self.attributeFromConstInit(field_init, elem_ty);
            }
            return mlir.Attribute.arrayAttrGet(self.mlir_ctx, field_attrs);
        },
        .none => mlir.Attribute.getNull(),
        else => return error.Unsupported,
    };
}
/// Append an `llvm.return` operation carrying `val` into `block`.
fn appendReturnInBlock(self: *Codegen, block: *mlir.Block, val: mlir.Value) void {
    const op = self.buildOp("llvm.return", EmitOpArgs{
        .operands = &.{val},
    });
    block.appendOwnedOperation(op);
}

/// Append an `llvm.mlir.zero` of type `ty` into `block` and return the new value.
fn appendZeroValueInBlock(self: *Codegen, block: *mlir.Block, ty: mlir.Type) mlir.Value {
    const op = self.buildOp("llvm.mlir.zero", EmitOpArgs{
        .results = &.{ty},
    });
    block.appendOwnedOperation(op);
    return op.getResult(0);
}

/// Emit MLIR declarations for the extern globals and functions referenced in `t`.
fn emitExternDecls(self: *Codegen, t: *tir.TIR) !void {
    const global_ids = t.funcs.global_pool.data.items;

    for (global_ids) |global_id| {
        const g = t.funcs.Global.get(global_id);
        const name = t.instrs.strs.get(g.name);
        const sym_id = g.name;

        if (self.context.type_store.getKind(g.ty) == .Function) {
            // If already present, return it.
            if (self.func_syms.contains(sym_id)) continue;

            const fnty = self.context.type_store.get(.Function, g.ty);
            var params_sr = self.context.type_store.type_pool.slice(fnty.params);
            if (fnty.is_variadic)
                params_sr = params_sr[0 .. params_sr.len - 1]; // drop trailing Any for varargs
            const ret_sr = fnty.result;

            // Pre-calculate the number of lowered parameters
            var num_lowered_params: usize = 0;
            const ret_kind = self.context.type_store.getKind(ret_sr);
            const ret_no_result = ret_kind == .Void or ret_kind == .Noreturn;
            if (!ret_no_result) {
                const retClass = abi.abiClassifyX64SysV(self, ret_sr, true);
                if (retClass.kind == .IndirectSRet) {
                    num_lowered_params += 1;
                }
            }
            for (params_sr) |psr| {
                const cls = abi.abiClassifyX64SysV(self, psr, false);
                switch (cls.kind) {
                    .IndirectByVal, .DirectScalar => num_lowered_params += 1,
                    .DirectPair => num_lowered_params += 2,
                    else => {},
                }
            }

            // Build lowered param list & arg attributes
            var lowered_params = try self.gpa.alloc(mlir.Type, num_lowered_params);
            defer self.gpa.free(lowered_params);
            var argAttrs = try self.gpa.alloc(mlir.Attribute, num_lowered_params);
            defer self.gpa.free(argAttrs);

            var n_args: usize = 0;

            // Return classification (may add leading sret)
            var ret_type: mlir.Type = self.void_ty;
            var retClass: abi.AbiClass = undefined;

            if (ret_no_result) {
                ret_type = self.void_ty;
            } else {
                retClass = abi.abiClassifyX64SysV(self, ret_sr, true);
                switch (retClass.kind) {
                    .IndirectSRet => {
                        // leading ptr arg with { llvm.sret = type(T), llvm.align = K }
                        lowered_params[n_args] = self.llvm_ptr_ty;
                        const stTy = try self.llvmTypeOf(ret_sr);
                        const sretDict = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &[_]mlir.NamedAttribute{
                            self.named("llvm.sret", mlir.Attribute.typeAttrGet(stTy)),
                            self.named("llvm.align", mlir.Attribute.integerAttrGet(self.i64_ty, retClass.alignment)),
                        });
                        argAttrs[n_args] = sretDict;
                        n_args += 1;
                        ret_type = self.void_ty;
                    },
                    .DirectScalar => {
                        ret_type = retClass.scalar0.?;
                    },
                    .DirectPair => {
                        // Return a literal LLVM struct of the two scalars
                        const pairTy = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{
                            retClass.scalar0.?, retClass.scalar1.?,
                        }, false);
                        ret_type = pairTy;
                    },
                    else => unreachable,
                }
            }

            // Params
            for (params_sr) |psr| {
                const cls = abi.abiClassifyX64SysV(self, psr, false);
                switch (cls.kind) {
                    .IndirectByVal => {
                        lowered_params[n_args] = self.llvm_ptr_ty;
                        const stTy = try self.llvmTypeOf(psr);
                        const byvalDict = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &[_]mlir.NamedAttribute{
                            self.named("llvm.byval", mlir.Attribute.typeAttrGet(stTy)),
                            self.named("llvm.align", mlir.Attribute.integerAttrGet(self.i64_ty, cls.alignment)),
                        });
                        argAttrs[n_args] = byvalDict;
                        n_args += 1;
                    },
                    .DirectScalar => {
                        lowered_params[n_args] = cls.scalar0.?;
                        argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &.{});
                        n_args += 1;
                    },
                    .DirectPair => {
                        lowered_params[n_args] = cls.scalar0.?;
                        argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &.{});
                        n_args += 1;
                        lowered_params[n_args] = cls.scalar1.?;
                        argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &.{});
                        n_args += 1;
                    },
                    else => unreachable,
                }
            }

            // Build function type & op
            const fty = mlir.LLVM.getLLVMFunctionType(ret_type, lowered_params[0..n_args], fnty.is_variadic);

            const argAttrsArray = mlir.Attribute.arrayAttrGet(self.mlir_ctx, argAttrs[0..n_args]);
            const attrs = [_]mlir.NamedAttribute{
                self.named("sym_name", self.strAttr(name)),
                self.named("function_type", mlir.Attribute.typeAttrGet(fty)),
                self.named("arg_attrs", argAttrsArray),
                self.named("sym_visibility", self.strAttr("private")),
            };
            const region = mlir.Region.create(); // extern: no body
            // Extern declarations originate from imported metadata and have no
            // source span, so we intentionally reuse the module location here.
            const fnop = self.buildOp("llvm.func", EmitOpArgs{
                .attributes = &attrs,
                .regions = &.{region},
            });
            var body = self.module.getBody();
            body.appendOwnedOperation(fnop);

            const param_types_copy = try self.gpa.alloc(mlir.Type, n_args);
            std.mem.copyForwards(mlir.Type, param_types_copy, lowered_params[0..n_args]);
            const info = FuncInfo{
                .op = fnop,
                .is_variadic = fnty.is_variadic,
                .n_formals = params_sr.len, // SR count, not lowered
                .ret_type = ret_type,
                .param_types = param_types_copy,
                .owns_param_types = true,
                .dbg_subprogram = null,
            };
            _ = try self.func_syms.put(sym_id, info);
        } else {
            // Handle global variables
            if (self.global_syms.contains(name)) {
                continue;
            }
            const var_mlir_ty = try self.llvmTypeOf(g.ty);

            var attr_buf: std.ArrayList(mlir.NamedAttribute) = .empty;
            defer attr_buf.deinit(self.gpa);

            try attr_buf.append(self.gpa, self.named("sym_name", self.strAttr(name)));
            try attr_buf.append(self.gpa, self.named("global_type", mlir.Attribute.typeAttrGet(var_mlir_ty)));
            try attr_buf.append(self.gpa, self.named("sym_visibility", self.strAttr("private")));
            try attr_buf.append(self.gpa, self.named(
                "linkage",
                mlir.LLVMAttributes.getLLVMLinkageAttr(self.mlir_ctx, mlir.LLVMLinkage.Internal),
            ));

            var init_region = mlir.Region.create();
            if (g.init != .none) {
                const attr = try self.attributeFromConstInit(g.init, var_mlir_ty);
                try attr_buf.append(self.gpa, self.named("value", attr));
            } else if (self.context.type_store.getKind(g.ty) == .DynArray) {
                var block = mlir.Block.create(&.{}, &.{});
                init_region.appendOwnedBlock(block);
                const zero = self.appendZeroValueInBlock(&block, var_mlir_ty);
                self.appendReturnInBlock(&block, zero);
            }

            const attrs = attr_buf.items;
            // Likewise, synthesized globals are emitted with the module location
            // because they are not backed by user-written syntax.
            const global_op = self.buildOp("llvm.mlir.global", EmitOpArgs{
                .attributes = attrs,
                .regions = &.{init_region},
            });

            var body = self.module.getBody();
            body.appendOwnedOperation(global_op);
            try self.global_syms.put(name, {});
        }
    }
}

/// Prepare the MLIR function declaration/operator for `f_id` before emitting its body.
fn emitFunctionHeader(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR) !void {
    const f = t.funcs.Function.get(f_id);
    const params = t.funcs.param_pool.slice(f.params);

    var param_tys = try self.gpa.alloc(mlir.Type, params.len);
    defer self.gpa.free(param_tys);

    for (params, 0..) |p_id, i| {
        const p = t.funcs.Param.get(p_id);
        param_tys[i] = try self.llvmTypeOf(p.ty);
    }

    var results: [1]mlir.Type = undefined;
    const n_res: usize = switch (self.context.type_store.getKind(f.result)) {
        .Void, .Noreturn => 0,
        else => 1,
    };
    if (n_res == 1) results[0] = try self.llvmTypeOf(f.result);

    // Decide whether to emit as func.func or llvm.func. We force llvm.func when
    // we know the function's address is taken (collected earlier).
    const f_attrs = t.instrs.attribute_pool.slice(f.attrs);
    const emit_c_iface = t.instrs.strs.intern("llvm.emit_c_interface");
    const emit_as_llvm_func = self.force_llvm_func_syms.get(f.name) != null;
    // NOTE: language-defined functions here are assumed non-variadic
    const fn_ret_ty: mlir.Type = if (n_res == 0) self.void_ty else results[0];
    const fty = blk: {
        if (emit_as_llvm_func) {
            break :blk mlir.LLVM.getLLVMFunctionType(fn_ret_ty, param_tys, false);
        } else {
            break :blk mlir.Type.getFunctionType(self.mlir_ctx, @intCast(param_tys.len), param_tys, @intCast(n_res), results[0..n_res]);
        }
    };

    const func_name = t.instrs.strs.get(f.name);
    const func_name_id = f.name;
    if (self.func_syms.contains(func_name_id)) return;

    var attrs: std.ArrayList(mlir.NamedAttribute) = .empty;
    defer attrs.deinit(self.gpa);

    try attrs.append(self.gpa, self.named("sym_name", self.strAttr(func_name)));
    try attrs.append(self.gpa, self.named("function_type", mlir.Attribute.typeAttrGet(fty)));
    try attrs.append(self.gpa, self.named("sym_visibility", self.strAttr("public")));
    if (emit_as_llvm_func) {
        // Ensure C calling convention when exposing to C/C++ callers.
        try attrs.append(self.gpa, self.named("CConv", mlir.LLVMAttributes.getLLVMCConvAttr(self.mlir_ctx, .C)));
    }

    const fn_loc = self.functionOptLoc(f_id, t);
    var maybe_dbg_attr: ?mlir.Attribute = null;
    if (enable_debug_info and !fn_loc.isNone()) {
        const loc_record = self.context.loc_store.get(fn_loc.unwrap());
        const src = self.getFileSource(loc_record.file_id) catch null;
        if (src) |src_text| {
            const lc = self.computeLineCol(src_text, loc_record.start, loc_record.file_id);
            const line = @as(u32, @intCast(lc.line + 1));
            const maybe_subp: ?*debug.DebugSubprogramInfo = debug.ensureDebugSubprogram(
                self,
                f_id,
                func_name,
                line,
                loc_record.file_id,
                fn_loc,
                f.result,
                params,
                t,
            ) catch null;
            if (maybe_subp) |subp| {
                maybe_dbg_attr = subp.attr;
            }
        }
    }

    if (maybe_dbg_attr) |dbg_attr| {
        try attrs.append(self.gpa, self.named("llvm.di.subprogram", dbg_attr));
    }

    for (f_attrs) |attr_id| {
        const attr = t.instrs.Attribute.get(attr_id);
        if (attr.name.eq(emit_c_iface)) {
            try attrs.append(self.gpa, self.named("llvm.emit_c_interface", mlir.Attribute.unitAttrGet(self.mlir_ctx)));
        }
    }

    const prev_loc = self.pushLocation(fn_loc);
    self.loc = prev_loc;

    const region = mlir.Region.create();
    const op_name = if (emit_as_llvm_func) "llvm.func" else "func.func";
    const fnop = self.buildOp(op_name, EmitOpArgs{
        .attributes = attrs.items,
        .regions = &.{region},
    });

    var body = self.module.getBody();
    body.appendOwnedOperation(fnop);

    const ret_mlir = fn_ret_ty;
    const finfo: FuncInfo = if (!emit_as_llvm_func) .{
        .op = fnop,
        .is_variadic = false,
        .n_formals = params.len,
        .ret_type = ret_mlir,
        .param_types = blk: {
            const n_params = param_tys.len;
            const copy = try self.gpa.alloc(mlir.Type, n_params);
            std.mem.copyForwards(mlir.Type, copy, param_tys);
            break :blk copy;
        },
        .owns_param_types = true,
        .dbg_subprogram = maybe_dbg_attr,
    } else blk_info: {
        // For llvm.func with body, keep param_types equal to SR-lowered types
        // (no ABI splitting here). This keeps body entry args consistent.
        const param_types_copy = try self.gpa.alloc(mlir.Type, param_tys.len);
        std.mem.copyForwards(mlir.Type, param_types_copy, param_tys);
        break :blk_info .{
            .op = fnop,
            .is_variadic = false,
            .n_formals = params.len,
            .ret_type = ret_mlir,
            .param_types = param_types_copy,
            .owns_param_types = true,
            .dbg_subprogram = maybe_dbg_attr,
        };
    };

    _ = try self.func_syms.put(func_name_id, finfo);
}

/// Return a cached `i64` constant that lives in the entry block.
fn getI64OneInEntry(self: *Codegen) mlir.Value {
    if (self.i64_one_in_entry) |v| return v;

    // Build the constant op but place it in the entry block
    const c = self.buildOp("llvm.mlir.constant", EmitOpArgs{
        .results = &.{self.i64_ty},
        .attributes = &.{self.named("value", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
    });

    self.appendInFuncEntry(c);
    const v = c.getResult(0);
    self.i64_one_in_entry = v;
    return v;
}

/// Lower the instructions of function `f_id` after its header has been emitted.
fn emitFunctionBody(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR) !void {
    // reset per-function state
    self.block_map.clearRetainingCapacity();
    self.value_map.clearRetainingCapacity();
    self.val_types.clearRetainingCapacity();
    self.def_instr.clearRetainingCapacity();
    self.tensor_slots.clearRetainingCapacity();
    self.clearTensorElemPtrs();
    self.cur_region = null;
    self.cur_block = null;
    self.func_entry_block = null;
    self.i64_one_in_entry = null;
    self.ret_join_block = null;
    self.ret_has_value = false;
    self.ret_type_cache = null;
    self.global_addr_cache.clearRetainingCapacity();

    const f = t.funcs.Function.get(f_id);
    const fn_opt_loc = self.functionOptLoc(f_id, t);
    const finfo = self.func_syms.get(f.name).?;
    self.current_scope = finfo.dbg_subprogram;
    defer self.current_scope = null;
    var func_op = finfo.op;
    var region = func_op.getRegion(0);

    const n_formals = finfo.n_formals;
    const params = t.funcs.param_pool.slice(f.params);
    const blocks = t.funcs.block_pool.slice(f.blocks);

    // entry block arg types
    var entry_arg_tys = try self.gpa.alloc(mlir.Type, n_formals);
    defer self.gpa.free(entry_arg_tys);
    for (params[0..n_formals], 0..) |p_id, i| {
        const p = t.funcs.Param.get(p_id);
        entry_arg_tys[i] = try self.llvmTypeOf(p.ty);
    }
    const entry_locs = try self.gpa.alloc(mlir.Location, n_formals);
    defer self.gpa.free(entry_locs);

    const entry_block_loc_opt = if (blocks.len > 0)
        self.blockOptLoc(blocks[0], t)
    else
        tir.OptLocId.none();
    const entry_prev = self.pushLocation(if (!entry_block_loc_opt.isNone()) entry_block_loc_opt else fn_opt_loc);
    const entry_mlir_loc = self.loc;
    self.loc = entry_prev;
    for (entry_locs) |*L| L.* = entry_mlir_loc;

    var entry_block = mlir.Block.create(entry_arg_tys, entry_locs);
    region.appendOwnedBlock(entry_block);
    self.cur_region = region;
    self.cur_block = entry_block;
    self.func_entry_block = entry_block;

    if (blocks.len > 0) {
        const entry_bid = blocks[0];
        try self.block_map.put(entry_bid, entry_block);
    }

    // seed param SSA values + SR types
    try self.value_map.ensureTotalCapacity(@intCast(n_formals));
    try self.val_types.ensureTotalCapacity(@intCast(n_formals));
    for (params[0..n_formals], 0..) |p_id, i| {
        const p = t.funcs.Param.get(p_id);
        const v = entry_block.getArgument(i);
        try self.value_map.put(p.value, v);
        try self.val_types.put(p.value, p.ty);
    }

    if (enable_debug_info) {
        debug.emitParameterDebugInfo(self, f_id, params[0..n_formals], entry_block, t) catch {};
    }

    // pre-create remaining blocks and map their params + SR types
    if (blocks.len > 1) {
        for (blocks[1..]) |b_id| {
            const bb = t.funcs.Block.get(b_id);
            const b_params = t.funcs.param_pool.slice(bb.params);
            const m = b_params.len;

            var arg_tys = try self.gpa.alloc(mlir.Type, m);
            defer self.gpa.free(arg_tys);
            var arg_locs = try self.gpa.alloc(mlir.Location, m);
            defer self.gpa.free(arg_locs);

            const block_loc_opt = self.blockOptLoc(b_id, t);
            const block_prev = self.pushLocation(if (!block_loc_opt.isNone()) block_loc_opt else fn_opt_loc);
            const block_mlir_loc = self.loc;
            self.loc = block_prev;

            for (b_params, 0..) |bp_id, i| {
                const bp = t.funcs.Param.get(bp_id);
                arg_tys[i] = try self.llvmTypeOf(bp.ty);
                arg_locs[i] = block_mlir_loc;
            }

            const b = mlir.Block.create(arg_tys, arg_locs);
            region.appendOwnedBlock(b);
            try self.block_map.put(b_id, b);
        }
    }

    // Create a dedicated return-join block at end of region for func.func
    const is_llvm_func = std.mem.eql(u8, func_op.getName().str().toSlice(), "llvm.func");
    if (!is_llvm_func) {
        const has_res = !finfo.ret_type.equal(self.void_ty);
        self.ret_has_value = has_res;
        self.ret_type_cache = finfo.ret_type;
        const arg_ty_slice: []const mlir.Type = if (has_res) &.{finfo.ret_type} else &.{};
        const arg_loc_slice: []const mlir.Location = if (has_res) &.{entry_mlir_loc} else &.{};
        const ret_blk = mlir.Block.create(arg_ty_slice, arg_loc_slice);
        region.appendOwnedBlock(ret_blk);
        self.ret_join_block = ret_blk;
    }

    // emit each block
    for (blocks) |b_id| {
        var mblock = self.block_map.get(b_id).?;
        self.cur_block = mblock;
        const bb = t.funcs.Block.get(b_id);

        // map block params to SSA + SR types
        const b_params = t.funcs.param_pool.slice(bb.params);
        for (b_params, 0..) |bp_id, i| {
            const bp = t.funcs.Param.get(bp_id);
            const arg = mblock.getArgument(i);
            try self.value_map.put(bp.value, arg);
            try self.val_types.put(bp.value, bp.ty);
        }

        // non-terminators
        const instrs = t.instrs.instr_pool.slice(bb.instrs);
        for (instrs) |ins_id| {
            const v = try self.emitInstr(ins_id, t);

            if (self.getInstrResultId(t, ins_id)) |rid| {
                try self.value_map.put(rid, v);
                if (self.instrResultSrType(t, ins_id)) |rt| {
                    try self.val_types.put(rid, rt);
                }
                try self.def_instr.put(rid, ins_id);
            }
        }

        // terminator
        try self.emitTerminator(bb.term, t);
    }

    // Emit the single func.return in the join block (if func.func)
    if (self.ret_join_block) |rb| {
        self.cur_block = rb;
        if (self.ret_has_value) {
            const arg = rb.getArgument(0);
            _ = self.appendOp("func.return", EmitOpArgs{
                .operands = &.{arg},
            });
        } else {
            _ = self.appendOp("func.return", EmitOpArgs{});
        }
    }

    self.func_entry_block = null;
    self.ret_join_block = null;
    self.ret_type_cache = null;
}

/// Return the lowered SSA value corresponding to `id` if it was already emitted.
fn getInstrResultId(self: *Codegen, t: *tir.TIR, id: tir.InstrId) ?tir.ValueId {
    _ = self;
    switch (t.kind(id)) {
        inline else => |k| return t.instrs.get(k, id).result,
        inline .Add, .Sub, .Mul, .BinWrapAdd, .BinWrapSub, .BinWrapMul, .BinSatAdd, .BinSatSub, .BinSatMul, .BinSatShl, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe, .LogicalAnd, .LogicalOr => |k| return t.instrs.get(k, id).result,
        inline .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => |k| return t.instrs.get(k, id).result,
        .Store => return null,
        .MlirBlock => {
            const p = t.instrs.get(.MlirBlock, id);
            if (p.result.isNone()) return null;
            return p.result.unwrap();
        },
    }
}

/// Retrieve the source-level type stamped on the result of `id`, if recorded.
fn instrResultSrType(_: *Codegen, t: *tir.TIR, id: tir.InstrId) ?types.TypeId {
    return switch (t.kind(id)) {
        inline else => |k| t.instrs.get(k, id).ty,
        inline .Add, .Sub, .Mul, .BinWrapAdd, .BinWrapSub, .BinWrapMul, .BinSatAdd, .BinSatSub, .BinSatMul, .BinSatShl, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe, .LogicalAnd, .LogicalOr => |k| t.instrs.get(k, id).ty,
        inline .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => |k| t.instrs.get(k, id).ty,
        .Store => null,
    };
}

/// Ensure the callee referenced by `p` has been emitted and return its `FuncInfo`.
fn ensureFuncDeclFromCall(self: *Codegen, p: tir.Rows.Call, t: *tir.TIR) !FuncInfo {
    const name = t.instrs.strs.get(p.callee);
    const callee_id = p.callee;

    // If already present, return it.
    if (self.func_syms.get(callee_id)) |fi| return fi;

    // Try to pick types from global (for varargs info etc.)
    const global_ids = t.funcs.global_pool.data.items;
    var found: bool = false;
    var is_var: bool = false;
    var params_sr_list = ArrayList(types.TypeId).init(self.gpa);
    defer params_sr_list.deinit();
    var params_sr: []const types.TypeId = &.{};
    var ret_sr: types.TypeId = types.TypeId.fromRaw(0);

    for (global_ids) |gid| {
        const g = t.funcs.Global.get(gid);
        if (self.context.type_store.getKind(g.ty) != .Function) continue;
        if (!g.name.eq(p.callee)) continue;
        const fnty = self.context.type_store.get(.Function, g.ty);
        is_var = fnty.is_variadic;
        params_sr = self.context.type_store.type_pool.slice(fnty.params);
        ret_sr = fnty.result;
        found = true;
        break;
    }

    if (!found) {
        // Fallback: infer SR types from call operands/result.
        const args_slice = t.instrs.val_list_pool.slice(p.args);
        for (args_slice) |vid| try params_sr_list.append(self.srTypeOfValue(vid));
        ret_sr = p.ty;
        is_var = false; // unknown: assume non-variadic
    }
    params_sr = params_sr_list.items;

    // Lower with classifier: same logic as emitExternDecls
    // Worst case: sret slot (+1) and each param expands to two scalars.
    var lowered_params = try self.gpa.alloc(mlir.Type, params_sr.len * 2 + 2);
    defer self.gpa.free(lowered_params);
    var argAttrs = try self.gpa.alloc(mlir.Attribute, params_sr.len * 2 + 2);
    defer self.gpa.free(argAttrs);
    var n_args: usize = 0;

    const ret_kind = self.context.type_store.getKind(ret_sr);
    const ret_no_result = switch (ret_kind) {
        .Void, .Noreturn => true,
        else => false,
    };
    var ret_type: mlir.Type = self.void_ty;
    var retClass: abi.AbiClass = undefined;

    if (ret_no_result) {
        ret_type = self.void_ty;
    } else {
        retClass = abi.abiClassifyX64SysV(self, ret_sr, true);
        switch (retClass.kind) {
            .IndirectSRet => {
                lowered_params[n_args] = self.llvm_ptr_ty;
                const stTy = try self.llvmTypeOf(ret_sr);
                argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &[_]mlir.NamedAttribute{
                    self.named("llvm.sret", mlir.Attribute.typeAttrGet(stTy)),
                    self.named("llvm.align", mlir.Attribute.integerAttrGet(self.i64_ty, retClass.alignment)),
                });
                n_args += 1;
                ret_type = self.void_ty;
            },
            .DirectScalar => ret_type = retClass.scalar0.?,
            .DirectPair => {
                const pairTy = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{
                    retClass.scalar0.?, retClass.scalar1.?,
                }, false);
                ret_type = pairTy;
            },
            else => unreachable,
        }
    }

    for (params_sr) |psr| {
        const cls = abi.abiClassifyX64SysV(self, psr, false);
        switch (cls.kind) {
            .IndirectByVal => {
                lowered_params[n_args] = self.llvm_ptr_ty;
                const stTy = try self.llvmTypeOf(psr);
                argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &[_]mlir.NamedAttribute{
                    self.named("llvm.byval", mlir.Attribute.typeAttrGet(stTy)),
                    self.named("llvm.align", mlir.Attribute.integerAttrGet(self.i64_ty, cls.alignment)),
                });
                n_args += 1;
            },
            .DirectScalar => {
                lowered_params[n_args] = cls.scalar0.?;
                argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &.{});
                n_args += 1;
            },
            .DirectPair => {
                lowered_params[n_args] = cls.scalar0.?;
                argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &.{});
                n_args += 1;
                lowered_params[n_args] = cls.scalar1.?;
                argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &.{});
                n_args += 1;
            },
            else => unreachable,
        }
    }

    const fty = mlir.LLVM.getLLVMFunctionType(ret_type, lowered_params[0..n_args], is_var);
    const argAttrsArray = mlir.Attribute.arrayAttrGet(self.mlir_ctx, argAttrs[0..n_args]);
    const attrs = [_]mlir.NamedAttribute{
        self.named("sym_name", self.strAttr(name)),
        self.named("function_type", mlir.Attribute.typeAttrGet(fty)),
        self.named("arg_attrs", argAttrsArray),
        self.named("sym_visibility", self.strAttr("private")),
    };
    const region = mlir.Region.create();
    const fnop = self.buildOp("llvm.func", EmitOpArgs{
        .attributes = &attrs,
        .regions = &.{region},
    });
    var body = self.module.getBody();
    body.appendOwnedOperation(fnop);

    const param_types_copy = try self.gpa.alloc(mlir.Type, n_args);
    std.mem.copyForwards(mlir.Type, param_types_copy, lowered_params[0..n_args]);
    const info: FuncInfo = .{
        .op = fnop,
        .is_variadic = is_var,
        .n_formals = params_sr.len,
        .ret_type = ret_type,
        .param_types = param_types_copy,
        .owns_param_types = true,
        .dbg_subprogram = null,
    };
    _ = try self.func_syms.put(callee_id, info);
    return info;
}

/// Make sure the lowered argument list can satisfy the callee's parameter types.
fn ensureCallArgType(
    self: *Codegen,
    value: mlir.Value,
    src_sr: types.TypeId,
    want_ty: mlir.Type,
) !mlir.Value {
    if (value.getType().equal(want_ty)) return value;

    const have_ty = value.getType();

    if (have_ty.isAInteger() and want_ty.isAInteger()) {
        const fw = try cast.intOrFloatWidth(have_ty);
        const tw = try cast.intOrFloatWidth(want_ty);
        if (fw == tw) return value;
        if (fw > tw) {
            return self.emitUnaryValueOp("llvm.trunc", value, want_ty);
        } else {
            const signed_from = self.isSignedInt(src_sr);
            const op_name = if (signed_from) "llvm.sext" else "llvm.zext";
            return self.emitUnaryValueOp(op_name, value, want_ty);
        }
    }

    if (have_ty.isAFloat() and want_ty.isAFloat()) {
        const fw = try cast.intOrFloatWidth(have_ty);
        const tw = try cast.intOrFloatWidth(want_ty);
        if (fw == tw) return value;
        const op_name = if (fw > tw) "llvm.fptrunc" else "llvm.fpext";
        return self.emitUnaryValueOp(op_name, value, want_ty);
    }

    if (mlir.LLVM.isLLVMPointerType(have_ty) and mlir.LLVM.isLLVMPointerType(want_ty)) {
        return self.emitUnaryValueOp("llvm.bitcast", value, want_ty);
    }

    return value;
}

/// Build the SSA operand list when calling a known function, handling ABI lowering.
fn prepareInternalCallArgs(
    self: *Codegen,
    src_vals: []const mlir.Value,
    src_sr: []const types.TypeId,
    finfo: FuncInfo,
) ![]mlir.Value {
    const param_types = finfo.param_types;
    var args = try self.gpa.alloc(mlir.Value, src_vals.len);
    var i: usize = 0;
    while (i < src_vals.len) : (i += 1) {
        const want_ty = if (i < param_types.len) param_types[i] else src_vals[i].getType();
        var passv = src_vals[i];
        if (!passv.getType().equal(want_ty)) {
            if (mlir.LLVM.isLLVMPointerType(want_ty) and !mlir.LLVM.isLLVMPointerType(passv.getType())) {
                const tmp = self.spillAgg(passv, passv.getType(), 0);
                passv = try self.ensureCallArgType(tmp, src_sr[i], want_ty);
            } else {
                passv = try self.ensureCallArgType(passv, src_sr[i], want_ty);
            }
        }
        args[i] = passv;
    }
    return args;
}

/// Emit an MLIR constant for the signed/unsigned integer `p`.
fn emitConstInt(self: *Codegen, p: tir.Rows.ConstInt) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const ty = try self.llvmTypeOf(p.ty);
    if (ty.isAFloat()) {
        return self.constFloat(ty, @floatFromInt(p.value));
    }
    return self.constInt(ty, p.value);
}

/// Emit an MLIR constant floating-point value.
fn emitConstFloat(self: *Codegen, p: tir.Rows.ConstFloat) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const ty = try self.llvmTypeOf(p.ty);
    return self.constFloat(ty, p.value);
}

/// Emit an MLIR boolean constant from `p`.
fn emitConstBool(self: *Codegen, p: tir.Rows.ConstBool) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    return self.constBool(p.value);
}

/// Emit an MLIR null pointer constant for `p`.
fn emitConstNull(self: *Codegen, p: tir.Rows.ConstNull) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const ty = try self.llvmTypeOf(p.ty);
    const zero_val = self.emitOp("llvm.mlir.zero", EmitOpArgs{
        .results = &.{ty},
    });
    const sr_kind = self.context.type_store.getKind(p.ty);
    if (sr_kind == .Optional and !self.context.type_store.isOptionalPointer(p.ty)) {
        const flag = self.constBool(false);
        const v = self.insertAt(zero_val, flag, &.{0});
        return v;
    }
    return zero_val;
}

/// Emit an MLIR `undef` value specializing to the target type.
fn emitConstUndef(self: *Codegen, p: tir.Rows.ConstUndef) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const ty = try self.llvmTypeOf(p.ty);
    return self.emitOp("llvm.mlir.undef", EmitOpArgs{
        .results = &.{ty},
    });
}

/// Emit an MLIR constant string filled with `p`’s text data.
fn emitConstString(self: *Codegen, p: tir.Rows.ConstString) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const str_text = self.context.interner.get(p.text);
    var ptr_op = try self.constStringPtr(str_text);
    const ptr_val = ptr_op.getResult(0);

    const string_ty = try self.llvmTypeOf(p.ty);
    if (mlir.LLVM.isLLVMPointerType(string_ty)) return ptr_val;

    const len_val = self.constInt(self.i64_ty, @intCast(str_text.len));
    var agg = self.undefOf(string_ty);
    agg = self.insertAt(agg, ptr_val, &.{0});
    agg = self.insertAt(agg, len_val, &.{1});
    return agg;
}

/// Emit a complex-number binary op (the caller is responsible for location).
fn emitComplexBinOp(self: *Codegen, name: []const u8, p: tir.Rows.Bin2) !mlir.Value {
    const lhs = self.getVal(p.lhs);
    const rhs = self.getVal(p.rhs);
    const cty = try self.llvmTypeOf(p.ty);
    return self.emitOp(name, EmitOpArgs{
        .operands = &.{ lhs, rhs },
        .results = &.{cty},
    });
}

/// Emit either a complex-number operation or a generic arithmetic op.
fn emitBinArithWithComplex(
    self: *Codegen,
    p: tir.Rows.Bin2,
    comptime op_kind: BinArithOp,
    complex_name: []const u8,
) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    if (self.srKind(p.ty) == .Complex) {
        return self.emitComplexBinOp(complex_name, p);
    }
    return self.binArith(op_kind, p);
}

/// Emit the MLIR representation of integer/floating point addition.
fn emitAdd(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    return self.emitBinArithWithComplex(p, .add, "complex.add");
}

/// Emit subtraction for the binary pair `p`.
fn emitSub(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    return self.emitBinArithWithComplex(p, .sub, "complex.sub");
}

/// Emit multiplication for `p`.
fn emitMul(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    return self.emitBinArithWithComplex(p, .mul, "complex.mul");
}

/// Emit division for `p`.
fn emitDiv(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    if (self.context.type_store.getKind(p.ty) == .Complex) {
        const lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;
        const cty = try self.llvmTypeOf(p.ty);
        return self.emitOp("complex.div", EmitOpArgs{
            .operands = &.{ lhs, rhs },
            .results = &.{cty},
        });
    }
    const lhs = self.value_map.get(p.lhs).?;
    const rhs = self.value_map.get(p.rhs).?;
    const ty = try self.llvmTypeOf(p.ty);
    const signed = !self.isUnsigned(self.srTypeOfValue(p.lhs));
    return self.arithDiv(lhs, rhs, ty, signed);
}

/// Emit modulo/remainder operations for `p`.
fn emitMod(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const lhs = self.value_map.get(p.lhs).?;
    const rhs = self.value_map.get(p.rhs).?;
    const ty = try self.llvmTypeOf(p.ty);
    const signed = !self.isUnsigned(self.srTypeOfValue(p.lhs));
    return self.arithRem(lhs, rhs, ty, signed);
}

/// Emit a left shift instruction for `p`.
fn emitShl(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const lhs = self.value_map.get(p.lhs).?;
    const rhs = self.value_map.get(p.rhs).?;
    const ty = try self.llvmTypeOf(p.ty);
    return self.arithShl(lhs, rhs, ty);
}

/// Emit a right shift instruction for `p`.
fn emitShr(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const lhs = self.value_map.get(p.lhs).?;
    const rhs = self.value_map.get(p.rhs).?;
    const ty = try self.llvmTypeOf(p.ty);
    const signed = !self.isUnsigned(self.srTypeOfValue(p.lhs));
    return self.arithShr(lhs, rhs, ty, signed);
}

/// Emit a bitcast for the single-operand `p`.
fn emitCastBit(self: *Codegen, p: tir.Rows.Un1) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const to_ty = try self.llvmTypeOf(p.ty);
    const from_v = self.value_map.get(p.value).?;
    const from_ty = from_v.getType();
    if (from_ty.equal(to_ty)) return from_v;
    if (self.isUndefValue(from_v)) return self.undefOf(to_ty);

    const src_is_ptr = mlir.LLVM.isLLVMPointerType(from_ty);
    const dst_is_ptr = mlir.LLVM.isLLVMPointerType(to_ty);
    const needs_spill = mlir.LLVM.isLLVMStructType(from_ty) or
        mlir.LLVM.isLLVMStructType(to_ty) or
        (src_is_ptr != dst_is_ptr);

    if (needs_spill) {
        const spill = self.spillAgg(from_v, from_ty, 0);
        return self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{spill},
            .results = &.{to_ty},
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
    }

    return self.emitUnaryValueOp("llvm.bitcast", from_v, to_ty);
}

/// Emit the normal cast instruction (usually zero/sign extend or truncate).
fn emitCastNormalInstr(self: *Codegen, p: tir.Rows.Un1) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const to_ty = try self.llvmTypeOf(p.ty);
    const from_v_opt = self.value_map.get(p.value);
    if (from_v_opt == null) {
        // Produce a diagnostic at the original source location for debugging.
        if (!p.loc.isNone()) {
            const loc_id = p.loc.unwrap();
            const loc_rec = self.context.loc_store.get(loc_id);
            try self.context.diags.addError(loc_rec, .tir_codegen_missing_operand, .{});
        }
        return error.CompilationFailed;
    }
    const from_v = from_v_opt.?;
    const src_sr = self.srTypeOfValue(p.value);
    const val = try cast.emitCastNormal(self, p.ty, to_ty, from_v, src_sr);
    return val;
}

/// Emit a saturating cast for `p`.
fn emitCastSaturate(self: *Codegen, p: tir.Rows.Un1) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const from_v = self.value_map.get(p.value).?;
    const src_sr = self.srTypeOfValue(p.value);
    const val = try cast.emitCast(self, .CastSaturate, p.ty, src_sr, from_v);
    return val;
}

/// Emit a wrapping cast when truncating down to a narrower type.
fn emitCastWrap(self: *Codegen, comptime x: tir.OpKind, p: tir.Rows.Un1) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const from_v = self.value_map.get(p.value).?;
    const src_sr = self.srTypeOfValue(p.value);
    const val = try cast.emitCast(self, x, p.ty, src_sr, from_v);
    return val;
}

/// Append `op` into the current function’s entry block.
fn appendInFuncEntry(self: *Codegen, op: mlir.Operation) void {
    var entry = self.func_entry_block orelse self.cur_block.?;
    const term = entry.getTerminator();
    if (!term.isNull()) entry.insertOwnedOperationBefore(term, op) else entry.appendOwnedOperation(op);
}

/// Emit an LLVM `alloca` for the stack allocation described by `p`.
fn emitAlloca(self: *Codegen, p: tir.Rows.Alloca) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    var elem_ty: mlir.Type = self.i8_ty;
    switch (self.context.type_store.getKind(p.ty)) {
        .Ptr => {
            const ptr_row = self.context.type_store.get(.Ptr, p.ty);
            if (self.context.type_store.getKind(ptr_row.elem) == .Tensor) {
                try self.tensor_slots.put(p.result, mlir.Value.empty());
                return self.llvmNullPtr();
            }
            if (self.context.type_store.getKind(ptr_row.elem) == .Complex) {
                const c = self.context.type_store.get(.Complex, ptr_row.elem);
                const ety = try self.llvmTypeOf(c.elem);
                elem_ty = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ ety, ety }, false);
            } else {
                elem_ty = try self.llvmTypeOf(ptr_row.elem);
            }
        },
        else => {},
    }

    // Count
    const one = self.getI64OneInEntry();
    const count_v: mlir.Value = if (!p.count.isNone())
        self.value_map.get(p.count.unwrap()).?
    else
        one;

    const alloca = self.buildOp("llvm.alloca", EmitOpArgs{
        .operands = &.{count_v},
        .results = &.{self.llvm_ptr_ty},
        .attributes = &.{self.named("elem_type", mlir.Attribute.typeAttrGet(elem_ty))},
    });

    // Heuristic: hoist fixed-size locals (no VLA) to entry.
    const should_hoist = p.count.isNone();
    if (should_hoist) self.appendInFuncEntry(alloca) else self.append(alloca); // dynamic-size: leave where it executes

    return alloca.getResult(0);
}

/// Emit the MLIR instructions for a load operation `p`.
fn emitLoad(self: *Codegen, p: tir.Rows.Load, t: *tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    if (try self.tryEmitTensorElementLoad(p, t)) |elem| return elem;
    var ptr_val_opt = self.value_map.get(p.ptr);
    if (ptr_val_opt == null) {
        // Try materializing or folding known-constant pointers directly to values as a last resort.
        if (self.def_instr.get(p.ptr)) |pid| {
            const kdef = t.kind(pid);
            const res_ty = try self.llvmTypeOf(p.ty);
            switch (kdef) {
                .ConstFloat => {
                    const rowf = t.instrs.get(.ConstFloat, pid);
                    return self.constFloat(res_ty, rowf.value);
                },
                .ConstInt => {
                    const rowi = t.instrs.get(.ConstInt, pid);
                    return self.constInt(res_ty, @intCast(rowi.value));
                },
                .ConstBool => {
                    const rowb = t.instrs.get(.ConstBool, pid);
                    return self.constBool(rowb.value);
                },
                else => {},
            }
            // Otherwise, attempt on-demand emission
            _ = try self.emitInstr(pid, t);
            ptr_val_opt = self.value_map.get(p.ptr);
        }
        if (ptr_val_opt == null) {
            // Last-resort: treat as value load and synthesize zero of result type.
            return self.zeroOf(try self.llvmTypeOf(p.ty));
        }
    }
    const ptr = ptr_val_opt.?;
    if (self.context.type_store.getKind(p.ty) == .Tensor) {
        return self.tensor_slots.get(p.ptr) orelse
            std.debug.panic("tensor load before store", .{});
    }
    if (self.context.type_store.getKind(p.ty) == .Complex) {
        const c = self.context.type_store.get(.Complex, p.ty);
        const elem_ty = try self.llvmTypeOf(c.elem);
        const storage_ty = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ elem_ty, elem_ty }, false);
        const agg = self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{ptr},
            .results = &.{storage_ty},
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
        const re = self.extractAt(agg, elem_ty, &.{0});
        const im = self.extractAt(agg, elem_ty, &.{1});
        const res_ty = try self.llvmTypeOf(p.ty);
        const mk = self.emitOp("complex.create", EmitOpArgs{
            .operands = &.{ re, im },
            .results = &.{res_ty},
        });
        return mk;
    } else {
        const res_ty = try self.llvmTypeOf(p.ty);
        // If the operand is not a pointer (opaque ptr model), treat it as a value and coerce if needed.
        if (!mlir.LLVM.isLLVMPointerType(ptr.getType())) {
            // Pass-through/coerce
            if (ptr.getType().equal(res_ty)) return ptr;
            const src_sr = self.srTypeOfValue(p.ptr);
            return try self.coerceOnBranch(ptr, res_ty, p.ty, src_sr);
        }
        return self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{ptr},
            .results = &.{res_ty},
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
    }
}

/// Emit the MLIR instructions for the store operation described by `p`.
fn emitStore(self: *Codegen, p: tir.Rows.Store, t: *tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const v = self.value_map.get(p.value).?;
    if (try self.handleTensorElementStore(p, v, t)) return .empty();
    const ptr_opt = self.value_map.get(p.ptr);
    if (ptr_opt == null) {
        return error.CompileError;
    }
    const ptr = ptr_opt.?;
    const v_sr = self.srTypeOfValue(p.value);
    const ptr_sr = self.srTypeOfValue(p.ptr);
    if (self.context.type_store.getKind(ptr_sr) == .Ptr and self.context.type_store.getKind(self.context.type_store.get(.Ptr, ptr_sr).elem) == .Tensor) {
        try self.tensor_slots.put(p.ptr, v);
        return .empty();
    }
    if (self.context.type_store.getKind(v_sr) == .Complex) {
        const c = self.context.type_store.get(.Complex, v_sr);
        const elem_ty = try self.llvmTypeOf(c.elem);
        // Spill complex into {elem, elem}
        const reop = self.emitUnaryValueOp("complex.re", v, elem_ty);
        const imop = self.emitUnaryValueOp("complex.im", v, elem_ty);
        const storage_ty = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ elem_ty, elem_ty }, false);
        var acc = self.undefOf(storage_ty);
        acc = self.insertAt(acc, reop, &.{0});
        acc = self.insertAt(acc, imop, &.{1});
        _ = self.emitOp("llvm.store", EmitOpArgs{
            .operands = &.{ acc, ptr },
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
    } else {
        _ = self.emitOp("llvm.store", EmitOpArgs{
            .operands = &.{ v, ptr },
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
    }
    return .empty();
}

/// Emit a GEP instruction and cache the resulting pointer value.
fn emitGepInstr(self: *Codegen, ins_id: tir.InstrId, t: *tir.TIR) !mlir.Value {
    if (try self.tryEmitTensorGep(ins_id, t)) |special| return special;

    const p = t.instrs.get(.Gep, ins_id);
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const base = self.value_map.get(p.base).?;
    const base_sr = self.srTypeOfValue(p.base);
    var elem_mlir: mlir.Type = self.i8_ty;
    if (self.context.type_store.getKind(base_sr) == .Ptr) {
        const ptr_row = self.context.type_store.get(.Ptr, base_sr);
        elem_mlir = try self.llvmTypeOf(ptr_row.elem);
    }

    const index_ids = t.instrs.gep_pool.slice(p.indices);
    var indices_data = try self.gpa.alloc(tir.Rows.GepIndex, index_ids.len);
    defer self.gpa.free(indices_data);
    for (index_ids, 0..) |id, i| {
        indices_data[i] = t.instrs.GepIndex.get(id);
    }
    return self.emitGep(base, elem_mlir, indices_data);
}

/// Emit an LLVM global address constant for `p`.
fn emitGlobalAddr(self: *Codegen, p: tir.Rows.GlobalAddr) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const name = self.context.interner.get(p.name);
    const ty = try self.llvmTypeOf(p.ty);
    if (self.global_addr_cache.get(name)) |cached| return cached;

    const gsym = mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(name));
    const addr = self.buildOp("llvm.mlir.addressof", EmitOpArgs{
        .results = &.{ty},
        .attributes = &.{self.named("global_name", gsym)},
    });
    var entry_block = if (self.func_entry_block) |eb|
        eb
    else blk2: {
        std.debug.assert(self.cur_block != null);
        break :blk2 self.cur_block.?;
    };
    const term = entry_block.getTerminator();
    if (!term.isNull()) {
        entry_block.insertOwnedOperationBefore(term, addr);
    } else {
        entry_block.appendOwnedOperation(addr);
    }

    const value = addr.getResult(0);
    try self.global_addr_cache.put(name, value);
    return value;
}

/// Emit a tuple construction operation for `p`.
fn emitTupleMake(self: *Codegen, p: tir.Rows.TupleMake, t: *const tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const tup_ty = try self.llvmTypeOf(p.ty);
    const tuple_row = self.context.type_store.get(.Tuple, p.ty);
    const elem_srs = self.context.type_store.type_pool.slice(tuple_row.elems);
    var acc = self.zeroOf(tup_ty);
    const elems = t.instrs.value_pool.slice(p.elems);
    std.debug.assert(elem_srs.len == elems.len);
    for (elems, 0..) |vid, i| {
        const elem_sr = elem_srs[@intCast(i)];
        const elem_mlir = try self.llvmTypeOf(elem_sr);
        var v = self.value_map.get(vid).?;
        const src_sr = self.srTypeOfValue(vid);
        v = try self.coerceOnBranch(v, elem_mlir, elem_sr, src_sr);
        acc = self.insertAt(acc, v, &.{@intCast(i)});
    }
    return acc;
}

/// Emit the runtime representation for a range literal.
fn emitRangeMake(self: *Codegen, p: tir.Rows.RangeMake) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    // Materialize as struct<i64,i64> { start, end } (inclusive handled by consumers)
    const i64t = self.i64_ty;
    const pairTy = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ i64t, i64t }, false);
    var acc = self.zeroOf(pairTy);
    const s = self.value_map.get(p.start).?;
    const e = self.value_map.get(p.end).?;
    const s64 = try self.coerceOnBranch(s, i64t, self.context.type_store.tI64(), self.srTypeOfValue(p.start));
    const e64 = try self.coerceOnBranch(e, i64t, self.context.type_store.tI64(), self.srTypeOfValue(p.end));
    acc = self.insertAt(acc, s64, &.{0});
    acc = self.insertAt(acc, e64, &.{1});
    return acc;
}

/// Emit a broadcast operation for SIMD values described by `p`.
fn emitBroadcast(self: *Codegen, p: tir.Rows.Broadcast) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const vector_ty = try self.llvmTypeOf(p.ty);
    const scalar_val = self.value_map.get(p.value).?;
    return self.emitOp("vector.broadcast", EmitOpArgs{
        .operands = &.{scalar_val},
        .results = &.{vector_ty},
    });
}

/// Emit a SIMD vector literal from `p`.
fn emitSimdMake(self: *Codegen, p: tir.Rows.ArrayMake, t: *const tir.TIR) !mlir.Value {
    const simd_ty = self.context.type_store.get(.Simd, p.ty);
    const lanes: usize = @intCast(simd_ty.lanes);
    const elems = t.instrs.value_pool.slice(p.elems);
    std.debug.assert(elems.len == lanes);

    const elem_mlir = try self.llvmTypeOf(simd_ty.elem);
    const vec_ty = try self.llvmTypeOf(p.ty);
    var operands = try self.gpa.alloc(mlir.Value, elems.len);
    defer self.gpa.free(operands);

    for (elems, 0..) |vid, i| {
        var v = self.value_map.get(vid).?;
        if (!v.getType().equal(elem_mlir)) {
            v = try self.coerceOnBranch(v, elem_mlir, simd_ty.elem, self.srTypeOfValue(vid));
        }
        operands[i] = v;
    }

    return self.emitOp("vector.from_elements", EmitOpArgs{
        .operands = operands,
        .results = &.{vec_ty},
    });
}

/// Emit a tensor literal materializing `p`’s values into `t`.
fn emitTensorMake(self: *Codegen, p: tir.Rows.ArrayMake, t: *const tir.TIR) !mlir.Value {
    const tensor_sr = self.context.type_store.get(.Tensor, p.ty);
    const tensor_ty = try self.llvmTypeOf(p.ty);
    const elems = t.instrs.value_pool.slice(p.elems);
    const scalar_elem_mlir = try self.llvmTypeOf(tensor_sr.elem);

    var total: usize = 1;
    var dim_idx: usize = 0;
    while (dim_idx < tensor_sr.rank) : (dim_idx += 1) {
        total *= @intCast(tensor_sr.dims[dim_idx]);
    }
    std.debug.assert(total == elems.len);

    var operands = try self.gpa.alloc(mlir.Value, elems.len);
    defer self.gpa.free(operands);

    for (elems, 0..) |vid, i| {
        var v = self.value_map.get(vid).?;
        if (!v.getType().equal(scalar_elem_mlir)) {
            const src_sr = self.srTypeOfValue(vid);
            v = try self.coerceOnBranch(v, scalar_elem_mlir, tensor_sr.elem, src_sr);
        }
        operands[i] = v;
    }

    return self.emitOp("tensor.from_elements", EmitOpArgs{
        .operands = operands,
        .results = &.{tensor_ty},
    });
}

/// Emit the general array literal building logic for `p`.
fn emitArrayMake(self: *Codegen, p: tir.Rows.ArrayMake, t: *const tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const result_kind = self.context.type_store.getKind(p.ty);
    switch (result_kind) {
        .Simd => return self.emitSimdMake(p, t),
        .Tensor => return self.emitTensorMake(p, t),
        else => {},
    }
    const arr_ty = try self.llvmTypeOf(p.ty);
    // Determine element MLIR type from SR array element
    const arr_sr = self.context.type_store.get(.Array, p.ty);
    const elem_mlir = try self.llvmTypeOf(arr_sr.elem);
    var acc = self.zeroOf(arr_ty);
    // Array elements are stored in value_pool
    const elems = t.instrs.value_pool.slice(p.elems);
    for (elems, 0..) |vid, i| {
        var v = self.value_map.get(vid).?;
        // Best-effort: coerce value to the array element type if it doesn't match
        if (!v.getType().equal(elem_mlir)) {
            v = try self.coerceOnBranch(v, elem_mlir, arr_sr.elem, self.srTypeOfValue(vid));
        }
        acc = self.insertAt(acc, v, &.{@as(i64, @intCast(i))});
    }
    return acc;
}

/// Emit the index access operation `p`.
fn emitIndex(self: *Codegen, p: tir.Rows.Index, t: *tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const base = self.value_map.get(p.base).?;
    const res_ty = try self.llvmTypeOf(p.ty);
    const res_sr_kind = self.context.type_store.getKind(p.ty);
    const base_sr_ty = self.srTypeOfValue(p.base);

    // Slicing: result is a slice type ([]T). Build {ptr,len} from base + range.
    if (self.context.type_store.getKind(base_sr_ty) == .Tensor) {
        const base_tensor = self.context.type_store.get(.Tensor, base_sr_ty);
        const base_rank: usize = @intCast(base_tensor.rank);
        const idx_raw = self.value_map.get(p.index).?;
        const idx_val = try self.ensureIndexValue(idx_raw);

        if (base_rank == 1 and res_sr_kind != .Tensor and res_sr_kind != .Slice) {
            // Rank-1 tensor indexed by scalar -> tensor.extract returning element value.
            return self.emitOp("tensor.extract", EmitOpArgs{
                .operands = &.{ base, idx_val },
                .results = &.{res_ty},
            });
        }

        std.debug.assert(res_sr_kind == .Tensor);
        const res_tensor = self.context.type_store.get(.Tensor, p.ty);
        const new_rank: usize = @intCast(res_tensor.rank);
        std.debug.assert(new_rank + 1 == base_rank);

        const elem_mlir = try self.llvmTypeOf(base_tensor.elem);

        var slice_dims_storage: [types.max_tensor_rank]i64 = undefined;
        var i: usize = 0;
        slice_dims_storage[0] = 1;
        while (i + 1 < base_rank) : (i += 1) {
            slice_dims_storage[i + 1] = @intCast(base_tensor.dims[i + 1]);
        }
        const slice_dims = slice_dims_storage[0..base_rank];
        const slice_ty = mlir.Type.getRankedTensorType(@intCast(base_rank), slice_dims, elem_mlir, mlir.Attribute.getNull());

        var static_offsets_buf: [types.max_tensor_rank]i64 = undefined;
        var static_sizes_buf: [types.max_tensor_rank]i64 = undefined;
        var static_strides_buf: [types.max_tensor_rank]i64 = undefined;
        static_offsets_buf[0] = mlir.Type.getDynamicStrideOrOffset();
        static_sizes_buf[0] = 1;
        static_strides_buf[0] = 1;
        var j: usize = 1;
        while (j < base_rank) : (j += 1) {
            static_offsets_buf[j] = 0;
            static_sizes_buf[j] = @intCast(base_tensor.dims[j]);
            static_strides_buf[j] = 1;
        }
        const offsets_attr = mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, static_offsets_buf[0..base_rank]);
        const sizes_attr = mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, static_sizes_buf[0..base_rank]);
        const strides_attr = mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, static_strides_buf[0..base_rank]);

        const operand_segment = mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ 1, 1, 0, 0 });

        var extract_attrs = [_]mlir.NamedAttribute{
            self.named("static_offsets", offsets_attr),
            self.named("static_sizes", sizes_attr),
            self.named("static_strides", strides_attr),
            self.named("operand_segment_sizes", operand_segment),
        };

        var extract_operands = [_]mlir.Value{ base, idx_val };
        const slice = self.appendOp("tensor.extract_slice", EmitOpArgs{
            .operands = &extract_operands,
            .results = &.{slice_ty},
            .attributes = &extract_attrs,
        });

        const collapse_result_ty = res_ty;
        const reassoc_rank = new_rank;
        var reassoc_groups = try self.gpa.alloc(mlir.Attribute, reassoc_rank);
        defer self.gpa.free(reassoc_groups);
        const i64_ty = mlir.Type.getSignlessIntegerType(self.mlir_ctx, 64);

        var first_group_elems = [_]mlir.Attribute{
            mlir.Attribute.integerAttrGet(i64_ty, 0),
            mlir.Attribute.integerAttrGet(i64_ty, 1),
        };
        reassoc_groups[0] = mlir.Attribute.arrayAttrGet(self.mlir_ctx, first_group_elems[0..]);
        var g: usize = 1;
        while (g < reassoc_rank) : (g += 1) {
            const orig_dim: i64 = @intCast(g + 1);
            var elem_attr = [_]mlir.Attribute{mlir.Attribute.integerAttrGet(i64_ty, orig_dim)};
            reassoc_groups[g] = mlir.Attribute.arrayAttrGet(self.mlir_ctx, elem_attr[0..]);
        }
        const reassoc_attr = mlir.Attribute.arrayAttrGet(self.mlir_ctx, reassoc_groups);

        var collapse_attrs = [_]mlir.NamedAttribute{self.named("reassociation", reassoc_attr)};
        return self.emitOp("tensor.collapse_shape", EmitOpArgs{
            .operands = &.{slice.getResult(0)},
            .results = &.{collapse_result_ty},
            .attributes = &collapse_attrs,
        });
    }

    if (self.context.type_store.getKind(base_sr_ty) == .Simd) {
        const idx_val = try self.ensureIndexValue(self.value_map.get(p.index).?);
        const static_pos_attr = mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, &.{mlir.Type.getDynamicSize()});
        return self.emitOp("vector.extract", EmitOpArgs{
            .operands = &.{ base, idx_val },
            .attributes = &.{self.named("static_position", static_pos_attr)},
            .results = &.{res_ty},
        });
    }

    if (res_sr_kind == .Slice or res_sr_kind == .String) {
        // Peel optional CastNormal from the index to find builtin.range.make
        var idx_vid: tir.ValueId = p.index;
        if (self.def_instr.get(idx_vid)) |iid1| {
            const k1 = t.kind(iid1);
            if (k1 == .CastNormal) {
                const crow = t.instrs.get(.CastNormal, iid1);
                idx_vid = crow.value;
            }
        }
        var start_vid: tir.ValueId = undefined;
        var end_vid: tir.ValueId = undefined;
        var incl_vid: tir.ValueId = undefined;
        if (self.def_instr.get(idx_vid)) |iid2| {
            const k2 = t.kind(iid2);
            if (k2 == .RangeMake) {
                const r = t.instrs.get(.RangeMake, iid2);
                start_vid = r.start;
                end_vid = r.end;
                incl_vid = r.inclusive;
            } else if (k2 == .Call) {
                const call = t.instrs.get(.Call, iid2);
                const name = t.instrs.strs.get(call.callee);
                if (std.mem.eql(u8, name, "builtin.range.make")) {
                    const args = t.instrs.val_list_pool.slice(call.args);
                    if (args.len >= 3) {
                        start_vid = args[0];
                        end_vid = args[1];
                        incl_vid = args[2];
                    } else {
                        return self.zeroOf(res_ty);
                    }
                } else {
                    return self.zeroOf(res_ty);
                }
            } else {
                return self.zeroOf(res_ty);
            }
        } else {
            return self.zeroOf(res_ty);
        }

        // Compute data pointer for the slice
        var data_ptr: mlir.Value = undefined;
        var elem_sr: types.TypeId = undefined;
        switch (self.context.type_store.getKind(base_sr_ty)) {
            .Array => {
                const arr = self.context.type_store.get(.Array, base_sr_ty);
                elem_sr = arr.elem;
                const arr_mlir = try self.llvmTypeOf(base_sr_ty);
                // Spill SSA array to memory to get a pointer
                const base_ptr = self.spillAgg(base, arr_mlir, 0);
                const idxs = [_]tir.Rows.GepIndex{
                    .{ .Const = 0 },
                    .{ .Value = start_vid },
                };
                data_ptr = try self.emitGep(base_ptr, arr_mlir, &idxs);
            },
            .Slice => {
                // Base is already a slice: extract ptr and compute ptr + start
                elem_sr = self.context.type_store.get(.Slice, base_sr_ty).elem;
                const ptr0 = self.extractAt(base, self.llvm_ptr_ty, &.{0});
                const idxs = [_]tir.Rows.GepIndex{.{ .Value = start_vid }};
                const elem_mlir = try self.llvmTypeOf(elem_sr);
                data_ptr = try self.emitGep(ptr0, elem_mlir, &idxs);
            },
            .DynArray => {
                elem_sr = self.context.type_store.get(.DynArray, base_sr_ty).elem;
                const elem_ptr_sr = self.context.type_store.mkPtr(elem_sr, false);
                const ptr_ty_mlir = try self.llvmTypeOf(elem_ptr_sr);
                const ptr0 = self.extractAt(base, ptr_ty_mlir, &.{0});
                const idxs = [_]tir.Rows.GepIndex{.{ .Value = start_vid }};
                const elem_mlir = try self.llvmTypeOf(elem_sr);
                data_ptr = try self.emitGep(ptr0, elem_mlir, &idxs);
            },
            .Ptr => {
                const ptr_row = self.context.type_store.get(.Ptr, base_sr_ty);
                elem_sr = ptr_row.elem;
                const elem_mlir = try self.llvmTypeOf(elem_sr);
                const idxs = [_]tir.Rows.GepIndex{.{ .Value = start_vid }};
                data_ptr = try self.emitGep(base, elem_mlir, &idxs);
            },
            .String => {
                elem_sr = self.context.type_store.tU8();
                const ptr0 = self.extractAt(base, self.llvm_ptr_ty, &.{0});
                const idxs = [_]tir.Rows.GepIndex{.{ .Value = start_vid }};
                const elem_mlir = self.i8_ty;
                data_ptr = try self.emitGep(ptr0, elem_mlir, &idxs);
            },
            else => return self.zeroOf(res_ty),
        }

        // Compute length: (end - start) + (inclusive ? 1 : 0)
        const start_v = self.value_map.get(start_vid).?;
        const end_v = self.value_map.get(end_vid).?;
        const incl_v = self.value_map.get(incl_vid).?;
        const i64t = self.i64_ty;
        // Ensure operands are i64
        const start64 = try self.coerceOnBranch(start_v, i64t, self.context.type_store.tI64(), self.srTypeOfValue(start_vid));
        const end64 = try self.coerceOnBranch(end_v, i64t, self.context.type_store.tI64(), self.srTypeOfValue(end_vid));
        const diff = self.emitBinaryValueOp("llvm.sub", end64, start64, i64t, null);
        // zext bool to i64
        const z = self.emitUnaryValueOp("llvm.zext", incl_v, i64t);
        const len64 = self.emitBinaryValueOp("llvm.add", diff, z, i64t, null);

        // Build slice {ptr,len}
        var acc = self.zeroOf(res_ty);
        acc = self.insertAt(acc, data_ptr, &.{0});
        acc = self.insertAt(acc, len64, &.{1});
        return acc;
    }

    // Indexing into a slice value (in-SSA): extract ptr and load *(ptr+idx)
    if (!base.getType().equal(self.llvm_ptr_ty) and (self.context.type_store.getKind(base_sr_ty) == .Slice or self.context.type_store.getKind(base_sr_ty) == .DynArray) and res_sr_kind != .Slice) {
        const elem_mlir = res_ty; // result type is the element type
        const ptr0 = switch (self.context.type_store.getKind(base_sr_ty)) {
            .Slice => self.extractAt(base, self.llvm_ptr_ty, &.{0}),
            .DynArray => ptr_case: {
                const elem_ptr_ty = try self.llvmTypeOf(self.context.type_store.mkPtr(self.context.type_store.get(.DynArray, base_sr_ty).elem, false));
                break :ptr_case self.extractAt(base, elem_ptr_ty, &.{0});
            },
            else => unreachable,
        };
        const vptr = try self.emitGep(ptr0, elem_mlir, &.{.{ .Value = p.index }});
        return self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{vptr},
            .results = &.{res_ty},
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
    }

    if (base.getType().equal(self.llvm_ptr_ty)) {
        const base_sr = self.srTypeOfValue(p.base);
        var elem_mlir2: mlir.Type = res_ty; // fallback
        if (self.context.type_store.getKind(base_sr) == .Ptr) {
            const ptr_row2 = self.context.type_store.get(.Ptr, base_sr);
            elem_mlir2 = try self.llvmTypeOf(ptr_row2.elem);
        }
        const vptr = try self.emitGep(base, elem_mlir2, &.{.{ .Value = p.index }});
        return self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{vptr},
            .results = &.{res_ty},
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
    } else {
        const base_ty = base.getType();
        const tmp_ptr = self.spillAgg(base, base_ty, 0);
        const vptr = try self.emitGep(tmp_ptr, base_ty, &.{.{ .Value = p.index }});
        return self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{vptr},
            .results = &.{res_ty},
        });
    }
}

/// Expand a trailing tuple argument into individual elements for variadic calls.
fn expandVariadicArgTuple(
    self: *Codegen,
    value: mlir.Value,
    sr_ty: types.TypeId,
    out_vals: *ArrayList(mlir.Value),
    out_sr: *ArrayList(types.TypeId),
) anyerror!void {
    const kind = self.context.type_store.getKind(sr_ty);
    switch (kind) {
        .Tuple => {
            const tuple_row = self.context.type_store.get(.Tuple, sr_ty);
            const elems = self.context.type_store.type_pool.slice(tuple_row.elems);
            for (elems, 0..) |elem_sr, idx| {
                const elem_ty = try self.llvmTypeOf(elem_sr);
                const elem_val = self.extractAt(value, elem_ty, &.{@intCast(idx)});
                try self.expandVariadicArgTuple(elem_val, elem_sr, out_vals, out_sr);
            }
            return;
        },
        .String => {
            const ptr_sr = self.context.type_store.mkPtr(self.context.type_store.tU8(), false);
            const ptr_ty = try self.llvmTypeOf(ptr_sr);
            const ptr_val = self.extractAt(value, ptr_ty, &.{0});
            try out_vals.append(ptr_val);
            try out_sr.append(ptr_sr);
            return;
        },
        .Slice => {
            const slice_row = self.context.type_store.get(.Slice, sr_ty);
            const ptr_sr = self.context.type_store.mkPtr(slice_row.elem, false);
            const ptr_ty = try self.llvmTypeOf(ptr_sr);
            const ptr_val = self.extractAt(value, ptr_ty, &.{0});
            try out_vals.append(ptr_val);
            try out_sr.append(ptr_sr);
            return;
        },
        .DynArray => {
            const dyn = self.context.type_store.get(.DynArray, sr_ty);
            const ptr_sr = self.context.type_store.mkPtr(dyn.elem, false);
            const ptr_ty = try self.llvmTypeOf(ptr_sr);
            const ptr_val = self.extractAt(value, ptr_ty, &.{0});
            try out_vals.append(ptr_val);
            try out_sr.append(ptr_sr);
            return;
        },
        .Bool => {
            const ext = self.emitUnaryValueOp("arith.extui", value, self.i32_ty);
            try out_vals.append(ext);
            try out_sr.append(self.context.type_store.tI32());
            return;
        },
        else => {},
    }

    try out_vals.append(value);
    try out_sr.append(sr_ty);
}

/// Emit an MLIR call instruction for `p`, wiring argument lists and return types.
fn emitCall(self: *Codegen, p: tir.Rows.Call, t: *tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const callee_name = t.instrs.strs.get(p.callee);
    const callee_id = p.callee;

    var finfo = self.func_syms.get(callee_id);
    if (finfo == null) {
        // If callee is in this module, ensure a func.func decl; else extern (llvm.func)
        var is_local = false;
        const fids = t.funcs.func_pool.data.items;
        var ii: usize = 0;
        while (ii < fids.len) : (ii += 1) {
            const fname_id = t.funcs.Function.get(fids[ii]).name;
            if (fname_id.eq(callee_id)) {
                is_local = true;
                break;
            }
        }
        if (is_local) {
            _ = try self.ensureDeclFromCall(p, t);
            finfo = self.func_syms.get(callee_id);
        } else {
            finfo = try self.ensureFuncDeclFromCall(p, t);
        }
    }

    const isExternLL = std.mem.eql(u8, finfo.?.op.getName().str().toSlice(), "llvm.func");

    // Gather SR arg types and MLIR values
    const args_slice = t.instrs.val_list_pool.slice(p.args);
    var src_vals = try self.gpa.alloc(mlir.Value, args_slice.len);
    defer self.gpa.free(src_vals);
    var src_sr = try self.gpa.alloc(types.TypeId, args_slice.len);
    defer self.gpa.free(src_sr);
    for (args_slice, 0..) |vid, i| {
        src_vals[i] = self.value_map.get(vid).?;
        src_sr[i] = self.srTypeOfValue(vid);
    }

    if (isExternLL and finfo.?.is_variadic and src_vals.len > finfo.?.n_formals) {
        var expanded_vals = ArrayList(mlir.Value).init(self.gpa);
        defer expanded_vals.deinit();
        var expanded_sr = ArrayList(types.TypeId).init(self.gpa);
        defer expanded_sr.deinit();

        for (src_vals, 0..) |val, idx| {
            if (idx < finfo.?.n_formals) {
                try expanded_vals.append(val);
                try expanded_sr.append(src_sr[idx]);
                continue;
            }
            try self.expandVariadicArgTuple(val, src_sr[idx], &expanded_vals, &expanded_sr);
        }

        self.gpa.free(src_vals);
        self.gpa.free(src_sr);
        src_vals = try expanded_vals.toOwnedSlice();
        src_sr = try expanded_sr.toOwnedSlice();
    }

    if (isExternLL and finfo.?.is_variadic and src_vals.len > finfo.?.n_formals) {
        var expanded_vals = ArrayList(mlir.Value).init(self.gpa);
        defer expanded_vals.deinit();
        var expanded_sr = ArrayList(types.TypeId).init(self.gpa);
        defer expanded_sr.deinit();

        for (src_vals, 0..) |val, idx| {
            if (idx < finfo.?.n_formals) {
                try expanded_vals.append(val);
                try expanded_sr.append(src_sr[idx]);
                continue;
            }
            try self.expandVariadicArgTuple(val, src_sr[idx], &expanded_vals, &expanded_sr);
        }

        self.gpa.free(src_vals);
        self.gpa.free(src_sr);
        src_vals = try expanded_vals.toOwnedSlice();
        src_sr = try expanded_sr.toOwnedSlice();
    }

    const want_res_sr = p.ty;
    const want_kind = self.context.type_store.getKind(want_res_sr);
    const want_no_result = switch (want_kind) {
        .Void, .Noreturn => true,
        else => false,
    };
    const want_res_mlir = try self.llvmTypeOf(want_res_sr);
    const want_has_res = !want_no_result and !self.void_ty.equal(want_res_mlir);

    if (!isExternLL) {
        // Internal call: unchanged (func.call)
        const call_args = try self.prepareInternalCallArgs(src_vals, src_sr, finfo.?);
        defer self.gpa.free(call_args);
        const attrs = [_]mlir.NamedAttribute{
            self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(callee_name))),
        };
        const call = self.appendOp("func.call", EmitOpArgs{
            .operands = call_args,
            .results = if (want_has_res) &.{want_res_mlir} else &.{},
            .attributes = &attrs,
        });
        return if (want_has_res) call.getResult(0) else .empty();
    }

    // ===== Extern C call via llvm.func (ABI-lowered) =====

    // Handle sret (if any): if return is IndirectSRet, first argument becomes out pointer.
    var retClass: abi.AbiClass = undefined;
    if (!want_no_result) {
        retClass = abi.abiClassifyX64SysV(self, want_res_sr, true);
    }

    var lowered_ops = ArrayList(mlir.Value).init(self.gpa);
    defer lowered_ops.deinit();

    var formal_index: usize = 0;
    var retbuf: mlir.Value = mlir.Value.empty();
    if (!want_no_result and retClass.kind == .IndirectSRet) {
        // allocate result, pass as first arg
        retbuf = self.spillAgg(self.undefOf(want_res_mlir), want_res_mlir, @intCast(retClass.alignment));
        // The alloca above created memory; but we stored undef just to materialize it.
        // Overwrite with real result after the call; passing the pointer now:
        lowered_ops.append(retbuf) catch unreachable;
        formal_index += 1;
    }

    // Lower each argument
    for (src_vals, 0..) |v, i| {
        const sr = src_sr[i];
        const cls = abi.abiClassifyX64SysV(self, sr, false);

        switch (cls.kind) {
            .IndirectByVal => {
                // build a temp agg, pass pointer
                const stTy = try self.llvmTypeOf(sr);
                const tmp = self.spillAgg(v, stTy, if (cls.alignment == 0) 8 else cls.alignment);
                var passv = tmp;
                if (formal_index < finfo.?.param_types.len) {
                    const want_ty = finfo.?.param_types[formal_index];
                    passv = try self.ensureCallArgType(passv, sr, want_ty);
                }
                lowered_ops.append(passv) catch unreachable;
                formal_index += 1;
            },
            .DirectScalar => {
                const stTy = try self.llvmTypeOf(sr);
                var passv: mlir.Value = undefined;
                if (!stTy.isAInteger() and !stTy.isAFloat() and !stTy.isAVector()) {
                    // aggregate -> pack (use natural alignment for the SR type)
                    const natural_align_usize = abi.abiSizeAlign(self, sr).alignment;
                    const natural_align: u32 = @intCast(@min(natural_align_usize, @as(usize, std.math.maxInt(u32))));
                    const tmp = self.spillAgg(v, stTy, if (natural_align == 0) 8 else natural_align);
                    if (cls.scalar0.?.isAInteger()) {
                        const bits = cls.scalar0.?.getIntegerBitwidth();
                        passv = self.loadIntAt(tmp, bits, 0);
                    } else {
                        passv = self.emitOp("llvm.load", EmitOpArgs{
                            .operands = &.{tmp},
                            .results = &.{cls.scalar0.?},
                        });
                    }
                } else {
                    passv = v;
                }
                const want_ty = if (formal_index < finfo.?.param_types.len)
                    finfo.?.param_types[formal_index]
                else
                    passv.getType();
                passv = try self.ensureCallArgType(passv, sr, want_ty);
                lowered_ops.append(passv) catch unreachable;
                formal_index += 1;
            },
            .DirectPair => {
                // spill -> load lo i64, hi iN
                const stTy = try self.llvmTypeOf(sr);
                const tmp = self.spillAgg(v, stTy, 1);
                const lo = self.loadIntAt(tmp, 64, 0);
                const hibits = cls.scalar1.?.getIntegerBitwidth();
                const hi = self.loadIntAt(tmp, hibits, 8);
                var lo_cast = lo;
                if (formal_index < finfo.?.param_types.len) {
                    const want0 = finfo.?.param_types[formal_index];
                    lo_cast = try self.ensureCallArgType(lo_cast, sr, want0);
                }
                var hi_cast = hi;
                if (formal_index + 1 < finfo.?.param_types.len) {
                    const want1 = finfo.?.param_types[formal_index + 1];
                    hi_cast = try self.ensureCallArgType(hi_cast, sr, want1);
                }
                lowered_ops.append(lo_cast) catch unreachable;
                lowered_ops.append(hi_cast) catch unreachable;
                formal_index += 2;
            },
            else => unreachable,
        }
    }

    // Build llvm.call

    const seg = mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ @as(i32, @intCast(lowered_ops.items.len)), 0 });
    // if variadic function, add var_callee_type attribute
    var callAttrsList = ArrayList(mlir.NamedAttribute).init(self.gpa);
    defer callAttrsList.deinit();
    try callAttrsList.append(self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(callee_name))));
    try callAttrsList.append(self.named("operand_segment_sizes", seg));
    try callAttrsList.append(self.named("op_bundle_sizes", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{})));

    if (finfo.?.is_variadic) {
        const func_ty = finfo.?.op.getInherentAttributeByName(mlir.StringRef.from("function_type"));
        callAttrsList.append(self.named("var_callee_type", func_ty)) catch unreachable;
    }
    const call = self.appendOp("llvm.call", EmitOpArgs{
        .operands = lowered_ops.items,
        .results = if (want_no_result)
            &.{}
        else if (retClass.kind == .IndirectSRet)
            &.{}
        else
            &.{finfo.?.ret_type},
        .attributes = callAttrsList.items,
    });

    // Reconstruct desired result (structural) from ABI return
    if (want_no_result) return .empty();

    switch (retClass.kind) {
        .IndirectSRet => {
            // load structural result from retbuf
            return self.emitOp("llvm.load", EmitOpArgs{
                .operands = &.{retbuf},
                .results = &.{want_res_mlir},
                .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
            });
        },
        .DirectScalar => {
            const rv = call.getResult(0);
            // If caller expects a scalar too, just return it
            if (want_res_mlir.isAInteger() or want_res_mlir.isAFloat() or want_res_mlir.isAVector()) {
                var coerced = rv;
                if (!rv.getType().equal(want_res_mlir)) {
                    coerced = try self.ensureCallArgType(rv, want_res_sr, want_res_mlir);
                }
                return coerced;
            }
            // Caller expects an aggregate: write scalar into buffer and reload as struct
            const tmp = self.spillAgg(self.undefOf(want_res_mlir), want_res_mlir, 8);
            self.storeAt(tmp, rv, 0);
            return self.emitOp("llvm.load", EmitOpArgs{
                .operands = &.{tmp},
                .results = &.{want_res_mlir},
                .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
            });
        },
        .DirectPair => {
            // Return value is a literal LLVM struct {lo,hi}
            const rv = call.getResult(0);
            const loTy = retClass.scalar0.?;
            const hiTy = retClass.scalar1.?;
            // extract pieces
            const ex0 = self.emitOp("llvm.extractvalue", EmitOpArgs{
                .operands = &.{rv},
                .results = &.{loTy},
                .attributes = &.{self.named("position", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, &[_]i64{0}))},
            });
            const ex1 = self.emitOp("llvm.extractvalue", EmitOpArgs{
                .operands = &.{rv},
                .results = &.{hiTy},
                .attributes = &.{self.named("position", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, &[_]i64{1}))},
            });
            // Compose the aggregate via insertvalue instead of spilling to memory
            var agg = self.insertAt(self.undefOf(want_res_mlir), ex0, &.{0});
            agg = self.insertAt(agg, ex1, &.{1});
            return agg;
        },
        else => unreachable,
    }
}

/// Emit an MLIR block, including splices and argument lowering.
fn emitMlirBlock(self: *Codegen, p: tir.Rows.MlirBlock, t: *tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const mlir_kind = p.kind;
    const piece_ids = t.instrs.mlir_piece_pool.slice(p.pieces);
    const mlir_template = try self.renderMlirTemplate(t, piece_ids);
    defer self.gpa.free(mlir_template);

    const arg_vids = t.instrs.value_pool.slice(p.args);
    if (mlir_kind == .Operation) {
        const result_ty = if (p.result.isNone()) self.void_ty else try self.llvmTypeOf(p.ty);
        const value = try self.emitInlineMlirOperation(mlir_template, arg_vids, result_ty, p.loc);
        return if (p.result.isNone()) .empty() else value;
    }

    if (mlir_kind != .Operation) {
        if (self.active_type_info) |ti| {
            if (ti.getComptimeValue(p.expr)) |cached_ptr| {
                const cached_value = cached_ptr.*;
                switch (mlir_kind) {
                    .Module => {
                        switch (cached_value) {
                            .MlirModule => |module| {
                                const cloned_op = mlir.Operation.clone(module.getOperation());
                                var cloned_module = mlir.Module.fromOperation(cloned_op);
                                defer cloned_module.destroy();
                                var cloned_body = cloned_module.getBody();
                                cloned_body.detach();
                                var current_op = cloned_body.getFirstOperation();
                                while (!current_op.isNull()) {
                                    const next_op = current_op.getNextInBlock();

                                    const op_name_ref = current_op.getName().str();
                                    if (std.mem.eql(u8, op_name_ref.toSlice(), "func.func")) {
                                        const sym_name_attr = current_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
                                        if (!sym_name_attr.isNull()) {
                                            const sym_name_text = sym_name_attr.stringAttrGetValue().toSlice();
                                            const sym_name_id = self.context.interner.intern(sym_name_text);
                                            if (!self.func_syms.contains(sym_name_id)) {
                                                const func_type_attr = current_op.getInherentAttributeByName(mlir.StringRef.from("function_type"));
                                                const func_type = func_type_attr.typeAttrGetValue();
                                                const n_formals = func_type.getFunctionNumInputs();
                                                const n_results = func_type.getFunctionNumResults();
                                                const ret_type = if (n_results == 1) func_type.getFunctionResult(0) else self.void_ty;

                                                const param_len: usize = @intCast(n_formals);
                                                const param_types_copy = try self.gpa.alloc(mlir.Type, param_len);
                                                var pi: usize = 0;
                                                while (pi < param_len) : (pi += 1) {
                                                    param_types_copy[pi] = func_type.getFunctionInput(@intCast(pi));
                                                }
                                                const info = FuncInfo{
                                                    .op = current_op,
                                                    .is_variadic = false,
                                                    .n_formals = @intCast(n_formals),
                                                    .ret_type = ret_type,
                                                    .param_types = param_types_copy,
                                                    .owns_param_types = true,
                                                    .dbg_subprogram = null,
                                                };
                                                _ = try self.func_syms.put(sym_name_id, info);
                                            }
                                        }
                                    }

                                    current_op.removeFromParent();
                                    var body = self.module.getBody();
                                    body.appendOwnedOperation(current_op);
                                    current_op = next_op;
                                }
                                return .empty();
                            },
                            else => {},
                        }
                    },
                    .Type => {
                        switch (cached_value) {
                            .MlirType => return .empty(),
                            else => {},
                        }
                    },
                    .Attribute => {
                        switch (cached_value) {
                            .MlirAttribute => return .empty(),
                            else => {},
                        }
                    },
                    .Operation => {},
                }
            }
        }
    }

    var mlir_text_list: std.ArrayList(u8) = .empty;
    defer mlir_text_list.deinit(self.gpa);

    if (arg_vids.len > 0) {
        var arg_names: std.ArrayList([]const u8) = .empty;
        defer {
            for (arg_names.items) |item| self.gpa.free(item);
            arg_names.deinit(self.gpa);
        }

        for (arg_vids) |arg_vid| {
            const mlir_val = self.value_map.get(arg_vid).?;

            var str_buf = ArrayList(u8).init(self.gpa);
            defer str_buf.deinit();
            var had_error = false;
            var sink = PrintBuffer{ .list = &str_buf, .had_error = &had_error };
            mlir_val.print(printCallback, &sink);

            const owned = try str_buf.toOwnedSlice();
            var trimmed: []const u8 = owned;

            if (std.mem.indexOfScalar(u8, trimmed, '=')) |eq_idx| {
                trimmed = std.mem.trimRight(u8, trimmed[0..eq_idx], " \t\r\n");
            } else if (std.mem.indexOfScalar(u8, trimmed, ' ')) |sp_idx| {
                trimmed = std.mem.trimRight(u8, trimmed[0..sp_idx], " \t\r\n");
            }

            trimmed = std.mem.trimRight(u8, trimmed, " \t\r\n");

            const final = try self.gpa.dupe(u8, trimmed);
            self.gpa.free(owned);
            try arg_names.append(self.gpa, final);
        }

        var writer = mlir_text_list.writer(self.gpa);

        var i: usize = 0;
        while (i < mlir_template.len) {
            if (mlir_template[i] == '%') {
                var j = i + 1;
                var num: u32 = 0;
                var num_len: u32 = 0;
                while (j < mlir_template.len and std.ascii.isDigit(mlir_template[j])) {
                    num = num * 10 + (mlir_template[j] - '0');
                    num_len += 1;
                    j += 1;
                }

                if (num_len > 0 and num < arg_names.items.len) {
                    try writer.writeAll(arg_names.items[num]);
                    i += num_len + 1;
                } else {
                    try writer.writeByte(mlir_template[i]);
                    i += 1;
                }
            } else {
                try writer.writeByte(mlir_template[i]);
                i += 1;
            }
        }
    } else {
        try mlir_text_list.appendSlice(self.gpa, mlir_template);
    }
    const mlir_text = mlir_text_list.items;

    switch (mlir_kind) {
        else => unreachable,
        .Module => {
            var parsed_module = mlir.Module.createParse(
                self.mlir_ctx,
                mlir.StringRef.from(mlir_text),
            );
            if (parsed_module.isNull()) {
                const loc = self.context.loc_store.get(p.loc.unwrap());
                try self.context.diags.addError(loc, .mlir_parse_error, .{});
                return error.MlirParseError;
            }
            var parsed_module_body = parsed_module.getBody();
            parsed_module_body.detach();
            var current_op = parsed_module_body.getFirstOperation();
            while (!current_op.isNull()) {
                const next_op = current_op.getNextInBlock();

                const op_name_ref = current_op.getName().str();
                if (std.mem.eql(u8, op_name_ref.toSlice(), "func.func")) {
                    const sym_name_attr = current_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
                    if (!sym_name_attr.isNull()) {
                        const sym_name_text = sym_name_attr.stringAttrGetValue().toSlice();
                        const sym_name_id = self.context.interner.intern(sym_name_text);
                        if (!self.func_syms.contains(sym_name_id)) {
                            const func_type_attr = current_op.getInherentAttributeByName(mlir.StringRef.from("function_type"));
                            const func_type = func_type_attr.typeAttrGetValue();
                            const n_formals = func_type.getFunctionNumInputs();
                            const n_results = func_type.getFunctionNumResults();
                            const ret_type = if (n_results == 1) func_type.getFunctionResult(0) else self.void_ty;

                            const param_len: usize = @intCast(n_formals);
                            const param_types_copy = try self.gpa.alloc(mlir.Type, param_len);
                            var pi: usize = 0;
                            while (pi < param_len) : (pi += 1) {
                                param_types_copy[pi] = func_type.getFunctionInput(@intCast(pi));
                            }
                            const info = FuncInfo{
                                .op = current_op,
                                .is_variadic = false,
                                .n_formals = @intCast(n_formals),
                                .ret_type = ret_type,
                                .param_types = param_types_copy,
                                .owns_param_types = true,
                                .dbg_subprogram = null,
                            };
                            _ = try self.func_syms.put(sym_name_id, info);
                        }
                    }
                }

                current_op.removeFromParent();
                var body = self.module.getBody();
                body.appendOwnedOperation(current_op);
                current_op = next_op;
            }
            parsed_module.destroy();
            if (p.result.isNone()) {
                return .empty();
            } else {
                // Materialize a dummy pointer value to satisfy SSA uses of mlir.module type
                const ty = try self.llvmTypeOf(p.ty);
                return self.emitOp("llvm.mlir.zero", EmitOpArgs{
                    .results = &.{ty},
                });
            }
        },
        .Type => {
            var parsed_type = mlir.Type.parseGet(self.mlir_ctx, mlir.StringRef.from(mlir_text));
            if (parsed_type.isNull()) {
                std.debug.print("Error parsing inline MLIR type: {s}\n", .{mlir_text});
                return error.MlirParseError;
            }
            if (p.result.isNone()) {
                return .empty();
            } else {
                const ty = try self.llvmTypeOf(p.ty);
                return self.emitOp("llvm.mlir.zero", EmitOpArgs{
                    .results = &.{ty},
                });
            }
        },
        .Attribute => {
            var parsed_attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(mlir_text));
            if (parsed_attr.isNull()) {
                std.debug.print("Error parsing inline MLIR attribute: {s}\n", .{mlir_text});
                return error.MlirParseError;
            }
            if (p.result.isNone()) {
                return .empty();
            } else {
                const ty = try self.llvmTypeOf(p.ty);
                return self.emitOp("llvm.mlir.zero", EmitOpArgs{
                    .results = &.{ty},
                });
            }
        },
    }
}

// ----------------------------------------------------------------
// Instructions
// ----------------------------------------------------------------
/// Lower a single SSA instruction `ins_id` from `t` into MLIR and return its result value.
fn emitInstr(self: *Codegen, ins_id: tir.InstrId, t: *tir.TIR) !mlir.Value {
    return switch (t.kind(ins_id)) {
        // ------------- Constants -------------
        .ConstInt => self.emitConstInt(t.instrs.get(.ConstInt, ins_id)),
        .ConstFloat => self.emitConstFloat(t.instrs.get(.ConstFloat, ins_id)),
        .ConstBool => self.emitConstBool(t.instrs.get(.ConstBool, ins_id)),
        .ConstNull => self.emitConstNull(t.instrs.get(.ConstNull, ins_id)),
        .ConstUndef => self.emitConstUndef(t.instrs.get(.ConstUndef, ins_id)),
        .ConstString => self.emitConstString(t.instrs.get(.ConstString, ins_id)),

        // ------------- Arithmetic / bitwise (now arith.*) -------------
        .Add => self.emitAdd(t.instrs.get(.Add, ins_id)),
        .Sub => self.emitSub(t.instrs.get(.Sub, ins_id)),
        .Mul => self.emitMul(t.instrs.get(.Mul, ins_id)),
        .BinWrapAdd => self.binArith(.add, t.instrs.get(.BinWrapAdd, ins_id)),
        .BinWrapSub => self.binArith(.sub, t.instrs.get(.BinWrapSub, ins_id)),
        .BinWrapMul => self.binArith(.mul, t.instrs.get(.BinWrapMul, ins_id)),
        .BinSatAdd => self.emitSaturatingIntBinary(t.instrs.get(.BinSatAdd, ins_id), "arith.addi", true),
        .BinSatSub => self.emitSaturatingIntBinary(t.instrs.get(.BinSatSub, ins_id), "arith.subi", true),
        .BinSatMul => self.emitSaturatingIntBinary(t.instrs.get(.BinSatMul, ins_id), "arith.muli", true),
        .Div => self.emitDiv(t.instrs.get(.Div, ins_id)),
        .Mod => self.emitMod(t.instrs.get(.Mod, ins_id)),
        .Shl => self.emitShl(t.instrs.get(.Shl, ins_id)),
        .BinSatShl => self.emitSaturatingIntBinary(t.instrs.get(.BinSatShl, ins_id), "arith.shli", false),
        .Shr => self.emitShr(t.instrs.get(.Shr, ins_id)),
        .BitAnd => try self.binBit(.@"and", t.instrs.get(.BitAnd, ins_id)),
        .BitOr => try self.binBit(.@"or", t.instrs.get(.BitOr, ins_id)),
        .BitXor => try self.binBit(.xor, t.instrs.get(.BitXor, ins_id)),

        // ------------- Logical (arith.*) -------------
        .LogicalAnd => try self.binBit(.@"and", t.instrs.get(.LogicalAnd, ins_id)),
        .LogicalOr => try self.binBit(.@"or", t.instrs.get(.LogicalOr, ins_id)),
        .LogicalNot => blk: {
            const p = t.instrs.get(.LogicalNot, ins_id);
            const v = self.value_map.get(p.value).?;
            break :blk self.arithLogicalNotI1(v, p.loc);
        },

        // ------------- Comparisons (keep LLVM for robust attrs) -------------
        .CmpEq => self.emitCmp("eq", "eq", "oeq", t.instrs.get(.CmpEq, ins_id)),
        .CmpNe => self.emitCmp("ne", "ne", "one", t.instrs.get(.CmpNe, ins_id)),
        .CmpLt => self.emitCmp("ult", "slt", "olt", t.instrs.get(.CmpLt, ins_id)),
        .CmpLe => self.emitCmp("ule", "sle", "ole", t.instrs.get(.CmpLe, ins_id)),
        .CmpGt => self.emitCmp("ugt", "sgt", "ogt", t.instrs.get(.CmpGt, ins_id)),
        .CmpGe => self.emitCmp("uge", "sge", "oge", t.instrs.get(.CmpGe, ins_id)),

        // ------------- Casts -------------
        .CastBit => self.emitCastBit(t.instrs.get(.CastBit, ins_id)),
        .CastNormal => self.emitCastNormalInstr(t.instrs.get(.CastNormal, ins_id)),
        .CastSaturate => self.emitCastSaturate(t.instrs.get(.CastSaturate, ins_id)),
        inline .CastWrap, .CastChecked => |x| self.emitCastWrap(x, t.instrs.get(x, ins_id)),

        // ------------- Memory -------------
        .Alloca => self.emitAlloca(t.instrs.get(.Alloca, ins_id)),
        .Load => self.emitLoad(t.instrs.get(.Load, ins_id), t),
        .Store => self.emitStore(t.instrs.get(.Store, ins_id), t),
        .Gep => self.emitGepInstr(ins_id, t),
        .GlobalAddr => self.emitGlobalAddr(t.instrs.get(.GlobalAddr, ins_id)),

        // ------------- Aggregates -------------
        .TupleMake => self.emitTupleMake(t.instrs.get(.TupleMake, ins_id), t),
        .RangeMake => self.emitRangeMake(t.instrs.get(.RangeMake, ins_id)),
        .Broadcast => self.emitBroadcast(t.instrs.get(.Broadcast, ins_id)),
        .ArrayMake => self.emitArrayMake(t.instrs.get(.ArrayMake, ins_id), t),
        .StructMake => blk: {
            const p = t.instrs.get(.StructMake, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const st_ty = try self.llvmTypeOf(p.ty);
            var acc = self.zeroOf(st_ty);
            const fields = t.instrs.sfi_pool.slice(p.fields);
            for (fields) |f_id| {
                const f = t.instrs.StructFieldInit.get(f_id);
                const v = self.value_map.get(f.value).?;
                acc = self.insertAt(acc, v, &.{@as(i64, @intCast(f.index))});
            }
            break :blk acc;
        },
        .ComplexMake => blk: {
            const p = t.instrs.get(.ComplexMake, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const cty = try self.llvmTypeOf(p.ty);
            const re = self.value_map.get(p.re).?;
            const im = self.value_map.get(p.im).?;
            const result = self.emitOp("complex.create", EmitOpArgs{
                .operands = &.{ re, im },
                .results = &.{cty},
            });
            break :blk result;
        },
        .ExtractElem => blk: {
            const p = t.instrs.get(.ExtractElem, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const agg = self.value_map.get(p.agg).?;
            const res_ty = try self.llvmTypeOf(p.ty);
            const v = self.extractAt(agg, res_ty, &.{@as(i64, @intCast(p.index))});
            break :blk v;
        },

        .InsertElem => blk: {
            const p = t.instrs.get(.InsertElem, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const agg = self.value_map.get(p.agg).?;
            const val = self.value_map.get(p.value).?;
            const v = self.insertAt(agg, val, &.{@as(i64, @intCast(p.index))});
            break :blk v;
        },

        .ExtractField => blk: {
            const p = t.instrs.get(.ExtractField, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const agg = self.value_map.get(p.agg).?;
            const res_ty = try self.llvmTypeOf(p.ty);
            // Special-case: Complex field access -> complex.re/complex.im
            const parent_sr = self.srTypeOfValue(p.agg);
            const parent_kind = self.context.type_store.getKind(parent_sr);
            if (parent_kind == .Complex) {
                var which_re: bool = false;
                var which_im: bool = false;
                if (!p.name.isNone()) {
                    const nm = t.instrs.strs.get(p.name.unwrap());
                    if (std.mem.eql(u8, nm, "real") or std.mem.eql(u8, nm, "re")) which_re = true;
                    if (std.mem.eql(u8, nm, "imag") or std.mem.eql(u8, nm, "im")) which_im = true;
                } else {
                    if (p.index == 0) which_re = true;
                    if (p.index == 1) which_im = true;
                }
                if (which_re or which_im) {
                    const opname = if (which_re) "complex.re" else "complex.im";
                    const result = self.emitUnaryValueOp(opname, agg, res_ty);
                    break :blk result;
                }
            }
            if (!p.name.isNone()) {
                const field_name = t.instrs.strs.get(p.name.unwrap());
                if (std.mem.eql(u8, field_name, "len")) {
                    const v = self.extractAt(agg, res_ty, &.{@as(i64, @intCast(1))});
                    break :blk v;
                }
                if (std.mem.eql(u8, field_name, "capacity")) {
                    const v = self.extractAt(agg, res_ty, &.{@as(i64, @intCast(2))});
                    break :blk v;
                }
            }
            // For Optionals, trust the container layout for field types.
            var eff_res_ty = res_ty;
            if (parent_kind == .Optional) {
                if (self.context.type_store.isOptionalPointer(parent_sr)) {
                    if (p.index == 0) {
                        const ptr_int = self.emitUnaryValueOp("llvm.ptrtoint", agg, self.i64_ty);
                        const zero = self.constInt(self.i64_ty, 0);
                        const cmp = self.emitBinaryValueOp("arith.cmpi", ptr_int, zero, self.i1_ty, &.{
                            self.named("predicate", self.arithCmpIPredAttr("ne")),
                        });
                        break :blk cmp;
                    } else if (p.index == 1) {
                        if (!agg.getType().equal(res_ty)) {
                            const bc = self.emitUnaryValueOp("llvm.bitcast", agg, res_ty);
                            break :blk bc;
                        }
                        break :blk agg;
                    }
                } else {
                    const opt = self.context.type_store.get(.Optional, parent_sr);
                    if (p.index == 0) {
                        eff_res_ty = self.i1_ty;
                    } else if (p.index == 1) {
                        eff_res_ty = try self.llvmTypeOf(opt.elem);
                    }
                }
            }
            const v = self.extractAt(agg, eff_res_ty, &.{@as(i64, @intCast(p.index))});
            break :blk v;
        },

        .InsertField => blk: {
            const p = t.instrs.get(.InsertField, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const agg = self.value_map.get(p.agg).?;
            const val = self.value_map.get(p.value).?;
            const v = self.insertAt(agg, val, &.{@as(i64, @intCast(p.index))});
            break :blk v;
        },

        .VariantMake => blk: {
            const p = t.instrs.get(.VariantMake, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const var_ty = try self.llvmTypeOf(p.ty);
            var acc = self.undefOf(var_ty);

            const tag_val = self.constInt(self.i32_ty, @intCast(p.tag));
            acc = self.insertAt(acc, tag_val, &.{0});

            if (!p.payload.isNone()) {
                const payload_val_id = p.payload.unwrap();
                const payload_val = self.value_map.get(payload_val_id).?;

                const struct_ty = self.context.type_store.get(.Struct, p.ty);
                const union_field = self.context.type_store.field_pool.slice(struct_ty.fields)[1];
                const union_ty = self.context.type_store.Field.get(union_field).ty;
                const union_mlir_ty = try self.llvmTypeOf(union_ty);

                var union_acc = self.undefOf(union_mlir_ty);
                union_acc = self.insertAt(union_acc, payload_val, &.{0});
                acc = self.insertAt(acc, union_acc, &.{1});
            }

            break :blk acc;
        },
        .VariantTag => blk: {
            const p = t.instrs.get(.VariantTag, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const v = self.value_map.get(p.value).?;
            const i32ty = mlir.Type.getSignlessIntegerType(self.mlir_ctx, 32);
            const tag = self.extractAt(v, i32ty, &.{0});
            break :blk tag;
        },
        .VariantPayloadPtr => blk: {
            const p = t.instrs.get(.VariantPayloadPtr, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const v = self.value_map.get(p.value).?;
            // Extract field 1 (payload pointer)
            const ptr = self.extractAt(v, self.llvm_ptr_ty, &.{1});
            break :blk ptr;
        },

        .UnionMake => blk: {
            const p = t.instrs.get(.UnionMake, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            // MLIR type of the union "storage blob"
            const u_mlir = try self.llvmTypeOf(p.ty);

            // Figure out the chosen field type and coerce payload to it
            var payload = self.value_map.get(p.value).?;
            const urow = self.context.type_store.get(.Union, p.ty);
            const f_ids = self.context.type_store.field_pool.slice(urow.fields);
            const f_sr = self.context.type_store.Field.get(f_ids[@intCast(p.field_index)]).ty;
            const f_mlir = try self.llvmTypeOf(f_sr);
            if (!payload.getType().equal(f_mlir)) {
                payload = try self.coerceOnBranch(payload, f_mlir, f_sr, self.srTypeOfValue(p.value));
            }

            // Materialize the union by writing the chosen field at offset 0
            const tmp = self.spillAgg(self.undefOf(u_mlir), u_mlir, 0);
            self.storeAt(tmp, payload, 0);

            const result = self.emitOp("llvm.load", EmitOpArgs{
                .operands = &.{tmp},
                .results = &.{u_mlir},
            });
            break :blk result;
        },
        .UnionField => blk: {
            const p = t.instrs.get(.UnionField, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            // Base & SR type
            const base = self.value_map.get(p.base).?;
            const base_is_ptr = base.getType().equal(self.llvm_ptr_ty);
            const union_sr = self.srTypeOfValue(p.base);
            var core_union_sr = union_sr;
            if (base_is_ptr and self.context.type_store.getKind(union_sr) == .Ptr) {
                core_union_sr = self.context.type_store.get(.Ptr, union_sr).elem;
            }

            // Desired field type (from the union's SR type)
            const urow = self.context.type_store.get(.Union, core_union_sr);
            const f_ids = self.context.type_store.field_pool.slice(urow.fields);
            const f_sr = self.context.type_store.Field.get(f_ids[@intCast(p.field_index)]).ty;
            const f_mlir = try self.llvmTypeOf(f_sr);

            // Get a pointer to the union storage (spill SSA value if needed),
            // aligning to the field's alignment for a correct typed load.
            var storage_ptr: mlir.Value = base;
            if (!base_is_ptr) {
                const u_mlir = try self.llvmTypeOf(core_union_sr);
                const field_align = abi.abiSizeAlign(self, f_sr).alignment;
                storage_ptr = self.spillAgg(base, u_mlir, @intCast(field_align));
            }

            // Reinterpret the same address as a pointer-to-field-type at offset 0.
            // With opaque pointers in MLIR, use a zero-index GEP with the desired element type.
            const idxs = [_]tir.Rows.GepIndex{.{ .Const = 0 }};
            const fptr = try self.emitGep(storage_ptr, f_mlir, &idxs);
            // load the field value from the pointer
            const load_result = self.emitOp("llvm.load", EmitOpArgs{
                .operands = &.{fptr},
                .results = &.{f_mlir},
                .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
            });
            break :blk load_result;
        },

        .UnionFieldPtr => blk: {
            const p = t.instrs.get(.UnionFieldPtr, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            const base = self.value_map.get(p.base).?;
            const base_is_ptr = base.getType().equal(self.llvm_ptr_ty);
            const union_sr = self.srTypeOfValue(p.base);
            var core_union_sr = union_sr;
            if (base_is_ptr and self.context.type_store.getKind(union_sr) == .Ptr) {
                core_union_sr = self.context.type_store.get(.Ptr, union_sr).elem;
            }

            // Desired field type
            const urow = self.context.type_store.get(.Union, core_union_sr);
            const f_ids = self.context.type_store.field_pool.slice(urow.fields);
            const f_sr = self.context.type_store.Field.get(f_ids[@intCast(p.field_index)]).ty;
            const f_mlir = try self.llvmTypeOf(f_sr);

            // Spill SSA union value if needed, aligned to field alignment.
            var storage_ptr: mlir.Value = base;
            if (!base_is_ptr) {
                const u_mlir = try self.llvmTypeOf(core_union_sr);
                const field_align = abi.abiSizeAlign(self, f_sr).alignment;
                storage_ptr = self.spillAgg(base, u_mlir, @intCast(field_align));
            }

            // Reinterpret the same address as a pointer-to-field-type at offset 0.
            // With opaque pointers in MLIR, use a zero-index GEP with the desired element type.
            const idxs = [_]tir.Rows.GepIndex{.{ .Const = 0 }};
            const fptr = try self.emitGep(storage_ptr, f_mlir, &idxs);
            break :blk fptr;
        },
        // ------------- Pointers/Indexing -------------
        .AddressOf => blk: {
            const p = t.instrs.get(.AddressOf, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const v = self.value_map.get(p.value).?;
            if (mlir.LLVM.isLLVMPointerType(v.getType())) break :blk v;
            break :blk v.opResultGetOwner().getOperand(0);
        },

        .Index => self.emitIndex(t.instrs.get(.Index, ins_id), t),

        // ------------- Data movement -------------
        .Select => blk: {
            const p = t.instrs.get(.Select, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const c = self.value_map.get(p.cond).?;
            const tv = self.value_map.get(p.then_value).?;
            const ev = self.value_map.get(p.else_value).?;
            const ty = try self.llvmTypeOf(p.ty);
            break :blk self.arithSelect(c, tv, ev, ty);
        },

        .IndirectCall => blk: {
            const p = t.instrs.get(.IndirectCall, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const callee = self.value_map.get(p.callee).?;
            const args_slice = t.instrs.val_list_pool.slice(p.args);
            var ops = try self.gpa.alloc(mlir.Value, 1 + args_slice.len);
            defer self.gpa.free(ops);
            ops[0] = callee;
            for (args_slice, 0..) |vid, i| {
                ops[i + 1] = self.value_map.get(vid).?;
            }

            const ret_ty = try self.llvmTypeOf(p.ty);
            const has_res = !ret_ty.equal(self.void_ty);

            var callAttrsList = ArrayList(mlir.NamedAttribute).init(self.gpa);

            defer callAttrsList.deinit();

            try callAttrsList.append(self.named("operand_segment_sizes", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ @as(i32, @intCast(args_slice.len + 1)), 0 })));

            try callAttrsList.append(self.named("op_bundle_sizes", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{})));

            const call = self.appendOp("llvm.call", EmitOpArgs{
                .operands = ops,
                .results = if (has_res) &.{ret_ty} else &.{},
                .attributes = callAttrsList.items,
            });
            break :blk if (has_res) call.getResult(0) else mlir.Value.empty();
        },
        .Call => self.emitCall(t.instrs.get(.Call, ins_id), t),
        .MlirBlock => self.emitMlirBlock(t.instrs.get(.MlirBlock, ins_id), t),
    };
}

/// Inline the given MLIR operation within the current block.
fn emitInlineMlirOperation(
    self: *Codegen,
    mlir_text_raw: []const u8,
    arg_vids: []const tir.ValueId,
    result_ty: mlir.Type,
    loc: tir.OptLocId,
) !mlir.Value {
    var arg_values = ArrayList(mlir.Value).init(self.gpa);
    defer arg_values.deinit();
    var arg_types = ArrayList(mlir.Type).init(self.gpa);
    defer arg_types.deinit();

    try arg_values.ensureUnusedCapacity(arg_vids.len);
    try arg_types.ensureUnusedCapacity(arg_vids.len);

    for (arg_vids) |arg_vid| {
        const arg_val = self.value_map.get(arg_vid).?;
        try arg_values.append(arg_val);
        try arg_types.append(arg_val.getType());
    }

    // 1. Generate unique function name
    const func_name_buf = try std.fmt.allocPrint(self.gpa, "__sr_inline_mlir_{d}", .{self.inline_mlir_counter});
    self.inline_mlir_counter += 1;
    defer self.gpa.free(func_name_buf);

    // 2. Build the function string inside a module
    var func_str = ArrayList(u8).init(self.gpa);
    defer func_str.deinit();
    var writer = func_str.writer();

    try writer.print("module {{\nfunc.func private @{s}(", .{func_name_buf});
    for (arg_types.items, 0..) |*ty, i| {
        if (i > 0) try writer.writeAll(", ");
        try writer.print("%arg{d}: ", .{i});
        var type_str_buf = ArrayList(u8).init(self.gpa);
        defer type_str_buf.deinit();
        var had_error = false;
        var sink = PrintBuffer{ .list = &type_str_buf, .had_error = &had_error };
        ty.print(printCallback, &sink);
        try writer.writeAll(type_str_buf.items);
    }
    try writer.writeAll(")");

    const has_result = !result_ty.equal(self.void_ty);
    if (has_result) {
        try writer.writeAll(" -> ");
        var type_str_buf = ArrayList(u8).init(self.gpa);
        defer type_str_buf.deinit();
        var had_error = false;
        var sink = PrintBuffer{ .list = &type_str_buf, .had_error = &had_error };
        result_ty.print(printCallback, &sink);
        try writer.writeAll(type_str_buf.items);
    }

    try writer.writeAll(" {\n");

    if (has_result) {
        try writer.writeAll("  %res = ");
    } else {
        try writer.writeAll("  ");
    }
    try writer.writeAll(mlir_text_raw);
    try writer.writeAll("\n");

    if (has_result) {
        try writer.writeAll("  func.return %res : ");
        var type_str_buf = ArrayList(u8).init(self.gpa);
        defer type_str_buf.deinit();
        var had_error = false;
        var sink = PrintBuffer{ .list = &type_str_buf, .had_error = &had_error };
        result_ty.print(printCallback, &sink);
        try writer.writeAll(type_str_buf.items);
        try writer.writeAll("\n");
    } else {
        try writer.writeAll("  func.return\n");
    }
    try writer.writeAll("}\n}"); // close func and module

    // 3. Parse the module containing the function
    var parsed_module = mlir.Module.createParse(
        self.mlir_ctx,
        mlir.StringRef.from(func_str.items),
    );
    if (parsed_module.isNull()) {
        const msg = self.diagnostic_data.msg orelse return error.CompilationFailed;
        const span = self.diagnostic_data.span orelse return error.CompilationFailed;
        var diag_loc = self.context.loc_store.get(loc.unwrap());
        diag_loc.start += @intCast(span.start -| 10);
        diag_loc.end += @intCast(span.end -| 10);

        try self.context.diags.addError(diag_loc, .mlir_parse_error, .{msg});
        return error.CompilationFailed;
    }
    defer parsed_module.destroy();

    var func_op = parsed_module.getBody().getFirstOperation();
    func_op.removeFromParent();

    // 4. Add the function to the current module
    var body = self.module.getBody();
    body.appendOwnedOperation(func_op);

    // 5. Create a call to this new function
    const attrs = [_]mlir.NamedAttribute{
        self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(func_name_buf))),
    };
    const call = self.appendOp("func.call", EmitOpArgs{
        .operands = arg_values.items,
        .results = if (has_result) &.{result_ty} else &.{},
        .attributes = &attrs,
    });

    if (has_result) {
        return call.getResult(0);
    } else {
        return mlir.Value.empty();
    }
}

/// Emit comparison instructions for binary compare operations recorded in `p`.
fn emitCmp(
    self: *Codegen,
    comptime pred_u: []const u8, // for unsigned ints (ult, ule, ugt, uge)
    comptime pred_s: []const u8, // for signed ints   (slt, sle, sgt, sge)
    comptime pred_f: []const u8, // for floats        (oeq, one, olt, ole, ogt, oge, ...)
    p: tir.Rows.Bin2,
) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    var lhs = self.value_map.get(p.lhs).?;
    var rhs = self.value_map.get(p.rhs).?;

    if (mlir.LLVM.isLLVMPointerType(lhs.getType())) {
        lhs = self.emitUnaryValueOp("llvm.ptrtoint", lhs, self.i64_ty);
    }
    if (mlir.LLVM.isLLVMPointerType(rhs.getType())) {
        rhs = self.emitUnaryValueOp("llvm.ptrtoint", rhs, self.i64_ty);
    }

    if (lhs.getType().isAFloat()) {
        return self.emitBinaryValueOp("arith.cmpf", lhs, rhs, self.i1_ty, &.{
            self.named("predicate", self.arithCmpFPredAttr(pred_f)),
        });
    } else {
        const unsigned = self.isUnsigned(self.srTypeOfValue(p.lhs));
        const pred = if (unsigned)
            self.arithCmpIPredAttr(pred_u)
        else
            self.arithCmpIPredAttr(pred_s);

        return self.emitBinaryValueOp("arith.cmpi", lhs, rhs, self.i1_ty, &.{
            self.named("predicate", pred),
        });
    }
}

/// Emit the terminator instruction corresponding to `term_id`.
fn emitTerminator(self: *Codegen, term_id: tir.TermId, t: *tir.TIR) !void {
    switch (t.kind(term_id)) {
        .Return => {
            const p = t.terms.get(.Return, term_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            var func_op = self.cur_block.?.getParentOperation();
            var name_attr = func_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
            const name_attr_value = name_attr.stringAttrGetValue().toSlice();
            const sym_name_id = self.context.interner.intern(name_attr_value);
            const finfo = self.func_syms.get(sym_name_id).?;
            const ret_ty = finfo.ret_type;
            const in_llvm_func = std.mem.eql(u8, func_op.getName().str().toSlice(), "llvm.func");
            if (in_llvm_func) {
                // LLVM functions still return directly
                if (!p.value.isNone()) {
                    const maybe_v = self.value_map.get(p.value.unwrap());
                    const v = if (maybe_v) |mv| mv else self.zeroOf(ret_ty);
                    if (ret_ty.equal(self.void_ty)) {
                        _ = self.appendOp("llvm.return", EmitOpArgs{});
                    } else {
                        _ = self.appendOp("llvm.return", EmitOpArgs{ .operands = &.{v} });
                    }
                } else {
                    if (!ret_ty.equal(self.void_ty)) {
                        const z = self.zeroOf(ret_ty);
                        _ = self.appendOp("llvm.return", EmitOpArgs{ .operands = &.{z} });
                    } else {
                        _ = self.appendOp("llvm.return", EmitOpArgs{});
                    }
                }
            } else {
                // For func.func: branch to the join-return block with optional value.
                const dest = self.ret_join_block.?;
                if (self.ret_has_value) {
                    const v = if (!p.value.isNone()) (self.value_map.get(p.value.unwrap()) orelse self.zeroOf(ret_ty)) else self.zeroOf(ret_ty);
                    _ = self.appendOp("cf.br", EmitOpArgs{
                        .operands = &.{v},
                        .successors = &.{dest},
                    });
                } else {
                    _ = self.appendOp("cf.br", EmitOpArgs{
                        .successors = &.{dest},
                    });
                }
            }
        },

        .Br => {
            const p = t.terms.get(.Br, term_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const edge = t.terms.Edge.get(p.edge);
            var dest = self.block_map.get(edge.dest).?;
            const args = t.instrs.value_pool.slice(edge.args);
            std.debug.assert(dest.getNumArguments() == args.len);

            var tmp4: [4]mlir.Value = undefined;
            var argv: []mlir.Value = if (args.len <= tmp4.len) tmp4[0..args.len] else try self.gpa.alloc(mlir.Value, args.len);
            defer if (argv.ptr != &tmp4) self.gpa.free(argv);

            for (args, 0..) |avid, i| argv[i] = self.value_map.get(avid).?;

            _ = self.appendOp("cf.br", EmitOpArgs{
                .operands = argv,
                .successors = &.{dest},
            });
        },

        .CondBr => {
            const p = t.terms.get(.CondBr, term_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const cond = self.value_map.get(p.cond).?;

            const tedge = t.terms.Edge.get(p.then_edge);
            const eedge = t.terms.Edge.get(p.else_edge);
            const tdest = self.block_map.get(tedge.dest).?;
            const edest = self.block_map.get(eedge.dest).?;

            const targs = t.instrs.value_pool.slice(tedge.args);
            const eargs = t.instrs.value_pool.slice(eedge.args);

            var tbuf = try self.gpa.alloc(mlir.Value, targs.len);
            defer self.gpa.free(tbuf);
            for (targs, 0..) |vid, i| tbuf[i] = self.value_map.get(vid).?;

            var ebuf = try self.gpa.alloc(mlir.Value, eargs.len);
            defer self.gpa.free(ebuf);
            for (eargs, 0..) |vid, i| ebuf[i] = self.value_map.get(vid).?;

            // one combined operand vector: [cond, then..., else...]
            const total = 1 + tbuf.len + ebuf.len;
            var ops = try self.gpa.alloc(mlir.Value, total);
            defer self.gpa.free(ops);
            ops[0] = cond;
            @memcpy(ops[1 .. 1 + tbuf.len], tbuf);
            @memcpy(ops[1 + tbuf.len ..], ebuf);

            const seg = mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ 1, @intCast(tbuf.len), @intCast(ebuf.len) });

            _ = self.appendOp("cf.cond_br", EmitOpArgs{
                .operands = ops,
                .successors = &.{ tdest, edest },
                .attributes = &.{self.named("operand_segment_sizes", seg)},
            });
        },

        .SwitchInt => {
            std.debug.panic("Not Implemented, Switch Int", .{});
        },

        .Unreachable => {
            const p = t.terms.get(.Unreachable, term_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            _ = self.appendOp("llvm.unreachable", EmitOpArgs{});
        },
    }
}

/// Try to emit a specialized GEP for tensor operations, returning null if not applicable.
fn tryEmitTensorGep(self: *Codegen, ins_id: tir.InstrId, t: *tir.TIR) !?mlir.Value {
    const p = t.instrs.get(.Gep, ins_id);
    if (self.context.type_store.getKind(p.ty) != .Ptr) return null;

    const base_vid = p.base;
    var root_ptr: ?tir.ValueId = null;
    var base_indices: []const TensorIndex = &[_]TensorIndex{};

    if (self.tensor_slots.get(base_vid)) |_| {
        root_ptr = base_vid;
    } else if (self.tensor_elem_ptrs.get(base_vid)) |base_info| {
        root_ptr = base_info.root_ptr;
        base_indices = base_info.indices;
    } else {
        return null;
    }

    const root = root_ptr.?;
    const root_sr = self.srTypeOfValue(root);
    if (self.context.type_store.getKind(root_sr) != .Ptr) return null;
    const root_elem = self.context.type_store.get(.Ptr, root_sr).elem;
    if (self.context.type_store.getKind(root_elem) != .Tensor) return null;

    const index_ids = t.instrs.gep_pool.slice(p.indices);
    const combined = try self.combineTensorIndexIds(t, base_indices, index_ids);
    errdefer if (combined.len != 0) self.gpa.free(combined);

    const placeholder = self.llvmNullPtr();
    const info = TensorElemPtrInfo{
        .root_ptr = root,
        .elem_ty = self.context.type_store.get(.Ptr, p.ty).elem,
        .indices = combined,
    };

    if (self.tensor_elem_ptrs.getPtr(p.result)) |old_ptr| {
        self.freeTensorElemPtrInfo(old_ptr);
        old_ptr.* = info;
    } else {
        try self.tensor_elem_ptrs.put(p.result, info);
    }

    try self.value_map.put(p.result, placeholder);
    try self.val_types.put(p.result, p.ty);
    return placeholder;
}

/// Combine tensor index operands into the format expected by the lowered tensor GEP.
fn combineTensorIndexIds(
    self: *Codegen,
    t: *tir.TIR,
    base: []const TensorIndex,
    ids: []const tir.GepIndexId,
) ![]TensorIndex {
    if (base.len == 0 and ids.len == 0) return &[_]TensorIndex{};
    const total = base.len + ids.len;
    var buf = try self.gpa.alloc(TensorIndex, total);
    if (base.len != 0) std.mem.copyForwards(TensorIndex, buf[0..base.len], base);
    var idx: usize = base.len;
    for (ids) |gid| {
        const g = t.instrs.GepIndex.get(gid);
        buf[idx] = switch (g) {
            .Const => |c| TensorIndex{ .constant = @as(i64, @intCast(c)) },
            .Value => |vid| blk: {
                if (self.constIntOf(t, vid)) |const_val| {
                    break :blk TensorIndex{ .constant = @as(i64, @intCast(const_val)) };
                }
                break :blk TensorIndex{ .value = vid };
            },
        };
        idx += 1;
    }
    return buf;
}

/// Lower tensor index expressions into LLVM values based on the given f_id.
fn buildTensorIndexValues(
    self: *Codegen,
    t: *tir.TIR,
    indices: []const TensorIndex,
) ![]mlir.Value {
    if (indices.len == 0) return &[_]mlir.Value{};
    var out = try self.gpa.alloc(mlir.Value, indices.len);
    const idx_ty = mlir.Type.getIndexType(self.mlir_ctx);
    var i: usize = 0;
    while (i < indices.len) : (i += 1) {
        const entry = indices[i];
        out[i] = switch (entry) {
            .constant => |c| blk: {
                const attr = mlir.Attribute.integerAttrGet(idx_ty, c);
                break :blk self.emitOp("arith.constant", EmitOpArgs{
                    .results = &.{idx_ty},
                    .attributes = &.{self.named("value", attr)},
                });
            },
            .value => |vid| blk: {
                const raw = try self.ensureValue(t, vid);
                break :blk try self.ensureIndexValue(raw);
            },
        };
    }
    return out;
}

/// Ensure the TIR value `vid` has a corresponding MLIR value, emitting it if needed.
fn ensureValue(self: *Codegen, t: *tir.TIR, vid: tir.ValueId) anyerror!mlir.Value {
    if (self.value_map.get(vid)) |v| return v;
    if (self.def_instr.get(vid)) |iid| {
        return try self.emitInstr(iid, t);
    }
    return error.CompileError;
}

/// Handle storing a scalar into a tensor element using indexed GEPs.
fn handleTensorElementStore(
    self: *Codegen,
    p: tir.Rows.Store,
    value: mlir.Value,
    t: *tir.TIR,
) !bool {
    if (self.tensor_elem_ptrs.get(p.ptr)) |info| {
        if (self.context.type_store.getKind(info.elem_ty) == .Tensor) return false;
        const tensor_sr = self.srTypeOfValue(info.root_ptr);
        if (self.context.type_store.getKind(tensor_sr) != .Ptr) return false;
        const tensor_ty = self.context.type_store.get(.Ptr, tensor_sr).elem;
        const tensor_mlir_ty = try self.llvmTypeOf(tensor_ty);
        var base_val = self.tensor_slots.get(info.root_ptr) orelse mlir.Value.empty();
        if (base_val.isNull()) base_val = self.zeroOf(tensor_mlir_ty);
        const index_vals = try self.buildTensorIndexValues(t, info.indices);
        defer if (index_vals.len != 0) self.gpa.free(index_vals);
        const new_tensor = try self.tensorInsertScalar(tensor_ty, info.elem_ty, base_val, value, index_vals);
        try self.tensor_slots.put(info.root_ptr, new_tensor);
        return true;
    }
    return false;
}

/// Attempt to lower scalar loads from tensor elements by following tensor GEP helpers.
fn tryEmitTensorElementLoad(
    self: *Codegen,
    p: tir.Rows.Load,
    t: *tir.TIR,
) !?mlir.Value {
    if (self.tensor_elem_ptrs.get(p.ptr)) |info| {
        if (self.context.type_store.getKind(info.elem_ty) == .Tensor) return null;
        const tensor_sr = self.srTypeOfValue(info.root_ptr);
        if (self.context.type_store.getKind(tensor_sr) != .Ptr) return null;
        const tensor_ty = self.context.type_store.get(.Ptr, tensor_sr).elem;
        const tensor_mlir_ty = try self.llvmTypeOf(tensor_ty);
        var base_val = self.tensor_slots.get(info.root_ptr) orelse mlir.Value.empty();
        if (base_val.isNull()) base_val = self.zeroOf(tensor_mlir_ty);
        const index_vals = try self.buildTensorIndexValues(t, info.indices);
        defer if (index_vals.len != 0) self.gpa.free(index_vals);
        const elem_val = try self.tensorExtractScalar(info.elem_ty, base_val, index_vals);
        return elem_val;
    }
    return null;
}

/// Insert a scalar into a tensor value at the computed index.
fn tensorInsertScalar(
    self: *Codegen,
    tensor_ty: types.TypeId,
    elem_ty: types.TypeId,
    base_tensor: mlir.Value,
    elem_value: mlir.Value,
    indices: []const mlir.Value,
) !mlir.Value {
    _ = elem_ty;
    const tensor_mlir = try self.llvmTypeOf(tensor_ty);
    var ops = try self.gpa.alloc(mlir.Value, 2 + indices.len);
    defer self.gpa.free(ops);
    ops[0] = elem_value;
    ops[1] = base_tensor;
    if (indices.len != 0) std.mem.copyForwards(mlir.Value, ops[2..], indices);
    return self.emitOp("tensor.insert", EmitOpArgs{
        .operands = ops,
        .results = &.{tensor_mlir},
    });
}

/// Extract a scalar from the tensor located at the computed index.
fn tensorExtractScalar(
    self: *Codegen,
    elem_ty: types.TypeId,
    base_tensor: mlir.Value,
    indices: []const mlir.Value,
) !mlir.Value {
    const elem_mlir = try self.llvmTypeOf(elem_ty);
    var ops = try self.gpa.alloc(mlir.Value, 1 + indices.len);
    defer self.gpa.free(ops);
    ops[0] = base_tensor;
    if (indices.len != 0) std.mem.copyForwards(mlir.Value, ops[1..], indices);
    return self.emitOp("tensor.extract", EmitOpArgs{
        .operands = ops,
        .results = &.{elem_mlir},
    });
}

/// Emit a pointer `getelementptr` operation for the TIR `p`.
fn emitGep(
    self: *Codegen,
    base: mlir.Value,
    elem_ty: mlir.Type,
    idxs: []const tir.Rows.GepIndex,
) !mlir.Value {
    // Ensure GEP base is always a pointer. For aggregate-in-SSA cases, spill to memory
    // using the provided element type (the pointee type for the GEP) and use that pointer.
    var base_ptr = base;
    if (!mlir.LLVM.isLLVMPointerType(base.getType())) {
        base_ptr = self.spillAgg(base, elem_ty, 0);
    }
    const dyn_min = std.math.minInt(i32);

    var use_idxs = idxs;
    var allocated_extra = false;
    const is_scalarish =
        elem_ty.isAInteger() or
        elem_ty.isAFloat() or
        elem_ty.isAComplex() or
        elem_ty.isAVector() or
        mlir.LLVM.isLLVMPointerType(elem_ty);
    if (!is_scalarish) {
        // For opaque-pointer GEPs:
        // - Reinterpretation GEP (idxs = [0]) needs a leading zero (handled by caller).
        // - Array element access on pointer-to-array needs a leading zero to step into the array.
        // - Pointer arithmetic across elements of pointer-to-struct MUST NOT insert an extra
        //   leading zero, otherwise the dynamic index becomes a struct field index which must
        //   be constant in MLIR/LLVM. In that case, we want a single dynamic index.
        const is_struct = mlir.LLVM.isLLVMStructType(elem_ty);
        const need_leading_zero = if (idxs.len == 0) true else switch (idxs[0]) {
            .Const => |c| c != 0,
            .Value => !is_struct,
        };
        if (need_leading_zero) {
            var tmp = try self.gpa.alloc(tir.Rows.GepIndex, idxs.len + 1);
            tmp[0] = .{ .Const = 0 };
            if (idxs.len != 0) std.mem.copyForwards(tir.Rows.GepIndex, tmp[1..], idxs);
            use_idxs = tmp;
            allocated_extra = true;
        }
    }
    defer if (allocated_extra) self.gpa.free(use_idxs);

    var dyn = try self.gpa.alloc(mlir.Value, use_idxs.len);
    defer self.gpa.free(dyn);
    var raw = try self.gpa.alloc(i32, use_idxs.len);
    defer self.gpa.free(raw);

    var ndyn: usize = 0;
    for (use_idxs, 0..) |g, i| {
        switch (g) {
            .Const => |c| raw[i] = @intCast(c),
            .Value => |vid| {
                raw[i] = dyn_min;
                dyn[ndyn] = self.value_map.get(vid).?;
                ndyn += 1;
            },
        }
    }

    var ops = try self.gpa.alloc(mlir.Value, 1 + ndyn);
    defer self.gpa.free(ops);

    ops[0] = base_ptr;
    for (dyn[0..ndyn], 0..) |v, i| ops[1 + i] = v;

    return self.emitOp("llvm.getelementptr", EmitOpArgs{
        .operands = ops,
        .results = &.{self.llvm_ptr_ty},
        .attributes = &.{
            self.named("elem_type", mlir.Attribute.typeAttrGet(elem_ty)),
            self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, raw)),
        },
    });
}

// ----------------------------------------------------------------
// Helpers
// ----------------------------------------------------------------
/// Build an MLIR integer predicate attribute from the string `pred`.
fn arithCmpIPredAttr(self: *Codegen, comptime pred: []const u8) mlir.Attribute {
    const val: i64 = if (std.mem.eql(u8, pred, "eq")) 0 else if (std.mem.eql(u8, pred, "ne"))
        1
    else if (std.mem.eql(u8, pred, "slt")) 2 else if (std.mem.eql(u8, pred, "sle"))
        3
    else if (std.mem.eql(u8, pred, "sgt")) 4 else if (std.mem.eql(u8, pred, "sge"))
        5
    else if (std.mem.eql(u8, pred, "ult")) 6 else if (std.mem.eql(u8, pred, "ule"))
        7
    else if (std.mem.eql(u8, pred, "ugt")) 8 else if (std.mem.eql(u8, pred, "uge"))
        9
    else
        unreachable;
    return mlir.Attribute.integerAttrGet(self.i64_ty, val);
}

/// Build an MLIR floating-point predicate attribute from the string `pred`.
fn arithCmpFPredAttr(self: *Codegen, comptime pred: []const u8) mlir.Attribute {
    const val: i64 = if (std.mem.eql(u8, pred, "false")) 0 else if (std.mem.eql(u8, pred, "oeq"))
        1
    else if (std.mem.eql(u8, pred, "ogt")) 2 else if (std.mem.eql(u8, pred, "oge"))
        3
    else if (std.mem.eql(u8, pred, "olt")) 4 else if (std.mem.eql(u8, pred, "ole"))
        5
    else if (std.mem.eql(u8, pred, "one")) 6 else if (std.mem.eql(u8, pred, "ord"))
        7
    else if (std.mem.eql(u8, pred, "ueq")) 8 else if (std.mem.eql(u8, pred, "ugt"))
        9
    else if (std.mem.eql(u8, pred, "uge")) 10 else if (std.mem.eql(u8, pred, "ult"))
        11
    else if (std.mem.eql(u8, pred, "ule")) 12 else if (std.mem.eql(u8, pred, "une"))
        13
    else if (std.mem.eql(u8, pred, "uno")) 14 else if (std.mem.eql(u8, pred, "true"))
        15
    else
        unreachable;
    return mlir.Attribute.integerAttrGet(self.i64_ty, val);
}

/// Append `op` into the current block held by `Codegen`.
pub fn append(self: *Codegen, op: mlir.Operation) void {
    self.cur_block.?.appendOwnedOperation(op);
}

/// Check whether `v` represents an `llvm.mlir.undef` placeholder.
pub fn isUndefValue(self: *const Codegen, v: mlir.Value) bool {
    _ = self;
    if (!v.isAOpResult()) return false;
    var owner = v.opResultGetOwner();
    if (owner.isNull()) return false;
    var name_id = owner.getName();
    const name = name_id.str().toSlice();
    return std.mem.eql(u8, name, "llvm.mlir.undef");
}

/// Wrap `attr` and `name` into a MLIR `NamedAttribute`.
pub fn named(self: *const Codegen, name: []const u8, attr: mlir.Attribute) mlir.NamedAttribute {
    return .{
        .inner = .{
            .name = mlir.c.mlirIdentifierGet(self.mlir_ctx.handle, mlir.StringRef.from(name).inner),
            .attribute = attr.handle,
        },
    };
}
/// Helper that interns a string into an MLIR StringAttr.
pub fn strAttr(self: *const Codegen, s: []const u8) mlir.Attribute {
    return mlir.Attribute.stringAttrGet(self.mlir_ctx, mlir.StringRef.from(s));
}

/// Lightweight builder arguments for `emitOp`.
pub const EmitOpArgs = struct {
    operands: ?[]const mlir.Value = null,
    results: ?[]const mlir.Type = null,
    attributes: ?[]const mlir.NamedAttribute = null,
    regions: ?[]const mlir.Region = null,
    successors: ?[]const mlir.Block = null,
};

/// Build `name` with the given operands/results/etc. without appending.
pub fn buildOp(self: *Codegen, name: []const u8, args: EmitOpArgs) mlir.Operation {
    var builder = OpBuilder.init(name, self.loc).builder();
    if (args.operands) |ops| _ = builder.operands(ops);
    if (args.results) |res| _ = builder.results(res);
    if (args.attributes) |attrs| _ = builder.attributes(attrs);
    if (args.regions) |regs| _ = builder.regions(regs);
    if (args.successors) |succs| _ = builder.successors(succs);

    return builder.build();
}

/// Append the previously built operation into the current block.
pub fn appendOp(self: *Codegen, name: []const u8, args: EmitOpArgs) mlir.Operation {
    const op = self.buildOp(name, args);
    self.append(op);
    return op;
}

/// Emit `name` with the given operands/results and append its result if available.
pub fn emitOp(self: *Codegen, name: []const u8, args: EmitOpArgs) mlir.Value {
    const op = self.appendOp(name, args);
    if (op.getNumResults() == 0) return .empty();
    return op.getResult(0);
}

/// Emit a binary operation that consumes two values and produces one result.
pub fn emitBinaryValueOp(
    self: *Codegen,
    name: []const u8,
    lhs: mlir.Value,
    rhs: mlir.Value,
    result_ty: mlir.Type,
    attrs: ?[]const mlir.NamedAttribute,
) mlir.Value {
    return self.emitOp(name, EmitOpArgs{
        .operands = &.{ lhs, rhs },
        .results = &.{result_ty},
        .attributes = attrs,
    });
}

/// Emit a unary operation that consumes one value and produces one result.
pub fn emitUnaryValueOp(self: *Codegen, name: []const u8, operand: mlir.Value, result_ty: mlir.Type) mlir.Value {
    return self.emitOp(name, EmitOpArgs{
        .operands = &.{operand},
        .results = &.{result_ty},
    });
}

/// Helper that panics if a value ID is missing from the map.
fn getVal(self: *Codegen, id: tir.ValueId) mlir.Value {
    return self.value_map.get(id) orelse std.debug.panic("missing value for instr {}", .{id});
}

/// Shortcut for getting the SR kind for a type.
fn srKind(self: *Codegen, ty: types.TypeId) types.TypeKind {
    return self.context.type_store.getKind(ty);
}

/// Emit a zero constant for `ty`, using splat for vectors and `llvm.mlir.zero` otherwise.
pub fn zeroOf(self: *Codegen, ty: mlir.Type) mlir.Value {
    if (ty.isAVector()) {
        const elem_ty = ty.getShapedElementType();
        var elem_zero: mlir.Attribute = undefined;
        if (elem_ty.isAFloat()) {
            elem_zero = mlir.Attribute.floatAttrDoubleGet(self.mlir_ctx, elem_ty, 0.0);
        } else if (elem_ty.isAInteger()) {
            elem_zero = mlir.Attribute.integerAttrGet(elem_ty, 0);
        } else {
            return self.undefOf(ty);
        }
        const dense = mlir.Attribute.denseElementsAttrSplatGet(ty, elem_zero);
        return self.emitOp("arith.constant", EmitOpArgs{
            .results = &.{ty},
            .attributes = &.{self.named("value", dense)},
        });
    }
    return self.emitOp("llvm.mlir.zero", EmitOpArgs{
        .results = &.{ty},
    });
}

/// Convert `value` to the MLIR `index` type, emitting a cast if needed.
fn ensureIndexValue(self: *Codegen, value: mlir.Value) !mlir.Value {
    const idx_ty = mlir.Type.getIndexType(self.mlir_ctx);
    if (value.getType().equal(idx_ty)) return value;
    if (value.getType().isAInteger()) {
        return self.emitUnaryValueOp("arith.index_cast", value, idx_ty);
    }
    return value;
}

/// Emit a null pointer constant of `llvm_ptr_ty`.
fn llvmNullPtr(self: *Codegen) mlir.Value {
    // Create a null pointer via constant integer 0 casted to ptr
    const zero = self.constInt(self.i64_ty, 0);
    return self.emitUnaryValueOp("llvm.inttoptr", zero, self.llvm_ptr_ty);
}

/// Emit an `llvm.mlir.undef` of type `ty`.
pub fn undefOf(self: *Codegen, ty: mlir.Type) mlir.Value {
    return self.emitOp("llvm.mlir.undef", EmitOpArgs{
        .results = &.{ty},
    });
}

/// Insert `val` at `pos` into the aggregate `agg`.
pub fn insertAt(self: *Codegen, agg: mlir.Value, val: mlir.Value, pos: []const i64) mlir.Value {
    std.debug.assert(!mlir.LLVM.isLLVMPointerType(agg.getType()));
    const pos_attr = mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, pos);
    return self.emitOp("llvm.insertvalue", EmitOpArgs{
        .operands = &.{ agg, val },
        .results = &.{agg.getType()},
        .attributes = &.{self.named("position", pos_attr)},
    });
}

/// Extract the element at `pos` from `agg` and cast it to `res_ty`.
pub fn extractAt(self: *Codegen, agg: mlir.Value, res_ty: mlir.Type, pos: []const i64) mlir.Value {
    // If the source is a pointer, load the requested type directly. This avoids
    // invalid extractvalue-on-pointer and matches our opaque-pointer lowering model.
    if (mlir.LLVM.isLLVMPointerType(agg.getType())) {
        return self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{agg},
            .results = &.{res_ty},
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
    }
    const pos_attr = mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, pos);
    return self.emitOp("llvm.extractvalue", EmitOpArgs{
        .operands = &.{agg},
        .results = &.{res_ty},
        .attributes = &.{self.named("position", pos_attr)},
    });
}

/// Spill `aggVal` into a temporary alloca and return the pointer, honoring `alignment` bytes.
pub fn spillAgg(self: *Codegen, aggVal: mlir.Value, elemTy: mlir.Type, alignment: u32) mlir.Value {
    var n_attrs: usize = 1;
    var attrs_buf: [2]mlir.NamedAttribute = undefined;
    attrs_buf[0] = self.named("elem_type", mlir.Attribute.typeAttrGet(elemTy));
    if (alignment != 0) {
        attrs_buf[1] = self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, alignment));
        n_attrs = 2;
    }
    const attrs = attrs_buf[0..n_attrs];

    const one = self.getI64OneInEntry();
    const a = self.buildOp("llvm.alloca", EmitOpArgs{
        .operands = &.{one},
        .results = &.{self.llvm_ptr_ty},
        .attributes = attrs,
    });
    self.appendInFuncEntry(a);

    _ = self.appendOp("llvm.store", EmitOpArgs{
        .operands = &.{ aggVal, a.getResult(0) },
    });
    return a.getResult(0);
}

// Load iN from ptr + offset
/// Load an integer of `bits` width from the buffer at `base` plus `offset`.
fn loadIntAt(self: *Codegen, base: mlir.Value, bits: u32, offset: usize) mlir.Value {
    const ity = mlir.Type.getSignlessIntegerType(self.mlir_ctx, bits);
    var p = base;
    if (offset != 0) {
        const offv = self.constInt(self.i64_ty, @intCast(offset));
        p = self.emitOp("llvm.getelementptr", EmitOpArgs{
            .operands = &.{ base, offv },
            .results = &.{self.llvm_ptr_ty},
            .attributes = &.{
                self.named("elem_type", mlir.Attribute.typeAttrGet(self.i8_ty)),
                self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{std.math.minInt(i32)})),
            },
        });
    }
    return self.emitOp("llvm.load", EmitOpArgs{
        .operands = &.{p},
        .results = &.{ity},
        .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
    });
}

// Store scalar at ptr + offset
/// Store `val` at the byte offset `offset` relative to `base`.
pub fn storeAt(self: *Codegen, base: mlir.Value, val: mlir.Value, offset: usize) void {
    var p = base;
    if (offset != 0) {
        const offv = self.constInt(self.i64_ty, @intCast(offset));
        p = self.emitOp("llvm.getelementptr", EmitOpArgs{
            .operands = &.{ base, offv },
            .results = &.{self.llvm_ptr_ty},
            .attributes = &.{
                self.named("elem_type", mlir.Attribute.typeAttrGet(self.i8_ty)),
                self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{std.math.minInt(i32)})),
            },
        });
    }
    _ = self.appendOp("llvm.store", EmitOpArgs{
        .operands = &.{ val, p },
        .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
    });
}

/// Emit a constant integer `v` of MLIR type `ty`.
pub fn constInt(self: *Codegen, ty: mlir.Type, v: i128) mlir.Value {
    return self.emitOp("llvm.mlir.constant", EmitOpArgs{
        .results = &.{ty},
        .attributes = &.{self.named("value", mlir.Attribute.integerAttrGet(ty, @intCast(v)))},
    });
}

/// Emit a constant floating-point value `v` of MLIR type `ty`.
pub fn constFloat(self: *Codegen, ty: mlir.Type, v: f64) mlir.Value {
    const attr = mlir.Attribute.floatAttrDoubleGet(self.mlir_ctx, ty, v);
    return self.emitOp("llvm.mlir.constant", EmitOpArgs{
        .results = &.{ty},
        .attributes = &.{self.named("value", attr)},
    });
}

/// Emit an MLIR `i1` constant representing `v`.
pub fn constBool(self: *Codegen, v: bool) mlir.Value {
    return self.constInt(self.i1_ty, if (v) 1 else 0);
}

/// Return true when `ty` represents an unsigned integer kind.
fn isUnsigned(self: *Codegen, ty: types.TypeId) bool {
    return switch (self.context.type_store.getKind(ty)) {
        .U8, .U16, .U32, .U64, .Usize => true,
        else => false,
    };
}

/// Emit a generic binary operation using the provided MLIR opcode and result type.
fn emitBinOp(self: *Codegen, p: tir.Rows.Bin2, op_name: []const u8, ty: mlir.Type) !mlir.Value {
    const lhs = self.getVal(p.lhs);
    const rhs = self.getVal(p.rhs);
    return self.emitOp(op_name, EmitOpArgs{
        .operands = &.{ lhs, rhs },
        .results = &.{ty},
    });
}

/// Emit binary arithmetic operations (add/sub/mul) for `p` with float/int dispatch.
fn binArith(
    self: *Codegen,
    comptime op_kind: BinArithOp,
    p: tir.Rows.Bin2,
) !mlir.Value {
    const ty = try self.llvmTypeOf(p.ty);
    const elem_ty = if (ty.isAVector()) ty.getShapedElementType() else ty;

    const op_name = if (elem_ty.isAFloat())
        switch (op_kind) {
            .add => "arith.addf",
            .sub => "arith.subf",
            .mul => "arith.mulf",
        }
    else switch (op_kind) {
        .add => "arith.addi",
        .sub => "arith.subi",
        .mul => "arith.muli",
    };

    return self.emitBinOp(p, op_name, ty);
}

/// Extend or truncate `v` to `to_ty` respecting signedness.
fn extendIntegerValue(self: *Codegen, v: mlir.Value, signed: bool, to_ty: mlir.Type) mlir.Value {
    const from_ty = v.getType();
    const from_w = cast.intOrFloatWidth(from_ty) catch 0;
    const to_w = cast.intOrFloatWidth(to_ty) catch 0;
    if (from_w >= to_w) return v;
    const opname = if (signed) "arith.extsi" else "arith.extui";
    return self.emitUnaryValueOp(opname, v, to_ty);
}

/// Emit integer binary ops that saturate (used only when requested).
fn emitSaturatingIntBinary(
    self: *Codegen,
    p: tir.Rows.Bin2,
    arith_name: []const u8,
    rhs_uses_lhs_sign: bool,
) !mlir.Value {
    const kind = self.context.type_store.getKind(p.ty);
    std.debug.assert(switch (kind) {
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
        else => false,
    });
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const lhs = self.value_map.get(p.lhs).?;
    const rhs = self.value_map.get(p.rhs).?;
    const res_ty = try self.llvmTypeOf(p.ty);
    const base_width = cast.intOrFloatWidth(res_ty) catch unreachable;
    std.debug.assert(base_width > 0);
    const wide_width = base_width * 2;
    const ext_ty = mlir.Type.getSignlessIntegerType(self.mlir_ctx, @intCast(wide_width));

    const lhs_signed = self.isSignedInt(p.ty);
    const rhs_signed = if (rhs_uses_lhs_sign) lhs_signed else false;

    const lhs_ext = self.extendIntegerValue(lhs, lhs_signed, ext_ty);
    const rhs_ext = self.extendIntegerValue(rhs, rhs_signed, ext_ty);

    const wide = self.emitBinaryValueOp(arith_name, lhs_ext, rhs_ext, ext_ty, null);
    return cast.saturateIntToInt(self, wide, lhs_signed, res_ty, lhs_signed);
}

/// Emit bitwise binary operations (and/or/xor) for `p`.
fn binBit(
    self: *Codegen,
    comptime op_kind: BinBitOp,
    p: tir.Rows.Bin2,
) !mlir.Value {
    const lhs = self.getVal(p.lhs);
    const rhs = self.getVal(p.rhs);
    const ty = try self.llvmTypeOf(p.ty);

    const op_name = switch (op_kind) {
        .@"and" => "arith.andi",
        .@"or" => "arith.ori",
        .xor => "arith.xori",
    };
    return self.emitBinaryValueOp(op_name, lhs, rhs, ty, null);
}

/// Emit division operations (signed or unsigned) for the arithmetic lowerings.
fn arithDiv(self: *Codegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type, signed: bool) mlir.Value {
    const elem_ty = if (res_ty.isAVector()) res_ty.getShapedElementType() else res_ty;
    const op_name = if (elem_ty.isAFloat()) "arith.divf" else (if (signed) "arith.divsi" else "arith.divui");
    return self.emitBinaryValueOp(op_name, lhs, rhs, res_ty, null);
}

/// Emit remainder operations for signed/unsigned integers.
fn arithRem(self: *Codegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type, signed: bool) mlir.Value {
    const elem_ty = if (res_ty.isAVector()) res_ty.getShapedElementType() else res_ty;
    const op_name = if (elem_ty.isAFloat()) "arith.remf" else (if (signed) "arith.remsi" else "arith.remui");
    return self.emitBinaryValueOp(op_name, lhs, rhs, res_ty, null);
}

/// Emit a shift-left operation for `lhs` and `rhs`.
fn arithShl(self: *Codegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type) mlir.Value {
    return self.emitBinaryValueOp("arith.shli", lhs, rhs, res_ty, null);
}

/// Emit a shift-right operation, choosing arithmetic vs logical based on `signed`.
fn arithShr(self: *Codegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type, signed: bool) mlir.Value {
    const op_name = if (signed) "arith.shrsi" else "arith.shrui";
    return self.emitBinaryValueOp(op_name, lhs, rhs, res_ty, null);
}

/// Emit a logical-not operation on i1 values.
fn arithLogicalNotI1(self: *Codegen, v: mlir.Value, loc: tir.OptLocId) mlir.Value {
    const prev_loc = self.pushLocation(loc);
    defer self.loc = prev_loc;
    // !v  ==  xori v, true
    return self.emitBinaryValueOp("arith.xori", v, self.constBool(true), self.i1_ty, null);
}

/// Emit a select operation `c ? tv : ev` returning `res_ty`.
fn arithSelect(self: *Codegen, c: mlir.Value, tv: mlir.Value, ev: mlir.Value, res_ty: mlir.Type) mlir.Value {
    return self.emitOp("arith.select", EmitOpArgs{
        .operands = &.{ c, tv, ev },
        .results = &.{res_ty},
    });
}

/// Lookup or rebuild the `FuncInfo` for the call target `p`.
fn ensureDeclFromCall(self: *Codegen, p: tir.Rows.Call, t: *const tir.TIR) !FuncInfo {
    const args_slice = t.instrs.val_list_pool.slice(p.args);
    var arg_tys = try self.gpa.alloc(mlir.Type, args_slice.len);
    defer self.gpa.free(arg_tys);
    for (args_slice, 0..) |vid, i| arg_tys[i] = self.value_map.get(vid).?.getType();
    const ret_ty = try self.llvmTypeOf(p.ty);
    const name = t.instrs.strs.get(p.callee);
    const callee_id = p.callee;

    if (std.mem.startsWith(u8, name, "m$")) {
        return .{
            .op = self.module.getOperation(),
            .is_variadic = false,
            .n_formals = arg_tys.len,
            .ret_type = ret_ty,
            .param_types = @constCast((&[_]mlir.Type{})[0..]),
            .owns_param_types = false,
            .dbg_subprogram = null,
        };
    }

    // Create a plain func.func declaration so internal functions remain in the
    // Func dialect; externs are handled via emitExternDecls.
    const n_res: usize = if (ret_ty.equal(self.void_ty)) 0 else 1;
    var res_buf: [1]mlir.Type = undefined;
    if (n_res == 1) res_buf[0] = ret_ty;
    const func_type = mlir.Type.getFunctionType(self.mlir_ctx, @intCast(arg_tys.len), arg_tys, @intCast(n_res), res_buf[0..n_res]);
    const attrs = [_]mlir.NamedAttribute{
        self.named("sym_name", self.strAttr(name)),
        self.named("function_type", mlir.Attribute.typeAttrGet(func_type)),
        self.named("sym_visibility", self.strAttr("private")),
    };
    const region = mlir.Region.create();
    const func_op = self.buildOp("func.func", EmitOpArgs{
        .attributes = &attrs,
        .regions = &.{region},
    });
    var body = self.module.getBody();
    body.appendOwnedOperation(func_op);

    const param_types_copy = try self.gpa.alloc(mlir.Type, arg_tys.len);
    std.mem.copyForwards(mlir.Type, param_types_copy, arg_tys);
    const info: FuncInfo = .{
        .op = func_op,
        .is_variadic = false,
        .n_formals = arg_tys.len,
        .ret_type = ret_ty,
        .param_types = param_types_copy,
        .owns_param_types = true,
        .dbg_subprogram = null,
    };
    _ = try self.func_syms.put(callee_id, info);
    return info;
}

/// Emit an LLVM global string literal for `text`.
fn constStringPtr(self: *Codegen, text: []const u8) !mlir.Operation {
    if (self.str_pool.get(text)) |*g| {
        // known length: bytes + NUL
        return self.addrOfFirstCharLen(@constCast(g), text.len + 1);
    }

    var hasher = std.hash.Fnv1a_64.init();
    hasher.update(text);
    const h = hasher.final();
    const name = try std.fmt.allocPrint(self.gpa, "__str_{x}", .{h});
    defer self.gpa.free(name);

    const esc = try self.escapeForMlirString(text);
    defer self.gpa.free(esc);

    const glb_src = try std.fmt.allocPrint(
        self.gpa,
        "llvm.mlir.global internal constant @{s}(\"{s}\\00\") {{addr_space = 0:i32}}",
        .{ name, esc },
    );
    defer self.gpa.free(glb_src);

    var global_op = mlir.Operation.createParse(
        self.mlir_ctx,
        mlir.StringRef.from(glb_src),
        mlir.StringRef.from("llvm.mlir.global"),
    );
    var body = self.module.getBody();
    body.appendOwnedOperation(global_op);
    _ = try self.str_pool.put(text, global_op);

    return self.addrOfFirstCharLen(&global_op, text.len + 1);
}

/// Return a pointer to an element inside `global_op` at `n_bytes` offset (first char).
fn addrOfFirstCharLen(self: *Codegen, global_op: *mlir.Operation, n_bytes: usize) !mlir.Operation {
    // &@global
    const name_attr = global_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
    const gsym = mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.Attribute.stringAttrGetValue(name_attr));

    const addr = self.appendOp("llvm.mlir.addressof", EmitOpArgs{
        .results = &.{self.llvm_ptr_ty},
        .attributes = &.{self.named("global_name", gsym)},
    });

    // GEP 0,0 into [n x i8] to get pointer to first char
    const arr_ty = mlir.LLVM.getLLVMArrayType(self.i8_ty, @intCast(n_bytes));
    return self.appendOp("llvm.getelementptr", EmitOpArgs{
        .operands = &.{addr.getResult(0)},
        .results = &.{self.llvm_ptr_ty},
        .attributes = &.{
            self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ 0, 0 })),
            self.named("elem_type", mlir.Attribute.typeAttrGet(arr_ty)),
        },
    });
}

/// Escape special characters in `s` so it can be used as an MLIR string literal.
fn escapeForMlirString(self: *Codegen, s: []const u8) ![]u8 {
    var out = ArrayList(u8).init(self.gpa);
    for (s) |c| {
        switch (c) {
            '"' => try out.appendSlice("\\22"),
            '\\' => try out.appendSlice("\\5C"),
            '\n' => try out.appendSlice("\\0A"),
            '\r' => try out.appendSlice("\\0D"),
            '\t' => try out.appendSlice("\\09"),
            else => try out.append(c),
        }
    }
    return out.toOwnedSlice();
}

/// Return true when `ty` is a signed integer in the SR type store.
pub fn isSignedInt(self: *Codegen, ty: types.TypeId) bool {
    return switch (self.context.type_store.getKind(ty)) {
        .I8, .I16, .I32, .I64 => true,
        else => false,
    };
}

/// Lookup the source-level type recorded for TIR value `vid`.
fn srTypeOfValue(self: *Codegen, vid: tir.ValueId) types.TypeId {
    if (self.val_types.get(vid)) |ty| return ty;
    // fallback: if unknown, prefer signed behavior
    return types.TypeId.fromRaw(0);
}

/// Retrieve the integer constant value stored by `vid`, if any.
fn constIntOf(self: *Codegen, t: *tir.TIR, vid: tir.ValueId) ?i128 {
    if (self.def_instr.get(vid)) |iid| {
        if (t.kind(iid) == .ConstInt) {
            return t.instrs.get(.ConstInt, iid).value;
        }
    }
    return null;
}

const AggregateElemCoercer = fn (
    *Codegen,
    types.TypeId,
    mlir.Type,
    mlir.Value,
    types.TypeId,
) anyerror!mlir.Value;

/// Return true if `kind` represents an aggregate (tuple/struct/array etc.) type.
fn isAggregateKind(kind: types.TypeKind) bool {
    return switch (kind) {
        .Struct, .Tuple, .Array, .Optional, .Union, .ErrorSet, .Error => true,
        else => false,
    };
}

/// Attempt to copy `src_val` from `src_sr` into `dst_ty` for `dst_sr` aggregates.
pub fn tryCopyAggregateValue(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
    elem_coercer: AggregateElemCoercer,
) anyerror!?mlir.Value {
    const dst_kind = self.context.type_store.getKind(dst_sr);
    const src_kind = self.context.type_store.getKind(src_sr);
    if (!isAggregateKind(dst_kind) or !isAggregateKind(src_kind)) return null;

    switch (dst_kind) {
        .Array => if (src_kind == .Array)
            return self.copyArrayAggregate(dst_sr, dst_ty, src_val, src_sr, elem_coercer),
        .Struct => if (src_kind == .Struct)
            return self.copyStructAggregate(dst_sr, dst_ty, src_val, src_sr, elem_coercer),
        .Tuple => if (src_kind == .Tuple)
            return self.copyTupleAggregate(dst_sr, dst_ty, src_val, src_sr, elem_coercer),
        .Optional => if (src_kind == .Optional)
            return self.copyOptionalAggregate(dst_sr, dst_ty, src_val, src_sr, elem_coercer),
        .Union => if (src_kind == .Union)
            return self.copyUnionAggregate(dst_sr, dst_ty, src_val, src_sr),
        .ErrorSet => if (src_kind == .ErrorSet)
            return self.copyErrorSetAggregate(dst_sr, dst_ty, src_val, src_sr, elem_coercer),
        .Error => if (src_kind == .ErrorSet)
            return self.copyErrorAggregate(dst_sr, dst_ty, src_val, src_sr, elem_coercer),
        else => {},
    }

    return null;
}

/// Copy a single indexed element from `src_val` into `result`.
fn copyAggregateElement(
    self: *Codegen,
    result: mlir.Value,
    idx: usize,
    dst_sr: types.TypeId,
    src_sr: types.TypeId,
    src_val: mlir.Value,
    elem_coercer: AggregateElemCoercer,
) anyerror!mlir.Value {
    const dst_elem_ty = try self.llvmTypeOf(dst_sr);
    const src_elem_ty = try self.llvmTypeOf(src_sr);
    const idx_arr = [_]i64{@intCast(idx)};
    const elem_val = self.extractAt(src_val, src_elem_ty, &idx_arr);
    const coerced = try elem_coercer(self, dst_sr, dst_elem_ty, elem_val, src_sr);
    return self.insertAt(result, coerced, &idx_arr);
}

/// Copy the contents of an error aggregate to the destination block.
fn copyErrorAggregate(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
    elem_coercer: AggregateElemCoercer,
) anyerror!?mlir.Value {
    const dst_info = self.context.type_store.get(.Error, dst_sr);
    const src_info = self.context.type_store.get(.Error, src_sr);

    const dst_variants = self.context.type_store.field_pool.slice(dst_info.variants);
    const src_variants = self.context.type_store.field_pool.slice(src_info.variants);
    if (dst_variants.len != src_variants.len) return null;

    var dst_union_fields = try self.gpa.alloc(types.TypeStore.StructFieldArg, dst_variants.len);
    defer self.gpa.free(dst_union_fields);
    var src_union_fields = try self.gpa.alloc(types.TypeStore.StructFieldArg, src_variants.len);
    defer self.gpa.free(src_union_fields);

    for (dst_variants, 0..) |dst_field_id, i| {
        const src_field_id = src_variants[i];
        const dst_field = self.context.type_store.Field.get(dst_field_id);
        const src_field = self.context.type_store.Field.get(src_field_id);
        if (!dst_field.name.eq(src_field.name)) return null;
        dst_union_fields[i] = .{ .name = dst_field.name, .ty = dst_field.ty };
        src_union_fields[i] = .{ .name = src_field.name, .ty = src_field.ty };
    }

    const dst_union_sr = self.context.type_store.mkUnion(dst_union_fields);
    const src_union_sr = self.context.type_store.mkUnion(src_union_fields);
    const dst_union_ty = try self.llvmTypeOf(dst_union_sr);
    const src_union_ty = try self.llvmTypeOf(src_union_sr);

    const tag = self.extractAt(src_val, self.i32_ty, &.{0});
    const src_payload = self.extractAt(src_val, src_union_ty, &.{1});

    var payload = try self.tryCopyAggregateValue(dst_union_sr, dst_union_ty, src_payload, src_union_sr, elem_coercer) orelse src_payload;
    if (!payload.getType().equal(dst_union_ty)) {
        payload = try elem_coercer(self, dst_union_sr, dst_union_ty, payload, src_union_sr);
    }

    var result = self.zeroOf(dst_ty);
    result = self.insertAt(result, tag, &.{0});
    result = self.insertAt(result, payload, &.{1});
    return result;
}

/// Copy the elements of an array aggregate into the destination region.
fn copyArrayAggregate(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
    elemCoercer: AggregateElemCoercer,
) anyerror!?mlir.Value {
    const dst_info = self.context.type_store.get(.Array, dst_sr);
    const src_info = self.context.type_store.get(.Array, src_sr);
    if (dst_info.len != src_info.len) return null;

    var result = self.undefOf(dst_ty);
    var idx: usize = 0;
    while (idx < dst_info.len) : (idx += 1) {
        result = try self.copyAggregateElement(result, idx, dst_info.elem, src_info.elem, src_val, elemCoercer);
    }
    return result;
}

/// Copy struct fields into the target aggregate storage.
fn copyStructAggregate(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
    elem_coercer: AggregateElemCoercer,
) anyerror!?mlir.Value {
    const dst_info = self.context.type_store.get(.Struct, dst_sr);
    const src_info = self.context.type_store.get(.Struct, src_sr);
    if (dst_info.fields.len != src_info.fields.len) return null;

    const dst_fields = self.context.type_store.field_pool.slice(dst_info.fields);
    const src_fields = self.context.type_store.field_pool.slice(src_info.fields);

    var result = self.undefOf(dst_ty);
    for (dst_fields, 0..) |dst_field_id, i| {
        const src_field_id = src_fields[i];
        const dst_field = self.context.type_store.Field.get(dst_field_id);
        const src_field = self.context.type_store.Field.get(src_field_id);
        result = try self.copyAggregateElement(
            result,
            i,
            dst_field.ty,
            src_field.ty,
            src_val,
            elem_coercer,
        );
    }
    return result;
}

/// Copy tuple elements into the destination.
fn copyTupleAggregate(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
    elem_coercer: AggregateElemCoercer,
) anyerror!?mlir.Value {
    const dst_info = self.context.type_store.get(.Tuple, dst_sr);
    const src_info = self.context.type_store.get(.Tuple, src_sr);
    if (dst_info.elems.len != src_info.elems.len) return null;

    const dst_elems = self.context.type_store.type_pool.slice(dst_info.elems);
    const src_elems = self.context.type_store.type_pool.slice(src_info.elems);

    var result = self.zeroOf(dst_ty);
    for (dst_elems, 0..) |dst_elem_sr, i| {
        const src_elem_sr = src_elems[i];
        result = try self.copyAggregateElement(result, i, dst_elem_sr, src_elem_sr, src_val, elem_coercer);
    }
    return result;
}

/// Copy optional aggregate elements, preserving flag/payload layout.
fn copyOptionalAggregate(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
    elem_coercer: AggregateElemCoercer,
) anyerror!?mlir.Value {
    const dst_info = self.context.type_store.get(.Optional, dst_sr);
    const src_info = self.context.type_store.get(.Optional, src_sr);

    const dst_ptr_opt = self.context.type_store.isOptionalPointer(dst_sr);
    const src_ptr_opt = self.context.type_store.isOptionalPointer(src_sr);
    if (dst_ptr_opt or src_ptr_opt) {
        if (!(dst_ptr_opt and src_ptr_opt)) return null;
        const dst_payload_ty = try self.llvmTypeOf(dst_info.elem);
        const coerced_payload = try elem_coercer(self, dst_info.elem, dst_payload_ty, src_val, src_info.elem);
        return coerced_payload;
    }

    const dst_payload_ty = try self.llvmTypeOf(dst_info.elem);
    const src_payload_ty = try self.llvmTypeOf(src_info.elem);

    const tag = self.extractAt(src_val, self.i1_ty, &.{0});
    const src_payload = self.extractAt(src_val, src_payload_ty, &.{1});
    const coerced_payload = try elem_coercer(self, dst_info.elem, dst_payload_ty, src_payload, src_info.elem);

    var result = self.zeroOf(dst_ty);
    result = self.insertAt(result, tag, &.{0});
    result = self.insertAt(result, coerced_payload, &.{1});
    return result;
}

/// Copy union aggregate data, selecting the active tag payload.
fn copyUnionAggregate(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
) anyerror!?mlir.Value {
    const dst_size = abi.abiSizeAlign(self, dst_sr).size;
    const src_size = abi.abiSizeAlign(self, src_sr).size;
    if (dst_size != src_size) return null;

    var result = self.zeroOf(dst_ty);
    var i: usize = 0;
    while (i < dst_size) : (i += 1) {
        const idx = [_]i64{@intCast(i)};
        const byte_val = self.extractAt(src_val, self.i8_ty, &idx);
        result = self.insertAt(result, byte_val, &idx);
    }
    return result;
}

/// Copy the fields of an error set aggregate, including tag/payload.
fn copyErrorSetAggregate(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
    elem_coercer: AggregateElemCoercer,
) anyerror!?mlir.Value {
    const dst_info = self.context.type_store.get(.ErrorSet, dst_sr);
    const src_info = self.context.type_store.get(.ErrorSet, src_sr);

    const ok_name = self.context.type_store.strs.intern("Ok");
    const err_name = self.context.type_store.strs.intern("Err");

    var dst_union_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = ok_name, .ty = dst_info.value_ty },
        .{ .name = err_name, .ty = dst_info.error_ty },
    };
    var src_union_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = ok_name, .ty = src_info.value_ty },
        .{ .name = err_name, .ty = src_info.error_ty },
    };

    const dst_union_sr = self.context.type_store.mkUnion(&dst_union_fields);
    const src_union_sr = self.context.type_store.mkUnion(&src_union_fields);
    const dst_union_ty = try self.llvmTypeOf(dst_union_sr);
    const src_union_ty = try self.llvmTypeOf(src_union_sr);

    const tag = self.extractAt(src_val, self.i32_ty, &.{0});
    const src_payload = self.extractAt(src_val, src_union_ty, &.{1});
    const coerced_payload = try self.tryCopyAggregateValue(dst_union_sr, dst_union_ty, src_payload, src_union_sr, elem_coercer) orelse src_payload;

    var result = self.undefOf(dst_ty);
    result = self.insertAt(result, tag, &.{0});
    result = self.insertAt(result, coerced_payload, &.{1});
    return result;
}

/// Reinterpret `src_val` as `dst_sr` by spilling aggregates to memory and copying bytes.
pub fn reinterpretAggregateViaSpill(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
) anyerror!?mlir.Value {
    const zero_sr = types.TypeId.fromRaw(0);
    if (dst_sr.eq(zero_sr) or src_sr.eq(zero_sr)) return null;

    const dst_kind = self.context.type_store.getKind(dst_sr);
    const src_kind = self.context.type_store.getKind(src_sr);
    // Only allow aggregate-to-aggregate reinterpret via spill. Reinterpreting an
    // aggregate into a scalar (or vice-versa) is semantically wrong for tagged
    // unions like ErrorSet and Optional and has been the source of corruption.
    if (!(isAggregateKind(dst_kind) and isAggregateKind(src_kind))) return null;

    const dst_layout = abi.abiSizeAlign(self, dst_sr);
    const src_layout = abi.abiSizeAlign(self, src_sr);

    const src_align = abi.abiSizeAlign(self, src_sr).alignment;
    const dst_align = abi.abiSizeAlign(self, dst_sr).alignment;
    const src_ptr = self.spillAgg(src_val, src_val.getType(), @intCast(src_align));
    const dst_init = self.zeroOf(dst_ty);
    const dst_ptr = self.spillAgg(dst_init, dst_ty, @intCast(dst_align));

    const copy_len = if (dst_layout.size < src_layout.size) dst_layout.size else src_layout.size;
    var i: usize = 0;
    while (i < copy_len) : (i += 1) {
        const byte = self.loadIntAt(src_ptr, 8, i);
        self.storeAt(dst_ptr, byte, i);
    }

    return self.emitOp("llvm.load", EmitOpArgs{
        .operands = &.{dst_ptr},
        .results = &.{dst_ty},
    });
}

/// Coerce an aggregate element when two branches need to reconcile differing layouts.
fn coerceAggregateElementOnBranch(
    self: *Codegen,
    dst_sr: types.TypeId,
    dst_ty: mlir.Type,
    src_val: mlir.Value,
    src_sr: types.TypeId,
) anyerror!mlir.Value {
    return self.coerceOnBranch(src_val, dst_ty, dst_sr, src_sr);
}

/// Coerce `v` to `want` type when branching requires a typed value of `dst_sr_ty`.
pub fn coerceOnBranch(
    self: *Codegen,
    v: mlir.Value,
    want: mlir.Type,
    dst_sr_ty: types.TypeId,
    src_sr_ty: types.TypeId,
) !mlir.Value {
    if (v.getType().equal(want)) return v;

    // (array-of-bytes to scalar typed-load path removed; implement at exact unwrap sites instead)

    // ptr <-> ptr : bitcast
    if (mlir.LLVM.isLLVMPointerType(v.getType()) and mlir.LLVM.isLLVMPointerType(want)) {
        return self.emitUnaryValueOp("llvm.bitcast", v, want);
    }

    // ptr -> int : ptrtoint
    if (mlir.LLVM.isLLVMPointerType(v.getType()) and want.isAInteger()) {
        return self.emitUnaryValueOp("llvm.ptrtoint", v, want);
    }

    // int -> ptr : inttoptr
    if (v.getType().isAInteger() and mlir.LLVM.isLLVMPointerType(want)) {
        return self.emitUnaryValueOp("llvm.inttoptr", v, want);
    }

    // vector float <-> vector int
    if (v.getType().isAVector() and want.isAVector()) {
        const v_elem = v.getType().getShapedElementType();
        const want_elem = want.getShapedElementType();

        if (v_elem.isAFloat() and want_elem.isAInteger()) {
            const to_signed = self.isSignedInt(dst_sr_ty);
            const op_name = if (to_signed) "arith.fptosi" else "arith.fptoui";
            return self.emitUnaryValueOp(op_name, v, want);
        }
        if (v_elem.isAInteger() and want_elem.isAFloat()) {
            const from_signed = self.isSignedInt(src_sr_ty);
            const op_name = if (from_signed) "arith.sitofp" else "arith.uitofp";
            return self.emitUnaryValueOp(op_name, v, want);
        }
    }

    // ints: zext/sext/trunc
    if (v.getType().isAInteger() and want.isAInteger()) {
        const fw = try cast.intOrFloatWidth(v.getType());
        const tw = try cast.intOrFloatWidth(want);
        if (fw == tw) return v;
        if (fw > tw) {
            return self.emitUnaryValueOp("arith.trunci", v, want);
        } else {
            const from_signed = self.isSignedInt(src_sr_ty);
            return self.emitUnaryValueOp(if (from_signed) "arith.extsi" else "arith.extui", v, want);
        }
    }

    // floats: fpext/fptrunc
    if (v.getType().isAFloat() and want.isAFloat()) {
        const fw = try cast.intOrFloatWidth(v.getType());
        const tw = try cast.intOrFloatWidth(want);
        if (fw == tw) return v;
        if (fw > tw) {
            return self.emitUnaryValueOp("arith.truncf", v, want);
        } else {
            return self.emitUnaryValueOp("arith.extf", v, want);
        }
    }

    // int<->float (rare here): use normal cast rules to avoid crashes
    if (v.getType().isAInteger() and want.isAFloat()) {
        const from_signed = self.isSignedInt(src_sr_ty);
        return self.emitUnaryValueOp(if (from_signed) "arith.sitofp" else "arith.uitofp", v, want);
    }
    if (v.getType().isAFloat() and want.isAInteger()) {
        const to_signed = self.isSignedInt(dst_sr_ty);
        return self.emitUnaryValueOp(if (to_signed) "arith.fptosi" else "arith.fptoui", v, want);
    }

    const zero_sr_ty = types.TypeId.fromRaw(0);
    if (!dst_sr_ty.eq(zero_sr_ty) and !src_sr_ty.eq(zero_sr_ty)) {
        const dst_kind = self.context.type_store.getKind(dst_sr_ty);
        const src_kind = self.context.type_store.getKind(src_sr_ty);

        if (dst_kind == .Error and src_kind == .ErrorSet) {
            return try self.errorSetToError(dst_sr_ty, want, src_sr_ty, v);
        }
    }

    if (try self.tryCopyAggregateValue(dst_sr_ty, want, v, src_sr_ty, coerceAggregateElementOnBranch)) |agg|
        return agg;

    if (try self.reinterpretAggregateViaSpill(dst_sr_ty, want, v, src_sr_ty)) |agg|
        return agg;

    // Avoid unsafe fallback bitcasts between aggregates and scalars.
    if (!dst_sr_ty.eq(zero_sr_ty) and !src_sr_ty.eq(zero_sr_ty)) {
        const dst_kind = self.context.type_store.getKind(dst_sr_ty);
        const src_kind = self.context.type_store.getKind(src_sr_ty);
        // If asked to coerce an ErrorSet to its Ok payload type, perform a
        // typed extraction instead of any byte-level reinterpretation.
        if (src_kind == .ErrorSet and !isAggregateKind(dst_kind)) {
            const es = self.context.type_store.get(.ErrorSet, src_sr_ty);
            const ok_mlir = try self.llvmTypeOf(es.value_ty);
            if (want.equal(ok_mlir)) {
                return try self.loadOkFromErrorSet(src_sr_ty, v);
            }
        }
        const dst_is_agg = isAggregateKind(dst_kind);
        const src_is_agg = isAggregateKind(src_kind);
        if (dst_is_agg != src_is_agg) {
            // Give up on coercion here; the caller should already be producing
            // the correct shaped value for aggregates at this point.
            return v;
        }
    }

    // last resort (should be rare): bitcast
    return self.emitUnaryValueOp("llvm.bitcast", v, want);
}

/// Extract the `Err` case from an `ErrorSet` value and coerce it into the `Error` union.
fn errorSetToError(
    self: *Codegen,
    dst_err_sr: types.TypeId,
    dst_err_ty: mlir.Type,
    src_errset_sr: types.TypeId,
    src_val: mlir.Value,
) anyerror!mlir.Value {
    const es = self.context.type_store.get(.ErrorSet, src_errset_sr);

    const ok_name = self.context.type_store.strs.intern("Ok");
    const err_name = self.context.type_store.strs.intern("Err");
    var union_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = ok_name, .ty = es.value_ty },
        .{ .name = err_name, .ty = es.error_ty },
    };

    const union_sr = self.context.type_store.mkUnion(&union_fields);
    const union_ty = try self.llvmTypeOf(union_sr);
    const payload = self.extractAt(src_val, union_ty, &.{1});

    const err_mlir = try self.llvmTypeOf(es.error_ty);
    const union_ptr = self.spillAgg(payload, union_ty, 0);
    const idxs = [_]tir.Rows.GepIndex{.{ .Const = 0 }};
    const err_ptr = try self.emitGep(union_ptr, err_mlir, &idxs);
    var err_val = self.emitOp("llvm.load", EmitOpArgs{
        .operands = &.{err_ptr},
        .results = &.{err_mlir},
    });
    if (!err_mlir.equal(dst_err_ty)) {
        err_val = try self.coerceOnBranch(err_val, dst_err_ty, dst_err_sr, es.error_ty);
    }

    return err_val;
}

// Typed load of the Ok payload from an ErrorSet aggregate value.
// src_val has SR type ErrorSet(V,E) with MLIR type { i32, union }.
// We extract field 1 (the union storage), spill to memory, GEP as a pointer to V,
// then perform a typed load of V.
/// Load the `Ok` payload from an `ErrorSet` when the tag indicates success.
fn loadOkFromErrorSet(
    self: *Codegen,
    src_errset_sr: types.TypeId,
    src_val: mlir.Value,
) !mlir.Value {
    const es = self.context.type_store.get(.ErrorSet, src_errset_sr);
    const ok_name = self.context.type_store.strs.intern("Ok");
    const err_name = self.context.type_store.strs.intern("Err");
    var union_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = ok_name, .ty = es.value_ty },
        .{ .name = err_name, .ty = es.error_ty },
    };
    const union_sr = self.context.type_store.mkUnion(&union_fields);
    const union_ty = try self.llvmTypeOf(union_sr);
    const payload = self.extractAt(src_val, union_ty, &.{1});

    const ok_mlir = try self.llvmTypeOf(es.value_ty);
    const alignment = abi.abiSizeAlign(self, es.value_ty).alignment;
    const union_ptr = self.spillAgg(payload, union_ty, @intCast(alignment));
    const idxs = [_]tir.Rows.GepIndex{.{ .Const = 0 }};
    const ok_ptr = try self.emitGep(union_ptr, ok_mlir, &idxs);
    return self.emitOp("llvm.load", EmitOpArgs{
        .operands = &.{ok_ptr},
        .results = &.{ok_mlir},
    });
}

/// Append `op` to the current block and return its single result if present.
pub fn appendIfHasResult(self: *Codegen, op: mlir.Operation) mlir.Value {
    if (op.getNumResults() == 0) return mlir.Value.empty();
    self.append(op);
    return op.getResult(0);
}

// boolean ops
/// Emit a boolean OR between `a` and `b`.
pub fn boolOr(self: *Codegen, a: mlir.Value, b: mlir.Value) mlir.Value {
    return appendIfHasResult(self, self.buildOp("arith.ori", EmitOpArgs{
        .operands = &.{ a, b },
        .results = &.{self.i1_ty},
    }));
}
/// Emit a boolean AND between `a` and `b`.
pub fn boolAnd(self: *Codegen, a: mlir.Value, b: mlir.Value) mlir.Value {
    return appendIfHasResult(self, self.buildOp("arith.andi", EmitOpArgs{
        .operands = &.{ a, b },
        .results = &.{self.i1_ty},
    }));
}
/// Emit a boolean NOT of `a`.
pub fn boolNot(self: *Codegen, a: mlir.Value) mlir.Value {
    const constants = self.emitOp("llvm.mlir.constant", EmitOpArgs{
        .results = &.{self.i1_ty},
        .attributes = &.{self.named("value", mlir.Attribute.integerAttrGet(self.i1_ty, 1))},
    });
    return self.emitBinaryValueOp("arith.xori", a, constants, self.i1_ty, null);
}

// call the lowered @assert(bool)
/// Emit a runtime `assert` call that aborts when `cond` is false.
fn emitAssertCall(self: *Codegen, cond: mlir.Value) void {
    const op = self.buildOp("func.call", EmitOpArgs{
        .operands = &.{cond},
        .attributes = &.{
            self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.Attribute.stringAttrGetValue(self.strAttr("assert")))),
            self.named("sym_visibility", self.strAttr("private")),
            self.named("function_type", mlir.Attribute.typeAttrGet(mlir.LLVM.getLLVMFunctionType(self.i1_ty, &.{self.i1_ty}, false))),
        },
    });
    _ = appendIfHasResult(self, op);
}

// --- Complex helpers ---

/// Extract the real part of the complex value `v`.
pub fn complexRe(self: *Codegen, v: mlir.Value, elem_ty: mlir.Type) mlir.Value {
    return self.emitUnaryValueOp("complex.re", v, elem_ty);
}

/// Extract the imaginary part of the complex value `v`.
pub fn complexIm(self: *Codegen, v: mlir.Value, elem_ty: mlir.Type) mlir.Value {
    return self.emitUnaryValueOp("complex.im", v, elem_ty);
}

/// Compose a complex value of type `complex_ty` from `re` and `im`.
pub fn complexFromParts(self: *Codegen, re: mlir.Value, im: mlir.Value, complex_ty: mlir.Type) mlir.Value {
    return self.emitOp("complex.create", EmitOpArgs{
        .operands = &.{ re, im },
        .results = &.{complex_ty},
    });
}

/// Map an SR type id to the corresponding MLIR type used during lowering.
pub fn llvmTypeOf(self: *Codegen, ty: types.TypeId) !mlir.Type {
    return switch (self.context.type_store.getKind(ty)) {
        .Void => self.void_ty,
        .Noreturn => self.void_ty,
        .Bool => self.i1_ty,

        .I8, .U8 => mlir.Type.getSignlessIntegerType(self.mlir_ctx, 8),
        .I16, .U16 => mlir.Type.getSignlessIntegerType(self.mlir_ctx, 16),
        .I32, .U32 => mlir.Type.getSignlessIntegerType(self.mlir_ctx, 32),
        .I64, .U64 => mlir.Type.getSignlessIntegerType(self.mlir_ctx, 64),

        .F32 => self.f32_ty,
        .F64 => self.f64_ty,
        .Usize => self.i64_ty,

        .Any, .Function, .Ptr, .MlirModule, .MlirAttribute, .MlirType => self.llvm_ptr_ty,

        .String, .Slice => blk: {
            // { ptr, len } (opaque ptr for data)
            const fields = [_]mlir.Type{ self.llvm_ptr_ty, self.i64_ty };
            break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
        },

        .Array => blk: {
            const arr_ty = self.context.type_store.get(.Array, ty);
            const e = try self.llvmTypeOf(arr_ty.elem);
            break :blk mlir.LLVM.getLLVMArrayType(e, @intCast(arr_ty.len));
        },
        .DynArray => blk: {
            const dyn_ty = self.context.type_store.get(.DynArray, ty);
            const elem_ptr_sr = self.context.type_store.mkPtr(dyn_ty.elem, false);
            const ptr_ty = try self.llvmTypeOf(elem_ptr_sr);
            const fields = [_]mlir.Type{ ptr_ty, self.i64_ty, self.i64_ty };
            break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
        },
        .Map => blk: {
            const map_ty = self.context.type_store.get(.Map, ty);
            // Materialize an entry struct type so we can reuse normal pointer lowering.
            const key_name = self.context.type_store.strs.intern("key");
            const val_name = self.context.type_store.strs.intern("value");
            const entry_sr_ty = self.context.type_store.mkStruct(&.{
                .{ .name = key_name, .ty = map_ty.key },
                .{ .name = val_name, .ty = map_ty.value },
            });
            const entry_ptr_ty = try self.llvmTypeOf(self.context.type_store.mkPtr(entry_sr_ty, false));
            // DynArray<Entry> = { ptr, len, cap }
            const dyn_fields = [_]mlir.Type{ entry_ptr_ty, self.i64_ty, self.i64_ty };
            const dyn_ty = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &dyn_fields, false);
            // Map = { len, entries }
            const map_fields = [_]mlir.Type{ self.i64_ty, dyn_ty };
            break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &map_fields, false);
        },
        .Simd => blk: {
            const simd_ty = self.context.type_store.get(.Simd, ty);
            const elem_ty = try self.llvmTypeOf(simd_ty.elem);
            var shape = [_]i64{@intCast(simd_ty.lanes)};
            break :blk mlir.Type.getVectorType(1, shape[0..], elem_ty);
        },
        .Tensor => blk: {
            const ten = self.context.type_store.get(.Tensor, ty);
            const rank: usize = @intCast(ten.rank);
            var shape_storage: [types.max_tensor_rank]i64 = undefined;
            var shape_slice: []const i64 = &[_]i64{};
            if (rank != 0) {
                var i: usize = 0;
                while (i < rank) : (i += 1) {
                    shape_storage[i] = @intCast(ten.dims[i]);
                }
                shape_slice = shape_storage[0..rank];
            }
            const elem_ty = try self.llvmTypeOf(ten.elem);
            break :blk mlir.Type.getRankedTensorType(@intCast(rank), shape_slice, elem_ty, mlir.Attribute.getNull());
        },
        .Complex => blk: {
            const c = self.context.type_store.get(.Complex, ty);
            const elem = try self.llvmTypeOf(c.elem);
            break :blk mlir.Type.getComplexType(elem);
        },

        .Optional => blk: {
            const opt_ty = self.context.type_store.get(.Optional, ty);
            if (self.context.type_store.isOptionalPointer(ty)) {
                break :blk try self.llvmTypeOf(opt_ty.elem);
            }
            const inner = try self.llvmTypeOf(opt_ty.elem);
            const fields = [_]mlir.Type{ self.i1_ty, inner };
            break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
        },

        .ErrorSet => blk: {
            const es = self.context.type_store.get(.ErrorSet, ty);
            const ok_name = self.context.type_store.strs.intern("Ok");
            const err_name = self.context.type_store.strs.intern("Err");
            var union_fields = [_]types.TypeStore.StructFieldArg{
                .{ .name = ok_name, .ty = es.value_ty },
                .{ .name = err_name, .ty = es.error_ty },
            };
            const payload_union = self.context.type_store.mkUnion(&union_fields);
            const payload_mlir = try self.llvmTypeOf(payload_union);
            const parts = [_]mlir.Type{ self.i32_ty, payload_mlir };
            break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &parts, false);
        },

        .Tuple => blk: {
            const tup_ty = self.context.type_store.get(.Tuple, ty);
            const n = tup_ty.elems.len;
            var buf = try self.gpa.alloc(mlir.Type, n);
            defer self.gpa.free(buf);
            const elems = self.context.type_store.type_pool.slice(tup_ty.elems);
            for (elems, 0..) |eid, i| buf[i] = try self.llvmTypeOf(eid);
            break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, buf, false);
        },

        .Struct => blk: {
            const st_ty = self.context.type_store.get(.Struct, ty);
            const n = st_ty.fields.len;
            var buf = try self.gpa.alloc(mlir.Type, n);
            defer self.gpa.free(buf);
            const fields = self.context.type_store.field_pool.slice(st_ty.fields);
            for (fields, 0..) |f, i| {
                const field = self.context.type_store.Field.get(f);
                buf[i] = try self.llvmTypeOf(field.ty);
            }
            break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, buf, false);
        },

        .Enum => blk: {
            // TODO: usee backing integer type if specified
            break :blk mlir.Type.getSignlessIntegerType(self.mlir_ctx, 32);
        },

        .Union => blk: {
            const un_ty = self.context.type_store.get(.Union, ty);
            const n = un_ty.fields.len;
            if (n == 0) break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{}, false);

            var max_size: usize = 0;
            var max_align: usize = 1;
            const fields = self.context.type_store.field_pool.slice(un_ty.fields);
            for (fields) |f| {
                const field = self.context.type_store.Field.get(f);
                const sa = abi.abiSizeAlign(self, field.ty);
                if (sa.size > max_size) max_size = sa.size;
                if (sa.alignment > max_align) max_align = sa.alignment;
            }
            const padded = std.mem.alignForward(usize, max_size, max_align);
            break :blk mlir.LLVM.getLLVMArrayType(self.i8_ty, @intCast(padded));
        },

        .Error => blk: {
            const e_ty = self.context.type_store.get(.Error, ty);
            const fields = self.context.type_store.field_pool.slice(e_ty.variants);
            if (fields.len == 0) {
                const parts = [_]mlir.Type{self.i32_ty};
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &parts, false);
            }

            var payload_types = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
            defer self.gpa.free(payload_types);
            for (fields, 0..) |f, i| {
                const field = self.context.type_store.Field.get(f);
                payload_types[i] = .{ .name = field.name, .ty = field.ty };
            }
            const union_ty = self.context.type_store.mkUnion(payload_types);
            const union_mlir_ty = try self.llvmTypeOf(union_ty);

            const parts = [_]mlir.Type{ self.i32_ty, union_mlir_ty };
            break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &parts, false);
        },

        .Variant => blk: {
            const v_ty = self.context.type_store.get(.Variant, ty);
            const n = v_ty.variants.len;
            var payload_types = try self.gpa.alloc(types.TypeStore.StructFieldArg, n);
            defer self.gpa.free(payload_types);

            const fields = self.context.type_store.field_pool.slice(v_ty.variants);
            for (fields, 0..) |f, i| {
                const field = self.context.type_store.Field.get(f);
                payload_types[i] = .{ .name = field.name, .ty = field.ty };
            }

            const union_ty = self.context.type_store.mkUnion(payload_types);
            const union_mlir_ty = try self.llvmTypeOf(union_ty);

            const fields_mlir = [_]mlir.Type{ self.i32_ty, union_mlir_ty };
            break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields_mlir, false);
        },
        .TypeType => return self.i64_ty,
        .Ast => return self.llvm_ptr_ty,
        .TypeError => return error.CompilationFailed,
        else => std.debug.panic("unhandled type: {}", .{self.context.type_store.getKind(ty)}),
    };
}
