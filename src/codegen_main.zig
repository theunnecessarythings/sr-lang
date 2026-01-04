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

const Allocator = std.mem.Allocator;
const ArrayList = std.array_list.Managed;

pub var enable_debug_info: bool = false;

/// Recorded line and column numbers computed from a source index.
const LineInfo = struct {
    line: usize,
    col: usize,
};

/// Operation kinds for binary arithmetic lowering helpers.
const BinArithOp = enum {
    add,
    sub,
    mul,
};
/// Binary bitwise/logical helpers emitted during lowering.
const BinBitOp = enum {
    @"and",
    @"or",
    xor,
};

/// Thin wrapper used by `mlir.Module.dump` callbacks to capture output as bytes.
pub const PrintBuffer = struct {
    list: *ArrayList(u8),
    had_error: *bool,
};

/// Callback invoked by MLIR printing helpers to stream characters into a buffer.
pub fn printCallback(str: mlir.c.MlirStringRef, user_data: ?*anyopaque) callconv(.c) void {
    const buf: *PrintBuffer = @ptrCast(@alignCast(user_data));
    buf.list.appendSlice(str.data[0..str.length]) catch {
        buf.had_error.* = true;
    };
}

fn computeLineIndex(line_starts: []const usize, offset: usize) usize {
    // Binary search for the line index
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
    var line: usize = 0;
    var last_nl: usize = 0;
    for (src[0..offset], 0..) |c, i| {
        if (c == '\n') {
            line += 1;
            last_nl = i + 1;
        }
    }
    return .{ .line = line, .col = if (offset >= last_nl) offset - last_nl else 0 };
}

fn ensureLineStarts(self: *Codegen, file_id: u32, src: []const u8) ![]usize {
    if (self.line_index_cache.get(file_id)) |cached| return cached;

    // Optimization: Use vectorized count for pre-allocation
    const count = std.mem.count(u8, src, "\n") + 1;
    var buf = try self.gpa.alloc(usize, count);

    buf[0] = 0;
    var line_idx: usize = 1;
    var pos: usize = 0;

    // Optimization: Use memchr (vectorized search) instead of byte-by-byte loop
    while (std.mem.indexOfScalarPos(u8, src, pos, '\n')) |nl_pos| {
        if (line_idx >= count) break;
        buf[line_idx] = nl_pos + 1;
        line_idx += 1;
        pos = nl_pos + 1;
    }

    try self.line_index_cache.put(file_id, buf);
    return buf;
}

/// Convert a byte index into a `LineInfo` so diagnostics can report (line,col).
fn computeLineCol(self: *Codegen, src: []const u8, index: usize, file_id: u32) LineInfo {
    const limit = @min(index, src.len);
    const lines = self.ensureLineStarts(file_id, src) catch return computeLineColFallback(src, limit);
    const line = computeLineIndex(lines, limit);
    return .{ .line = line, .col = limit - lines[line] };
}

/// Primary code generation driver that lowers TIR to MLIR/LLVM IR.
pub const Codegen = @This();

gpa: Allocator,
context: *compile.Context,
mlir_ctx: mlir.Context,
loc: mlir.Location,
module: mlir.Module,
emit_only_triton: bool,
has_triton_fns: bool = false,

// Caches
loc_cache: std.AutoHashMap(cst.LocId, mlir.Location),
file_cache: std.AutoHashMap(u32, []const u8),
line_index_cache: std.AutoHashMap(u32, []usize),
di_files: std.AutoHashMap(u32, debug.DebugFileInfo),
di_subprograms: std.AutoHashMap(tir.FuncId, debug.DebugSubprogramInfo),

// DI Attributes
di_null_type_attr: mlir.Attribute,
di_subroutine_null_type_attr: mlir.Attribute,
di_empty_expr_attr: mlir.Attribute,
di_type_cache: std.AutoHashMap(types.TypeId, mlir.Attribute),
di_recursive_ids: std.AutoHashMap(types.TypeId, mlir.Attribute),
next_di_id: usize = 0,
debug_module_attrs_initialized: bool = false,

// Common Types
void_ty: mlir.Type,
i1_ty: mlir.Type,
i8_ty: mlir.Type,
i32_ty: mlir.Type,
i64_ty: mlir.Type,
f32_ty: mlir.Type,
f64_ty: mlir.Type,
llvm_ptr_ty: mlir.Type,

// Symbol Tables & Maps
func_syms: std.AutoHashMap(tir.StrId, FuncInfo),
global_syms: std.StringHashMap(void),
str_pool: std.StringHashMap(mlir.Operation),
block_map: std.AutoHashMap(tir.BlockId, mlir.Block),
value_map: std.AutoHashMap(tir.ValueId, mlir.Value),
tensor_slots: std.AutoHashMap(tir.ValueId, mlir.Value),
tensor_elem_ptrs: std.AutoHashMap(tir.ValueId, TensorElemPtrInfo),
val_types: std.AutoHashMap(tir.ValueId, types.TypeId),
def_instr: std.AutoHashMap(tir.ValueId, tir.InstrId),
global_addr_cache: std.StringHashMap(mlir.Value),
force_llvm_func_syms: std.AutoHashMap(tir.StrId, void),
async_body_syms: std.AutoHashMap(tir.FuncId, tir.StrId),

// Function Context
cur_region: ?mlir.Region = null,
cur_block: ?mlir.Block = null,
func_entry_block: ?mlir.Block = null,
current_func_sym: ?tir.StrId = null,
i64_one_in_entry: ?mlir.Value = null,
ret_join_block: ?mlir.Block = null,
ret_has_value: bool = false,
ret_type_cache: ?mlir.Type = null,
current_func_is_async: bool = false,
current_scope: ?mlir.Attribute = null,
inline_mlir_counter: u32 = 0,

// Diagnostics
diagnostic_handler: mlir.c.MlirDiagnosticHandlerID,
diagnostic_data: *DiagnosticData,
active_type_info: ?*types.TypeInfo,
debug_arena: std.heap.ArenaAllocator,

pub fn getStr(self: *Codegen, id: cst.StrId) []const u8 {
    return self.context.type_store.strs.get(id);
}

pub const FuncInfo = struct {
    op: mlir.Operation,
    is_variadic: bool,
    n_formals: usize,
    ret_type: mlir.Type,
    param_types: []mlir.Type = &[_]mlir.Type{},
    owns_param_types: bool = false,
    dbg_subprogram: ?mlir.Attribute = null,
};

const TensorIndex = union(enum) { constant: i64, value: tir.ValueId };

const TensorElemPtrInfo = struct {
    root_ptr: tir.ValueId,
    elem_ty: types.TypeId,
    indices: []TensorIndex,
};

fn freeTensorElemPtrInfo(self: *Codegen, info: *TensorElemPtrInfo) void {
    if (info.indices.len != 0) {
        self.gpa.free(info.indices);
        info.indices = &.{};
    }
}

fn clearTensorElemPtrs(self: *Codegen) void {
    var it = self.tensor_elem_ptrs.valueIterator();
    while (it.next()) |info| self.freeTensorElemPtrInfo(info);
    self.tensor_elem_ptrs.clearRetainingCapacity();
}

fn releaseTensorElemPtrs(self: *Codegen) void {
    var it = self.tensor_elem_ptrs.valueIterator();
    while (it.next()) |info| self.freeTensorElemPtrInfo(info);
    self.tensor_elem_ptrs.clearRetainingCapacity();
}

/// Helper builder that accumulates operands/results/regions before creating an MLIR operation.
pub const OpBuilder = struct {
    ops: ?[]const mlir.Value = null,
    tys: ?[]const mlir.Type = null,
    attrs: ?[]const mlir.NamedAttribute = null,
    regs: ?[]const mlir.Region = null,
    succs: ?[]const mlir.Block = null,
    name: []const u8,
    loc: mlir.Location,

    pub fn init(name: []const u8, loc: mlir.Location) OpBuilder {
        return .{ .name = name, .loc = loc };
    }
    pub fn builder(self: *const OpBuilder) *OpBuilder {
        return @constCast(self);
    }
    pub fn operands(self: *OpBuilder, ops: []const mlir.Value) *OpBuilder {
        self.ops = ops;
        return self;
    }
    pub fn results(self: *OpBuilder, tys: []const mlir.Type) *OpBuilder {
        self.tys = tys;
        return self;
    }
    pub fn attributes(self: *OpBuilder, attrs: []const mlir.NamedAttribute) *OpBuilder {
        self.attrs = attrs;
        return self;
    }
    pub fn regions(self: *OpBuilder, regs: []const mlir.Region) *OpBuilder {
        self.regs = regs;
        return self;
    }
    pub fn successors(self: *OpBuilder, succs: []const mlir.Block) *OpBuilder {
        self.succs = succs;
        return self;
    }

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



fn appendMlirTypeText(self: *Codegen, buf: *ArrayList(u8), ty: mlir.Type) !void {
    try self.appendMlirPrintedText(buf, ty);
}

fn appendMlirAttributeText(self: *Codegen, buf: *ArrayList(u8), attr: mlir.Attribute) !void {
    try self.appendMlirPrintedText(buf, attr);
}

fn appendMlirModuleText(self: *Codegen, buf: *ArrayList(u8), module: mlir.Module) !void {
    try self.appendMlirPrintedText(buf, module.getOperation());
}

fn appendMlirPrintedText(self: *Codegen, buf: *ArrayList(u8), value: anytype) !void {
    var tmp = ArrayList(u8).init(self.gpa);
    defer tmp.deinit();
    var had_error = false;
    var pb = PrintBuffer{ .list = &tmp, .had_error = &had_error };
    value.print(printCallback, @ptrCast(&pb));
    if (had_error) return error.OutOfMemory;
    try buf.appendSlice(tmp.items);
}

fn appendMlirSpliceValue(self: *Codegen, buf: *ArrayList(u8), value: comp.ValueId, ty: ?types.TypeId) !void {
    const s = &self.active_type_info.?.val_store;
    switch (s.kind(value)) {
        .Void => return error.MlirSpliceMissingValue,
        .Int => {
            const v = s.get(.Int, value).value;
            if (ty) |tid| {
                const width: u32 = switch (self.context.type_store.getKind(tid)) {
                    .I8, .U8 => 8,
                    .I16, .U16 => 16,
                    .I32, .U32 => 32,
                    .I64, .U64 => 64,
                    else => 0,
                };
                if (width != 0) return buf.writer().print("{d} : i{d}", .{ v, width });
            }
            try buf.writer().print("{}", .{v});
        },
        .Float => try buf.writer().print("{}", .{s.get(.Float, value).value}),
        .Bool => try buf.appendSlice(if (s.get(.Bool, value).value) "true" else "false"),
        .String => try buf.appendSlice(s.get(.String, value).value),
        .Sequence => {
            const seq = s.get(.Sequence, value);
            try buf.writer().print("[sequence len={d}]", .{s.val_pool.slice(seq.elems).len});
        },
        .Struct => {
            const sv = s.get(.Struct, value);
            try buf.writer().print("<struct len={d}>", .{s.struct_field_pool.slice(sv.fields).len});
        },
        .Variant => try buf.appendSlice("<variant>"),
        .Map => {
            const mp = s.get(.Map, value);
            try buf.writer().print("<map len={d}>", .{s.map_entry_pool.slice(mp.entries).len});
        },
        .Range => {
            const rg = s.get(.Range, value);
            try buf.writer().print("range({d}..{d}{s})", .{ rg.start, rg.end, if (rg.inclusive) "=" else "" });
        },
        .Type => {
            const type_val = s.get(.Type, value).ty;
            const normalized = if (self.context.type_store.getKind(type_val) == .TypeType)
                self.context.type_store.get(.TypeType, type_val).of
            else
                type_val;
            if (self.llvmTypeOf(normalized)) |mlir_ty| {
                try self.appendMlirTypeText(buf, mlir_ty);
            } else |_| {
                try self.context.type_store.formatTypeForDiagnostic(type_val, .{}, buf.writer());
            }
        },
        .MlirType => try self.appendMlirTypeText(buf, s.get(.MlirType, value).ty),
        .MlirAttribute => try self.appendMlirAttributeText(buf, s.get(.MlirAttribute, value).attr),
        .MlirModule => try self.appendMlirModuleText(buf, s.get(.MlirModule, value).module),
        .Pointer => try buf.appendSlice("<pointer>"),
        .Function => return error.MlirSpliceMissingValue,
        .Code => return error.MlirSpliceMissingValue,
    }
}

fn renderMlirTemplate(self: *Codegen, t: *tir.TIR, pieces: []const tir.MlirPieceId) ![]u8 {
    var buf = ArrayList(u8).init(self.gpa);
    errdefer buf.deinit();
    for (pieces) |pid| {
        const piece = t.instrs.MlirPiece.get(pid);
        switch (piece.kind) {
            .literal => try buf.appendSlice(t.instrs.strs.get(piece.text)),
            .splice => try self.appendMlirSpliceValue(&buf, piece.value, piece.ty),
        }
    }
    return buf.toOwnedSlice();
}

const DiagnosticData = struct {
    context: *compile.Context,
    msg: ?[]const u8 = null,
    span: ?struct { start: u32, end: u32 } = null,
};

fn diagnosticHandler(diag: mlir.c.MlirDiagnostic, userdata: ?*anyopaque) callconv(.c) mlir.c.MlirLogicalResult {
    const data: *DiagnosticData = @ptrCast(@alignCast(userdata));
    var buf = ArrayList(u8).init(data.context.gpa);
    defer buf.deinit();

    var had_error = false;
    var pb = PrintBuffer{ .list = &buf, .had_error = &had_error };
    mlir.c.mlirDiagnosticPrint(diag, printCallback, @ptrCast(&pb));

    // Debug output for internal tracing
    std.debug.print("MLIR Diagnostic Raw: {s}\n", .{buf.items});

    const loc = mlir.c.mlirDiagnosticGetLocation(diag);
    const start = mlir.c.mlirLocationFileLineColRangeGetStartColumn(loc);
    const end = mlir.c.mlirLocationFileLineColRangeGetEndColumn(loc);

    data.msg = buf.toOwnedSlice() catch unreachable;
    data.span = .{ .start = if (start < 0) 0 else @intCast(start), .end = if (end < 0) 0 else @intCast(end) };
    return .{ .value = 1 };
}

pub fn init(gpa: Allocator, context: *compile.Context, mlir_ctx: *mlir.Context, emit_only_triton: bool) Codegen {
    const ctx = mlir_ctx.*;
    mlir_ctx.setAllowUnregisteredDialects(true);
    const diag_data = gpa.create(DiagnosticData) catch unreachable;
    diag_data.* = .{ .context = context };

    return .{
        .gpa = gpa,
        .context = context,
        .mlir_ctx = ctx,
        .loc = mlir.Location.unknownGet(ctx),
        .module = mlir.Module.createEmpty(mlir.Location.unknownGet(ctx)),
        .emit_only_triton = emit_only_triton,
        .loc_cache = .init(gpa),
        .file_cache = .init(gpa),
        .line_index_cache = .init(gpa),
        .di_files = .init(gpa),
        .di_subprograms = .init(gpa),
        .di_null_type_attr = .empty(),
        .di_subroutine_null_type_attr = .empty(),
        .di_empty_expr_attr = .empty(),
        .di_type_cache = .init(gpa),
        .di_recursive_ids = .init(gpa),
        .void_ty = .{ .handle = mlir.c.mlirLLVMVoidTypeGet(ctx.handle) },
        .i1_ty = mlir.Type.getSignlessIntegerType(ctx, 1),
        .i8_ty = mlir.Type.getSignlessIntegerType(ctx, 8),
        .i32_ty = mlir.Type.getSignlessIntegerType(ctx, 32),
        .i64_ty = mlir.Type.getSignlessIntegerType(ctx, 64),
        .f32_ty = mlir.Type.getFloat32Type(ctx),
        .f64_ty = mlir.Type.getFloat64Type(ctx),
        .llvm_ptr_ty = mlir.LLVM.getPointerType(ctx, 0),
        .func_syms = .init(gpa),
        .global_syms = .init(gpa),
        .str_pool = .init(gpa),
        .block_map = .init(gpa),
        .value_map = .init(gpa),
        .tensor_slots = .init(gpa),
        .tensor_elem_ptrs = .init(gpa),
        .val_types = .init(gpa),
        .def_instr = .init(gpa),
        .global_addr_cache = .init(gpa),
        .force_llvm_func_syms = .init(gpa),
        .async_body_syms = .init(gpa),
        .diagnostic_handler = mlir.c.mlirContextAttachDiagnosticHandler(ctx.handle, diagnosticHandler, @ptrCast(diag_data), null),
        .diagnostic_data = diag_data,
        .active_type_info = null,
        .debug_arena = std.heap.ArenaAllocator.init(gpa),
    };
}

pub fn deinit(self: *Codegen) void {
    self.debug_arena.deinit();
    self.resetDebugCaches();
    self.di_subprograms.deinit();
    self.di_files.deinit();
    self.di_type_cache.deinit();
    self.di_recursive_ids.deinit();

    var fit = self.func_syms.valueIterator();
    while (fit.next()) |info| if (info.owns_param_types) self.gpa.free(info.param_types);
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
    self.async_body_syms.deinit();

    var li_it = self.line_index_cache.valueIterator();
    while (li_it.next()) |lines| self.gpa.free(lines.*);
    self.line_index_cache.deinit();

    var it = self.file_cache.valueIterator();
    while (it.next()) |src| self.context.source_manager.gpa.free(@constCast(src.*));
    self.file_cache.deinit();
    self.loc_cache.deinit();

    if (self.diagnostic_data.msg) |msg| self.gpa.free(msg);
    self.gpa.destroy(self.diagnostic_data);
    mlir.c.mlirContextDetachDiagnosticHandler(self.mlir_ctx.handle, self.diagnostic_handler);
    self.module.destroy();
}

pub fn resetDebugCaches(self: *Codegen) void {
    debug.resetDebugCaches(self);
}

fn getFileSource(self: *Codegen, file_id: u32) ![]const u8 {
    if (self.file_cache.get(file_id)) |buf| return buf;
    const data = try self.context.source_manager.read(file_id);
    try self.file_cache.put(file_id, data);
    return data;
}

fn instrOptLoc(_: *Codegen, t: *tir.TIR, ins_id: tir.InstrId) tir.OptLocId {
    return switch (t.kind(ins_id)) {
        inline else => |k| t.instrs.get(k, ins_id).loc,
    };
}

fn termOptLoc(_: *Codegen, t: *tir.TIR, term_id: tir.TermId) tir.OptLocId {
    return switch (t.kind(term_id)) {
        inline else => |k| t.terms.get(k, term_id).loc,
    };
}

fn blockOptLoc(self: *Codegen, block_id: tir.BlockId, t: *tir.TIR) tir.OptLocId {
    const block = t.funcs.Block.get(block_id);
    const instrs = t.instrs.instr_pool.slice(block.instrs);
    for (instrs) |ins_id| {
        const loc = self.instrOptLoc(t, ins_id);
        if (!loc.isNone()) return loc;
    }
    return self.termOptLoc(t, block.term);
}

/// Helper to scan a specific block for GlobalAddr instructions that take function addresses.
fn analyzeBlockForAddrTaken(self: *Codegen, block_id: tir.BlockId, t: *tir.TIR) !void {
    const b = t.funcs.Block.get(block_id);
    const instrs = t.instrs.instr_pool.slice(b.instrs);
    const type_store = self.context.type_store;

    for (instrs) |iid| {
        if (t.kind(iid) != .GlobalAddr) continue;
        const row = t.instrs.get(.GlobalAddr, iid);

        if (type_store.getKind(row.ty) != .Ptr) continue;
        const ptr = type_store.get(.Ptr, row.ty);
        if (type_store.getKind(ptr.elem) != .Function) continue;

        _ = try self.force_llvm_func_syms.put(row.name, {});
    }
}

/// Populate a list of functions whose LLVM symbols must be emitted because addresses are taken.
fn collectForceLlvmFuncSyms(self: *Codegen, t: *tir.TIR) !void {
    self.force_llvm_func_syms.clearRetainingCapacity();
    const funcs = t.funcs.func_pool.inner.data.items;

    // Denestified loop: iterate functions -> iterate blocks -> analyze block
    for (funcs) |fid_raw| {
        const f = t.funcs.Function.get(tir.FuncId.fromRaw(fid_raw));
        const blocks = t.funcs.block_pool.slice(f.blocks);
        for (blocks) |bid| {
            try self.analyzeBlockForAddrTaken(bid, t);
        }
    }
}

fn functionOptLoc(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR) tir.OptLocId {
    const f = t.funcs.Function.get(f_id);
    const blocks = t.funcs.block_pool.slice(f.blocks);
    for (blocks) |block_id| {
        const loc = self.blockOptLoc(block_id, t);
        if (!loc.isNone()) return loc;
    }
    return .none();
}

// ----------------------------------------------------------------
// Public entry
// ----------------------------------------------------------------

/// Lower all dependency levels into MLIR by iterating through TIR units.
pub fn emit(self: *Codegen, levels: *const compile.DependencyLevels) !mlir.Module {
    var unit_by_file: std.AutoHashMap(u32, *package.FileUnit) = .init(self.gpa);
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
            if (unit.tir == null or unit.ast == null) {
                const path = self.context.source_manager.get(file_id) orelse "?";
                std.debug.print("codegen: missing {s} for file {s}\n", .{
                    if (unit.tir == null) "tir" else "ast",
                    path,
                });
                return error.MissingAstOrTir;
            }
            _ = try self.emitModule(unit.tir.?, &unit.ast.?.type_info);
        }
    }
    return self.module;
}

pub fn emitTritonModule(self: *Codegen, levels: *const compile.DependencyLevels) !mlir.Module {
    self.emit_only_triton = true;
    var unit_by_file: std.AutoHashMap(u32, *package.FileUnit) = .init(self.gpa);
    defer unit_by_file.deinit();

    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var source_iter = pkg.value_ptr.sources.iterator();
        while (source_iter.next()) |unit| {
            try unit_by_file.put(unit.value_ptr.file_id, unit.value_ptr);
        }
    }

    var ttg_target: ?[]const u8 = null;
    var ttg_num_warps: ?i32 = null;
    var ttg_threads_per_warp: ?i32 = null;
    var ttg_ptx_version: ?i32 = null;

    for (levels.levels.items) |level| {
        if (level.items.len == 0) continue;

        for (level.items) |file_id| {
            const unit = unit_by_file.get(file_id) orelse continue;
            if (unit.tir == null or unit.ast == null) {
                const path = self.context.source_manager.get(file_id) orelse "?";
                std.debug.print("codegen: missing {s} for file {s}\n", .{
                    if (unit.tir == null) "tir" else "ast",
                    path,
                });
                return error.MissingAstOrTir;
            }
            self.active_type_info = &unit.ast.?.type_info;
            defer self.active_type_info = null;
            for (unit.tir.?.funcs.func_pool.inner.data.items) |fid_raw| {
                const fid = tir.FuncId.fromRaw(fid_raw);
                const f = unit.tir.?.funcs.Function.get(fid);
                if (!f.is_triton_fn) continue;

                // Check attributes
                const attrs = unit.tir.?.instrs.attribute_pool.slice(f.attrs);
                for (attrs) |aid| {
                    const attr = unit.tir.?.instrs.Attribute.get(aid);
                    const name = unit.tir.?.instrs.strs.get(attr.name);
                    if (!attr.value.isNone()) {
                        const vid = attr.value.unwrap();
                        if (vid.toRaw() < unit.tir.?.value_defs.items.len) {
                            const instr_id = unit.tir.?.value_defs.items[vid.toRaw()];
                            if (instr_id.toRaw() != std.math.maxInt(u32)) {
                                const okind = unit.tir.?.instrs.index.kinds.items[instr_id.toRaw()];
                                const row_idx = unit.tir.?.instrs.index.rows.items[instr_id.toRaw()];

                                if (std.mem.eql(u8, name, "triton_target")) {
                                    if (okind == .ConstString) {
                                        const row = unit.tir.?.instrs.ConstString.get(cst.Index(tir.Rows.ConstString).fromRaw(row_idx));
                                        ttg_target = unit.tir.?.instrs.strs.get(row.text);
                                    }
                                } else if (std.mem.eql(u8, name, "triton_num_warps")) {
                                    if (okind == .ConstInt) {
                                        const row = unit.tir.?.instrs.ConstInt.get(cst.Index(tir.Rows.ConstInt).fromRaw(row_idx));
                                        ttg_num_warps = @intCast(row.value);
                                    }
                                } else if (std.mem.eql(u8, name, "triton_threads_per_warp")) {
                                    if (okind == .ConstInt) {
                                        const row = unit.tir.?.instrs.ConstInt.get(cst.Index(tir.Rows.ConstInt).fromRaw(row_idx));
                                        ttg_threads_per_warp = @intCast(row.value);
                                    }
                                } else if (std.mem.eql(u8, name, "triton_ptx_version")) {
                                    if (okind == .ConstInt) {
                                        const row = unit.tir.?.instrs.ConstInt.get(cst.Index(tir.Rows.ConstInt).fromRaw(row_idx));
                                        ttg_ptx_version = @intCast(row.value);
                                    }
                                }
                            }
                        }
                    }
                }

                const params = unit.tir.?.funcs.param_pool.slice(f.params);
                var has_any = self.context.type_store.getKind(f.result) == .Any;
                for (params) |pid| {
                    const p = unit.tir.?.funcs.Param.get(pid);
                    if (self.context.type_store.getKind(p.ty) == .Any) {
                        has_any = true;
                        break;
                    }
                }
                if (has_any) continue;
                try self.emitTritonFunction(fid, unit.tir.?);
            }
        }
    }

    var mod_op = self.module.getOperation();
    if (ttg_target) |t| {
        mod_op.setDiscardableAttributeByName(mlir.StringRef.from("ttg.target"), self.strAttr(t));
    }
    if (ttg_num_warps) |n| {
        mod_op.setDiscardableAttributeByName(mlir.StringRef.from("ttg.num-warps"), mlir.Attribute.integerAttrGet(self.i32_ty, n));
    }
    if (ttg_threads_per_warp) |n| {
        mod_op.setDiscardableAttributeByName(mlir.StringRef.from("ttg.threads-per-warp"), mlir.Attribute.integerAttrGet(self.i32_ty, n));
    }
    if (ttg_ptx_version) |n| {
        mod_op.setDiscardableAttributeByName(mlir.StringRef.from("ttg.ptx-version"), mlir.Attribute.integerAttrGet(self.i32_ty, n));
    }

    for (levels.levels.items) |level| {
        if (level.items.len == 0) continue;
        for (level.items) |file_id| {
            const unit = unit_by_file.get(file_id) orelse continue;
            if (unit.tir == null or unit.ast == null) {
                const path = self.context.source_manager.get(file_id) orelse "?";
                std.debug.print("codegen: missing {s} for file {s}\n", .{
                    if (unit.tir == null) "tir" else "ast",
                    path,
                });
                return error.MissingAstOrTir;
            }
            self.active_type_info = &unit.ast.?.type_info;
            defer self.active_type_info = null;
            for (unit.tir.?.funcs.func_pool.inner.data.items) |fid_raw| {
                const fid = tir.FuncId.fromRaw(fid_raw);
                const f = unit.tir.?.funcs.Function.get(fid);
                if (!f.is_triton_fn) continue;
                const params = unit.tir.?.funcs.param_pool.slice(f.params);
                var has_any = self.context.type_store.getKind(f.result) == .Any;
                for (params) |pid| {
                    const p = unit.tir.?.funcs.Param.get(pid);
                    if (self.context.type_store.getKind(p.ty) == .Any) {
                        has_any = true;
                        break;
                    }
                }
                if (has_any) continue;
                const blocks = unit.tir.?.funcs.block_pool.slice(f.blocks);
                if (blocks.len > 0) try self.emitFunctionBody(fid, unit.tir.?);
            }
        }
    }

    return self.module;
}

/// Lower a single TIR unit into MLIR, emitting functions and debug info.
pub fn emitModule(
    self: *Codegen,
    t: *tir.TIR,
    type_info: *types.TypeInfo,
) !mlir.Module {
    self.active_type_info = type_info;
    defer self.active_type_info = null;

    const prev_loc = self.loc;
    defer self.loc = prev_loc;

    self.di_subprograms.clearRetainingCapacity();
    self.loc_cache.clearRetainingCapacity();
    self.async_body_syms.clearRetainingCapacity();
    try self.collectForceLlvmFuncSyms(t);
    try debug.attachTargetInfo(self);
    try debug.ensureDebugModuleAttrs(self);
    try self.emitExternDecls(t);

    const func_ids = t.funcs.func_pool.inner.data.items;

    for (func_ids) |fid_raw| {
        const fid = tir.FuncId.fromRaw(fid_raw);
        const row = t.funcs.Function.get(fid);
        if (row.is_triton_fn) continue;
        try self.emitFunctionHeader(fid, t);
        if (row.is_async) {
            const body_sym = try self.asyncBodyName(fid, t);
            try self.emitAsyncBodyHeader(fid, t, body_sym);
        }
    }
    const module_has_async = blk: {
        for (func_ids) |fid_raw| {
            const fid = tir.FuncId.fromRaw(fid_raw);
            const row = t.funcs.Function.get(fid);
            if (row.is_async) break :blk true;
        }
        break :blk false;
    };
    if (module_has_async) {
        var mod_op = self.module.getOperation();
        mod_op.setDiscardableAttributeByName(
            mlir.StringRef.from("sr.has_async"),
            mlir.Attribute.unitAttrGet(self.mlir_ctx),
        );
    }
    for (func_ids) |fid_raw| {
        const fid = tir.FuncId.fromRaw(fid_raw);
        const row = t.funcs.Function.get(fid);
        if (row.is_triton_fn) {
            self.has_triton_fns = true;
            continue;
        }
        const blocks = t.funcs.block_pool.slice(row.blocks);
        if (blocks.len > 0) {
            if (row.is_async) {
                const body_sym = self.async_body_syms.get(fid) orelse try self.asyncBodyName(fid, t);
                const body_ret_ty = blk: {
                    if (self.context.type_store.getKind(row.result) == .Future) {
                        const fut = self.context.type_store.get(.Future, row.result);
                        break :blk try self.llvmTypeOf(fut.elem);
                    }
                    break :blk try self.llvmTypeOf(row.result);
                };
                try self.emitFunctionBodyWith(fid, t, body_sym, false, body_ret_ty);
                try self.emitAsyncWrapperBody(fid, t, body_sym);
            } else {
                try self.emitFunctionBody(fid, t);
            }
        }
    }
    return self.module;
}

/// Map `opt_loc` to an MLIR `Location`, caching repeated lookups.
fn mlirFileLineColLocation(self: *Codegen, opt_loc: tir.OptLocId) mlir.Location {
    if (opt_loc.isNone()) return self.loc;
    const loc_id = opt_loc.unwrap();
    if (self.loc_cache.get(loc_id)) |cached| return cached;

    const loc_record = self.context.loc_store.get(loc_id);
    // Use catch with payload to avoid double lookup or redundant flow
    const src = self.getFileSource(loc_record.file_id) catch return self.loc;

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
        self.loc = if (s.isNull()) file_loc else mlir.Location.fusedGet(self.mlir_ctx, &.{file_loc}, s);
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
            if (mlir.LLVM.getLLVMStructTypeNumElementTypes(ty) != fields.len) return error.Unexpected;

            // SBO for struct fields
            var buf: [32]mlir.Attribute = undefined;
            const field_attrs = if (fields.len <= 32) buf[0..fields.len] else try self.gpa.alloc(mlir.Attribute, fields.len);
            defer if (fields.len > 32) self.gpa.free(field_attrs);

            for (fields, 0..) |field_init, i| {
                field_attrs[i] = try self.attributeFromConstInit(field_init, mlir.LLVM.getLLVMStructTypeElementType(ty, i));
            }
            return mlir.Attribute.arrayAttrGet(self.mlir_ctx, field_attrs);
        },
        .none => mlir.Attribute.getNull(),
        else => error.Unsupported,
    };
}

/// Append an `llvm.return` operation carrying `val` into `block`.
fn appendReturnInBlock(self: *Codegen, block: *mlir.Block, val: mlir.Value) void {
    block.appendOwnedOperation(self.buildOp("llvm.return", EmitOpArgs{ .operands = &.{val} }));
}

/// Append an `llvm.mlir.zero` of type `ty` into `block` and return the new value.
fn appendZeroValueInBlock(self: *Codegen, block: *mlir.Block, ty: mlir.Type) mlir.Value {
    const op = self.buildOp("llvm.mlir.zero", EmitOpArgs{ .results = &.{ty} });
    block.appendOwnedOperation(op);
    return op.getResult(0);
}

/// Emit MLIR declarations for the extern globals and functions referenced in `t`.
fn emitExternDecls(self: *Codegen, t: *tir.TIR) !void {
    const global_ids = t.funcs.global_pool.inner.data.items;

    // Reusable buffers for SBO
    var param_ty_buf: [16]mlir.Type = undefined;
    var arg_attr_buf: [16]mlir.Attribute = undefined;
    for (global_ids) |gid_raw| {
        const gid = tir.GlobalId.fromRaw(gid_raw);
        const g = t.funcs.Global.get(gid);
        const name = t.instrs.strs.get(g.name);

        // --- Function Handling ---
        if (self.context.type_store.getKind(g.ty) == .Function) {
            if (self.func_syms.contains(g.name)) continue;

            const fnty = self.context.type_store.get(.Function, g.ty);
            var params_sr = self.context.type_store.type_pool.slice(fnty.params);
            if (fnty.is_variadic) params_sr = params_sr[0 .. params_sr.len - 1];

            // 1. Calculate lowered parameter count
            var num_lowered = @as(usize, 0);
            const ret_kind = self.context.type_store.getKind(fnty.result);
            const ret_no_res = ret_kind == .Void or ret_kind == .Noreturn;

            if (!ret_no_res) {
                if (abi.abiClassifyX64SysV(self, fnty.result, true).kind == .IndirectSRet) num_lowered += 1;
            }
            for (params_sr) |psr| {
                switch (abi.abiClassifyX64SysV(self, psr, false).kind) {
                    .IndirectByVal, .DirectScalar => num_lowered += 1,
                    .DirectPair => num_lowered += 2,
                    else => {},
                }
            }

            // 2. Alloc buffers (SBO)
            const lowered_params = if (num_lowered <= 16) param_ty_buf[0..num_lowered] else try self.gpa.alloc(mlir.Type, num_lowered);
            const argAttrs = if (num_lowered <= 16) arg_attr_buf[0..num_lowered] else try self.gpa.alloc(mlir.Attribute, num_lowered);
            defer if (num_lowered > 16) {
                self.gpa.free(lowered_params);
                self.gpa.free(argAttrs);
            };

            var n_args: usize = 0;
            var ret_type: mlir.Type = self.void_ty;

            // 3. ABI Lowering (Return)
            if (!ret_no_res) {
                const retClass = abi.abiClassifyX64SysV(self, fnty.result, true);
                switch (retClass.kind) {
                    .IndirectSRet => {
                        lowered_params[n_args] = self.llvm_ptr_ty;
                        argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &[_]mlir.NamedAttribute{
                            self.named("llvm.sret", mlir.Attribute.typeAttrGet(try self.llvmTypeOf(fnty.result))),
                            self.named("llvm.align", mlir.Attribute.integerAttrGet(self.i64_ty, retClass.alignment)),
                        });
                        n_args += 1;
                    },
                    .DirectScalar => ret_type = retClass.scalar0.?,
                    .DirectPair => ret_type = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ retClass.scalar0.?, retClass.scalar1.? }, false),
                    else => unreachable,
                }
            }

            // 4. ABI Lowering (Params)
            for (params_sr) |psr| {
                const cls = abi.abiClassifyX64SysV(self, psr, false);
                switch (cls.kind) {
                    .IndirectByVal => {
                        lowered_params[n_args] = self.llvm_ptr_ty;
                        argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &[_]mlir.NamedAttribute{
                            self.named("llvm.byval", mlir.Attribute.typeAttrGet(try self.llvmTypeOf(psr))),
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

            // 5. Build Op
            const fty = mlir.LLVM.getLLVMFunctionType(ret_type, lowered_params[0..n_args], fnty.is_variadic);
            const attrs = [_]mlir.NamedAttribute{
                self.named("sym_name", self.strAttr(name)),
                self.named("function_type", mlir.Attribute.typeAttrGet(fty)),
                self.named("arg_attrs", mlir.Attribute.arrayAttrGet(self.mlir_ctx, argAttrs[0..n_args])),
                self.named("sym_visibility", self.strAttr("private")),
            };

            const fnop = self.buildOp("llvm.func", EmitOpArgs{ .attributes = &attrs, .regions = &.{mlir.Region.create()} });
            var body = self.module.getBody();
            body.appendOwnedOperation(fnop);

            // 6. Cache Info
            const param_types_copy = try self.gpa.alloc(mlir.Type, n_args);
            @memcpy(param_types_copy, lowered_params[0..n_args]);
            try self.func_syms.put(g.name, .{
                .op = fnop,
                .is_variadic = fnty.is_variadic,
                .n_formals = params_sr.len,
                .ret_type = ret_type,
                .param_types = param_types_copy,
                .owns_param_types = true,
                .dbg_subprogram = null,
            });
        } else {
            // --- Global Variable Handling ---
            if (self.global_syms.contains(name)) continue;

            const var_mlir_ty = try self.llvmTypeOf(g.ty);
            var attrs = ArrayList(mlir.NamedAttribute).init(self.gpa);
            defer attrs.deinit();

            try attrs.append(self.named("sym_name", self.strAttr(name)));
            try attrs.append(self.named("global_type", mlir.Attribute.typeAttrGet(var_mlir_ty)));
            try attrs.append(self.named("sym_visibility", self.strAttr("private")));
            try attrs.append(self.named("linkage", mlir.LLVMAttributes.getLLVMLinkageAttr(self.mlir_ctx, .Internal)));

            var init_region = mlir.Region.create();
            if (g.init != .none) {
                try attrs.append(self.named("value", try self.attributeFromConstInit(g.init, var_mlir_ty)));
            } else if (self.context.type_store.getKind(g.ty) == .DynArray) {
                var block = mlir.Block.create(&.{}, &.{});
                init_region.appendOwnedBlock(block);
                self.appendReturnInBlock(&block, self.appendZeroValueInBlock(&block, var_mlir_ty));
            }

            const global_op = self.buildOp("llvm.mlir.global", EmitOpArgs{
                .attributes = attrs.items,
                .regions = &.{init_region},
            });
            var body = self.module.getBody();
            body.appendOwnedOperation(global_op);
            try self.global_syms.put(name, {});
        }
    }
}

/// Emit a Triton kernel declaration (`tt.func`) for `f_id`. Body is filled later.
fn emitTritonFunction(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR) !void {
    const f = t.funcs.Function.get(f_id);
    const func_name_id = f.name;

    if (self.func_syms.contains(func_name_id)) return;

    const params = t.funcs.param_pool.slice(f.params);
    const n_params = params.len;

    // SBO for parameter types
    var param_tys_buf: [16]mlir.Type = undefined;
    const param_tys = if (n_params <= 16) param_tys_buf[0..n_params] else try self.gpa.alloc(mlir.Type, n_params);
    defer if (n_params > 16) self.gpa.free(param_tys);

    for (params, 0..) |p_id, i| {
        param_tys[i] = try self.llvmTypeOf(t.funcs.Param.get(p_id).ty);
    }

    const ret_kind = self.context.type_store.getKind(f.result);
    const ret_no_result = (ret_kind == .Void or ret_kind == .Noreturn);
    const ret_ty = if (ret_no_result) self.void_ty else try self.llvmTypeOf(f.result);
    const results: []const mlir.Type = if (ret_no_result) &.{} else &.{ret_ty};

    const fty = mlir.Type.getFunctionType(self.mlir_ctx, @intCast(n_params), param_tys, @intCast(results.len), results);

    var attrs = ArrayList(mlir.NamedAttribute).init(self.gpa);
    defer attrs.deinit();

    // Check for kernel attributes
    var is_kernel = false;
    const attr_ids = t.instrs.attribute_pool.slice(f.attrs);
    for (attr_ids) |aid| {
        const name = t.instrs.strs.get(t.instrs.Attribute.get(aid).name);
        if (std.mem.eql(u8, name, "kernel") or std.mem.eql(u8, name, "triton_kernel")) {
            is_kernel = true;
            break;
        }
    }

    try attrs.append(self.named("sym_name", self.strAttr(t.instrs.strs.get(f.name))));
    try attrs.append(self.named("function_type", mlir.Attribute.typeAttrGet(fty)));
    try attrs.append(self.named("sym_visibility", self.strAttr(if (is_kernel) "public" else "private")));

    const fnop = self.buildOp("tt.func", EmitOpArgs{
        .attributes = attrs.items,
        .regions = &.{mlir.Region.create()},
    });

    var body = self.module.getBody();
    body.appendOwnedOperation(fnop);

    // Persist param types for FuncInfo (must own memory)
    const stored_param_tys = try self.gpa.alloc(mlir.Type, n_params);
    @memcpy(stored_param_tys, param_tys);

    try self.func_syms.put(func_name_id, .{
        .op = fnop,
        .is_variadic = false,
        .n_formals = n_params,
        .ret_type = ret_ty,
        .param_types = stored_param_tys,
        .owns_param_types = true,
        .dbg_subprogram = null,
    });
}

/// Prepare the MLIR function declaration/operator for `f_id` before emitting its body.
fn emitFunctionHeader(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR) !void {
    const f = t.funcs.Function.get(f_id);
    const func_name_id = f.name;
    if (self.func_syms.contains(func_name_id)) return;

    const params = t.funcs.param_pool.slice(f.params);
    const n_params = params.len;

    // SBO for parameter types
    var param_tys_buf: [16]mlir.Type = undefined;
    const param_tys = if (n_params <= 16) param_tys_buf[0..n_params] else try self.gpa.alloc(mlir.Type, n_params);
    defer if (n_params > 16) self.gpa.free(param_tys);

    for (params, 0..) |p_id, i| param_tys[i] = try self.llvmTypeOf(t.funcs.Param.get(p_id).ty);

    // Determine return type
    const ret_kind = self.context.type_store.getKind(f.result);
    const has_res = (ret_kind != .Void and ret_kind != .Noreturn);
    var res_buf: [1]mlir.Type = undefined;
    if (has_res) res_buf[0] = try self.llvmTypeOf(f.result);
    const results = if (has_res) res_buf[0..1] else res_buf[0..0];
    const fn_ret_ty = if (has_res) res_buf[0] else self.void_ty;

    const emit_as_llvm = self.force_llvm_func_syms.get(f.name) != null;
    const fty = if (emit_as_llvm)
        mlir.LLVM.getLLVMFunctionType(fn_ret_ty, param_tys, false)
    else
        mlir.Type.getFunctionType(self.mlir_ctx, @intCast(n_params), param_tys, @intCast(results.len), results);

    var attrs = ArrayList(mlir.NamedAttribute).init(self.gpa);
    defer attrs.deinit();

    try attrs.append(self.named("sym_name", self.strAttr(t.instrs.strs.get(f.name))));
    try attrs.append(self.named("function_type", mlir.Attribute.typeAttrGet(fty)));
    try attrs.append(self.named("sym_visibility", self.strAttr("public")));
    if (f.is_async) try attrs.append(self.named("async", mlir.Attribute.unitAttrGet(self.mlir_ctx)));
    if (emit_as_llvm) try attrs.append(self.named("CConv", mlir.LLVMAttributes.getLLVMCConvAttr(self.mlir_ctx, .C)));

    // Debug Info Logic (Flattened)
    const fn_loc = self.functionOptLoc(f_id, t);
    var maybe_dbg_attr: ?mlir.Attribute = null;
    if (enable_debug_info and !fn_loc.isNone()) blk: {
        const loc_record = self.context.loc_store.get(fn_loc.unwrap());
        const src = self.getFileSource(loc_record.file_id) catch break :blk;
        const lc = self.computeLineCol(src, loc_record.start, loc_record.file_id);

        const subp = debug.ensureDebugSubprogram(self, f_id, t.instrs.strs.get(f.name), @intCast(lc.line + 1), loc_record.file_id, fn_loc, f.result, params, t) catch break :blk;
        maybe_dbg_attr = subp.attr;
    }

    // Attribute Pass-through
    const emit_c_iface = t.instrs.strs.intern("llvm.emit_c_interface");
    const f_attrs = t.instrs.attribute_pool.slice(f.attrs);
    for (f_attrs) |aid| {
        if (t.instrs.Attribute.get(aid).name.eq(emit_c_iface)) {
            try attrs.append(self.named("llvm.emit_c_interface", mlir.Attribute.unitAttrGet(self.mlir_ctx)));
        }
    }

    // Emit Op
    const prev_loc = self.pushLocation(fn_loc);
    if (maybe_dbg_attr) |dbg| self.loc = mlir.Location.fusedGet(self.mlir_ctx, &.{self.loc}, dbg);
    defer self.loc = prev_loc;

    const fnop = self.buildOp(if (emit_as_llvm) "llvm.func" else "func.func", EmitOpArgs{
        .attributes = attrs.items,
        .regions = &.{mlir.Region.create()},
    });
    var body = self.module.getBody();
    body.appendOwnedOperation(fnop);

    // Save Info
    const stored_param_tys = try self.gpa.alloc(mlir.Type, n_params);
    @memcpy(stored_param_tys, param_tys);

    try self.func_syms.put(func_name_id, .{
        .op = fnop,
        .is_variadic = false,
        .n_formals = n_params,
        .ret_type = fn_ret_ty,
        .param_types = stored_param_tys,
        .owns_param_types = true,
        .dbg_subprogram = maybe_dbg_attr,
    });
}

/// Return a cached `i64` constant that lives in the entry block.
fn getI64OneInEntry(self: *Codegen) mlir.Value {
    if (self.i64_one_in_entry) |v| return v;
    const c = self.buildOp("llvm.mlir.constant", EmitOpArgs{
        .results = &.{self.i64_ty},
        .attributes = &.{self.named("value", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
    });
    self.appendInFuncEntry(c);
    self.i64_one_in_entry = c.getResult(0);
    return c.getResult(0);
}

/// Return (and cache) the outlined body symbol name for an async function.
fn asyncBodyName(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR) !tir.StrId {
    if (self.async_body_syms.get(f_id)) |sid| return sid;
    const name = try std.fmt.allocPrint(self.gpa, "{s}$async_body", .{t.instrs.strs.get(t.funcs.Function.get(f_id).name)});
    defer self.gpa.free(name);
    const sid = self.context.type_store.strs.intern(name);
    try self.async_body_syms.put(f_id, sid);
    return sid;
}

/// Emit the header for an outlined async body function.
fn emitAsyncBodyHeader(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR, body_sym: tir.StrId) !void {
    if (self.func_syms.contains(body_sym)) return;
    const f = t.funcs.Function.get(f_id);
    const params = t.funcs.param_pool.slice(f.params);
    const n_params = params.len;

    // SBO
    var param_tys_buf: [16]mlir.Type = undefined;
    const param_tys = if (n_params <= 16) param_tys_buf[0..n_params] else try self.gpa.alloc(mlir.Type, n_params);
    defer if (n_params > 16) self.gpa.free(param_tys);

    for (params, 0..) |p_id, i| param_tys[i] = try self.llvmTypeOf(t.funcs.Param.get(p_id).ty);

    var ret_sr = f.result;
    if (self.context.type_store.getKind(ret_sr) == .Future) {
        ret_sr = self.context.type_store.get(.Future, ret_sr).elem;
    }
    const ret_kind = self.context.type_store.getKind(ret_sr);
    const has_res = (ret_kind != .Void and ret_kind != .Noreturn);
    const ret_ty = if (has_res) try self.llvmTypeOf(ret_sr) else self.void_ty;
    const results = if (has_res) @as([]const mlir.Type, &.{ret_ty}) else &.{};

    const fty = mlir.Type.getFunctionType(self.mlir_ctx, @intCast(n_params), param_tys, @intCast(results.len), results);

    var attrs = ArrayList(mlir.NamedAttribute).init(self.gpa);
    defer attrs.deinit();
    try attrs.append(self.named("sym_name", self.strAttr(self.context.type_store.strs.get(body_sym))));
    try attrs.append(self.named("function_type", mlir.Attribute.typeAttrGet(fty)));
    try attrs.append(self.named("sym_visibility", self.strAttr("private")));

    const fn_loc = self.functionOptLoc(f_id, t);
    const prev_loc = self.pushLocation(fn_loc);
    defer self.loc = prev_loc;

    const fnop = self.buildOp("func.func", EmitOpArgs{ .attributes = attrs.items, .regions = &.{mlir.Region.create()} });
    var body = self.module.getBody();
    body.appendOwnedOperation(fnop);

    const stored_param_tys = try self.gpa.alloc(mlir.Type, n_params);
    @memcpy(stored_param_tys, param_tys);

    try self.func_syms.put(body_sym, .{
        .op = fnop,
        .is_variadic = false,
        .n_formals = n_params,
        .ret_type = ret_ty,
        .param_types = stored_param_tys,
        .owns_param_types = true,
        .dbg_subprogram = null,
    });
}

fn emitFunctionBody(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR) !void {
    return self.emitFunctionBodyWith(f_id, t, null, null, null);
}

fn emitFunctionBodyWith(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR, sym_override: ?tir.StrId, async_override: ?bool, ret_type_override: ?mlir.Type) !void {
    // 1. Reset State
    self.block_map.clearRetainingCapacity();
    self.value_map.clearRetainingCapacity();
    self.val_types.clearRetainingCapacity();
    self.def_instr.clearRetainingCapacity();
    self.tensor_slots.clearRetainingCapacity();
    self.clearTensorElemPtrs();
    self.global_addr_cache.clearRetainingCapacity();
    self.cur_region = null;
    self.cur_block = null;
    self.func_entry_block = null;
    self.i64_one_in_entry = null;
    self.ret_join_block = null;
    self.ret_has_value = false;

    // 2. Setup Function Context
    const f = t.funcs.Function.get(f_id);
    const func_sym = sym_override orelse f.name;
    const finfo = self.func_syms.get(func_sym).?;

    self.current_scope = finfo.dbg_subprogram;
    self.current_func_sym = func_sym;
    const is_async = async_override orelse f.is_async;
    self.current_func_is_async = is_async;

    defer {
        self.current_scope = null;
        self.current_func_sym = null;
        self.current_func_is_async = false;
        self.func_entry_block = null;
        self.ret_join_block = null;
        self.ret_type_cache = null;
    }

    self.ret_type_cache = if (ret_type_override) |rt| rt else if (is_async and self.context.type_store.getKind(f.result) == .Future)
        try self.llvmTypeOf(self.context.type_store.get(.Future, f.result).elem)
    else
        finfo.ret_type;

    if (!f.raw_asm.isNone()) return self.emitInlineAsmBody(f_id, t, func_sym);

    // 3. Entry Block Setup (SBO)
    const n_formals = finfo.n_formals;
    const params = t.funcs.param_pool.slice(f.params);
    var entry_tys_buf: [16]mlir.Type = undefined;
    var entry_locs_buf: [16]mlir.Location = undefined;
    const entry_arg_tys = if (n_formals <= 16) entry_tys_buf[0..n_formals] else try self.gpa.alloc(mlir.Type, n_formals);
    const entry_locs = if (n_formals <= 16) entry_locs_buf[0..n_formals] else try self.gpa.alloc(mlir.Location, n_formals);
    defer if (n_formals > 16) {
        self.gpa.free(entry_arg_tys);
        self.gpa.free(entry_locs);
    };

    for (params[0..n_formals], 0..) |p_id, i| entry_arg_tys[i] = try self.llvmTypeOf(t.funcs.Param.get(p_id).ty);

    const blocks = t.funcs.block_pool.slice(f.blocks);
    const fn_opt_loc = self.functionOptLoc(f_id, t);
    const entry_loc = if (blocks.len > 0) self.blockOptLoc(blocks[0], t) else tir.OptLocId.none();

    const prev_loc = self.pushLocation(if (!entry_loc.isNone()) entry_loc else fn_opt_loc);
    @memset(entry_locs, self.loc);
    self.loc = prev_loc;

    var entry_block = mlir.Block.create(entry_arg_tys, entry_locs);
    self.cur_region = finfo.op.getRegion(0);
    self.cur_region.?.appendOwnedBlock(entry_block);
    self.cur_block = entry_block;
    self.func_entry_block = entry_block;

    // 4. Async Region Setup

    var async_result: ?mlir.Value = null;
    if (is_async) {
        const fut_row = self.context.type_store.get(.Future, f.result);
        const is_void = self.context.type_store.getKind(fut_row.elem) == .Void;

        var exec_res_buf: [2]mlir.Type = undefined;
        exec_res_buf[0] = mlir.Type.parseGet(self.mlir_ctx, mlir.StringRef.from("!async.token"));
        if (!is_void) exec_res_buf[1] = try self.llvmTypeOf(f.result);

        const execute_op = self.appendOp("async.execute", EmitOpArgs{
            .results = if (is_void) exec_res_buf[0..1] else exec_res_buf[0..2],
            .regions = &.{mlir.Region.create()},
        });

        // Setup async region
        self.cur_region = execute_op.getRegion(0);
        self.cur_region.?.appendOwnedBlock(mlir.Block.create(&.{}, &.{}));
        self.cur_block = self.cur_region.?.getFirstBlock();

        async_result = if (is_void) execute_op.getResult(0) else execute_op.getResult(1);
    }

    if (blocks.len > 0) try self.block_map.put(blocks[0], self.cur_block.?);

    // 5. Parameter Mapping
    try self.value_map.ensureTotalCapacity(@intCast(n_formals));
    try self.val_types.ensureTotalCapacity(@intCast(n_formals));
    for (params[0..n_formals], 0..) |p_id, i| {
        const p = t.funcs.Param.get(p_id);
        const arg = entry_block.getArgument(i);
        var v = arg;
        const want_ty = try self.llvmTypeOf(p.ty);
        if (mlir.LLVM.isLLVMPointerType(arg.getType()) and !mlir.LLVM.isLLVMPointerType(want_ty) and isAggregateKind(self.context.type_store.getKind(p.ty))) {
            v = self.emitOp("llvm.load", EmitOpArgs{
                .operands = &.{arg},
                .results = &.{want_ty},
                .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
            });
        }
        try self.value_map.put(p.value, v);
        try self.val_types.put(p.value, p.ty);
    }
    if (enable_debug_info) debug.emitParameterDebugInfo(self, f_id, params[0..n_formals], entry_block, t) catch {};

    // 6. Block Pre-creation
    if (blocks.len > 1) {
        for (blocks[1..]) |b_id| {
            const bb = t.funcs.Block.get(b_id);
            const b_params = t.funcs.param_pool.slice(bb.params);
            const m = b_params.len;

            // SBO for block args
            var blk_tys_buf: [8]mlir.Type = undefined;
            var blk_locs_buf: [8]mlir.Location = undefined;
            const blk_tys = if (m <= 8) blk_tys_buf[0..m] else try self.gpa.alloc(mlir.Type, m);
            const blk_locs = if (m <= 8) blk_locs_buf[0..m] else try self.gpa.alloc(mlir.Location, m);
            defer if (m > 8) {
                self.gpa.free(blk_tys);
                self.gpa.free(blk_locs);
            };

            const bloc = self.blockOptLoc(b_id, t);
            const bloc_prev = self.pushLocation(if (!bloc.isNone()) bloc else fn_opt_loc);
            for (b_params, 0..) |bp, i| {
                blk_tys[i] = try self.llvmTypeOf(t.funcs.Param.get(bp).ty);
                blk_locs[i] = self.loc;
            }
            self.loc = bloc_prev;

            const b = mlir.Block.create(blk_tys, blk_locs);
            self.cur_region.?.appendOwnedBlock(b);
            try self.block_map.put(b_id, b);
        }
    }

    // 7. Join Block Setup
    const op_name = finfo.op.getName().str().toSlice();
    if (!std.mem.eql(u8, op_name, "llvm.func") and !std.mem.eql(u8, op_name, "tt.func") and !is_async) {
        const ret_ty = self.ret_type_cache.?;
        const has_res = !ret_ty.equal(self.void_ty);
        self.ret_has_value = has_res;

        const ret_blk = mlir.Block.create(if (has_res) &.{ret_ty} else &.{}, if (has_res) &.{self.loc} else &.{});
        var reg = finfo.op.getRegion(0);
        reg.appendOwnedBlock(ret_blk);
        self.ret_join_block = ret_blk;
    }

    // 8. Instruction Emission Loop
    for (blocks) |b_id| {
        const mblock = self.block_map.get(b_id).?;
        self.cur_block = mblock;
        const bb = t.funcs.Block.get(b_id);

        const b_params = t.funcs.param_pool.slice(bb.params);
        for (b_params, 0..) |bp_id, i| {
            const bp = t.funcs.Param.get(bp_id);
            try self.value_map.put(bp.value, mblock.getArgument(i));
            try self.val_types.put(bp.value, bp.ty);
        }

        const instrs = t.instrs.instr_pool.slice(bb.instrs);
        for (instrs) |ins_id| {
            const v = try self.emitInstr(ins_id, t);
            if (self.getInstrResultId(t, ins_id)) |rid| {
                try self.value_map.put(rid, v);
                if (self.instrResultSrType(t, ins_id)) |rt| try self.val_types.put(rid, rt);
                try self.def_instr.put(rid, ins_id);
            }
        }
        try self.emitTerminator(bb.term, t);
    }

    // 9. Function Finalization (Return/Yield)
    if (self.ret_join_block) |rb| {
        self.cur_block = rb;
        const op = if (is_async) "async.yield" else "func.return";
        if (self.ret_has_value) {
            _ = self.appendOp(op, EmitOpArgs{ .operands = &.{rb.getArgument(0)} });
        } else {
            _ = self.appendOp(op, EmitOpArgs{});
        }
    }

    if (is_async) {
        self.cur_block = self.func_entry_block;
        _ = self.appendOp("func.return", EmitOpArgs{ .operands = &.{async_result.?} });
    }
}
fn isIdentStart(c: u8) bool {
    return (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or c == '_';
}

fn isIdentChar(c: u8) bool {
    return isIdentStart(c) or (c >= '0' and c <= '9');
}

fn stripAsmBraces(raw: []const u8) []const u8 {
    var trimmed = std.mem.trim(u8, raw, " \t\r\n");
    if (trimmed.len >= 2 and trimmed[0] == '{' and trimmed[trimmed.len - 1] == '}') {
        return std.mem.trim(u8, trimmed[1 .. trimmed.len - 1], " \t\r\n");
    }
    return trimmed;
}

fn rewriteAsmParams(self: *Codegen, text: []const u8, params: []const tir.ParamId, t: *tir.TIR, has_res: bool) ![]u8 {
    var out = ArrayList(u8).init(self.gpa);
    defer out.deinit();

    var i: usize = 0;
    while (i < text.len) {
        const c = text[i];
        if (isIdentStart(c)) {
            var j = i + 1;
            while (j < text.len and isIdentChar(text[j])) : (j += 1) {}
            const tok = text[i..j];

            var replaced = false;
            for (params, 0..) |p_id, idx| {
                const p = t.funcs.Param.get(p_id);
                if (p.name.isNone()) continue;
                if (std.mem.eql(u8, tok, t.instrs.strs.get(p.name.unwrap()))) {
                    try out.writer().print("${d}", .{if (has_res) idx + 1 else idx});
                    replaced = true;
                    break;
                }
            }

            if (!replaced and has_res) {
                if (std.mem.eql(u8, tok, "rax") or std.mem.eql(u8, tok, "rdx") or
                    std.mem.eql(u8, tok, "eax") or std.mem.eql(u8, tok, "edx"))
                {
                    try out.appendSlice("$0");
                    replaced = true;
                }
            }
            if (!replaced) try out.appendSlice(tok);
            i = j;
            continue;
        }
        try out.append(c);
        i += 1;
    }
    return out.toOwnedSlice();
}

fn emitInlineAsmBody(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR, func_sym: tir.StrId) !void {
    const f = t.funcs.Function.get(f_id);
    const finfo = self.func_syms.get(func_sym).?;
    const n_formals = finfo.n_formals;
    const params = t.funcs.param_pool.slice(f.params);

    // SBO for Entry Block Setup
    var arg_tys_buf: [16]mlir.Type = undefined;
    var locs_buf: [16]mlir.Location = undefined;
    var ops_buf: [16]mlir.Value = undefined;

    const entry_arg_tys = if (n_formals <= 16) arg_tys_buf[0..n_formals] else try self.gpa.alloc(mlir.Type, n_formals);
    const entry_locs = if (n_formals <= 16) locs_buf[0..n_formals] else try self.gpa.alloc(mlir.Location, n_formals);
    const operand_vals = if (n_formals <= 16) ops_buf[0..n_formals] else try self.gpa.alloc(mlir.Value, n_formals);

    defer if (n_formals > 16) {
        self.gpa.free(entry_arg_tys);
        self.gpa.free(entry_locs);
        self.gpa.free(operand_vals);
    };

    for (params[0..n_formals], 0..) |p_id, i| entry_arg_tys[i] = try self.llvmTypeOf(t.funcs.Param.get(p_id).ty);

    const entry_prev = self.pushLocation(self.functionOptLoc(f_id, t));
    @memset(entry_locs, self.loc);
    self.loc = entry_prev;

    var entry_block = mlir.Block.create(entry_arg_tys, entry_locs);
    var reg = finfo.op.getRegion(0);
    reg.appendOwnedBlock(entry_block);

    self.cur_region = finfo.op.getRegion(0);
    self.cur_block = entry_block;
    self.func_entry_block = entry_block;

    // ASM Generation
    const result_kind = self.context.type_store.getKind(f.result);
    const has_res = result_kind != .Void and result_kind != .Noreturn;
    const res_ty = if (has_res) try self.llvmTypeOf(f.result) else self.void_ty;
    const asm_text = try self.rewriteAsmParams(stripAsmBraces(t.instrs.strs.get(f.raw_asm.unwrap())), params, t, has_res);
    defer self.gpa.free(asm_text);

    // Constraints construction (No ArrayList overhead)
    var constraints = ArrayList(u8).init(self.gpa);
    defer constraints.deinit();

    if (has_res) {
        const use_rax = std.mem.indexOf(u8, asm_text, "rax") != null;
        try constraints.appendSlice(if (use_rax) "={rax}" else "=r");
    }
    for (params) |_| {
        if (constraints.items.len > 0) try constraints.append(',');
        try constraints.append('r');
    }

    for (params[0..n_formals], 0..) |_, i| operand_vals[i] = entry_block.getArgument(i);

    const attrs = [_]mlir.NamedAttribute{
        self.named("asm_string", self.strAttr(asm_text)),
        self.named("constraints", self.strAttr(constraints.items)),
        self.named("has_side_effects", mlir.Attribute.unitAttrGet(self.mlir_ctx)),
    };

    const asm_op = self.appendOp("llvm.inline_asm", EmitOpArgs{
        .operands = operand_vals,
        .results = if (has_res) &.{res_ty} else &.{},
        .attributes = &attrs,
    });

    _ = self.appendOp("func.return", EmitOpArgs{
        .operands = if (has_res) &.{asm_op.getResult(0)} else &.{},
    });

    self.func_entry_block = null;
    self.ret_join_block = null;
    self.ret_type_cache = null;
    self.cur_region = null;
    self.cur_block = null;
}

fn emitAsyncWrapperBody(self: *Codegen, f_id: tir.FuncId, t: *tir.TIR, body_sym: tir.StrId) !void {
    const f = t.funcs.Function.get(f_id);
    const finfo = self.func_syms.get(f.name).?;

    // Scope management
    self.current_scope = finfo.dbg_subprogram;
    self.current_func_sym = f.name;
    self.current_func_is_async = true;
    defer {
        self.current_scope = null;
        self.current_func_sym = null;
        self.current_func_is_async = false;
        self.cur_region = null;
        self.cur_block = null;
    }

    const n_formals = finfo.n_formals;
    const params = t.funcs.param_pool.slice(f.params);

    // SBO for Entry Block
    var arg_tys_buf: [16]mlir.Type = undefined;
    var locs_buf: [16]mlir.Location = undefined;
    var args_buf: [16]mlir.Value = undefined;

    const entry_arg_tys = if (n_formals <= 16) arg_tys_buf[0..n_formals] else try self.gpa.alloc(mlir.Type, n_formals);
    const entry_locs = if (n_formals <= 16) locs_buf[0..n_formals] else try self.gpa.alloc(mlir.Location, n_formals);
    const call_args = if (n_formals <= 16) args_buf[0..n_formals] else try self.gpa.alloc(mlir.Value, n_formals);

    defer if (n_formals > 16) {
        self.gpa.free(entry_arg_tys);
        self.gpa.free(entry_locs);
        self.gpa.free(call_args);
    };

    for (params[0..n_formals], 0..) |p_id, i| entry_arg_tys[i] = try self.llvmTypeOf(t.funcs.Param.get(p_id).ty);

    const entry_prev = self.pushLocation(self.functionOptLoc(f_id, t));
    @memset(entry_locs, self.loc);
    self.loc = entry_prev;

    var entry_block = mlir.Block.create(entry_arg_tys, entry_locs);
    var reg = finfo.op.getRegion(0);
    reg.appendOwnedBlock(entry_block);
    self.cur_region = finfo.op.getRegion(0);
    self.cur_block = entry_block;

    // async.execute setup
    const fut_row = self.context.type_store.get(.Future, f.result);
    const is_void_future = self.context.type_store.getKind(fut_row.elem) == .Void;

    var exec_res_buf: [2]mlir.Type = undefined;
    exec_res_buf[0] = mlir.Type.parseGet(self.mlir_ctx, mlir.StringRef.from("!async.token"));
    if (!is_void_future) exec_res_buf[1] = try self.llvmTypeOf(f.result);

    var exec_region = mlir.Region.create();
    exec_region.appendOwnedBlock(mlir.Block.create(&.{}, &.{}));

    const execute_op = self.appendOp("async.execute", EmitOpArgs{
        .results = if (is_void_future) exec_res_buf[0..1] else exec_res_buf[0..2],
        .regions = &.{exec_region},
    });

    // Body Call inside async.execute
    self.cur_region = execute_op.getRegion(0);
    self.cur_block = self.cur_region.?.getFirstBlock();

    for (params[0..n_formals], 0..) |_, i| call_args[i] = entry_block.getArgument(i);

    const body_attrs = [_]mlir.NamedAttribute{
        self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(self.context.type_store.strs.get(body_sym)))),
    };

    if (is_void_future) {
        _ = self.appendOp("func.call", EmitOpArgs{ .operands = call_args, .results = &.{}, .attributes = &body_attrs });
        _ = self.appendOp("async.yield", EmitOpArgs{});
    } else {
        const rv = self.appendOp("func.call", EmitOpArgs{
            .operands = call_args,
            .results = &.{try self.llvmTypeOf(fut_row.elem)},
            .attributes = &body_attrs,
        }).getResult(0);
        _ = self.appendOp("async.yield", EmitOpArgs{ .operands = &.{rv} });
    }

    // Return future
    self.cur_region = finfo.op.getRegion(0);
    self.cur_block = entry_block;
    _ = self.appendOp("func.return", EmitOpArgs{
        .operands = &.{if (is_void_future) execute_op.getResult(0) else execute_op.getResult(1)},
    });
}

fn getInstrResultId(_: *Codegen, t: *tir.TIR, id: tir.InstrId) ?tir.ValueId {
    switch (t.kind(id)) {
        .DbgDeclare => return t.instrs.get(.DbgDeclare, id).result,
        .Store => return null,
        .MlirBlock => return t.instrs.get(.MlirBlock, id).result.unwrap(),
        inline else => |k| if (@hasField(@TypeOf(t.instrs.get(k, id)), "result")) return t.instrs.get(k, id).result else return null,
    }
}

fn instrResultSrType(_: *Codegen, t: *tir.TIR, id: tir.InstrId) ?types.TypeId {
    switch (t.kind(id)) {
        .DbgDeclare => return t.instrs.get(.DbgDeclare, id).ty,
        .Store => return null,
        inline else => |k| if (@hasField(@TypeOf(t.instrs.get(k, id)), "ty")) return t.instrs.get(k, id).ty else return null,
    }
}
/// Ensure the callee referenced by `p` has been emitted and return its `FuncInfo`.
fn ensureFuncDeclFromCall(self: *Codegen, p: tir.Rows.Call, t: *tir.TIR) !FuncInfo {
    const callee_id = p.callee;
    if (self.func_syms.get(callee_id)) |fi| return fi; // Cached hit

    const name = t.instrs.strs.get(callee_id);
    var is_var = false;
    var ret_sr: types.TypeId = undefined;

    // SBO: Avoid allocs for common arg counts
    var params_buf: [16]types.TypeId = undefined;
    var params_sr: []const types.TypeId = &.{};
    var params_list: ArrayList(types.TypeId) = undefined;
    defer if (params_sr.len > 16) params_list.deinit();

    // 1. Resolve Function Signature (Global Map vs Inference)
    if (self.context.global_func_map.get(callee_id)) |item| {
        const funcs = item.@"1";
        const fn_info = funcs.Function.get(item.@"0");
        is_var = fn_info.is_variadic;
        ret_sr = fn_info.result;

        const p_ids = funcs.param_pool.slice(fn_info.params);
        if (p_ids.len <= 16) {
            for (p_ids, 0..) |pid, i| params_buf[i] = funcs.Param.get(pid).ty;
            params_sr = params_buf[0..p_ids.len];
        } else {
            params_list = try ArrayList(types.TypeId).initCapacity(self.gpa, p_ids.len);
            for (p_ids) |pid| params_list.appendAssumeCapacity(funcs.Param.get(pid).ty);
            params_sr = params_list.items;
        }
    } else {
        // Fallback inference
        const args = t.instrs.val_list_pool.slice(p.args);
        ret_sr = p.ty;
        if (args.len <= 16) {
            for (args, 0..) |vid, i| params_buf[i] = self.srTypeOfValue(vid);
            params_sr = params_buf[0..args.len];
        } else {
            params_list = try ArrayList(types.TypeId).initCapacity(self.gpa, args.len);
            for (args) |vid| params_list.appendAssumeCapacity(self.srTypeOfValue(vid));
            params_sr = params_list.items;
        }
    }

    const ret_kind = self.context.type_store.getKind(ret_sr);
    const ret_void = ret_kind == .Void or ret_kind == .Noreturn;

    // 2. Emit Triton Function
    if (self.emit_only_triton) {
        const param_tys = try self.gpa.alloc(mlir.Type, params_sr.len);
        for (params_sr, 0..) |psr, i| param_tys[i] = try self.llvmTypeOf(psr);

        const res_ty = if (ret_void) &[_]mlir.Type{} else &[_]mlir.Type{try self.llvmTypeOf(ret_sr)};
        const param_tys_slice = param_tys[0..param_tys.len];
        const res_ty_slice = res_ty[0..];
        const fty = mlir.Type.getFunctionType(self.mlir_ctx, @intCast(param_tys_slice.len), param_tys_slice, @intCast(res_ty_slice.len), res_ty_slice);

        const prev_loc = self.pushLocation(p.loc);
        defer self.loc = prev_loc;

        const fnop = self.buildOp("tt.func", EmitOpArgs{
            .attributes = &.{
                self.named("sym_name", self.strAttr(name)),
                self.named("function_type", mlir.Attribute.typeAttrGet(fty)),
                self.named("sym_visibility", self.strAttr("private")),
            },
            .regions = &.{mlir.Region.create()},
        });
        var body = self.module.getBody();
        body.appendOwnedOperation(fnop);

        const info: FuncInfo = .{
            .op = fnop,
            .is_variadic = is_var,
            .n_formals = params_sr.len,
            .ret_type = if (ret_void) self.void_ty else res_ty[0],
            .param_types = param_tys,
            .owns_param_types = true,
            .dbg_subprogram = null,
        };
        try self.func_syms.put(callee_id, info);
        return info;
    }

    // 3. Emit LLVM Function (ABI Lowering)
    // Worst case expansion: 1 (sret) + N*2 (params) + 2 (padding)
    const max_args = params_sr.len * 2 + 3;
    var lowered_params = try self.gpa.alloc(mlir.Type, max_args);
    var argAttrs = try self.gpa.alloc(mlir.Attribute, max_args);
    // We pass ownership of these arrays to FuncInfo later, so we only free on error/unused path,
    // but here we slice them into a new buffer at the end to fit exact size.
    defer self.gpa.free(lowered_params);
    defer self.gpa.free(argAttrs);

    var n_args: usize = 0;
    var ret_type: mlir.Type = self.void_ty;

    // Handle Return ABI
    if (!ret_void) {
        const rc = abi.abiClassifyX64SysV(self, ret_sr, true);
        switch (rc.kind) {
            .IndirectSRet => {
                lowered_params[n_args] = self.llvm_ptr_ty;
                argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &.{
                    self.named("llvm.sret", mlir.Attribute.typeAttrGet(try self.llvmTypeOf(ret_sr))),
                    self.named("llvm.align", mlir.Attribute.integerAttrGet(self.i64_ty, rc.alignment)),
                });
                n_args += 1;
            },
            .DirectScalar => ret_type = rc.scalar0.?,
            .DirectPair => ret_type = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &.{ rc.scalar0.?, rc.scalar1.? }, false),
            else => unreachable,
        }
    }

    // Handle Params ABI
    const empty_dict = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &.{});
    for (params_sr) |psr| {
        const cls = abi.abiClassifyX64SysV(self, psr, false);
        switch (cls.kind) {
            .IndirectByVal => {
                lowered_params[n_args] = self.llvm_ptr_ty;
                argAttrs[n_args] = mlir.Attribute.dictionaryAttrGet(self.mlir_ctx, &.{
                    self.named("llvm.byval", mlir.Attribute.typeAttrGet(try self.llvmTypeOf(psr))),
                    self.named("llvm.align", mlir.Attribute.integerAttrGet(self.i64_ty, cls.alignment)),
                });
                n_args += 1;
            },
            .DirectScalar => {
                lowered_params[n_args] = cls.scalar0.?;
                argAttrs[n_args] = empty_dict;
                n_args += 1;
            },
            .DirectPair => {
                lowered_params[n_args] = cls.scalar0.?;
                argAttrs[n_args] = empty_dict;
                n_args += 1;
                lowered_params[n_args] = cls.scalar1.?;
                argAttrs[n_args] = empty_dict;
                n_args += 1;
            },
            else => unreachable,
        }
    }

    // Finalize LLVM Function
    const final_params = try self.gpa.alloc(mlir.Type, n_args);
    @memcpy(final_params, lowered_params[0..n_args]);

    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const fnop = self.buildOp("llvm.func", EmitOpArgs{
        .attributes = &.{
            self.named("sym_name", self.strAttr(name)),
            self.named("function_type", mlir.Attribute.typeAttrGet(mlir.LLVM.getLLVMFunctionType(ret_type, final_params, is_var))),
            self.named("arg_attrs", mlir.Attribute.arrayAttrGet(self.mlir_ctx, argAttrs[0..n_args])),
            self.named("sym_visibility", self.strAttr("private")),
        },
        .regions = &.{mlir.Region.create()},
    });
    var body = self.module.getBody();
    body.appendOwnedOperation(fnop);

    const info: FuncInfo = .{
        .op = fnop,
        .is_variadic = is_var,
        .n_formals = params_sr.len,
        .ret_type = ret_type,
        .param_types = final_params,
        .owns_param_types = true,
        .dbg_subprogram = null,
    };
    try self.func_syms.put(callee_id, info);
    return info;
}

/// Make sure the lowered argument list can satisfy the callee's parameter types.
fn ensureCallArgType(self: *Codegen, value: mlir.Value, src_sr: types.TypeId, want_ty: mlir.Type) !mlir.Value {
    if (value.getType().equal(want_ty)) return value;
    const have_ty = value.getType();

    if (have_ty.isAInteger() and want_ty.isAInteger()) {
        const fw = try cast.intOrFloatWidth(have_ty);
        const tw = try cast.intOrFloatWidth(want_ty);
        if (fw == tw) return value;
        if (fw > tw) return self.emitUnaryValueOp("llvm.trunc", value, want_ty);
        const op = if (self.isSignedInt(src_sr)) "llvm.sext" else "llvm.zext";
        return self.emitUnaryValueOp(op, value, want_ty);
    }

    if (have_ty.isAFloat() and want_ty.isAFloat()) {
        const fw = try cast.intOrFloatWidth(have_ty);
        const tw = try cast.intOrFloatWidth(want_ty);
        if (fw == tw) return value;
        return self.emitUnaryValueOp(if (fw > tw) "llvm.fptrunc" else "llvm.fpext", value, want_ty);
    }

    if (mlir.LLVM.isLLVMPointerType(have_ty) and mlir.LLVM.isLLVMPointerType(want_ty)) {
        return self.emitUnaryValueOp("llvm.bitcast", value, want_ty);
    }
    return value;
}

/// Build the SSA operand list when calling a known function, handling ABI lowering.
fn prepareInternalCallArgs(self: *Codegen, src_vals: []const mlir.Value, src_sr: []const types.TypeId, finfo: FuncInfo) ![]mlir.Value {
    const args = try self.gpa.alloc(mlir.Value, src_vals.len);
    for (src_vals, 0..) |v, i| {
        // Variadic args may exceed param_types length, use own type in that case
        const want_ty = if (i < finfo.param_types.len) finfo.param_types[i] else v.getType();

        if (v.getType().equal(want_ty)) {
            args[i] = v;
        } else if (mlir.LLVM.isLLVMPointerType(want_ty) and !mlir.LLVM.isLLVMPointerType(v.getType())) {
            // Spill aggregate to memory to pass by pointer (IndirectByVal/SRet)
            const tmp = self.spillAgg(v, v.getType(), 0);
            args[i] = try self.ensureCallArgType(tmp, src_sr[i], want_ty);
        } else {
            args[i] = try self.ensureCallArgType(v, src_sr[i], want_ty);
        }
    }
    return args;
}
/// Emit an MLIR constant for the signed/unsigned integer `p`.
fn emitConstInt(self: *Codegen, p: tir.Rows.ConstInt) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const ty = try self.llvmTypeOf(p.ty);
    return if (ty.isAFloat()) self.constFloat(ty, @floatFromInt(p.value)) else self.constInt(ty, p.value);
}

/// Emit an MLIR constant floating-point value.
fn emitConstFloat(self: *Codegen, p: tir.Rows.ConstFloat) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    return self.constFloat(try self.llvmTypeOf(p.ty), p.value);
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
    const zero = self.emitOp("llvm.mlir.zero", EmitOpArgs{ .results = &.{ty} });

    // Optional pointers are represented as {ptr, bool} (non-null flag)
    if (self.context.type_store.getKind(p.ty) == .Optional and !self.context.type_store.isOptionalPointer(p.ty)) {
        return self.insertAt(zero, self.constBool(false), &.{0});
    }
    return zero;
}

/// Emit an MLIR `undef` value specializing to the target type.
fn emitConstUndef(self: *Codegen, p: tir.Rows.ConstUndef) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    if (self.context.type_store.getKind(p.ty) == .Union) {
        return self.zeroOf(try self.llvmTypeOf(p.ty));
    }
    return self.emitOp("llvm.mlir.undef", EmitOpArgs{ .results = &.{try self.llvmTypeOf(p.ty)} });
}

/// Emit an MLIR constant string filled with `p`’s text data.
fn emitConstString(self: *Codegen, p: tir.Rows.ConstString) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const str_text = self.context.interner.get(p.text);
    const ptr_val = (try self.constStringPtr(str_text)).getResult(0);
    const string_ty = try self.llvmTypeOf(p.ty);

    if (mlir.LLVM.isLLVMPointerType(string_ty)) return ptr_val;

    // Construct string slice {ptr, len}
    const agg = self.insertAt(self.undefOf(string_ty), ptr_val, &.{0});
    return self.insertAt(agg, self.constInt(self.i64_ty, @intCast(str_text.len)), &.{1});
}

/// Emit a complex-number binary op (the caller is responsible for location).
fn emitComplexBinOp(self: *Codegen, name: []const u8, p: tir.Rows.Bin2) !mlir.Value {
    return self.emitOp(name, EmitOpArgs{
        .operands = &.{ self.getVal(p.lhs), self.getVal(p.rhs) },
        .results = &.{try self.llvmTypeOf(p.ty)},
    });
}

/// Emit either a complex-number operation or a generic arithmetic op.
fn emitBinArithWithComplex(self: *Codegen, p: tir.Rows.Bin2, comptime op_kind: BinArithOp, complex_name: []const u8) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    if (self.srKind(p.ty) == .Complex) return self.emitComplexBinOp(complex_name, p);
    return self.binArith(op_kind, p);
}

/// Emit the MLIR representation of integer/floating point addition.
fn emitAdd(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    // Detect Triton context
    var in_triton = self.emit_only_triton;
    if (!in_triton) {
        if (self.current_func_sym) |sym| if (self.func_syms.get(sym)) |cinfo| {
            in_triton = std.mem.eql(u8, cinfo.op.getName().str().toSlice(), "tt.func");
        };
    }

    if (in_triton) {
        const res_kind = self.srKind(p.ty);
        const lhs_ty = self.srTypeOfValue(p.lhs);
        const rhs_ty = self.srTypeOfValue(p.rhs);

        // Check for pointer arithmetic scenarios in Triton
        const res_is_ptr_tensor = res_kind == .Tensor and blk: {
            const ek = self.context.type_store.getKind(self.context.type_store.get(.Tensor, p.ty).elem);
            break :blk ek == .Ptr or ek == .MlirType;
        };
        const lhs_ptr = self.srKind(lhs_ty) == .Ptr or self.srKind(lhs_ty) == .MlirType;
        const rhs_ptr = self.srKind(rhs_ty) == .Ptr or self.srKind(rhs_ty) == .MlirType;

        if (res_kind == .Ptr or res_kind == .MlirType or res_is_ptr_tensor or
            (lhs_ptr and self.srKind(p.ty) == .Tensor) or (rhs_ptr and self.srKind(p.ty) == .Tensor))
        {
            const lhs = self.getVal(p.lhs);
            const rhs = self.getVal(p.rhs);
            // Canonicalize: ptr is first arg for tt.addptr
            var ptr_arg = if (lhs_ptr) lhs else rhs;
            const off_arg = if (lhs_ptr) rhs else lhs;
            const res_mlir = try self.llvmTypeOf(p.ty);

            // Broadcast scalar pointer to tensor if needed
            if (res_kind == .Tensor and !ptr_arg.getType().equal(res_mlir)) {
                ptr_arg = self.emitOp("tt.splat", EmitOpArgs{ .operands = &.{ptr_arg}, .results = &.{res_mlir} });
            }
            return self.emitOp("tt.addptr", EmitOpArgs{ .operands = &.{ ptr_arg, off_arg }, .results = &.{res_mlir} });
        }
    }
    return self.emitBinArithWithComplex(p, .add, "complex.add");
}

fn emitSub(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    return self.emitBinArithWithComplex(p, .sub, "complex.sub");
}
fn emitMul(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    return self.emitBinArithWithComplex(p, .mul, "complex.mul");
}

fn emitDiv(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    if (self.context.type_store.getKind(p.ty) == .Complex) return self.emitComplexBinOp("complex.div", p);
    return self.arithDiv(self.getVal(p.lhs), self.getVal(p.rhs), try self.llvmTypeOf(p.ty), !self.isUnsigned(self.srTypeOfValue(p.lhs)));
}

fn emitMod(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    return self.arithRem(self.getVal(p.lhs), self.getVal(p.rhs), try self.llvmTypeOf(p.ty), !self.isUnsigned(self.srTypeOfValue(p.lhs)));
}

fn emitShl(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    return self.arithShl(self.getVal(p.lhs), self.getVal(p.rhs), try self.llvmTypeOf(p.ty));
}

fn emitShr(self: *Codegen, p: tir.Rows.Bin2) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    return self.arithShr(self.getVal(p.lhs), self.getVal(p.rhs), try self.llvmTypeOf(p.ty), !self.isUnsigned(self.srTypeOfValue(p.lhs)));
}

/// Emit a bitcast for the single-operand `p`.
fn emitCastBit(self: *Codegen, p: tir.Rows.Un1) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    const to_ty = try self.llvmTypeOf(p.ty);
    const from_v = self.getVal(p.value);
    const from_ty = from_v.getType();

    if (from_ty.equal(to_ty)) return from_v;
    if (self.isUndefValue(from_v)) return self.undefOf(to_ty);

    // Spill required for Aggregate <-> Aggregate or Pointer <-> Non-Pointer casts
    const needs_spill = mlir.LLVM.isLLVMStructType(from_ty) or mlir.LLVM.isLLVMStructType(to_ty) or
        (mlir.LLVM.isLLVMPointerType(from_ty) != mlir.LLVM.isLLVMPointerType(to_ty));

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

fn emitCastNormalInstr(self: *Codegen, p: tir.Rows.Un1) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    return cast.emitCastNormal(self, p.ty, try self.llvmTypeOf(p.ty), self.getVal(p.value), self.srTypeOfValue(p.value));
}

fn emitCastSaturate(self: *Codegen, p: tir.Rows.Un1) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    return cast.emitCast(self, .CastSaturate, p.ty, self.srTypeOfValue(p.value), self.getVal(p.value));
}

fn emitCastWrap(self: *Codegen, comptime x: tir.OpKind, p: tir.Rows.Un1) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;
    return cast.emitCast(self, x, p.ty, self.srTypeOfValue(p.value), self.getVal(p.value));
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
    const kind = self.context.type_store.getKind(p.ty);
    if (kind == .Ptr) {
        const ptr_row = self.context.type_store.get(.Ptr, p.ty);
        const elem_kind = self.context.type_store.getKind(ptr_row.elem);

        if (elem_kind == .Tensor) {
            try self.tensor_slots.put(p.result, mlir.Value.empty());
            return self.llvmNullPtr();
        }

        if (elem_kind == .Complex) {
            const ety = try self.llvmTypeOf(self.context.type_store.get(.Complex, ptr_row.elem).elem);
            elem_ty = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ ety, ety }, false);
        } else {
            elem_ty = try self.llvmTypeOf(ptr_row.elem);
        }
    }

    const count_v = if (p.count.isNone()) self.getI64OneInEntry() else self.getVal(p.count.unwrap());

    const alloca = self.buildOp("llvm.alloca", EmitOpArgs{
        .operands = &.{count_v},
        .results = &.{self.llvm_ptr_ty},
        .attributes = &.{self.named("elem_type", mlir.Attribute.typeAttrGet(elem_ty))},
    });

    if (p.count.isNone()) self.appendInFuncEntry(alloca) else self.append(alloca);
    return alloca.getResult(0);
}

/// Emit the MLIR instructions for a load operation `p`.
fn emitLoad(self: *Codegen, p: tir.Rows.Load) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    if (try self.tryEmitTensorElementLoad(p)) |elem| return elem;

    var ptr = self.getVal(p.ptr);
    const ty_kind = self.context.type_store.getKind(p.ty);

    if (ty_kind == .Tensor) return self.tensor_slots.get(p.ptr) orelse std.debug.panic("tensor load before store", .{});

    if (ty_kind == .Complex) {
        const c = self.context.type_store.get(.Complex, p.ty);
        const elem_ty = try self.llvmTypeOf(c.elem);
        // Load struct {re, im} then construct complex value
        const storage_ty = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ elem_ty, elem_ty }, false);
        const agg = self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{ptr},
            .results = &.{storage_ty},
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
        return self.emitOp("complex.create", EmitOpArgs{
            .operands = &.{ self.extractAt(agg, elem_ty, &.{0}), self.extractAt(agg, elem_ty, &.{1}) },
            .results = &.{try self.llvmTypeOf(p.ty)},
        });
    }

    const res_ty = try self.llvmTypeOf(p.ty);
    // Support opaque pointer model or direct value coercion
    if (!mlir.LLVM.isLLVMPointerType(ptr.getType())) {
        if (ptr.getType().equal(res_ty)) return ptr;
        return try self.coerceOnBranch(ptr, res_ty, p.ty, self.srTypeOfValue(p.ptr));
    }

    return self.emitOp("llvm.load", EmitOpArgs{
        .operands = &.{ptr},
        .results = &.{res_ty},
        .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
    });
}

/// Emit the MLIR instructions for the store operation described by `p`.
fn emitStore(self: *Codegen, p: tir.Rows.Store) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const v = self.getVal(p.value);
    if (try self.handleTensorElementStore(p, v)) return .empty();

    const ptr = self.getVal(p.ptr);
    const v_sr = self.srTypeOfValue(p.value);
    const ptr_sr = self.srTypeOfValue(p.ptr);

    // Handle Tensor Slot Stores (Logical Ptr)
    if (self.context.type_store.getKind(ptr_sr) == .Ptr) {
        if (self.context.type_store.getKind(self.context.type_store.get(.Ptr, ptr_sr).elem) == .Tensor) {
            try self.tensor_slots.put(p.ptr, v);
            return .empty();
        }
    }

    if (self.context.type_store.getKind(v_sr) == .Complex) {
        const c = self.context.type_store.get(.Complex, v_sr);
        const elem_ty = try self.llvmTypeOf(c.elem);
        // Spill complex into {re, im} struct before storing
        var acc = self.undefOf(mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ elem_ty, elem_ty }, false));
        acc = self.insertAt(acc, self.emitUnaryValueOp("complex.re", v, elem_ty), &.{0});
        acc = self.insertAt(acc, self.emitUnaryValueOp("complex.im", v, elem_ty), &.{1});

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

    const base_sr = self.srTypeOfValue(p.base);
    var elem_mlir: mlir.Type = self.i8_ty;
    if (self.context.type_store.getKind(base_sr) == .Ptr) {
        elem_mlir = try self.llvmTypeOf(self.context.type_store.get(.Ptr, base_sr).elem);
    }

    const index_ids = t.instrs.gep_pool.slice(p.indices);

    // Small Buffer Optimization (SBO) for indices
    var buf: [8]tir.Rows.GepIndex = undefined;
    const indices_data = if (index_ids.len <= 8) buf[0..index_ids.len] else try self.gpa.alloc(tir.Rows.GepIndex, index_ids.len);
    defer if (index_ids.len > 8) self.gpa.free(indices_data);

    for (index_ids, 0..) |id, i| {
        indices_data[i] = t.instrs.GepIndex.get(id);
    }
    return self.emitGep(self.getVal(p.base), elem_mlir, indices_data);
}

/// Emit an LLVM global address constant for `p`.
fn emitGlobalAddr(self: *Codegen, p: tir.Rows.GlobalAddr) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const name = self.context.interner.get(p.name);
    if (self.global_addr_cache.get(name)) |cached| return cached;

    const addr = self.buildOp("llvm.mlir.addressof", EmitOpArgs{
        .results = &.{try self.llvmTypeOf(p.ty)},
        .attributes = &.{self.named("global_name", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(name)))},
    });

    var entry = self.func_entry_block orelse self.cur_block.?;
    const term = entry.getTerminator();
    if (!term.isNull()) entry.insertOwnedOperationBefore(term, addr) else entry.appendOwnedOperation(addr);

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
    const elems = t.instrs.value_pool.slice(p.elems);

    std.debug.assert(elem_srs.len == elems.len);

    var acc = self.zeroOf(tup_ty);
    for (elems, 0..) |vid, i| {
        const elem_sr = elem_srs[i];
        const elem_mlir = try self.llvmTypeOf(elem_sr);
        const v = self.getVal(vid);
        // Direct coercion attempt
        const coerced = try self.coerceOnBranch(v, elem_mlir, elem_sr, self.srTypeOfValue(vid));
        acc = self.insertAt(acc, coerced, &.{@intCast(i)});
    }
    return acc;
}

/// Emit the runtime representation for a range literal.
fn emitRangeMake(self: *Codegen, p: tir.Rows.RangeMake) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const i64t = self.i64_ty;
    const i64_sr = self.context.type_store.tI64();

    // Coerce start/end to i64
    const s_val = try self.coerceOnBranch(self.getVal(p.start), i64t, i64_sr, self.srTypeOfValue(p.start));
    const e_val = try self.coerceOnBranch(self.getVal(p.end), i64t, i64_sr, self.srTypeOfValue(p.end));

    // Materialize as struct<i64,i64> { start, end }
    const pairTy = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ i64t, i64t }, false);
    var acc = self.zeroOf(pairTy);
    acc = self.insertAt(acc, s_val, &.{0});
    acc = self.insertAt(acc, e_val, &.{1});
    return acc;
}

/// Emit a broadcast operation for SIMD values described by `p`.
fn emitBroadcast(self: *Codegen, p: tir.Rows.Broadcast) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const target_ty = try self.llvmTypeOf(p.ty);
    const sr_kind = self.context.type_store.getKind(p.ty);

    // Unify element type extraction
    const elem_sr = switch (sr_kind) {
        .Tensor => self.context.type_store.get(.Tensor, p.ty).elem,
        else => self.context.type_store.get(.Simd, p.ty).elem,
    };

    const elem_mlir = try self.llvmTypeOf(elem_sr);
    var scalar_val = self.getVal(p.value);

    if (!scalar_val.getType().equal(elem_mlir)) {
        scalar_val = try self.coerceOnBranch(scalar_val, elem_mlir, elem_sr, self.srTypeOfValue(p.value));
    }

    if (sr_kind == .Tensor) {
        const op_name = if (self.emit_only_triton) "tt.splat" else "tensor.splat";
        return self.emitOp(op_name, EmitOpArgs{ .operands = &.{scalar_val}, .results = &.{target_ty} });
    } else {
        return self.emitOp("vector.broadcast", EmitOpArgs{ .operands = &.{scalar_val}, .results = &.{target_ty} });
    }
}

/// Emit a SIMD vector literal from `p`.
fn emitSimdMake(self: *Codegen, p: tir.Rows.ArrayMake, t: *const tir.TIR) !mlir.Value {
    const simd_ty = self.context.type_store.get(.Simd, p.ty);
    const elems = t.instrs.value_pool.slice(p.elems);
    std.debug.assert(elems.len == @as(usize, @intCast(simd_ty.lanes)));

    const elem_mlir = try self.llvmTypeOf(simd_ty.elem);
    const vec_ty = try self.llvmTypeOf(p.ty);

    // Small Buffer Optimization: Avoid malloc for common SIMD sizes (<= 16)
    var buf: [16]mlir.Value = undefined;
    const operands = if (elems.len <= 16) buf[0..elems.len] else try self.gpa.alloc(mlir.Value, elems.len);
    defer if (elems.len > 16) self.gpa.free(operands);

    for (elems, 0..) |vid, i| {
        operands[i] = try self.coerceOnBranch(self.getVal(vid), elem_mlir, simd_ty.elem, self.srTypeOfValue(vid));
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

    // Small Buffer Optimization
    var buf: [16]mlir.Value = undefined;
    const operands = if (elems.len <= 16) buf[0..elems.len] else try self.gpa.alloc(mlir.Value, elems.len);
    defer if (elems.len > 16) self.gpa.free(operands);

    for (elems, 0..) |vid, i| {
        operands[i] = try self.coerceOnBranch(self.getVal(vid), scalar_elem_mlir, tensor_sr.elem, self.srTypeOfValue(vid));
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

    // Dispatch specialized makes
    switch (self.context.type_store.getKind(p.ty)) {
        .Simd => return self.emitSimdMake(p, t),
        .Tensor => return self.emitTensorMake(p, t),
        else => {},
    }

    const arr_ty = try self.llvmTypeOf(p.ty);
    const arr_sr = self.context.type_store.get(.Array, p.ty);
    const elem_mlir = try self.llvmTypeOf(arr_sr.elem);

    var acc = self.zeroOf(arr_ty);
    const elems = t.instrs.value_pool.slice(p.elems);

    for (elems, 0..) |vid, i| {
        const val = try self.coerceOnBranch(self.getVal(vid), elem_mlir, arr_sr.elem, self.srTypeOfValue(vid));
        acc = self.insertAt(acc, val, &.{@as(i64, @intCast(i))});
    }
    return acc;
}

/// Emit the index access operation `p`.
fn emitIndex(self: *Codegen, p: tir.Rows.Index, t: *tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const base = self.getVal(p.base);
    const res_ty = try self.llvmTypeOf(p.ty);
    const res_sr_kind = self.context.type_store.getKind(p.ty);
    const base_sr_ty = self.srTypeOfValue(p.base);
    const base_sr_kind = self.context.type_store.getKind(base_sr_ty);

    // 1. Handle Tensor Indexing (Extract or Slice)
    if (base_sr_kind == .Tensor) {
        const base_tensor = self.context.type_store.get(.Tensor, base_sr_ty);
        const base_rank: usize = @intCast(base_tensor.rank);
        const idx_val = try self.ensureIndexValue(self.getVal(p.index));

        // Rank-1 scalar extraction
        if (base_rank == 1 and res_sr_kind != .Tensor and res_sr_kind != .Slice) {
            return self.emitOp("tensor.extract", EmitOpArgs{
                .operands = &.{ base, idx_val },
                .results = &.{res_ty},
            });
        }

        // Tensor Slicing logic
        std.debug.assert(res_sr_kind == .Tensor);
        const elem_mlir = try self.llvmTypeOf(base_tensor.elem);

        // Prepare slice attributes
        var static_offsets = [_]i64{mlir.Type.getDynamicStrideOrOffset()} ** types.max_tensor_rank;
        var static_sizes = [_]i64{1} ** types.max_tensor_rank;
        var static_strides = [_]i64{1} ** types.max_tensor_rank;

        // Copy dims for slice type construction
        var slice_dims: [types.max_tensor_rank]i64 = undefined;
        slice_dims[0] = 1;
        var i: usize = 1;
        while (i < base_rank) : (i += 1) {
            static_offsets[i] = 0;
            static_sizes[i] = @intCast(base_tensor.dims[i]);
            slice_dims[i] = @intCast(base_tensor.dims[i]);
        }

        const slice_ty = mlir.Type.getRankedTensorType(@intCast(base_rank), slice_dims[0..base_rank], elem_mlir, mlir.Attribute.getNull());

        const extract_attrs = [_]mlir.NamedAttribute{
            self.named("static_offsets", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, static_offsets[0..base_rank])),
            self.named("static_sizes", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, static_sizes[0..base_rank])),
            self.named("static_strides", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, static_strides[0..base_rank])),
            self.named("operand_segment_sizes", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ 1, 1, 0, 0 })),
        };

        const slice = self.appendOp("tensor.extract_slice", EmitOpArgs{
            .operands = &.{ base, idx_val },
            .results = &.{slice_ty},
            .attributes = &extract_attrs,
        });

        // Collapse shape (Rank Reduction)
        const i64_ty = mlir.Type.getSignlessIntegerType(self.mlir_ctx, 64);
        var reassoc_groups = try self.gpa.alloc(mlir.Attribute, @intCast(self.context.type_store.get(.Tensor, p.ty).rank));
        defer self.gpa.free(reassoc_groups);

        // First group merges dim 0 and 1
        var grp0 = [_]mlir.Attribute{ mlir.Attribute.integerAttrGet(i64_ty, 0), mlir.Attribute.integerAttrGet(i64_ty, 1) };
        reassoc_groups[0] = mlir.Attribute.arrayAttrGet(self.mlir_ctx, &grp0);

        var g: usize = 1;
        while (g < reassoc_groups.len) : (g += 1) {
            var el = [_]mlir.Attribute{mlir.Attribute.integerAttrGet(i64_ty, @intCast(g + 1))};
            reassoc_groups[g] = mlir.Attribute.arrayAttrGet(self.mlir_ctx, &el);
        }

        return self.emitOp("tensor.collapse_shape", EmitOpArgs{
            .operands = &.{slice.getResult(0)},
            .results = &.{res_ty},
            .attributes = &.{self.named("reassociation", mlir.Attribute.arrayAttrGet(self.mlir_ctx, reassoc_groups))},
        });
    }

    // 2. Handle Simd Indexing
    if (base_sr_kind == .Simd) {
        const idx_val = try self.ensureIndexValue(self.getVal(p.index));
        return self.emitOp("vector.extract", EmitOpArgs{
            .operands = &.{ base, idx_val },
            .attributes = &.{self.named("static_position", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, &.{mlir.Type.getDynamicSize()}))},
            .results = &.{res_ty},
        });
    }

    // 3. Handle Slicing (Creating a Slice View)
    const idx_kind = self.context.type_store.getKind(self.srTypeOfValue(p.index));
    if (idx_kind == .Slice) {
        // Attempt to peel `builtin.range.make` arguments
        var args: struct { start: tir.ValueId, end: tir.ValueId, incl: tir.ValueId } = undefined;
        var found_range = false;

        var idx_vid: tir.ValueId = p.index;
        // Peel CastNormal
        if (self.def_instr.get(idx_vid)) |id| if (t.kind(id) == .CastNormal) {
            idx_vid = t.instrs.get(.CastNormal, id).value;
        };

        if (self.def_instr.get(idx_vid)) |iid| {
            switch (t.kind(iid)) {
                .RangeMake => {
                    const r = t.instrs.get(.RangeMake, iid);
                    args = .{ .start = r.start, .end = r.end, .incl = r.inclusive };
                    found_range = true;
                },
                .Call => {
                    const call = t.instrs.get(.Call, iid);
                    if (std.mem.eql(u8, t.instrs.strs.get(call.callee), "builtin.range.make")) {
                        const c_args = t.instrs.val_list_pool.slice(call.args);
                        if (c_args.len >= 3) {
                            args = .{ .start = c_args[0], .end = c_args[1], .incl = c_args[2] };
                            found_range = true;
                        }
                    }
                },
                else => {},
            }
        }

        if (!found_range) return self.zeroOf(res_ty);

        // Compute Base Pointer for the slice
        var data_ptr: mlir.Value = undefined;
        var elem_sr: types.TypeId = undefined;

        switch (base_sr_kind) {
            .Array => {
                elem_sr = self.context.type_store.get(.Array, base_sr_ty).elem;
                const ptr = self.spillAgg(base, try self.llvmTypeOf(base_sr_ty), 0);
                const idxs = [_]tir.Rows.GepIndex{ .{ .Const = 0 }, .{ .Value = args.start } };
                data_ptr = try self.emitGep(ptr, try self.llvmTypeOf(base_sr_ty), &idxs); // Passing base type but logic uses elem
            },
            .Slice, .DynArray => {
                // Slice and DynArray structure is {ptr, len} or similar, ptr is at 0
                elem_sr = if (base_sr_kind == .Slice) self.context.type_store.get(.Slice, base_sr_ty).elem else self.context.type_store.get(.DynArray, base_sr_ty).elem;

                const ptr_ty = if (base_sr_kind == .Slice) self.llvm_ptr_ty else try self.llvmTypeOf(self.context.type_store.mkPtr(elem_sr, false));

                const ptr0 = self.extractAt(base, ptr_ty, &.{0});
                const idxs = [_]tir.Rows.GepIndex{.{ .Value = args.start }};
                data_ptr = try self.emitGep(ptr0, try self.llvmTypeOf(elem_sr), &idxs);
            },
            .Ptr => {
                const ptr_row = self.context.type_store.get(.Ptr, base_sr_ty);
                elem_sr = ptr_row.elem;
                const is_arr = self.context.type_store.getKind(elem_sr) == .Array;

                var idxs_buf: [2]tir.Rows.GepIndex = undefined;
                idxs_buf[0] = if (is_arr) .{ .Const = 0 } else .{ .Value = args.start };
                if (is_arr) idxs_buf[1] = .{ .Value = args.start };

                const idxs = if (is_arr) idxs_buf[0..2] else idxs_buf[0..1];
                data_ptr = try self.emitGep(base, try self.llvmTypeOf(elem_sr), idxs);
            },
            .String => {
                elem_sr = self.context.type_store.tU8();
                const ptr0 = self.extractAt(base, self.llvm_ptr_ty, &.{0});
                data_ptr = try self.emitGep(ptr0, self.i8_ty, &.{.{ .Value = args.start }});
            },
            else => return self.zeroOf(res_ty),
        }

        // Compute Length
        const i64t = self.i64_ty;
        const i64_sr = self.context.type_store.tI64();
        const start64 = try self.coerceOnBranch(self.getVal(args.start), i64t, i64_sr, self.srTypeOfValue(args.start));
        const end64 = try self.coerceOnBranch(self.getVal(args.end), i64t, i64_sr, self.srTypeOfValue(args.end));

        const diff = self.emitBinaryValueOp("llvm.sub", end64, start64, i64t, null);
        const z = self.emitUnaryValueOp("llvm.zext", self.getVal(args.incl), i64t);
        const len64 = self.emitBinaryValueOp("llvm.add", diff, z, i64t, null);

        // Build Result {ptr, len}
        var acc = self.zeroOf(res_ty);
        acc = self.insertAt(acc, data_ptr, &.{0});
        acc = self.insertAt(acc, len64, &.{1});
        return acc;
    }

    // 4. Standard Indexing (Load)
    // Case A: Indexing into Slice/DynArray value (not via ptr)
    if (!base.getType().equal(self.llvm_ptr_ty) and (base_sr_kind == .Slice or base_sr_kind == .DynArray)) {
        const elem_ptr_ty = if (base_sr_kind == .Slice) self.llvm_ptr_ty else try self.llvmTypeOf(self.context.type_store.mkPtr(self.context.type_store.get(.DynArray, base_sr_ty).elem, false));

        const ptr0 = self.extractAt(base, elem_ptr_ty, &.{0});
        // The GEP result type for load is simply the result type
        const vptr = try self.emitGep(ptr0, res_ty, &.{.{ .Value = p.index }});

        return self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{vptr},
            .results = &.{res_ty},
            .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
        });
    }

    // Case B: General Pointer or Aggregate Indexing
    var ptr_to_load: mlir.Value = undefined;
    var elem_type_hint: mlir.Type = res_ty;
    var gep_indices_buf: [2]tir.Rows.GepIndex = undefined;
    var gep_indices: []tir.Rows.GepIndex = &.{};

    if (base.getType().equal(self.llvm_ptr_ty)) {
        // Base is already a pointer
        ptr_to_load = base;
        var is_ptr_to_array = false;
        if (base_sr_kind == .Ptr) {
            const ptr_row = self.context.type_store.get(.Ptr, base_sr_ty);
            elem_type_hint = try self.llvmTypeOf(ptr_row.elem);
            if (self.context.type_store.getKind(ptr_row.elem) == .Array) is_ptr_to_array = true;
        }

        if (is_ptr_to_array) {
            gep_indices_buf[0] = .{ .Const = 0 };
            gep_indices_buf[1] = .{ .Value = p.index };
            gep_indices = gep_indices_buf[0..2];
        } else {
            gep_indices_buf[0] = .{ .Value = p.index };
            gep_indices = gep_indices_buf[0..1];
        }
    } else {
        // Base is an aggregate (Array/Struct value), spill to stack
        ptr_to_load = self.spillAgg(base, base.getType(), 0);
        elem_type_hint = base.getType(); // GEP needs agg type

        if (base_sr_kind == .Array) {
            gep_indices_buf[0] = .{ .Const = 0 };
            gep_indices_buf[1] = .{ .Value = p.index };
            gep_indices = gep_indices_buf[0..2];
        } else {
            gep_indices_buf[0] = .{ .Value = p.index };
            gep_indices = gep_indices_buf[0..1];
        }
    }

    const final_ptr = try self.emitGep(ptr_to_load, elem_type_hint, gep_indices);

    // For direct loads from aggregates, we might not need alignment (or use default),
    // keeping alignment=1 as per original for safety.
    const load_attrs = if (base.getType().equal(self.llvm_ptr_ty))
        &[_]mlir.NamedAttribute{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))}
    else
        &[_]mlir.NamedAttribute{};

    // Note: Original code uses alignment 1 for ptr loads, but not for spilled agg loads.
    // Preserving that distinction requires a check.
    if (base.getType().equal(self.llvm_ptr_ty)) {
        return self.emitOp("llvm.load", EmitOpArgs{
            .operands = &.{final_ptr},
            .results = &.{res_ty},
            .attributes = load_attrs,
        });
    } else {
        return self.emitOp("llvm.load", EmitOpArgs{ .operands = &.{final_ptr}, .results = &.{res_ty} });
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

    // Flatten logic for readability and reduce nesting
    if (kind == .Tuple) {
        const tuple_row = self.context.type_store.get(.Tuple, sr_ty);
        const elems = self.context.type_store.type_pool.slice(tuple_row.elems);

        // Ensure capacity once
        try out_vals.ensureUnusedCapacity(elems.len);
        try out_sr.ensureUnusedCapacity(elems.len);

        for (elems, 0..) |elem_sr, idx| {
            const elem_ty = try self.llvmTypeOf(elem_sr);
            const idx_arr = [_]i64{@intCast(idx)};
            const elem_val = self.extractAt(value, elem_ty, &idx_arr);
            try self.expandVariadicArgTuple(elem_val, elem_sr, out_vals, out_sr);
        }
        return;
    }

    // Handle string/slice/dynarray (pointer extraction)
    if (kind == .String or kind == .Slice or kind == .DynArray) {
        const ptr_sr = switch (kind) {
            .String => self.context.type_store.mkPtr(self.context.type_store.tU8(), false),
            .Slice => self.context.type_store.mkPtr(self.context.type_store.get(.Slice, sr_ty).elem, false),
            .DynArray => self.context.type_store.mkPtr(self.context.type_store.get(.DynArray, sr_ty).elem, false),
            else => unreachable,
        };
        const ptr_ty = try self.llvmTypeOf(ptr_sr);
        const ptr_val = self.extractAt(value, ptr_ty, &.{0});
        try out_vals.append(ptr_val);
        try out_sr.append(ptr_sr);
        return;
    }

    // Handle Bool (promotion)
    if (kind == .Bool) {
        const ext = self.emitUnaryValueOp("arith.extui", value, self.i32_ty);
        try out_vals.append(ext);
        try out_sr.append(self.context.type_store.tI32());
        return;
    }

    // Default: append as is
    try out_vals.append(value);
    try out_sr.append(sr_ty);
}

/// Emit an MLIR call instruction for `p`, wiring argument lists and return types.
fn emitCall(self: *Codegen, p: tir.Rows.Call, t: *tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const callee_name = t.instrs.strs.get(p.callee);
    var finfo = self.func_syms.get(p.callee);

    // Resolve declaration if missing
    if (finfo == null) {
        var is_local = false;
        if (self.context.global_func_map.get(p.callee)) |item| {
            const fn_info = item.@"1".Function.get(item.@"0");
            is_local = !fn_info.is_extern;
        }
        finfo = if (is_local) try self.ensureDeclFromCall(p, t) else try self.ensureFuncDeclFromCall(p, t);
    }
    const func_info = finfo.?;

    const callee_op_name = func_info.op.getName().str().toSlice();
    const isExternLL = std.mem.eql(u8, callee_op_name, "llvm.func");

    // Gather Arguments
    const args_slice = t.instrs.val_list_pool.slice(p.args);
    const arg_count = args_slice.len;

    // Stack Buffer Optimization: Arguments
    var val_buf: [32]mlir.Value = undefined;
    var sr_buf: [32]types.TypeId = undefined;

    const src_vals_stack = if (arg_count <= 32) val_buf[0..arg_count] else try self.gpa.alloc(mlir.Value, arg_count);
    defer if (arg_count > 32) self.gpa.free(src_vals_stack);

    const src_sr_stack = if (arg_count <= 32) sr_buf[0..arg_count] else try self.gpa.alloc(types.TypeId, arg_count);
    defer if (arg_count > 32) self.gpa.free(src_sr_stack);

    for (args_slice, 0..) |vid, i| {
        src_vals_stack[i] = self.getVal(vid);
        src_sr_stack[i] = self.srTypeOfValue(vid);
    }

    var final_vals: []mlir.Value = src_vals_stack;
    var final_sr: []types.TypeId = src_sr_stack;
    var expanded_list: ArrayList(mlir.Value) = undefined; // Init only if needed
    var expanded_sr_list: ArrayList(types.TypeId) = undefined;

    // Handle Variadic Expansion
    if (isExternLL and func_info.is_variadic and arg_count > func_info.n_formals) {
        expanded_list = ArrayList(mlir.Value).init(self.gpa);
        expanded_sr_list = ArrayList(types.TypeId).init(self.gpa);
        // Pre-reserve estimate
        try expanded_list.ensureTotalCapacity(arg_count + 4);
        try expanded_sr_list.ensureTotalCapacity(arg_count + 4);

        for (src_vals_stack, 0..) |val, idx| {
            if (idx < func_info.n_formals) {
                expanded_list.appendAssumeCapacity(val);
                expanded_sr_list.appendAssumeCapacity(src_sr_stack[idx]);
            } else {
                try self.expandVariadicArgTuple(val, src_sr_stack[idx], &expanded_list, &expanded_sr_list);
            }
        }
        final_vals = expanded_list.items;
        final_sr = expanded_sr_list.items;
    }
    defer if (isExternLL and func_info.is_variadic and arg_count > func_info.n_formals) {
        expanded_list.deinit();
        expanded_sr_list.deinit();
    };

    // Return Type Analysis
    const want_res_sr = p.ty;
    const want_kind = self.context.type_store.getKind(want_res_sr);
    const want_no_result = (want_kind == .Void or want_kind == .Noreturn);
    const want_res_mlir = try self.llvmTypeOf(want_res_sr);
    const want_has_res = !want_no_result and !self.void_ty.equal(want_res_mlir);

    // Call Type Dispatch
    const caller_is_tt = if (self.current_func_sym) |sym| blk: {
        if (self.func_syms.get(sym)) |cinfo| break :blk std.mem.eql(u8, cinfo.op.getName().str().toSlice(), "tt.func");
        break :blk false;
    } else false;

    const callee_is_tt = std.mem.eql(u8, callee_op_name, "tt.func");

    // --- Internal or Triton Call Path ---
    if (!isExternLL or self.emit_only_triton or callee_is_tt or caller_is_tt) {
        const call_args = try self.prepareInternalCallArgs(final_vals, final_sr, func_info);
        defer self.gpa.free(call_args);

        const op_name = if (self.emit_only_triton or callee_is_tt or caller_is_tt) "tt.call" else "func.call";

        var attr_buf: [1]mlir.NamedAttribute = undefined;
        attr_buf[0] = self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(callee_name)));

        const call = self.appendOp(op_name, EmitOpArgs{
            .operands = call_args,
            .results = if (want_has_res) &.{want_res_mlir} else &.{},
            .attributes = &attr_buf,
        });
        return if (want_has_res) call.getResult(0) else .empty();
    }

    // --- Extern LLVM ABI Call Path ---

    var retClass: abi.AbiClass = undefined;
    if (!want_no_result) retClass = abi.abiClassifyX64SysV(self, want_res_sr, true);

    var lowered_ops: ArrayList(mlir.Value) = .init(self.gpa);
    defer lowered_ops.deinit();
    try lowered_ops.ensureTotalCapacity(final_vals.len + 1); // Heuristic

    var formal_index: usize = 0;
    var retbuf: mlir.Value = .empty();

    // SRet handling
    if (!want_no_result and retClass.kind == .IndirectSRet) {
        retbuf = self.spillAgg(self.undefOf(want_res_mlir), want_res_mlir, @intCast(retClass.alignment));
        lowered_ops.appendAssumeCapacity(retbuf);
        formal_index += 1;
    }

    for (final_vals, 0..) |v, i| {
        const sr = final_sr[i];
        const cls = abi.abiClassifyX64SysV(self, sr, false);

        switch (cls.kind) {
            .IndirectByVal => {
                const stTy = try self.llvmTypeOf(sr);
                const align_val = if (cls.alignment == 0) 8 else cls.alignment;
                const tmp = self.spillAgg(v, stTy, align_val);

                var passv = tmp;
                if (formal_index < func_info.param_types.len) {
                    passv = try self.ensureCallArgType(passv, sr, func_info.param_types[formal_index]);
                }
                try lowered_ops.append(passv);
                formal_index += 1;
            },
            .DirectScalar => {
                const stTy = try self.llvmTypeOf(sr);
                var passv: mlir.Value = undefined;

                if (!stTy.isAInteger() and !stTy.isAFloat() and !stTy.isAVector()) {
                    const nat_align = @min(abi.abiSizeAlign(self, sr).alignment, @as(usize, std.math.maxInt(u32)));
                    const tmp = self.spillAgg(v, stTy, if (nat_align == 0) 8 else @intCast(nat_align));

                    if (cls.scalar0.?.isAInteger()) {
                        passv = self.loadIntAt(tmp, cls.scalar0.?.getIntegerBitwidth(), 0);
                    } else {
                        passv = self.emitOp("llvm.load", EmitOpArgs{ .operands = &.{tmp}, .results = &.{cls.scalar0.?} });
                    }
                } else {
                    passv = v;
                }

                const want_ty = if (formal_index < func_info.param_types.len) func_info.param_types[formal_index] else passv.getType();
                passv = try self.ensureCallArgType(passv, sr, want_ty);
                try lowered_ops.append(passv);
                formal_index += 1;
            },
            .DirectPair => {
                const stTy = try self.llvmTypeOf(sr);
                const tmp = self.spillAgg(v, stTy, 1);

                const lo = self.loadIntAt(tmp, 64, 0);
                const hi = self.loadIntAt(tmp, cls.scalar1.?.getIntegerBitwidth(), 8);

                var lo_cast = lo;
                if (formal_index < func_info.param_types.len) {
                    lo_cast = try self.ensureCallArgType(lo_cast, sr, func_info.param_types[formal_index]);
                }

                var hi_cast = hi;
                if (formal_index + 1 < func_info.param_types.len) {
                    hi_cast = try self.ensureCallArgType(hi_cast, sr, func_info.param_types[formal_index + 1]);
                }

                try lowered_ops.append(lo_cast);
                try lowered_ops.append(hi_cast);
                formal_index += 2;
            },
            else => unreachable,
        }
    }

    // Build Call Attributes
    const seg = mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ @as(i32, @intCast(lowered_ops.items.len)), 0 });
    const empty_bundle = mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{});

    var attr_list: ArrayList(mlir.NamedAttribute) = .init(self.gpa);
    defer attr_list.deinit();

    try attr_list.append(self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(callee_name))));
    try attr_list.append(self.named("operand_segment_sizes", seg));
    try attr_list.append(self.named("op_bundle_sizes", empty_bundle));

    if (func_info.is_variadic) {
        const func_ty = func_info.op.getInherentAttributeByName(mlir.StringRef.from("function_type"));
        try attr_list.append(self.named("var_callee_type", func_ty));
    }

    const call_results = if (want_no_result or retClass.kind == .IndirectSRet) &.{} else &.{func_info.ret_type};

    const call = self.appendOp("llvm.call", EmitOpArgs{
        .operands = lowered_ops.items,
        .results = call_results,
        .attributes = attr_list.items,
    });

    if (want_no_result) return .empty();

    // Reconstruct Result
    switch (retClass.kind) {
        .IndirectSRet => {
            return self.emitOp("llvm.load", EmitOpArgs{
                .operands = &.{retbuf},
                .results = &.{want_res_mlir},
                .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
            });
        },
        .DirectScalar => {
            const rv = call.getResult(0);
            if (want_res_mlir.isAInteger() or want_res_mlir.isAFloat() or want_res_mlir.isAVector()) {
                if (!rv.getType().equal(want_res_mlir)) {
                    return try self.ensureCallArgType(rv, want_res_sr, want_res_mlir);
                }
                return rv;
            }
            const tmp = self.spillAgg(self.undefOf(want_res_mlir), want_res_mlir, 8);
            self.storeAt(tmp, rv, 0);
            return self.emitOp("llvm.load", EmitOpArgs{
                .operands = &.{tmp},
                .results = &.{want_res_mlir},
                .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
            });
        },
        .DirectPair => {
            const rv = call.getResult(0);
            const loTy = retClass.scalar0.?;
            const hiTy = retClass.scalar1.?;

            // Extract lo
            const ex0 = self.emitOp("llvm.extractvalue", EmitOpArgs{
                .operands = &.{rv},
                .results = &.{loTy},
                .attributes = &.{self.named("position", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, &[_]i64{0}))},
            });
            // Extract hi
            const ex1 = self.emitOp("llvm.extractvalue", EmitOpArgs{
                .operands = &.{rv},
                .results = &.{hiTy},
                .attributes = &.{self.named("position", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, &[_]i64{1}))},
            });

            const agg = self.insertAt(self.undefOf(want_res_mlir), ex0, &.{0});
            return self.insertAt(agg, ex1, &.{1});
        },
        else => unreachable,
    }
}

/// Emit an MLIR block, including splices and argument lowering.
fn emitMlirBlock(self: *Codegen, p: tir.Rows.MlirBlock, t: *tir.TIR) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    // 1. Fast Path: Check for compile-time cached values (Modules, Types, Attrs)
    // This handles the deep nesting for comptime-known MLIR objects.
    if (p.kind != .Operation) {
        if (try self.checkCachedMlirValue(p)) |res| return res;
    }

    // 2. Build the textual MLIR representation with argument substitution
    const piece_ids = t.instrs.mlir_piece_pool.slice(p.pieces);
    const template = try self.renderMlirTemplate(t, piece_ids);
    defer self.gpa.free(template);

    const arg_vids = t.instrs.value_pool.slice(p.args);

    // 3. Handle Operations (Inline Assembly)
    if (p.kind == .Operation) {
        const result_ty = if (p.result.isNone()) self.void_ty else try self.llvmTypeOf(p.ty);
        const val = try self.emitInlineMlirOperation(template, arg_vids, result_ty, p.loc);
        return if (p.result.isNone()) .empty() else val;
    }

    // 4. Perform Textual Substitution for Definitions (Module/Type/Attr)
    const mlir_text = try self.buildMlirDefinitionText(template, arg_vids);
    defer self.gpa.free(mlir_text);

    // 5. Parse and Process Definitions
    return switch (p.kind) {
        .Module => self.parseAndMergeModule(mlir_text, p),
        .Type => self.parseMlirType(mlir_text, p),
        .Attribute => self.parseMlirAttribute(mlir_text, p),
        .Operation => unreachable,
    };
}

// --------------------------------------------------------------------------------
// Helpers
// --------------------------------------------------------------------------------

/// Check if the MLIR block resolves to a cached comptime value.
fn checkCachedMlirValue(self: *Codegen, p: tir.Rows.MlirBlock) !?mlir.Value {
    const ti = self.active_type_info orelse return null;
    const cached_ptr = ti.getComptimeValue(p.expr) orelse return null;
    const val = cached_ptr.*;
    const s = &ti.val_store;

    switch (p.kind) {
        .Module => {
            const module = switch (s.kind(val)) {
                .MlirModule => s.get(.MlirModule, val).module,
                else => return null,
            };

            // Clone the module operation to avoid modifying the cached source
            const cloned_op = mlir.Operation.clone(module.getOperation());
            var cloned_module = mlir.Module.fromOperation(cloned_op);
            defer cloned_module.destroy();

            // Extract function symbols and move operations to current module
            try self.mergeModuleBody(cloned_module);

            return if (p.result.isNone()) .empty() else self.zeroOf(try self.llvmTypeOf(p.ty));
        },
        .Type => return if (s.kind(val) == .MlirType) (if (p.result.isNone()) .empty() else self.zeroOf(try self.llvmTypeOf(p.ty))) else null,
        .Attribute => return if (s.kind(val) == .MlirAttribute) (if (p.result.isNone()) .empty() else self.zeroOf(try self.llvmTypeOf(p.ty))) else null,
        .Operation => unreachable,
    }
}

/// Construct the final MLIR text by substituting %N placeholders with SSA value string representations.
fn buildMlirDefinitionText(self: *Codegen, template: []const u8, arg_vids: []const tir.ValueId) ![]u8 {
    if (arg_vids.len == 0) return self.gpa.dupe(u8, template);

    var buf = ArrayList(u8).init(self.gpa);
    defer buf.deinit();
    try buf.ensureTotalCapacity(template.len + (arg_vids.len * 16));
    const writer = buf.writer();

    // Cache string representations of arguments on demand?
    // Optimization: Just print directly when encountered.
    // To support random access like %2, we need them indexed.

    var arg_strs = try self.gpa.alloc([]u8, arg_vids.len);
    defer {
        for (arg_strs) |s| self.gpa.free(s);
        self.gpa.free(arg_strs);
    }

    // Pre-print all arguments (optimizable: only print used ones, but simple is robust)
    var tmp_buf = ArrayList(u8).init(self.gpa);
    defer tmp_buf.deinit();

    for (arg_vids, 0..) |vid, i| {
        tmp_buf.clearRetainingCapacity();
        var had_err = false;
        var sink = PrintBuffer{ .list = &tmp_buf, .had_error = &had_err };

        self.getVal(vid).print(printCallback, &sink);

        const raw = tmp_buf.items;
        // Trim standard MLIR value output format: "  %name = ..." -> "%name"
        var trimmed = std.mem.trim(u8, raw, " \t\r\n");
        if (std.mem.indexOfScalar(u8, trimmed, '=')) |eq_idx| {
            trimmed = std.mem.trimRight(u8, trimmed[0..eq_idx], " \t\r\n");
        }
        arg_strs[i] = try self.gpa.dupe(u8, trimmed);
    }

    var i: usize = 0;
    while (i < template.len) {
        if (template[i] == '%') {
            var j = i + 1;
            var num: usize = 0;
            var num_len: usize = 0;
            while (j < template.len and std.ascii.isDigit(template[j])) {
                num = num * 10 + (template[j] - '0');
                num_len += 1;
                j += 1;
            }

            if (num_len > 0 and num < arg_strs.len) {
                try writer.writeAll(arg_strs[num]);
                i += num_len + 1;
            } else {
                try writer.writeByte('%');
                i += 1;
            }
        } else {
            try writer.writeByte(template[i]);
            i += 1;
        }
    }

    return buf.toOwnedSlice();
}

/// Parse an MLIR module string, extract symbols, and merge into the current context.
fn parseAndMergeModule(self: *Codegen, text: []const u8, p: tir.Rows.MlirBlock) !mlir.Value {
    var parsed_module = mlir.Module.createParse(self.mlir_ctx, mlir.StringRef.from(text));
    if (parsed_module.isNull()) {
        const loc = self.context.loc_store.get(p.loc.unwrap());
        try self.context.diags.addError(loc, .mlir_parse_error, .{});
        return error.MlirParseError;
    }
    defer parsed_module.destroy();

    try self.mergeModuleBody(parsed_module);

    if (p.result.isNone()) return .empty();
    return self.zeroOf(try self.llvmTypeOf(p.ty));
}

/// Helper to extract functions from a source module and move them to the Codegen module.
fn mergeModuleBody(self: *Codegen, src_module: mlir.Module) !void {
    var body = src_module.getBody();
    body.detach();

    var current_op = body.getFirstOperation();
    while (!current_op.isNull()) {
        const next_op = current_op.getNextInBlock();
        const op_name = current_op.getName().str().toSlice();

        if (std.mem.eql(u8, op_name, "func.func")) {
            try self.extractFunctionSymbol(current_op);
        }

        current_op.removeFromParent();
        var b = self.module.getBody();
        b.appendOwnedOperation(current_op);
        current_op = next_op;
    }
}

/// Extract symbol name and type info from a func operation and register it.
fn extractFunctionSymbol(self: *Codegen, op: mlir.Operation) !void {
    const sym_name_attr = op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
    if (sym_name_attr.isNull()) return;

    const sym_name = sym_name_attr.stringAttrGetValue().toSlice();
    const sym_id = self.context.interner.intern(sym_name);

    if (self.func_syms.contains(sym_id)) return;

    const type_attr = op.getInherentAttributeByName(mlir.StringRef.from("function_type"));
    const func_type = type_attr.typeAttrGetValue();
    const n_inputs = func_type.getFunctionNumInputs();
    const n_results = func_type.getFunctionNumResults();

    // Stack optimization for param types
    const param_count: usize = @intCast(n_inputs);
    var buf: [16]mlir.Type = undefined;
    const params = if (param_count <= 16) buf[0..param_count] else try self.gpa.alloc(mlir.Type, param_count);
    defer if (param_count > 16) self.gpa.free(params);

    for (0..param_count) |i| params[i] = func_type.getFunctionInput(@intCast(i));

    // Persist param types
    const persisted_params = try self.gpa.alloc(mlir.Type, param_count);
    std.mem.copyForwards(mlir.Type, persisted_params, params);

    const info = FuncInfo{
        .op = op,
        .is_variadic = false,
        .n_formals = @intCast(n_inputs),
        .ret_type = if (n_results == 1) func_type.getFunctionResult(0) else self.void_ty,
        .param_types = persisted_params,
        .owns_param_types = true,
        .dbg_subprogram = null,
    };
    _ = try self.func_syms.put(sym_id, info);
}

fn parseMlirType(self: *Codegen, text: []const u8, p: tir.Rows.MlirBlock) !mlir.Value {
    const ty = mlir.Type.parseGet(self.mlir_ctx, mlir.StringRef.from(text));
    if (ty.isNull()) {
        std.debug.print("Error parsing inline MLIR type: {s}\n", .{text});
        return error.MlirParseError;
    }
    if (p.result.isNone()) return .empty();
    return self.zeroOf(try self.llvmTypeOf(p.ty));
}

fn parseMlirAttribute(self: *Codegen, text: []const u8, p: tir.Rows.MlirBlock) !mlir.Value {
    const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(text));
    if (attr.isNull()) {
        std.debug.print("Error parsing inline MLIR attribute: {s}\n", .{text});
        return error.MlirParseError;
    }
    if (p.result.isNone()) return .empty();
    return self.zeroOf(try self.llvmTypeOf(p.ty));
}
// ----------------------------------------------------------------
// Instructions
// ----------------------------------------------------------------
/// Lower a single SSA instruction `ins_id` from `t` into MLIR and return its result value.
fn emitInstr(self: *Codegen, ins_id: tir.InstrId, t: *tir.TIR) !mlir.Value {
    // Common pattern: many instructions need location handling.
    // We handle it inside specific cases to avoid overhead for simple arithmetic.
    switch (t.kind(ins_id)) {
        // ------------- Constants -------------
        .ConstInt => return self.emitConstInt(t.instrs.get(.ConstInt, ins_id)),
        .ConstFloat => return self.emitConstFloat(t.instrs.get(.ConstFloat, ins_id)),
        .ConstBool => return self.emitConstBool(t.instrs.get(.ConstBool, ins_id)),
        .ConstNull => return self.emitConstNull(t.instrs.get(.ConstNull, ins_id)),
        .ConstUndef => return self.emitConstUndef(t.instrs.get(.ConstUndef, ins_id)),
        .ConstString => return self.emitConstString(t.instrs.get(.ConstString, ins_id)),

        // ------------- Arithmetic / bitwise -------------
        .Add => return self.emitAdd(t.instrs.get(.Add, ins_id)),
        .Sub => return self.emitSub(t.instrs.get(.Sub, ins_id)),
        .Mul => return self.emitMul(t.instrs.get(.Mul, ins_id)),
        .BinWrapAdd => return self.binArith(.add, t.instrs.get(.BinWrapAdd, ins_id)),
        .BinWrapSub => return self.binArith(.sub, t.instrs.get(.BinWrapSub, ins_id)),
        .BinWrapMul => return self.binArith(.mul, t.instrs.get(.BinWrapMul, ins_id)),
        .BinSatAdd => return self.emitSaturatingIntBinary(t.instrs.get(.BinSatAdd, ins_id), "arith.addi", true),
        .BinSatSub => return self.emitSaturatingIntBinary(t.instrs.get(.BinSatSub, ins_id), "arith.subi", true),
        .BinSatMul => return self.emitSaturatingIntBinary(t.instrs.get(.BinSatMul, ins_id), "arith.muli", true),
        .Div => return self.emitDiv(t.instrs.get(.Div, ins_id)),
        .Mod => return self.emitMod(t.instrs.get(.Mod, ins_id)),
        .Shl => return self.emitShl(t.instrs.get(.Shl, ins_id)),
        .BinSatShl => return self.emitSaturatingIntBinary(t.instrs.get(.BinSatShl, ins_id), "arith.shli", false),
        .Shr => return self.emitShr(t.instrs.get(.Shr, ins_id)),
        .BitAnd => return self.binBit(.@"and", t.instrs.get(.BitAnd, ins_id)),
        .BitOr => return self.binBit(.@"or", t.instrs.get(.BitOr, ins_id)),
        .BitXor => return self.binBit(.xor, t.instrs.get(.BitXor, ins_id)),

        // ------------- Logical -------------
        .LogicalAnd => return self.binBit(.@"and", t.instrs.get(.LogicalAnd, ins_id)),
        .LogicalOr => return self.binBit(.@"or", t.instrs.get(.LogicalOr, ins_id)),
        .LogicalNot => {
            const p = t.instrs.get(.LogicalNot, ins_id);
            return self.arithLogicalNotI1(self.getVal(p.value), p.loc);
        },

        // ------------- Comparisons -------------
        .CmpEq => return self.emitCmp("eq", "eq", "oeq", t.instrs.get(.CmpEq, ins_id)),
        .CmpNe => return self.emitCmp("ne", "ne", "one", t.instrs.get(.CmpNe, ins_id)),
        .CmpLt => return self.emitCmp("ult", "slt", "olt", t.instrs.get(.CmpLt, ins_id)),
        .CmpLe => return self.emitCmp("ule", "sle", "ole", t.instrs.get(.CmpLe, ins_id)),
        .CmpGt => return self.emitCmp("ugt", "sgt", "ogt", t.instrs.get(.CmpGt, ins_id)),
        .CmpGe => return self.emitCmp("uge", "sge", "oge", t.instrs.get(.CmpGe, ins_id)),

        // ------------- Casts -------------
        .CastBit => return self.emitCastBit(t.instrs.get(.CastBit, ins_id)),
        .CastNormal => return self.emitCastNormalInstr(t.instrs.get(.CastNormal, ins_id)),
        .CastSaturate => return self.emitCastSaturate(t.instrs.get(.CastSaturate, ins_id)),
        inline .CastWrap, .CastChecked => |x| return self.emitCastWrap(x, t.instrs.get(x, ins_id)),

        // ------------- Memory -------------
        .Alloca => return self.emitAlloca(t.instrs.get(.Alloca, ins_id)),
        .Load => return self.emitLoad(t.instrs.get(.Load, ins_id)),
        .Store => return self.emitStore(t.instrs.get(.Store, ins_id)),
        .Gep => return self.emitGepInstr(ins_id, t),
        .GlobalAddr => return self.emitGlobalAddr(t.instrs.get(.GlobalAddr, ins_id)),

        // ------------- Aggregates -------------
        .TupleMake => return self.emitTupleMake(t.instrs.get(.TupleMake, ins_id), t),
        .RangeMake => return self.emitRangeMake(t.instrs.get(.RangeMake, ins_id)),
        .Broadcast => return self.emitBroadcast(t.instrs.get(.Broadcast, ins_id)),

        .Await => {
            const p = t.instrs.get(.Await, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            const fut_val = self.getVal(p.operand);
            const op_ty = self.srTypeOfValue(p.operand);
            const fut_info = self.context.type_store.get(.Future, op_ty);

            if (self.context.type_store.getKind(fut_info.elem) != .Void) {
                // !async.value<T> -> returns T
                return self.emitOp("async.await", EmitOpArgs{
                    .operands = &.{fut_val},
                    .results = &.{try self.llvmTypeOf(p.ty)},
                });
            } else {
                // !async.token -> returns nothing
                _ = self.emitOp("async.await", EmitOpArgs{ .operands = &.{fut_val} });
                return .empty();
            }
        },

        .DbgDeclare => {
            const p = t.instrs.get(.DbgDeclare, ins_id);
            const v = self.getVal(p.value);
            const name = t.instrs.strs.get(p.name);
            try debug.emitLocalVariable(self, v, p.value, t, name, p.loc);
            return .empty();
        },

        .ArrayMake => return self.emitArrayMake(t.instrs.get(.ArrayMake, ins_id), t),

        .StructMake => {
            const p = t.instrs.get(.StructMake, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            var acc = self.zeroOf(try self.llvmTypeOf(p.ty));
            const fields = t.instrs.sfi_pool.slice(p.fields);

            // Reusing small buffer for indices to avoid allocator if possible
            for (fields) |f_id| {
                const f = t.instrs.StructFieldInit.get(f_id);
                const idx = [_]i64{@intCast(f.index)};
                acc = self.insertAt(acc, self.getVal(f.value), &idx);
            }
            return acc;
        },

        .ComplexMake => {
            const p = t.instrs.get(.ComplexMake, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            return self.emitOp("complex.create", EmitOpArgs{
                .operands = &.{ self.getVal(p.re), self.getVal(p.im) },
                .results = &.{try self.llvmTypeOf(p.ty)},
            });
        },

        .ExtractElem => {
            const p = t.instrs.get(.ExtractElem, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const idx = [_]i64{@intCast(p.index)};
            return self.extractAt(self.getVal(p.agg), try self.llvmTypeOf(p.ty), &idx);
        },

        .InsertElem => {
            const p = t.instrs.get(.InsertElem, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const idx = [_]i64{@intCast(p.index)};
            return self.insertAt(self.getVal(p.agg), self.getVal(p.value), &idx);
        },

        .ExtractField => {
            const p = t.instrs.get(.ExtractField, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            var agg = self.getVal(p.agg);
            const res_ty = try self.llvmTypeOf(p.ty);
            const parent_sr = self.srTypeOfValue(p.agg);
            const parent_kind = self.context.type_store.getKind(parent_sr);

            if (mlir.LLVM.isLLVMPointerType(agg.getType()) and isAggregateKind(parent_kind)) {
                const agg_ty = try self.llvmTypeOf(parent_sr);
                agg = self.emitOp("llvm.load", EmitOpArgs{
                    .operands = &.{agg},
                    .results = &.{agg_ty},
                    .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
                });
            }

            // Optimization: Handle Complex fast path
            if (parent_kind == .Complex) {
                const is_re = if (!p.name.isNone()) blk: {
                    const nm = t.instrs.strs.get(p.name.unwrap());
                    break :blk std.mem.eql(u8, nm, "real") or std.mem.eql(u8, nm, "re");
                } else p.index == 0;

                // If checking index 1 or name "im"/"imag", it's imaginary
                const is_im = if (!p.name.isNone()) blk: {
                    const nm = t.instrs.strs.get(p.name.unwrap());
                    break :blk std.mem.eql(u8, nm, "imag") or std.mem.eql(u8, nm, "im");
                } else p.index == 1;

                if (is_re) return self.emitUnaryValueOp("complex.re", agg, res_ty);
                if (is_im) return self.emitUnaryValueOp("complex.im", agg, res_ty);
            }

            // String properties (Slice/String)
            if (!p.name.isNone()) {
                const field_name = t.instrs.strs.get(p.name.unwrap());
                // Use fast byte check before memcmp
                if (field_name.len == 3 and std.mem.eql(u8, field_name, "len")) {
                    return self.extractAt(agg, res_ty, &.{1});
                }
                if (field_name.len == 8 and std.mem.eql(u8, field_name, "capacity")) {
                    return self.extractAt(agg, res_ty, &.{2});
                }
            }

            // Optional Handling
            if (parent_kind == .Optional) {
                if (self.context.type_store.isOptionalPointer(parent_sr)) {
                    // Optional Pointer Optimization
                    if (p.index == 0) {
                        const ptr_int = self.emitUnaryValueOp("llvm.ptrtoint", agg, self.i64_ty);
                        return self.emitBinaryValueOp("arith.cmpi", ptr_int, self.constInt(self.i64_ty, 0), self.i1_ty, &.{
                            self.named("predicate", self.arithCmpIPredAttr("ne")),
                        });
                    } else if (p.index == 1) {
                        return if (!agg.getType().equal(res_ty))
                            self.emitUnaryValueOp("llvm.bitcast", agg, res_ty)
                        else
                            agg;
                    }
                } else {
                    // Standard Optional { bool, T }
                    const eff_res_ty = if (p.index == 0) self.i1_ty else try self.llvmTypeOf(self.context.type_store.get(.Optional, parent_sr).elem);
                    return self.extractAt(agg, eff_res_ty, &.{@as(i64, @intCast(p.index))});
                }
            }

            // Default struct/tuple access
            return self.extractAt(agg, res_ty, &.{@as(i64, @intCast(p.index))});
        },

        .InsertField => {
            const p = t.instrs.get(.InsertField, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            const idx = [_]i64{@intCast(p.index)};
            return self.insertAt(self.getVal(p.agg), self.getVal(p.value), &idx);
        },

        .VariantMake => {
            const p = t.instrs.get(.VariantMake, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            var acc = self.zeroOf(try self.llvmTypeOf(p.ty));
            acc = self.insertAt(acc, self.constInt(self.i32_ty, @intCast(p.tag)), &.{0});

            if (!p.payload.isNone()) {
                const payload_val = self.getVal(p.payload.unwrap());
                // Accessing the union field of the wrapper struct {i32, union}
                // We construct the union part first
                const struct_ty = self.context.type_store.get(.Struct, p.ty);
                const union_field_id = self.context.type_store.field_pool.slice(struct_ty.fields)[1];
                const union_ty = self.context.type_store.Field.get(union_field_id).ty;

                var union_acc = self.zeroOf(try self.llvmTypeOf(union_ty));
                union_acc = self.insertAt(union_acc, payload_val, &.{0});
                acc = self.insertAt(acc, union_acc, &.{1});
            }
            return acc;
        },

        .VariantTag => {
            const p = t.instrs.get(.VariantTag, ins_id);
            return self.extractAt(self.getVal(p.value), mlir.Type.getSignlessIntegerType(self.mlir_ctx, 32), &.{0});
        },

        .VariantPayloadPtr => {
            const p = t.instrs.get(.VariantPayloadPtr, ins_id);
            return self.extractAt(self.getVal(p.value), self.llvm_ptr_ty, &.{1});
        },

        .UnionMake => {
            const p = t.instrs.get(.UnionMake, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            const u_mlir = try self.llvmTypeOf(p.ty);
            var payload = self.getVal(p.value);

            const urow = self.context.type_store.get(.Union, p.ty);
            const f_id = self.context.type_store.field_pool.slice(urow.fields)[@intCast(p.field_index)];
            const f_sr = self.context.type_store.Field.get(f_id).ty;
            const f_mlir = try self.llvmTypeOf(f_sr);

            if (!payload.getType().equal(f_mlir)) {
                payload = try self.coerceOnBranch(payload, f_mlir, f_sr, self.srTypeOfValue(p.value));
            }

            const tmp = self.spillAgg(self.undefOf(u_mlir), u_mlir, 0);
            self.storeAt(tmp, payload, 0);

            return self.emitOp("llvm.load", EmitOpArgs{
                .operands = &.{tmp},
                .results = &.{u_mlir},
            });
        },

        .UnionField => {
            const p = t.instrs.get(.UnionField, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            const base = self.getVal(p.base);
            const base_is_ptr = base.getType().equal(self.llvm_ptr_ty);
            const union_sr = self.srTypeOfValue(p.base);

            // Determine core union type (strip pointer if needed)
            const core_union_sr = if (base_is_ptr and self.context.type_store.getKind(union_sr) == .Ptr)
                self.context.type_store.get(.Ptr, union_sr).elem
            else
                union_sr;

            // Get field type
            const urow = self.context.type_store.get(.Union, core_union_sr);
            const f_id = self.context.type_store.field_pool.slice(urow.fields)[@intCast(p.field_index)];
            const f_sr = self.context.type_store.Field.get(f_id).ty;
            const f_mlir = try self.llvmTypeOf(f_sr);

            var storage_ptr = base;
            if (!base_is_ptr) {
                const u_mlir = try self.llvmTypeOf(core_union_sr);
                const field_align = abi.abiSizeAlign(self, f_sr).alignment;
                storage_ptr = self.spillAgg(base, u_mlir, @intCast(field_align));
            }

            // Gep 0 to typecast pointer
            const fptr = try self.emitGep(storage_ptr, f_mlir, &.{.{ .Const = 0 }});
            return self.emitOp("llvm.load", EmitOpArgs{
                .operands = &.{fptr},
                .results = &.{f_mlir},
                .attributes = &.{self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, 1))},
            });
        },

        .UnionFieldPtr => {
            const p = t.instrs.get(.UnionFieldPtr, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            const base = self.getVal(p.base);
            const base_is_ptr = base.getType().equal(self.llvm_ptr_ty);
            const union_sr = self.srTypeOfValue(p.base);

            const core_union_sr = if (base_is_ptr and self.context.type_store.getKind(union_sr) == .Ptr)
                self.context.type_store.get(.Ptr, union_sr).elem
            else
                union_sr;

            const urow = self.context.type_store.get(.Union, core_union_sr);
            const f_id = self.context.type_store.field_pool.slice(urow.fields)[@intCast(p.field_index)];
            const f_sr = self.context.type_store.Field.get(f_id).ty;
            const f_mlir = try self.llvmTypeOf(f_sr);

            var storage_ptr = base;
            if (!base_is_ptr) {
                const u_mlir = try self.llvmTypeOf(core_union_sr);
                const field_align = abi.abiSizeAlign(self, f_sr).alignment;
                storage_ptr = self.spillAgg(base, u_mlir, @intCast(field_align));
            }

            return self.emitGep(storage_ptr, f_mlir, &.{.{ .Const = 0 }});
        },

        .AddressOf => {
            const p = t.instrs.get(.AddressOf, ins_id);
            const v = self.getVal(p.value);
            if (mlir.LLVM.isLLVMPointerType(v.getType())) return v;
            // Unwrap from load
            return v.opResultGetOwner().getOperand(0);
        },

        .Index => return self.emitIndex(t.instrs.get(.Index, ins_id), t),

        .Select => {
            const p = t.instrs.get(.Select, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;
            return self.arithSelect(self.getVal(p.cond), self.getVal(p.then_value), self.getVal(p.else_value), try self.llvmTypeOf(p.ty));
        },

        .IndirectCall => {
            const p = t.instrs.get(.IndirectCall, ins_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            const args_slice = t.instrs.val_list_pool.slice(p.args);
            const count = args_slice.len + 1;

            // Stack optimization
            var buf: [32]mlir.Value = undefined;
            const ops = if (count <= 32) buf[0..count] else try self.gpa.alloc(mlir.Value, count);
            defer if (count > 32) self.gpa.free(ops);

            ops[0] = self.getVal(p.callee);
            for (args_slice, 0..) |vid, i| ops[i + 1] = self.getVal(vid);

            const ret_ty = try self.llvmTypeOf(p.ty);
            const has_res = !ret_ty.equal(self.void_ty);

            var attrs_buf: [2]mlir.NamedAttribute = undefined;
            const seg = mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ @as(i32, @intCast(count)), 0 });
            const bundles = mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{});
            attrs_buf[0] = self.named("operand_segment_sizes", seg);
            attrs_buf[1] = self.named("op_bundle_sizes", bundles);

            const call = self.appendOp("llvm.call", EmitOpArgs{
                .operands = ops,
                .results = if (has_res) &.{ret_ty} else &.{},
                .attributes = &attrs_buf,
            });
            return if (has_res) call.getResult(0) else .empty();
        },

        .Call => return self.emitCall(t.instrs.get(.Call, ins_id), t),
        .MlirBlock => return self.emitMlirBlock(t.instrs.get(.MlirBlock, ins_id), t),
    }
}

/// Inline the given MLIR operation within the current block.
fn emitInlineMlirOperation(
    self: *Codegen,
    mlir_text_raw: []const u8,
    arg_vids: []const tir.ValueId,
    result_ty: mlir.Type,
    loc: tir.OptLocId,
) !mlir.Value {
    const count = arg_vids.len;

    // Stack optimization for argument lists
    var val_buf: [32]mlir.Value = undefined;
    var ty_buf: [32]mlir.Type = undefined;

    const arg_values = if (count <= 32) val_buf[0..count] else try self.gpa.alloc(mlir.Value, count);
    defer if (count > 32) self.gpa.free(arg_values);

    const arg_types = if (count <= 32) ty_buf[0..count] else try self.gpa.alloc(mlir.Type, count);
    defer if (count > 32) self.gpa.free(arg_types);

    for (arg_vids, 0..) |arg_vid, i| {
        const v = self.getVal(arg_vid);
        arg_values[i] = v;
        arg_types[i] = v.getType();
    }

    // 1. Generate unique function name
    const func_name_buf = try std.fmt.allocPrint(self.gpa, "__sr_inline_mlir_{d}", .{self.inline_mlir_counter});
    self.inline_mlir_counter += 1;
    defer self.gpa.free(func_name_buf);

    // 2. Build the function string inside a module
    var func_str: ArrayList(u8) = .init(self.gpa);
    defer func_str.deinit();
    // Heuristic pre-alloc
    try func_str.ensureTotalCapacity(128 + mlir_text_raw.len + (count * 16));

    var writer = func_str.writer();
    try writer.print("module {{\nfunc.func private @{s}(", .{func_name_buf});

    // Reusable buffer for type printing
    var type_str_buf: ArrayList(u8) = .init(self.gpa);
    defer type_str_buf.deinit();

    for (arg_types, 0..) |*ty, i| {
        if (i > 0) try writer.writeAll(", ");
        try writer.print("%arg{d}: ", .{i});

        type_str_buf.clearRetainingCapacity();
        var had_error = false;
        var sink = PrintBuffer{ .list = &type_str_buf, .had_error = &had_error };
        ty.print(printCallback, &sink);
        try writer.writeAll(type_str_buf.items);
    }
    try writer.writeAll(")");

    const has_result = !result_ty.equal(self.void_ty);
    if (has_result) {
        try writer.writeAll(" -> ");
        type_str_buf.clearRetainingCapacity();
        var had_error = false;
        var sink = PrintBuffer{ .list = &type_str_buf, .had_error = &had_error };
        result_ty.print(printCallback, &sink);
        try writer.writeAll(type_str_buf.items);
    }

    try writer.writeAll(" {\n");
    if (has_result) try writer.writeAll("  %res = ");
    try writer.writeAll("  ");
    try writer.writeAll(mlir_text_raw);
    try writer.writeAll("\n");

    if (has_result) {
        try writer.writeAll("  func.return %res : ");
        try writer.writeAll(type_str_buf.items); // reuse cached result type string
        try writer.writeAll("\n");
    } else {
        try writer.writeAll("  func.return\n");
    }
    try writer.writeAll("}\n}");

    // 3. Parse module
    var parsed_module = mlir.Module.createParse(self.mlir_ctx, mlir.StringRef.from(func_str.items));
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
    var region = func_op.getRegion(0);
    var entry = region.getFirstBlock();

    // Remap block arguments
    for (arg_values, 0..) |av, i| {
        mlir.Value.replaceAllUsesOfWith(entry.getArgument(i), av);
    }

    // Capture return
    var ret_val: ?mlir.Value = null;
    var term = entry.getTerminator();
    if (has_result and term.getNumOperands() > 0) {
        ret_val = term.getOperand(0);
    }
    term.removeFromParent();
    term.destroy();

    // Move ops
    var op = entry.getFirstOperation();
    while (!op.isNull()) {
        const next = op.getNextInBlock();
        op.removeFromParent();
        self.cur_block.?.appendOwnedOperation(op);
        op = next;
    }

    return if (has_result) ret_val.? else .empty();
}

/// Emit comparison instructions for binary compare operations recorded in `p`.
fn emitCmp(
    self: *Codegen,
    comptime pred_u: []const u8,
    comptime pred_s: []const u8,
    comptime pred_f: []const u8,
    p: tir.Rows.Bin2,
) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    var lhs = self.getVal(p.lhs);
    var rhs = self.getVal(p.rhs);

    // Normalize pointers to integers for comparison
    if (mlir.LLVM.isLLVMPointerType(lhs.getType())) lhs = self.emitUnaryValueOp("llvm.ptrtoint", lhs, self.i64_ty);
    if (mlir.LLVM.isLLVMPointerType(rhs.getType())) rhs = self.emitUnaryValueOp("llvm.ptrtoint", rhs, self.i64_ty);

    if (lhs.getType().isAFloat()) {
        return self.emitBinaryValueOp("arith.cmpf", lhs, rhs, try self.llvmTypeOf(p.ty), &.{
            self.named("predicate", self.arithCmpFPredAttr(pred_f)),
        });
    } else {
        const pred = if (self.isUnsigned(self.srTypeOfValue(p.lhs))) self.arithCmpIPredAttr(pred_u) else self.arithCmpIPredAttr(pred_s);
        return self.emitBinaryValueOp("arith.cmpi", lhs, rhs, try self.llvmTypeOf(p.ty), &.{
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

            // Resolve function info once
            const finfo = self.func_syms.get(self.current_func_sym orelse return error.MlirMissingCurrentFunction) orelse return error.MlirMissingFunctionInfo;
            const ret_ty = self.ret_type_cache orelse finfo.ret_type;
            const name_ref = finfo.op.getName().str().toSlice();

            // Check context type (LLVM vs Triton vs Standard)
            if (std.mem.eql(u8, name_ref, "func.func")) {
                if (self.current_func_is_async) {
                    const ops = if (!p.value.isNone()) &.{self.getVal(p.value.unwrap())} else &.{};
                    _ = self.appendOp("async.yield", EmitOpArgs{ .operands = ops });
                } else {
                    const dest = self.ret_join_block.?;
                    if (self.ret_has_value) {
                        const v = if (!p.value.isNone()) self.getVal(p.value.unwrap()) else self.zeroOf(ret_ty);
                        _ = self.appendOp("cf.br", EmitOpArgs{ .operands = &.{v}, .successors = &.{dest} });
                    } else {
                        _ = self.appendOp("cf.br", EmitOpArgs{ .successors = &.{dest} });
                    }
                }
            } else if (std.mem.eql(u8, name_ref, "llvm.func")) {
                if (!p.value.isNone()) {
                    const v = self.getVal(p.value.unwrap());
                    const ops: []const mlir.Value = if (ret_ty.equal(self.void_ty)) &.{} else &.{v};
                    _ = self.appendOp("llvm.return", EmitOpArgs{ .operands = ops });
                } else {
                    if (!ret_ty.equal(self.void_ty)) {
                        _ = self.appendOp("llvm.return", EmitOpArgs{ .operands = &.{self.zeroOf(ret_ty)} });
                    } else {
                        _ = self.appendOp("llvm.return", EmitOpArgs{});
                    }
                }
            } else { // tt.func
                const ops = if (!p.value.isNone()) &.{self.getVal(p.value.unwrap())} else &.{};
                _ = self.appendOp("tt.return", EmitOpArgs{ .operands = ops });
            }
        },

        .Br => {
            const p = t.terms.get(.Br, term_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            const edge = t.terms.Edge.get(p.edge);
            const args = t.instrs.value_pool.slice(edge.args);
            const count = args.len;

            // Stack optimization
            var buf: [32]mlir.Value = undefined;
            const argv = if (count <= 32) buf[0..count] else try self.gpa.alloc(mlir.Value, count);
            defer if (count > 32) self.gpa.free(argv);

            for (args, 0..) |avid, i| argv[i] = self.getVal(avid);

            _ = self.appendOp("cf.br", EmitOpArgs{
                .operands = argv,
                .successors = &.{self.block_map.get(edge.dest).?},
            });
        },

        .CondBr => {
            const p = t.terms.get(.CondBr, term_id);
            const prev_loc = self.pushLocation(p.loc);
            defer self.loc = prev_loc;

            const tedge = t.terms.Edge.get(p.then_edge);
            const eedge = t.terms.Edge.get(p.else_edge);
            const targs = t.instrs.value_pool.slice(tedge.args);
            const eargs = t.instrs.value_pool.slice(eedge.args);

            const t_len = targs.len;
            const e_len = eargs.len;
            const total = 1 + t_len + e_len;

            // Stack optimization
            var buf: [64]mlir.Value = undefined;
            const ops = if (total <= 64) buf[0..total] else try self.gpa.alloc(mlir.Value, total);
            defer if (total > 64) self.gpa.free(ops);

            ops[0] = self.getVal(p.cond);
            for (targs, 0..) |vid, i| ops[1 + i] = self.getVal(vid);
            for (eargs, 0..) |vid, i| ops[1 + t_len + i] = self.getVal(vid);

            const seg = mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ 1, @intCast(t_len), @intCast(e_len) });

            _ = self.appendOp("cf.cond_br", EmitOpArgs{
                .operands = ops,
                .successors = &.{ self.block_map.get(tedge.dest).?, self.block_map.get(eedge.dest).? },
                .attributes = &.{self.named("operand_segment_sizes", seg)},
            });
        },

        .SwitchInt => @panic("Not Implemented, Switch Int"),

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

    // Resolve base tensor pointer info
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
    // Validation checks
    if (self.context.type_store.getKind(root_sr) != .Ptr) return null;
    const root_elem = self.context.type_store.get(.Ptr, root_sr).elem;
    if (self.context.type_store.getKind(root_elem) != .Tensor) return null;

    // Combine indices (Must alloc: this data persists in the map)
    const index_ids = t.instrs.gep_pool.slice(p.indices);
    const combined = try self.combineTensorIndexIds(t, base_indices, index_ids);
    errdefer if (combined.len != 0) self.gpa.free(combined);

    const info = TensorElemPtrInfo{
        .root_ptr = root,
        .elem_ty = self.context.type_store.get(.Ptr, p.ty).elem,
        .indices = combined,
    };

    // Update map (Ownership of 'combined' passes to the map entry)
    if (self.tensor_elem_ptrs.getPtr(p.result)) |old_ptr| {
        self.freeTensorElemPtrInfo(old_ptr);
        old_ptr.* = info;
    } else {
        try self.tensor_elem_ptrs.put(p.result, info);
    }

    // Return null pointer placeholder
    const placeholder = self.llvmNullPtr();
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

/// Handle storing a scalar into a tensor element using indexed GEPs.
fn handleTensorElementStore(
    self: *Codegen,
    p: tir.Rows.Store,
    value: mlir.Value,
) !bool {
    const info = self.tensor_elem_ptrs.get(p.ptr) orelse return false;

    // Validate types
    if (self.context.type_store.getKind(info.elem_ty) == .Tensor) return false;
    const tensor_sr = self.srTypeOfValue(info.root_ptr);
    if (self.context.type_store.getKind(tensor_sr) != .Ptr) return false;

    const tensor_ty = self.context.type_store.get(.Ptr, tensor_sr).elem;
    const tensor_mlir_ty = try self.llvmTypeOf(tensor_ty);

    var base_val = self.tensor_slots.get(info.root_ptr) orelse mlir.Value.empty();
    if (base_val.isNull()) base_val = self.zeroOf(tensor_mlir_ty);

    // Convert indices using Stack Buffer
    const count = info.indices.len;
    var idx_buf: [16]mlir.Value = undefined;
    const index_vals = if (count <= 16) idx_buf[0..count] else try self.gpa.alloc(mlir.Value, count);
    defer if (count > 16) self.gpa.free(index_vals);

    const idx_ty = mlir.Type.getIndexType(self.mlir_ctx);
    for (info.indices, 0..) |entry, i| {
        index_vals[i] = switch (entry) {
            .constant => |c| self.emitOp("arith.constant", EmitOpArgs{
                .results = &.{idx_ty},
                .attributes = &.{self.named("value", mlir.Attribute.integerAttrGet(idx_ty, c))},
            }),
            .value => |vid| try self.ensureIndexValue(self.getVal(vid)),
        };
    }

    const new_tensor = try self.tensorInsertScalar(tensor_ty, info.elem_ty, base_val, value, index_vals);
    try self.tensor_slots.put(info.root_ptr, new_tensor);
    return true;
}

/// Attempt to lower scalar loads from tensor elements by following tensor GEP helpers.
fn tryEmitTensorElementLoad(
    self: *Codegen,
    p: tir.Rows.Load,
) !?mlir.Value {
    const info = self.tensor_elem_ptrs.get(p.ptr) orelse return null;

    if (self.context.type_store.getKind(info.elem_ty) == .Tensor) return null;
    const tensor_sr = self.srTypeOfValue(info.root_ptr);
    if (self.context.type_store.getKind(tensor_sr) != .Ptr) return null;

    const tensor_ty = self.context.type_store.get(.Ptr, tensor_sr).elem;
    const tensor_mlir_ty = try self.llvmTypeOf(tensor_ty);

    var base_val = self.tensor_slots.get(info.root_ptr) orelse mlir.Value.empty();
    if (base_val.isNull()) base_val = self.zeroOf(tensor_mlir_ty);

    // Convert indices using Stack Buffer
    const count = info.indices.len;
    var idx_buf: [16]mlir.Value = undefined;
    const index_vals = if (count <= 16) idx_buf[0..count] else try self.gpa.alloc(mlir.Value, count);
    defer if (count > 16) self.gpa.free(index_vals);

    const idx_ty = mlir.Type.getIndexType(self.mlir_ctx);
    for (info.indices, 0..) |entry, i| {
        index_vals[i] = switch (entry) {
            .constant => |c| self.emitOp("arith.constant", EmitOpArgs{
                .results = &.{idx_ty},
                .attributes = &.{self.named("value", mlir.Attribute.integerAttrGet(idx_ty, c))},
            }),
            .value => |vid| try self.ensureIndexValue(self.getVal(vid)),
        };
    }

    return try self.tensorExtractScalar(info.elem_ty, base_val, index_vals);
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
    const count = indices.len + 2;

    // Stack optimization for operands
    var buf: [16]mlir.Value = undefined;
    const ops = if (count <= 16) buf[0..count] else try self.gpa.alloc(mlir.Value, count);
    defer if (count > 16) self.gpa.free(ops);

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
    const count = indices.len + 1;

    // Stack optimization for operands
    var buf: [16]mlir.Value = undefined;
    const ops = if (count <= 16) buf[0..count] else try self.gpa.alloc(mlir.Value, count);
    defer if (count > 16) self.gpa.free(ops);

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
    // Handle Aggregate Spilling (if base is not a ptr)
    var base_ptr = base;
    if (!mlir.LLVM.isLLVMPointerType(base.getType())) {
        base_ptr = self.spillAgg(base, elem_ty, 0);
    }

    const count = idxs.len;

    // Stack optimizations for construction arrays
    var dyn_buf: [16]mlir.Value = undefined;
    var raw_buf: [16]i32 = undefined;
    var ops_buf: [32]mlir.Value = undefined;

    const dyn = if (count <= 16) dyn_buf[0..count] else try self.gpa.alloc(mlir.Value, count);
    defer if (count > 16) self.gpa.free(dyn);

    const raw = if (count <= 16) raw_buf[0..count] else try self.gpa.alloc(i32, count);
    defer if (count > 16) self.gpa.free(raw);

    const dyn_min = std.math.minInt(i32);
    var ndyn: usize = 0;

    for (idxs, 0..) |g, i| {
        switch (g) {
            .Const => |c| raw[i] = @intCast(c),
            .Value => |vid| {
                raw[i] = dyn_min;
                dyn[ndyn] = self.getVal(vid);
                ndyn += 1;
            },
        }
    }

    const total_ops = 1 + ndyn;
    const ops = if (total_ops <= 32) ops_buf[0..total_ops] else try self.gpa.alloc(mlir.Value, total_ops);
    defer if (total_ops > 32) self.gpa.free(ops);

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
    const val: i64 = comptime blk: {
        if (std.mem.eql(u8, pred, "eq")) break :blk 0;
        if (std.mem.eql(u8, pred, "ne")) break :blk 1;
        if (std.mem.eql(u8, pred, "slt")) break :blk 2;
        if (std.mem.eql(u8, pred, "sle")) break :blk 3;
        if (std.mem.eql(u8, pred, "sgt")) break :blk 4;
        if (std.mem.eql(u8, pred, "sge")) break :blk 5;
        if (std.mem.eql(u8, pred, "ult")) break :blk 6;
        if (std.mem.eql(u8, pred, "ule")) break :blk 7;
        if (std.mem.eql(u8, pred, "ugt")) break :blk 8;
        if (std.mem.eql(u8, pred, "uge")) break :blk 9;
        unreachable;
    };
    return mlir.Attribute.integerAttrGet(self.i64_ty, val);
}

/// Build an MLIR floating-point predicate attribute from the string `pred`.
fn arithCmpFPredAttr(self: *Codegen, comptime pred: []const u8) mlir.Attribute {
    const val: i64 = comptime blk: {
        if (std.mem.eql(u8, pred, "false")) break :blk 0;
        if (std.mem.eql(u8, pred, "oeq")) break :blk 1;
        if (std.mem.eql(u8, pred, "ogt")) break :blk 2;
        if (std.mem.eql(u8, pred, "oge")) break :blk 3;
        if (std.mem.eql(u8, pred, "olt")) break :blk 4;
        if (std.mem.eql(u8, pred, "ole")) break :blk 5;
        if (std.mem.eql(u8, pred, "one")) break :blk 6;
        if (std.mem.eql(u8, pred, "ord")) break :blk 7;
        if (std.mem.eql(u8, pred, "ueq")) break :blk 8;
        if (std.mem.eql(u8, pred, "ugt")) break :blk 9;
        if (std.mem.eql(u8, pred, "uge")) break :blk 10;
        if (std.mem.eql(u8, pred, "ult")) break :blk 11;
        if (std.mem.eql(u8, pred, "ule")) break :blk 12;
        if (std.mem.eql(u8, pred, "une")) break :blk 13;
        if (std.mem.eql(u8, pred, "uno")) break :blk 14;
        if (std.mem.eql(u8, pred, "true")) break :blk 15;
        unreachable;
    };
    return mlir.Attribute.integerAttrGet(self.i64_ty, val);
}

/// Append `op` into the current block held by `Codegen`.
pub inline fn append(self: *Codegen, op: mlir.Operation) void {
    self.cur_block.?.appendOwnedOperation(op);
}

/// Check whether `v` represents an `llvm.mlir.undef` placeholder.
pub inline fn isUndefValue(self: *const Codegen, v: mlir.Value) bool {
    _ = self;
    if (!v.isAOpResult()) return false;
    const owner = v.opResultGetOwner();
    if (owner.isNull()) return false;
    const name = owner.getName().str().toSlice();
    return std.mem.eql(u8, name, "llvm.mlir.undef");
}

/// Wrap `attr` and `name` into a MLIR `NamedAttribute`.
pub inline fn named(self: *const Codegen, name: []const u8, attr: mlir.Attribute) mlir.NamedAttribute {
    return .{
        .inner = .{
            .name = mlir.c.mlirIdentifierGet(self.mlir_ctx.handle, mlir.StringRef.from(name).inner),
            .attribute = attr.handle,
        },
    };
}
/// Helper that interns a string into an MLIR StringAttr.
pub inline fn strAttr(self: *const Codegen, s: []const u8) mlir.Attribute {
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
pub inline fn emitOp(self: *Codegen, name: []const u8, args: EmitOpArgs) mlir.Value {
    const op = self.appendOp(name, args);
    if (op.getNumResults() == 0) return .empty();
    return op.getResult(0);
}

/// Emit a binary operation that consumes two values and produces one result.
pub inline fn emitBinaryValueOp(
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
pub inline fn emitUnaryValueOp(self: *Codegen, name: []const u8, operand: mlir.Value, result_ty: mlir.Type) mlir.Value {
    return self.emitOp(name, EmitOpArgs{
        .operands = &.{operand},
        .results = &.{result_ty},
    });
}

/// Helper that panics if a value ID is missing from the map.
inline fn getVal(self: *Codegen, id: tir.ValueId) mlir.Value {
    return self.value_map.get(id) orelse std.debug.panic("missing value for instr {}", .{id});
}

/// Shortcut for getting the SR kind for a type.
inline fn srKind(self: *Codegen, ty: types.TypeId) types.TypeKind {
    return self.context.type_store.getKind(ty);
}

/// Emit a zero constant for `ty`, using splat for vectors and `llvm.mlir.zero` otherwise.
pub fn zeroOf(self: *Codegen, ty: mlir.Type) mlir.Value {
    if (ty.isAVector() or ty.isATensor()) {
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
    return self.emitOp("llvm.mlir.zero", EmitOpArgs{ .results = &.{ty} });
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
    const zero = self.constInt(self.i64_ty, 0);
    return self.emitUnaryValueOp("llvm.inttoptr", zero, self.llvm_ptr_ty);
}

/// Emit an `llvm.mlir.undef` of type `ty`.
pub inline fn undefOf(self: *Codegen, ty: mlir.Type) mlir.Value {
    return self.emitOp("llvm.mlir.undef", EmitOpArgs{ .results = &.{ty} });
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
    var attrs_buf: [2]mlir.NamedAttribute = undefined;
    attrs_buf[0] = self.named("elem_type", mlir.Attribute.typeAttrGet(elemTy));
    const n_attrs: usize = if (alignment != 0) blk: {
        attrs_buf[1] = self.named("alignment", mlir.Attribute.integerAttrGet(self.i64_ty, alignment));
        break :blk 2;
    } else 1;

    const one = self.getI64OneInEntry();
    const a = self.buildOp("llvm.alloca", EmitOpArgs{
        .operands = &.{one},
        .results = &.{self.llvm_ptr_ty},
        .attributes = attrs_buf[0..n_attrs],
    });
    self.appendInFuncEntry(a);
    const ptr = a.getResult(0);

    _ = self.appendOp("llvm.store", EmitOpArgs{ .operands = &.{ aggVal, ptr } });
    return ptr;
}

// Load iN from ptr + offset
fn loadIntAt(self: *Codegen, base: mlir.Value, bits: u32, offset: usize) mlir.Value {
    const ity = mlir.Type.getSignlessIntegerType(self.mlir_ctx, bits);
    var p = base;
    if (offset != 0) {
        p = self.emitOp("llvm.getelementptr", EmitOpArgs{
            .operands = &.{ base, self.constInt(self.i64_ty, @intCast(offset)) },
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
pub fn storeAt(self: *Codegen, base: mlir.Value, val: mlir.Value, offset: usize) void {
    var p = base;
    if (offset != 0) {
        p = self.emitOp("llvm.getelementptr", EmitOpArgs{
            .operands = &.{ base, self.constInt(self.i64_ty, @intCast(offset)) },
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
    if (ty.isAVector() or ty.isATensor()) {
        const elem_ty = ty.getShapedElementType();
        const attr = mlir.Attribute.integerAttrGet(elem_ty, @intCast(v));
        return self.emitOp("arith.constant", EmitOpArgs{
            .results = &.{ty},
            .attributes = &.{self.named("value", mlir.Attribute.denseElementsAttrSplatGet(ty, attr))},
        });
    }
    return self.emitOp("llvm.mlir.constant", EmitOpArgs{
        .results = &.{ty},
        .attributes = &.{self.named("value", mlir.Attribute.integerAttrGet(ty, @intCast(v)))},
    });
}

/// Emit a constant floating-point value `v` of MLIR type `ty`.
pub fn constFloat(self: *Codegen, ty: mlir.Type, v: f64) mlir.Value {
    if (ty.isAVector() or ty.isATensor()) {
        const elem_ty = ty.getShapedElementType();
        const attr = mlir.Attribute.floatAttrDoubleGet(self.mlir_ctx, elem_ty, v);
        return self.emitOp("arith.constant", EmitOpArgs{
            .results = &.{ty},
            .attributes = &.{self.named("value", mlir.Attribute.denseElementsAttrSplatGet(ty, attr))},
        });
    }
    return self.emitOp("llvm.mlir.constant", EmitOpArgs{
        .results = &.{ty},
        .attributes = &.{self.named("value", mlir.Attribute.floatAttrDoubleGet(self.mlir_ctx, ty, v))},
    });
}

/// Emit an MLIR `i1` constant representing `v`.
pub inline fn constBool(self: *Codegen, v: bool) mlir.Value {
    return self.constInt(self.i1_ty, if (v) 1 else 0);
}

/// Return true when `ty` represents an unsigned integer kind.
fn isUnsigned(self: *Codegen, ty: types.TypeId) bool {
    const k = self.context.type_store.getKind(ty);
    return k == .U8 or k == .U16 or k == .U32 or k == .U64 or k == .Usize;
}

/// Emit a generic binary operation using the provided MLIR opcode and result type.
fn emitBinOp(self: *Codegen, p: tir.Rows.Bin2, op_name: []const u8, ty: mlir.Type) !mlir.Value {
    return self.emitOp(op_name, EmitOpArgs{
        .operands = &.{ self.getVal(p.lhs), self.getVal(p.rhs) },
        .results = &.{ty},
    });
}

/// Emit binary arithmetic operations (add/sub/mul) for `p` with float/int dispatch.
fn binArith(self: *Codegen, comptime op_kind: BinArithOp, p: tir.Rows.Bin2) !mlir.Value {
    const ty = try self.llvmTypeOf(p.ty);
    const elem_ty = if (ty.isAShaped()) ty.getShapedElementType() else ty;

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
    const from_w = cast.intOrFloatWidth(v.getType()) catch 0;
    const to_w = cast.intOrFloatWidth(to_ty) catch 0;
    if (from_w >= to_w) return v;
    return self.emitUnaryValueOp(if (signed) "arith.extsi" else "arith.extui", v, to_ty);
}

/// Emit integer binary ops that saturate (used only when requested).
fn emitSaturatingIntBinary(self: *Codegen, p: tir.Rows.Bin2, arith_name: []const u8, rhs_uses_lhs_sign: bool) !mlir.Value {
    const prev_loc = self.pushLocation(p.loc);
    defer self.loc = prev_loc;

    const res_ty = try self.llvmTypeOf(p.ty);
    const base_width = cast.intOrFloatWidth(res_ty) catch unreachable;
    const ext_ty = mlir.Type.getSignlessIntegerType(self.mlir_ctx, @intCast(base_width * 2));

    const lhs_signed = self.isSignedInt(p.ty);
    const lhs_ext = self.extendIntegerValue(self.getVal(p.lhs), lhs_signed, ext_ty);
    const rhs_ext = self.extendIntegerValue(self.getVal(p.rhs), if (rhs_uses_lhs_sign) lhs_signed else false, ext_ty);

    const wide = self.emitBinaryValueOp(arith_name, lhs_ext, rhs_ext, ext_ty, null);
    return cast.saturateIntToInt(self, wide, lhs_signed, res_ty, lhs_signed);
}

/// Emit bitwise binary operations (and/or/xor) for `p`.
fn binBit(self: *Codegen, comptime op_kind: BinBitOp, p: tir.Rows.Bin2) !mlir.Value {
    const op_name = switch (op_kind) {
        .@"and" => "arith.andi",
        .@"or" => "arith.ori",
        .xor => "arith.xori",
    };
    return self.emitBinaryValueOp(op_name, self.getVal(p.lhs), self.getVal(p.rhs), try self.llvmTypeOf(p.ty), null);
}

/// Emit division operations (signed or unsigned) for the arithmetic lowerings.
fn arithDiv(self: *Codegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type, signed: bool) mlir.Value {
    const elem_ty = if (res_ty.isAShaped()) res_ty.getShapedElementType() else res_ty;
    const op_name = if (elem_ty.isAFloat()) "arith.divf" else (if (signed) "arith.divsi" else "arith.divui");
    return self.emitBinaryValueOp(op_name, lhs, rhs, res_ty, null);
}

/// Emit remainder operations for signed/unsigned integers.
fn arithRem(self: *Codegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type, signed: bool) mlir.Value {
    const elem_ty = if (res_ty.isAShaped()) res_ty.getShapedElementType() else res_ty;
    const op_name = if (elem_ty.isAFloat()) "arith.remf" else (if (signed) "arith.remsi" else "arith.remui");
    return self.emitBinaryValueOp(op_name, lhs, rhs, res_ty, null);
}

fn arithShl(self: *Codegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type) mlir.Value {
    return self.emitBinaryValueOp("arith.shli", lhs, rhs, res_ty, null);
}

fn arithShr(self: *Codegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type, signed: bool) mlir.Value {
    return self.emitBinaryValueOp(if (signed) "arith.shrsi" else "arith.shrui", lhs, rhs, res_ty, null);
}

fn arithLogicalNotI1(self: *Codegen, v: mlir.Value, loc: tir.OptLocId) mlir.Value {
    const prev_loc = self.pushLocation(loc);
    defer self.loc = prev_loc;
    return self.emitBinaryValueOp("arith.xori", v, self.constBool(true), self.i1_ty, null);
}

fn arithSelect(self: *Codegen, c: mlir.Value, tv: mlir.Value, ev: mlir.Value, res_ty: mlir.Type) mlir.Value {
    return self.emitOp("arith.select", EmitOpArgs{
        .operands = &.{ c, tv, ev },
        .results = &.{res_ty},
    });
}

/// Lookup or rebuild the `FuncInfo` for the call target `p`.
fn ensureDeclFromCall(self: *Codegen, p: tir.Rows.Call, t: *const tir.TIR) !FuncInfo {
    const args_slice = t.instrs.val_list_pool.slice(p.args);
    const count = args_slice.len;

    // Stack optimization: Avoid allocation for common function signatures
    var buf: [32]mlir.Type = undefined;
    const arg_tys = if (count <= 32) buf[0..count] else try self.gpa.alloc(mlir.Type, count);
    defer if (count > 32) self.gpa.free(arg_tys);

    for (args_slice, 0..) |vid, i| arg_tys[i] = self.getVal(vid).getType();
    const ret_ty = try self.llvmTypeOf(p.ty);
    const name = t.instrs.strs.get(p.callee);

    // Builtin intrinsics
    if (std.mem.startsWith(u8, name, "m$")) {
        return .{
            .op = self.module.getOperation(),
            .is_variadic = false,
            .n_formals = count,
            .ret_type = ret_ty,
            .param_types = @constCast((&[_]mlir.Type{})[0..]),
            .owns_param_types = false,
            .dbg_subprogram = null,
        };
    }

    // Unify triton vs standard func creation logic
    const is_triton = self.emit_only_triton;
    const op_name = if (is_triton) "tt.func" else "func.func";

    const n_res: usize = if (ret_ty.equal(self.void_ty)) 0 else 1;
    var res_buf: [1]mlir.Type = undefined;
    if (n_res == 1) res_buf[0] = ret_ty;

    const func_type = mlir.Type.getFunctionType(self.mlir_ctx, @intCast(count), arg_tys, @intCast(n_res), res_buf[0..n_res]);

    const attrs = [_]mlir.NamedAttribute{
        self.named("sym_name", self.strAttr(name)),
        self.named("function_type", mlir.Attribute.typeAttrGet(func_type)),
        self.named("sym_visibility", self.strAttr("private")),
    };

    const region = mlir.Region.create();
    const func_op = self.buildOp(op_name, EmitOpArgs{ .attributes = &attrs, .regions = &.{region} });
    var body = self.module.getBody();
    body.appendOwnedOperation(func_op);

    // We must own the param types slice for the FuncInfo struct
    const param_types_copy = try self.gpa.alloc(mlir.Type, count);
    std.mem.copyForwards(mlir.Type, param_types_copy, arg_tys);

    const info: FuncInfo = .{
        .op = func_op,
        .is_variadic = false,
        .n_formals = count,
        .ret_type = ret_ty,
        .param_types = param_types_copy,
        .owns_param_types = true,
        .dbg_subprogram = null,
    };
    _ = try self.func_syms.put(p.callee, info);
    return info;
}

/// Emit an LLVM global string literal for `text`.
fn constStringPtr(self: *Codegen, text: []const u8) !mlir.Operation {
    if (self.str_pool.get(text)) |*g| return self.addrOfFirstCharLen(@constCast(g), text.len + 1);

    var hasher: std.hash.Fnv1a_64 = .init();
    hasher.update(text);
    const name = try std.fmt.allocPrint(self.gpa, "__str_{x}", .{hasher.final()});
    defer self.gpa.free(name);

    // Optimized: Append null terminator directly to create StringAttr, avoiding "llvm.mlir.global" parsing overhead
    var val_buf: ArrayList(u8) = .init(self.gpa);
    defer val_buf.deinit();
    try val_buf.ensureTotalCapacity(text.len + 1);
    val_buf.appendSliceAssumeCapacity(text);
    val_buf.appendAssumeCapacity(0);
    const val_attr = mlir.Attribute.stringAttrGet(self.mlir_ctx, mlir.StringRef.from(val_buf.items));

    // Construct array type [N x i8]
    const arr_ty = mlir.LLVM.getLLVMArrayType(self.i8_ty, @intCast(text.len + 1));

    // Directly build the global Op
    const init_region = mlir.Region.create();
    var global_op = self.buildOp("llvm.mlir.global", EmitOpArgs{ .attributes = &.{
        self.named("sym_name", self.strAttr(name)),
        self.named("value", val_attr),
        self.named("global_type", mlir.Attribute.typeAttrGet(arr_ty)),
        self.named("linkage", mlir.LLVMAttributes.getLLVMLinkageAttr(self.mlir_ctx, mlir.LLVMLinkage.Internal)),
        self.named("constant", mlir.Attribute.unitAttrGet(self.mlir_ctx)),
        self.named("addr_space", mlir.Attribute.integerAttrGet(self.i32_ty, 0)),
    }, .regions = &.{init_region} });

    var body = self.module.getBody();
    body.appendOwnedOperation(global_op);
    _ = try self.str_pool.put(text, global_op);

    return self.addrOfFirstCharLen(&global_op, text.len + 1);
}

/// Return a pointer to an element inside `global_op` at `n_bytes` offset (first char).
fn addrOfFirstCharLen(self: *Codegen, global_op: *mlir.Operation, n_bytes: usize) !mlir.Operation {
    const name_attr = global_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
    const gsym = mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.Attribute.stringAttrGetValue(name_attr));

    const addr = self.appendOp("llvm.mlir.addressof", EmitOpArgs{
        .results = &.{self.llvm_ptr_ty},
        .attributes = &.{self.named("global_name", gsym)},
    });

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

/// Return true when `ty` is a signed integer in the SR type store.
pub inline fn isSignedInt(self: *Codegen, ty: types.TypeId) bool {
    const k = self.context.type_store.getKind(ty);
    return k == .I8 or k == .I16 or k == .I32 or k == .I64;
}

/// Lookup the source-level type recorded for TIR value `vid`.
inline fn srTypeOfValue(self: *Codegen, vid: tir.ValueId) types.TypeId {
    return self.val_types.get(vid) orelse types.TypeId.fromRaw(0);
}

/// Retrieve the integer constant value stored by `vid`, if any.
fn constIntOf(self: *Codegen, t: *tir.TIR, vid: tir.ValueId) ?i128 {
    if (self.def_instr.get(vid)) |iid| {
        if (t.kind(iid) == .ConstInt) return t.instrs.get(.ConstInt, iid).value;
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
inline fn isAggregateKind(kind: types.TypeKind) bool {
    return switch (kind) {
        .Struct, .Tuple, .Array, .Optional, .Union, .ErrorSet, .Error, .Closure => true,
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

    // Quick exit for non-aggregates
    if (!isAggregateKind(dst_kind) or !isAggregateKind(src_kind)) return null;

    // Direct dispatch based on destination kind
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

    // Extract -> Coerce -> Insert
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
    const count = dst_variants.len;

    if (count != src_variants.len) return null;

    // Stack optimization: Avoid heap alloc for common small error sets
    var buf_dst: [32]types.TypeStore.StructFieldArg = undefined;
    var buf_src: [32]types.TypeStore.StructFieldArg = undefined;

    const dst_union_fields = if (count <= 32) buf_dst[0..count] else try self.gpa.alloc(types.TypeStore.StructFieldArg, count);
    defer if (count > 32) self.gpa.free(dst_union_fields);

    const src_union_fields = if (count <= 32) buf_src[0..count] else try self.gpa.alloc(types.TypeStore.StructFieldArg, count);
    defer if (count > 32) self.gpa.free(src_union_fields);

    for (dst_variants, 0..) |dst_fid, i| {
        const src_fid = src_variants[i];
        const dst_f = self.context.type_store.Field.get(dst_fid);
        const src_f = self.context.type_store.Field.get(src_fid);
        if (!dst_f.name.eq(src_f.name)) return null;

        dst_union_fields[i] = .{ .name = dst_f.name, .ty = dst_f.ty };
        src_union_fields[i] = .{ .name = src_f.name, .ty = src_f.ty };
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
    return self.insertAt(result, payload, &.{1});
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
    for (dst_fields, 0..) |dst_fid, i| {
        const dst_f = self.context.type_store.Field.get(dst_fid);
        const src_f = self.context.type_store.Field.get(src_fields[i]);
        result = try self.copyAggregateElement(result, i, dst_f.ty, src_f.ty, src_val, elem_coercer);
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

    var result = self.undefOf(dst_ty);
    for (dst_elems, 0..) |dst_e, i| {
        result = try self.copyAggregateElement(result, i, dst_e, src_elems[i], src_val, elem_coercer);
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

    // Optimized path for Optional Pointers
    if (dst_ptr_opt or src_ptr_opt) {
        if (!(dst_ptr_opt and src_ptr_opt)) return null;
        const dst_payload_ty = try self.llvmTypeOf(dst_info.elem);
        return try elem_coercer(self, dst_info.elem, dst_payload_ty, src_val, src_info.elem);
    }

    // Standard Optional { bool, value }
    const dst_payload_ty = try self.llvmTypeOf(dst_info.elem);
    const src_payload_ty = try self.llvmTypeOf(src_info.elem);

    const tag = self.extractAt(src_val, self.i1_ty, &.{0});
    const src_payload = self.extractAt(src_val, src_payload_ty, &.{1});
    const coerced_payload = try elem_coercer(self, dst_info.elem, dst_payload_ty, src_payload, src_info.elem);

    var result = self.zeroOf(dst_ty);
    result = self.insertAt(result, tag, &.{0});
    return self.insertAt(result, coerced_payload, &.{1});
}

/// Copy union aggregate data by raw byte copy (size check required).
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

    var dst_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = ok_name, .ty = dst_info.value_ty },
        .{ .name = err_name, .ty = dst_info.error_ty },
    };
    var src_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = ok_name, .ty = src_info.value_ty },
        .{ .name = err_name, .ty = src_info.error_ty },
    };

    const dst_union_sr = self.context.type_store.mkUnion(&dst_fields);
    const src_union_sr = self.context.type_store.mkUnion(&src_fields);

    // Recursive copy of payload
    const src_union_ty = try self.llvmTypeOf(src_union_sr);
    const src_payload = self.extractAt(src_val, src_union_ty, &.{1});

    const dst_union_ty = try self.llvmTypeOf(dst_union_sr);
    const coerced_payload = try self.tryCopyAggregateValue(dst_union_sr, dst_union_ty, src_payload, src_union_sr, elem_coercer) orelse src_payload;

    const tag = self.extractAt(src_val, self.i32_ty, &.{0});
    var result = self.undefOf(dst_ty);
    result = self.insertAt(result, tag, &.{0});
    return self.insertAt(result, coerced_payload, &.{1});
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

    // Aggregates only logic
    const dst_kind = self.context.type_store.getKind(dst_sr);
    const src_kind = self.context.type_store.getKind(src_sr);
    if (!(isAggregateKind(dst_kind) and isAggregateKind(src_kind))) return null;

    const dst_layout = abi.abiSizeAlign(self, dst_sr);
    const src_layout = abi.abiSizeAlign(self, src_sr);

    // Spill source
    const src_ptr = self.spillAgg(src_val, src_val.getType(), @intCast(src_layout.alignment));

    // Allocate dest
    const dst_init = self.zeroOf(dst_ty);
    const dst_ptr = self.spillAgg(dst_init, dst_ty, @intCast(dst_layout.alignment));

    // Byte copy
    const copy_len = @min(dst_layout.size, src_layout.size);
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
    // 1. Identity Check (Fastest)
    if (v.getType().equal(want)) return v;

    const src_ty = v.getType();
    const is_ptr_v = mlir.LLVM.isLLVMPointerType(src_ty);
    const is_ptr_want = mlir.LLVM.isLLVMPointerType(want);

    // 2. Pointer Casts
    if (is_ptr_v and is_ptr_want) return self.emitUnaryValueOp("llvm.bitcast", v, want);
    if (is_ptr_v and want.isAInteger()) return self.emitUnaryValueOp("llvm.ptrtoint", v, want);
    if (src_ty.isAInteger() and is_ptr_want) return self.emitUnaryValueOp("llvm.inttoptr", v, want);

    // 3. Integer / Float Scalar Casts
    if (src_ty.isAInteger() and want.isAInteger()) {
        const fw = try cast.intOrFloatWidth(src_ty);
        const tw = try cast.intOrFloatWidth(want);
        if (fw == tw) return v;
        if (fw > tw) return self.emitUnaryValueOp("arith.trunci", v, want);
        const from_signed = self.isSignedInt(src_sr_ty);
        return self.emitUnaryValueOp(if (from_signed) "arith.extsi" else "arith.extui", v, want);
    }

    if (src_ty.isAFloat() and want.isAFloat()) {
        const fw = try cast.intOrFloatWidth(src_ty);
        const tw = try cast.intOrFloatWidth(want);
        if (fw == tw) return v;
        if (fw > tw) return self.emitUnaryValueOp("arith.truncf", v, want);
        return self.emitUnaryValueOp("arith.extf", v, want);
    }

    // Int <-> Float
    if (src_ty.isAInteger() and want.isAFloat()) {
        const from_signed = self.isSignedInt(src_sr_ty);
        return self.emitUnaryValueOp(if (from_signed) "arith.sitofp" else "arith.uitofp", v, want);
    }
    if (src_ty.isAFloat() and want.isAInteger()) {
        const to_signed = self.isSignedInt(dst_sr_ty);
        return self.emitUnaryValueOp(if (to_signed) "arith.fptosi" else "arith.fptoui", v, want);
    }

    // 4. Vector Casts
    if (src_ty.isAVector() and want.isAVector()) {
        const v_elem = src_ty.getShapedElementType();
        const want_elem = want.getShapedElementType();
        if (v_elem.isAFloat() and want_elem.isAInteger()) {
            const to_signed = self.isSignedInt(dst_sr_ty);
            return self.emitUnaryValueOp(if (to_signed) "arith.fptosi" else "arith.fptoui", v, want);
        }
        if (v_elem.isAInteger() and want_elem.isAFloat()) {
            const from_signed = self.isSignedInt(src_sr_ty);
            return self.emitUnaryValueOp(if (from_signed) "arith.sitofp" else "arith.uitofp", v, want);
        }
    }

    // 5. Aggregate Handling
    const zero_sr_ty = types.TypeId.fromRaw(0);
    if (!dst_sr_ty.eq(zero_sr_ty) and !src_sr_ty.eq(zero_sr_ty)) {
        const dst_kind = self.context.type_store.getKind(dst_sr_ty);
        const src_kind = self.context.type_store.getKind(src_sr_ty);

        // Special Case: ErrorSet -> Error
        if (dst_kind == .Error and src_kind == .ErrorSet) {
            return try self.errorSetToError(dst_sr_ty, want, src_sr_ty, v);
        }

        // Structural Copy (Recursion)
        if (try self.tryCopyAggregateValue(dst_sr_ty, want, v, src_sr_ty, coerceAggregateElementOnBranch)) |agg| {
            return agg;
        }

        // Spill Reinterpretation
        if (try self.reinterpretAggregateViaSpill(dst_sr_ty, want, v, src_sr_ty)) |agg| {
            return agg;
        }

        // Special Case: ErrorSet -> Ok Payload extraction
        if (src_kind == .ErrorSet and !isAggregateKind(dst_kind)) {
            const es = self.context.type_store.get(.ErrorSet, src_sr_ty);
            const ok_mlir = try self.llvmTypeOf(es.value_ty);
            if (want.equal(ok_mlir)) {
                return try self.loadOkFromErrorSet(src_sr_ty, v);
            }
        }
    }

    // 6. Last Resort Bitcast
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

    // Create union type locally to access layout
    const ok_name = self.context.type_store.strs.intern("Ok");
    const err_name = self.context.type_store.strs.intern("Err");
    var fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = ok_name, .ty = es.value_ty },
        .{ .name = err_name, .ty = es.error_ty },
    };

    const union_sr = self.context.type_store.mkUnion(&fields);
    const union_ty = try self.llvmTypeOf(union_sr);

    // Extract payload from ErrorSet wrapper
    const payload = self.extractAt(src_val, union_ty, &.{1});

    // Spill union to stack to access it via pointer for GEP
    // The error payload is at offset 0 of the union storage conceptually in memory for this specialized cast
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
/// Load the `Ok` payload from an `ErrorSet` when the tag indicates success.
fn loadOkFromErrorSet(
    self: *Codegen,
    src_errset_sr: types.TypeId,
    src_val: mlir.Value,
) !mlir.Value {
    const es = self.context.type_store.get(.ErrorSet, src_errset_sr);

    // Create the union type { Ok: T, Err: E } to handle the memory layout bitcast
    const union_sr = blk: {
        const ok_name = self.context.type_store.strs.intern("Ok");
        const err_name = self.context.type_store.strs.intern("Err");
        var fields = [_]types.TypeStore.StructFieldArg{
            .{ .name = ok_name, .ty = es.value_ty },
            .{ .name = err_name, .ty = es.error_ty },
        };
        break :blk self.context.type_store.mkUnion(&fields);
    };

    // Extract union payload (field 1) from { tag, union }
    const union_ty = try self.llvmTypeOf(union_sr);
    const payload = self.extractAt(src_val, union_ty, &.{1});

    // Spill union to stack to perform pointer cast (Gep) -> Load typed value
    const ok_mlir = try self.llvmTypeOf(es.value_ty);
    const alignment = abi.abiSizeAlign(self, es.value_ty).alignment;
    const union_ptr = self.spillAgg(payload, union_ty, @intCast(alignment));

    // GEP to cast pointer type (offset 0)
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

// --- Boolean Ops ---

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
    const true_const = self.emitOp("llvm.mlir.constant", EmitOpArgs{
        .results = &.{self.i1_ty},
        .attributes = &.{self.named("value", mlir.Attribute.integerAttrGet(self.i1_ty, 1))},
    });
    return self.emitBinaryValueOp("arith.xori", a, true_const, self.i1_ty, null);
}

// --- Assert Call ---

/// Emit a runtime `assert` call that aborts when `cond` is false.
fn emitAssertCall(self: *Codegen, cond: mlir.Value) void {
    const assert_fn_type = mlir.LLVM.getLLVMFunctionType(self.i1_ty, &.{self.i1_ty}, false);
    const assert_ref = mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.Attribute.stringAttrGetValue(self.strAttr("assert")));

    const op = self.buildOp("func.call", EmitOpArgs{
        .operands = &.{cond},
        .attributes = &.{
            self.named("callee", assert_ref),
            self.named("sym_visibility", self.strAttr("private")),
            self.named("function_type", mlir.Attribute.typeAttrGet(assert_fn_type)),
        },
    });
    _ = appendIfHasResult(self, op);
}

// --- Complex Helpers ---

pub fn complexRe(self: *Codegen, v: mlir.Value, elem_ty: mlir.Type) mlir.Value {
    return self.emitUnaryValueOp("complex.re", v, elem_ty);
}

pub fn complexIm(self: *Codegen, v: mlir.Value, elem_ty: mlir.Type) mlir.Value {
    return self.emitUnaryValueOp("complex.im", v, elem_ty);
}

pub fn complexFromParts(self: *Codegen, re: mlir.Value, im: mlir.Value, complex_ty: mlir.Type) mlir.Value {
    return self.emitOp("complex.create", EmitOpArgs{
        .operands = &.{ re, im },
        .results = &.{complex_ty},
    });
}

// --- Type Lowering ---

/// Map an SR type id to the corresponding MLIR type used during lowering.
pub fn llvmTypeOf(self: *Codegen, ty: types.TypeId) !mlir.Type {
    const kind = self.context.type_store.getKind(ty);
    switch (kind) {
        .Void, .Noreturn => return self.void_ty,
        .Bool => return self.i1_ty,

        // Group integer types
        .I8, .U8 => return mlir.Type.getSignlessIntegerType(self.mlir_ctx, 8),
        .I16, .U16 => return mlir.Type.getSignlessIntegerType(self.mlir_ctx, 16),
        .I32, .U32 => return mlir.Type.getSignlessIntegerType(self.mlir_ctx, 32),
        .I64, .U64, .Usize => return mlir.Type.getSignlessIntegerType(self.mlir_ctx, 64), // Usize assumes 64-bit

        .F32 => return self.f32_ty,
        .F64 => return self.f64_ty,

        .Function, .Ptr, .MlirModule, .MlirAttribute, .Code => return self.llvm_ptr_ty,
        .Closure => {
            const fields = [_]mlir.Type{ self.llvm_ptr_ty, self.llvm_ptr_ty };
            return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
        },

        .MlirType => {
            const mt = self.context.type_store.get(.MlirType, ty);
            const src = self.context.type_store.strs.get(mt.src);
            const parsed = mlir.Type.parseGet(self.mlir_ctx, mlir.StringRef.from(src));
            return if (parsed.isNull()) self.llvm_ptr_ty else parsed;
        },

        .String, .Slice => {
            // { ptr, len }
            const fields = [_]mlir.Type{ self.llvm_ptr_ty, self.i64_ty };
            return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
        },

        .Array => {
            const arr_ty = self.context.type_store.get(.Array, ty);
            const elem_mlir = try self.llvmTypeOf(arr_ty.elem);
            return mlir.LLVM.getLLVMArrayType(elem_mlir, @intCast(arr_ty.len));
        },

        .DynArray => {
            const dyn_ty = self.context.type_store.get(.DynArray, ty);
            // Construct pointer to element: *T
            const ptr_sr = self.context.type_store.mkPtr(dyn_ty.elem, false);
            const ptr_mlir = try self.llvmTypeOf(ptr_sr);
            // { ptr, len, cap }
            const fields = [_]mlir.Type{ ptr_mlir, self.i64_ty, self.i64_ty };
            return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
        },

        .Map => {
            const map_ty = self.context.type_store.get(.Map, ty);
            // Entry { key, value }
            const entry_sr = self.context.type_store.mkStruct(&.{
                .{ .name = self.context.type_store.strs.intern("key"), .ty = map_ty.key },
                .{ .name = self.context.type_store.strs.intern("value"), .ty = map_ty.value },
            }, 0);

            // Ptr to Entry (*Entry)
            const entry_ptr_mlir = try self.llvmTypeOf(self.context.type_store.mkPtr(entry_sr, false));

            // DynArray<Entry> struct: { *Entry, len, cap }
            const dyn_fields = [_]mlir.Type{ entry_ptr_mlir, self.i64_ty, self.i64_ty };
            const dyn_mlir = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &dyn_fields, false);

            // Map struct: { len, entries_dynarray }
            const map_fields = [_]mlir.Type{ self.i64_ty, dyn_mlir };
            return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &map_fields, false);
        },

        .Simd => {
            const simd_ty = self.context.type_store.get(.Simd, ty);
            const elem_mlir = try self.llvmTypeOf(simd_ty.elem);
            const shape = [_]i64{@intCast(simd_ty.lanes)};
            return mlir.Type.getVectorType(1, &shape, elem_mlir);
        },

        .Tensor => {
            const ten = self.context.type_store.get(.Tensor, ty);
            const rank: usize = @intCast(ten.rank);
            var shape_buf: [types.max_tensor_rank]i64 = undefined;
            const shape_slice = if (rank == 0) &[_]i64{} else blk: {
                for (0..rank) |i| shape_buf[i] = @intCast(ten.dims[i]);
                break :blk shape_buf[0..rank];
            };
            return mlir.Type.getRankedTensorType(@intCast(rank), shape_slice, try self.llvmTypeOf(ten.elem), mlir.Attribute.getNull());
        },

        .Complex => return mlir.Type.getComplexType(try self.llvmTypeOf(self.context.type_store.get(.Complex, ty).elem)),

        .Optional => {
            if (self.context.type_store.isOptionalPointer(ty)) {
                return self.llvmTypeOf(self.context.type_store.get(.Optional, ty).elem);
            }
            const opt_ty = self.context.type_store.get(.Optional, ty);
            if (self.context.type_store.getKind(opt_ty.elem) == .Void) {
                const fields = [_]mlir.Type{self.i1_ty};
                return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
            }
            const fields = [_]mlir.Type{ self.i1_ty, try self.llvmTypeOf(opt_ty.elem) };
            return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
        },

        .Future => {
            const fut_ty = self.context.type_store.get(.Future, ty);
            if (self.context.type_store.getKind(fut_ty.elem) == .Void) {
                return mlir.Type.parseGet(self.mlir_ctx, mlir.StringRef.from("!async.token"));
            }
            // Construct "!async.value<T>"
            const inner = try self.llvmTypeOf(fut_ty.elem);
            var list = ArrayList(u8).init(self.gpa);
            defer list.deinit();
            try list.appendSlice("!async.value<");
            var had_error = false;
            var sink = PrintBuffer{ .list = &list, .had_error = &had_error };
            inner.print(printCallback, &sink);
            if (had_error) return error.OutOfMemory;
            try list.appendSlice(">");
            return mlir.Type.parseGet(self.mlir_ctx, mlir.StringRef.from(list.items));
        },

        .Tuple => {
            const elems = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, ty).elems);
            // Stack alloc optimization
            var buf: [64]mlir.Type = undefined;
            const fields = if (elems.len <= 64) buf[0..elems.len] else try self.gpa.alloc(mlir.Type, elems.len);
            defer if (elems.len > 64) self.gpa.free(fields);

            for (elems, 0..) |eid, i| fields[i] = try self.llvmTypeOf(eid);
            return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, fields, false);
        },

        .Struct => {
            const st_fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, ty).fields);
            // Stack alloc optimization
            var buf: [64]mlir.Type = undefined;
            const fields = if (st_fields.len <= 64) buf[0..st_fields.len] else try self.gpa.alloc(mlir.Type, st_fields.len);
            defer if (st_fields.len > 64) self.gpa.free(fields);

            for (st_fields, 0..) |fid, i| fields[i] = try self.llvmTypeOf(self.context.type_store.Field.get(fid).ty);
            return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, fields, false);
        },

        .Enum => return self.i32_ty, // TODO: use backing integer type if specified

        .Union => {
            const un_ty = self.context.type_store.get(.Union, ty);
            if (un_ty.fields.len == 0) {
                return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{}, false);
            }
            var max_size: usize = 0;
            var max_align: usize = 1;
            const fields = self.context.type_store.field_pool.slice(un_ty.fields);
            for (fields) |f| {
                const sa = abi.abiSizeAlign(self, self.context.type_store.Field.get(f).ty);
                if (sa.size > max_size) max_size = sa.size;
                if (sa.alignment > max_align) max_align = sa.alignment;
            }
            const padded = std.mem.alignForward(usize, max_size, max_align);
            return mlir.LLVM.getLLVMArrayType(self.i8_ty, @intCast(padded));
        },

        // Tagged Union Types (ErrorSet, Error, Variant) -> { i32, UnionPayload }
        .ErrorSet => {
            const es = self.context.type_store.get(.ErrorSet, ty);
            const ok_name = self.context.type_store.strs.intern("Ok");
            const err_name = self.context.type_store.strs.intern("Err");
            var fields = [_]types.TypeStore.StructFieldArg{
                .{ .name = ok_name, .ty = es.value_ty },
                .{ .name = err_name, .ty = es.error_ty },
            };
            return self.emitTaggedUnion(&fields);
        },

        .Error => {
            const fields_idx = self.context.type_store.get(.Error, ty).variants;
            const variants = self.context.type_store.field_pool.slice(fields_idx);
            if (variants.len == 0) {
                const parts = [_]mlir.Type{self.i32_ty};
                return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &parts, false);
            }
            return self.emitTaggedUnionFromIndices(variants);
        },

        .Variant => {
            const fields_idx = self.context.type_store.get(.Variant, ty).variants;
            return self.emitTaggedUnionFromIndices(self.context.type_store.field_pool.slice(fields_idx));
        },

        .TypeType => return self.i64_ty,
        .Ast => return self.llvm_ptr_ty,
        .TypeError => return error.CompilationFailed,
        .Any => {
            self.loc.getAttribute().dump();
            std.debug.panic("CodeGen: Unresolved 'Any' type encountered.\n", .{});
        },
        else => std.debug.panic("CodeGen: Unhandled type kind: {}\n", .{kind}),
    }
}

// Helper to create { i32, Union } from field indices
fn emitTaggedUnionFromIndices(self: *Codegen, fields: []const types.FieldId) !mlir.Type {
    // Stack optimization for gathering fields
    var buf: [32]types.TypeStore.StructFieldArg = undefined;
    const payload_args = if (fields.len <= 32) buf[0..fields.len] else try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
    defer if (fields.len > 32) self.gpa.free(payload_args);

    for (fields, 0..) |f, i| {
        const field = self.context.type_store.Field.get(f);
        payload_args[i] = .{ .name = field.name, .ty = field.ty };
    }
    return self.emitTaggedUnion(payload_args);
}

// Lowers a list of fields into { i32, Union }
fn emitTaggedUnion(self: *Codegen, fields: []const types.TypeStore.StructFieldArg) anyerror!mlir.Type {
    const union_sr = self.context.type_store.mkUnion(fields);
    const union_mlir = try self.llvmTypeOf(union_sr);
    const parts = [_]mlir.Type{ self.i32_ty, union_mlir };
    return mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &parts, false);
}
