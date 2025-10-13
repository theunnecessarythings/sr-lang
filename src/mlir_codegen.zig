const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const compile = @import("compile.zig");
const types = @import("types.zig");
const abi = @import("abi.zig");
const cst = @import("cst.zig");

const Allocator = std.mem.Allocator;
const ArrayList = std.array_list.Managed;

pub var enable_debug_info: bool = true;

const LocKey = struct {
    store: usize,
    raw: u32,
};

const LineInfo = struct {
    line: usize,
    col: usize,
};

const DebugFileInfo = struct {
    file_attr: mlir.Attribute,
    compile_unit_attr: mlir.Attribute,
    file_text: []const u8,
    compile_unit_text: []const u8,
};

const DebugSubprogramInfo = struct {
    attr: mlir.Attribute,
    file_id: u32,
    line: u32,
    scope_line: u32,
    loc: tir.OptLocId,
};

fn computeLineCol(src: []const u8, index: usize) LineInfo {
    var i: usize = 0;
    var line: usize = 0;
    var last_nl: usize = 0;
    const limit = if (index > src.len) src.len else index;
    while (i < limit) : (i += 1) {
        if (src[i] == '\n') {
            line += 1;
            last_nl = i + 1;
        }
    }
    const col = if (limit >= last_nl) limit - last_nl else 0;
    return .{ .line = line, .col = col };
}

pub const MlirCodegen = struct {
    gpa: Allocator,
    context: *compile.Context,
    mlir_ctx: mlir.Context,
    loc: mlir.Location,
    module: mlir.Module,

    active_loc_store: ?*const cst.LocStore = null,
    loc_cache: std.AutoHashMap(LocKey, mlir.Location),
    file_cache: std.AutoHashMap(u32, []const u8),
    di_files: std.AutoHashMap(u32, DebugFileInfo),
    di_subprograms: std.AutoHashMap(tir.FuncId, DebugSubprogramInfo),

    metadata_ty: mlir.Type,
    di_null_type_attr: mlir.Attribute,
    di_empty_expr_attr: mlir.Attribute,
    next_di_id: usize = 0,

    // common LLVM/arith types (opaque pointers on master)
    void_ty: mlir.Type,
    i1_ty: mlir.Type,
    i8_ty: mlir.Type,
    i32_ty: mlir.Type,
    i64_ty: mlir.Type,
    f32_ty: mlir.Type,
    f64_ty: mlir.Type,
    llvm_ptr_ty: mlir.Type, // !llvm.ptr (opaque)

    // per-module caches
    func_syms: std.StringHashMap(FuncInfo),
    str_pool: std.StringHashMap(mlir.Operation), // text -> llvm.mlir.global op

    // per-function state (reset each function)
    cur_region: ?mlir.Region = null,
    cur_block: ?mlir.Block = null,
    block_map: std.AutoHashMap(tir.BlockId, mlir.Block),
    value_map: std.AutoHashMap(tir.ValueId, mlir.Value),

    // NEW: for correctness decisions (signedness, etc.)
    val_types: std.AutoHashMap(tir.ValueId, types.TypeId), // SR types of SSA values
    def_instr: std.AutoHashMap(tir.ValueId, tir.InstrId), // SSA def site
    inline_mlir_counter: u32 = 0,

    pub const FuncInfo = struct {
        op: mlir.Operation,
        is_variadic: bool,
        n_formals: usize, // MLIR visible formals after dropping trailing Any
        ret_type: mlir.Type,
        dbg_subprogram: ?mlir.Attribute = null,
    };

    // ----------------------------------------------------------------
    // Op builder (unchanged)
    // ----------------------------------------------------------------
    const OpBuilder = struct {
        operands: ?[]const mlir.Value = null,
        results: ?[]const mlir.Type = null,
        attributes: ?[]const mlir.NamedAttribute = null,
        regions: ?[]const mlir.Region = null,
        successors: ?[]const mlir.Block = null,
        name: []const u8,
        loc: mlir.Location,

        pub fn init(name: []const u8, loc: mlir.Location) OpBuilder {
            return .{ .name = name, .loc = loc };
        }
        pub fn builder(self: *const OpBuilder) *OpBuilder {
            return @constCast(self);
        }
        pub fn add_operands(self: *OpBuilder, ops: []const mlir.Value) *OpBuilder {
            self.operands = ops;
            return self;
        }
        pub fn add_results(self: *OpBuilder, tys: []const mlir.Type) *OpBuilder {
            self.results = tys;
            return self;
        }
        pub fn add_attributes(self: *OpBuilder, attrs: []const mlir.NamedAttribute) *OpBuilder {
            self.attributes = attrs;
            return self;
        }
        pub fn add_regions(self: *OpBuilder, regs: []const mlir.Region) *OpBuilder {
            self.regions = regs;
            return self;
        }
        pub fn add_successors(self: *OpBuilder, succs: []const mlir.Block) *OpBuilder {
            self.successors = succs;
            return self;
        }
        pub fn build(self: *OpBuilder) mlir.Operation {
            var st = mlir.OperationState.get(mlir.StringRef.from(self.name), self.loc);
            if (self.results) |r| st.addResults(r);
            if (self.operands) |o| st.addOperands(o);
            if (self.attributes) |a| st.addAttributes(a);
            if (self.regions) |rg| st.addOwnedRegions(rg);
            if (self.successors) |s| st.addSuccessors(s);
            return mlir.Operation.create(&st);
        }
    };

    const PrintBuffer = struct {
        list: *std.ArrayList(u8),
        allocator: Allocator,
    };

    fn printCallback(s: mlir.c.MlirStringRef, user_data: ?*anyopaque) callconv(.c) void {
        const buf: *PrintBuffer = @ptrCast(@alignCast(user_data.?));
        buf.list.appendSlice(buf.allocator, s.data[0..s.length]) catch {};
    }

    fn ownedAttributeText(self: *MlirCodegen, attr: mlir.Attribute) ![]u8 {
        var list: std.ArrayList(u8) = .empty;
        errdefer list.deinit(self.gpa);
        var sink = PrintBuffer{ .list = &list, .allocator = self.gpa };
        attr.print(printCallback, &sink);
        return list.toOwnedSlice(self.gpa);
    }

    // ----------------------------------------------------------------
    // Init / Deinit
    // ----------------------------------------------------------------
    pub fn init(gpa: Allocator, context: *compile.Context, ctx: mlir.Context) MlirCodegen {
        const loc = mlir.Location.unknownGet(ctx);
        const module = mlir.Module.createEmpty(loc);
        const void_ty = mlir.Type{ .handle = mlir.c.mlirLLVMVoidTypeGet(ctx.handle) };
        return .{
            .gpa = gpa,
            .context = context,
            .mlir_ctx = ctx,
            .loc = loc,
            .module = module,
            .active_loc_store = null,
            .loc_cache = std.AutoHashMap(LocKey, mlir.Location).init(gpa),
            .file_cache = std.AutoHashMap(u32, []const u8).init(gpa),
            .di_files = std.AutoHashMap(u32, DebugFileInfo).init(gpa),
            .di_subprograms = std.AutoHashMap(tir.FuncId, DebugSubprogramInfo).init(gpa),
            .metadata_ty = mlir.Type.getNull(),
            .di_null_type_attr = mlir.Attribute.empty(),
            .di_empty_expr_attr = mlir.Attribute.empty(),
            .next_di_id = 0,
            .void_ty = void_ty,
            .i1_ty = mlir.Type.getSignlessIntegerType(ctx, 1),
            .i8_ty = mlir.Type.getSignlessIntegerType(ctx, 8),
            .i32_ty = mlir.Type.getSignlessIntegerType(ctx, 32),
            .i64_ty = mlir.Type.getSignlessIntegerType(ctx, 64),
            .f32_ty = mlir.Type.getFloat32Type(ctx),
            .f64_ty = mlir.Type.getFloat64Type(ctx),
            .llvm_ptr_ty = mlir.LLVM.getPointerType(ctx, 0),
            .func_syms = std.StringHashMap(FuncInfo).init(gpa),
            .str_pool = std.StringHashMap(mlir.Operation).init(gpa),
            .block_map = std.AutoHashMap(tir.BlockId, mlir.Block).init(gpa),
            .value_map = std.AutoHashMap(tir.ValueId, mlir.Value).init(gpa),
            .val_types = std.AutoHashMap(tir.ValueId, types.TypeId).init(gpa),
            .def_instr = std.AutoHashMap(tir.ValueId, tir.InstrId).init(gpa),
        };
    }

    pub fn deinit(self: *MlirCodegen) void {
        self.resetDebugCaches();
        self.di_subprograms.deinit();
        self.di_files.deinit();
        self.func_syms.deinit();
        self.str_pool.deinit();
        self.block_map.deinit();
        self.value_map.deinit();
        self.val_types.deinit();
        self.def_instr.deinit();
        var fit = self.file_cache.valueIterator();
        while (fit.next()) |src| {
            self.context.source_manager.gpa.free(@constCast(src.*));
        }
        self.file_cache.deinit();
        self.loc_cache.deinit();
        self.module.destroy();
    }

    // ----------------------------------------------------------------
    // Public entry
    // ----------------------------------------------------------------
    pub fn emitModule(
        self: *MlirCodegen,
        t: *const tir.TIR,
        context: *compile.Context,
        locs: ?*const cst.LocStore,
    ) !mlir.Module {
        const prev_loc = self.loc;
        defer self.loc = prev_loc;

        self.active_loc_store = locs;
        defer self.active_loc_store = null;

        self.loc_cache.clearRetainingCapacity();
        self.resetDebugCaches();
        self.attachTargetInfo();
        try self.emitExternDecls(t, &context.type_store);

        const func_ids = t.funcs.func_pool.data.items;
        for (func_ids) |fid| try self.emitFunctionHeader(fid, t, &context.type_store);
        for (func_ids) |fid| {
            const row = t.funcs.Function.get(fid);
            const blocks = t.funcs.block_pool.slice(row.blocks);
            if (blocks.len > 0) try self.emitFunctionBody(fid, t, &context.type_store);
        }
        return self.module;
    }

    fn mlirLocation(self: *MlirCodegen, opt_loc: tir.OptLocId) mlir.Location {
        if (opt_loc.isNone())
            // Preserve the current ambient location so callers can deliberately
            // keep emitting with whatever scope was active.
            return self.loc;
        const locs = self.active_loc_store orelse return self.loc;
        const loc_id = opt_loc.unwrap();
        const key = LocKey{ .store = @intFromPtr(locs), .raw = loc_id.toRaw() };
        if (self.loc_cache.get(key)) |cached| return cached;

        const loc_record = locs.get(loc_id);
        const src = self.getFileSource(loc_record.file_id) catch {
            return self.loc;
        };
        const lc = computeLineCol(src, loc_record.start);
        const filename = self.context.source_manager.get(loc_record.file_id) orelse "unknown";
        const mlir_loc = mlir.Location.fileLineColGet(
            self.mlir_ctx,
            mlir.StringRef.from(filename),
            @as(u32, @intCast(lc.line + 1)),
            @as(u32, @intCast(lc.col + 1)),
        );
        _ = self.loc_cache.put(key, mlir_loc) catch {};
        return mlir_loc;
    }

    fn pushLocation(self: *MlirCodegen, opt_loc: tir.OptLocId) mlir.Location {
        const prev = self.loc;
        self.loc = self.mlirLocation(opt_loc);
        return prev;
    }

    fn resetDebugCaches(self: *MlirCodegen) void {
        var file_it = self.di_files.valueIterator();
        while (file_it.next()) |info| {
            self.gpa.free(@constCast(info.file_text));
            self.gpa.free(@constCast(info.compile_unit_text));
        }
        self.di_files.clearRetainingCapacity();
        self.di_subprograms.clearRetainingCapacity();
        self.metadata_ty = mlir.Type.getNull();
        self.di_null_type_attr = mlir.Attribute.empty();
        self.di_empty_expr_attr = mlir.Attribute.empty();
        self.next_di_id = 0;
    }

    fn instrOptLoc(self: *MlirCodegen, t: *const tir.TIR, ins_id: tir.InstrId) tir.OptLocId {
        _ = self;
        const kind = t.instrs.index.kinds.items[ins_id.toRaw()];
        return switch (kind) {
            .ConstInt => t.instrs.get(.ConstInt, ins_id).loc,
            .ConstFloat => t.instrs.get(.ConstFloat, ins_id).loc,
            .ConstBool => t.instrs.get(.ConstBool, ins_id).loc,
            .ConstString => t.instrs.get(.ConstString, ins_id).loc,
            .ConstNull => t.instrs.get(.ConstNull, ins_id).loc,
            .ConstUndef => t.instrs.get(.ConstUndef, ins_id).loc,
            .RangeMake => t.instrs.get(.RangeMake, ins_id).loc,
            .BinWrapAdd => t.instrs.get(.BinWrapAdd, ins_id).loc,
            .BinWrapSub => t.instrs.get(.BinWrapSub, ins_id).loc,
            .BinWrapMul => t.instrs.get(.BinWrapMul, ins_id).loc,
            .BinSatAdd => t.instrs.get(.BinSatAdd, ins_id).loc,
            .BinSatSub => t.instrs.get(.BinSatSub, ins_id).loc,
            .BinSatMul => t.instrs.get(.BinSatMul, ins_id).loc,
            .BinSatShl => t.instrs.get(.BinSatShl, ins_id).loc,
            .Add => t.instrs.get(.Add, ins_id).loc,
            .Sub => t.instrs.get(.Sub, ins_id).loc,
            .Mul => t.instrs.get(.Mul, ins_id).loc,
            .Div => t.instrs.get(.Div, ins_id).loc,
            .Mod => t.instrs.get(.Mod, ins_id).loc,
            .Shl => t.instrs.get(.Shl, ins_id).loc,
            .Shr => t.instrs.get(.Shr, ins_id).loc,
            .BitAnd => t.instrs.get(.BitAnd, ins_id).loc,
            .BitOr => t.instrs.get(.BitOr, ins_id).loc,
            .BitXor => t.instrs.get(.BitXor, ins_id).loc,
            .CmpEq => t.instrs.get(.CmpEq, ins_id).loc,
            .CmpNe => t.instrs.get(.CmpNe, ins_id).loc,
            .CmpLt => t.instrs.get(.CmpLt, ins_id).loc,
            .CmpLe => t.instrs.get(.CmpLe, ins_id).loc,
            .CmpGt => t.instrs.get(.CmpGt, ins_id).loc,
            .CmpGe => t.instrs.get(.CmpGe, ins_id).loc,
            .LogicalAnd => t.instrs.get(.LogicalAnd, ins_id).loc,
            .LogicalOr => t.instrs.get(.LogicalOr, ins_id).loc,
            .LogicalNot => t.instrs.get(.LogicalNot, ins_id).loc,
            .CastNormal => t.instrs.get(.CastNormal, ins_id).loc,
            .CastBit => t.instrs.get(.CastBit, ins_id).loc,
            .CastSaturate => t.instrs.get(.CastSaturate, ins_id).loc,
            .CastWrap => t.instrs.get(.CastWrap, ins_id).loc,
            .CastChecked => t.instrs.get(.CastChecked, ins_id).loc,
            .Alloca => t.instrs.get(.Alloca, ins_id).loc,
            .Load => t.instrs.get(.Load, ins_id).loc,
            .Store => t.instrs.get(.Store, ins_id).loc,
            .Gep => t.instrs.get(.Gep, ins_id).loc,
            .GlobalAddr => t.instrs.get(.GlobalAddr, ins_id).loc,
            .ComplexMake => t.instrs.get(.ComplexMake, ins_id).loc,
            .TupleMake => t.instrs.get(.TupleMake, ins_id).loc,
            .ArrayMake => t.instrs.get(.ArrayMake, ins_id).loc,
            .StructMake => t.instrs.get(.StructMake, ins_id).loc,
            .ExtractElem => t.instrs.get(.ExtractElem, ins_id).loc,
            .InsertElem => t.instrs.get(.InsertElem, ins_id).loc,
            .ExtractField => t.instrs.get(.ExtractField, ins_id).loc,
            .InsertField => t.instrs.get(.InsertField, ins_id).loc,
            .Index => t.instrs.get(.Index, ins_id).loc,
            .AddressOf => t.instrs.get(.AddressOf, ins_id).loc,
            .Select => t.instrs.get(.Select, ins_id).loc,
            .Call => t.instrs.get(.Call, ins_id).loc,
            .IndirectCall => t.instrs.get(.IndirectCall, ins_id).loc,
            .VariantMake => t.instrs.get(.VariantMake, ins_id).loc,
            .VariantTag => t.instrs.get(.VariantTag, ins_id).loc,
            .VariantPayloadPtr => t.instrs.get(.VariantPayloadPtr, ins_id).loc,
            .UnionMake => t.instrs.get(.UnionMake, ins_id).loc,
            .UnionField => t.instrs.get(.UnionField, ins_id).loc,
            .UnionFieldPtr => t.instrs.get(.UnionFieldPtr, ins_id).loc,
            .MlirBlock => t.instrs.get(.MlirBlock, ins_id).loc,
        };
    }

    fn termOptLoc(self: *MlirCodegen, t: *const tir.TIR, term_id: tir.TermId) tir.OptLocId {
        _ = self;
        const kind = t.terms.index.kinds.items[term_id.toRaw()];
        return switch (kind) {
            .Return => t.terms.get(.Return, term_id).loc,
            .Br => t.terms.get(.Br, term_id).loc,
            .CondBr => t.terms.get(.CondBr, term_id).loc,
            .SwitchInt => t.terms.get(.SwitchInt, term_id).loc,
            .Unreachable => t.terms.get(.Unreachable, term_id).loc,
        };
    }

    fn blockOptLoc(self: *MlirCodegen, block_id: tir.BlockId, t: *const tir.TIR) tir.OptLocId {
        _ = self;
        const block = t.funcs.Block.get(block_id);
        const instrs = t.instrs.instr_pool.slice(block.instrs);
        for (instrs) |ins_id| {
            const loc = self.instrOptLoc(t, ins_id);
            if (!loc.isNone()) return loc;
        }
        return self.termOptLoc(t, block.term);
    }

    fn functionOptLoc(self: *MlirCodegen, f_id: tir.FuncId, t: *const tir.TIR) tir.OptLocId {
        _ = self;
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

    fn getFileSource(self: *MlirCodegen, file_id: u32) ![]const u8 {
        if (self.file_cache.get(file_id)) |buf| return buf;
        const data = try self.context.source_manager.read(file_id);
        errdefer self.context.source_manager.gpa.free(@constCast(data));
        try self.file_cache.put(file_id, data);
        return data;
    }

    fn nextDistinctId(self: *MlirCodegen) usize {
        const id = self.next_di_id;
        self.next_di_id += 1;
        return id;
    }

    fn ensureDebugFile(self: *MlirCodegen, file_id: u32) !*DebugFileInfo {
        if (self.di_files.getPtr(file_id)) |info| return info;

        const path = self.context.source_manager.get(file_id) orelse "unknown";
        const base = std.fs.path.basename(path);
        const dir = std.fs.path.dirname(path) orelse ".";

        const base_attr = self.strAttr(base);
        const dir_attr = self.strAttr(dir);
        const file_attr = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, base_attr, dir_attr);
        if (file_attr.isNull()) return error.DebugAttrParseFailed;

        const file_text_owned = try self.ownedAttributeText(file_attr);
        errdefer self.gpa.free(file_text_owned);

        const producer_attr = self.strAttr("sr-lang");
        const producer_text = try self.ownedAttributeText(producer_attr);
        defer self.gpa.free(producer_text);

        const cu_text = try std.fmt.allocPrint(
            self.gpa,
            "#llvm.di_compile_unit<id = distinct[{d}], source_language = DW_LANG_C, file = {s}, producer = {s}, is_optimized = false, runtime_version = 0, emission_kind = Full>",
            .{ self.nextDistinctId(), file_text_owned, producer_text },
        );
        errdefer self.gpa.free(cu_text);

        const cu_attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(cu_text));
        if (cu_attr.isNull()) return error.DebugAttrParseFailed;

        try self.di_files.put(file_id, .{
            .file_attr = file_attr,
            .compile_unit_attr = cu_attr,
            .file_text = file_text_owned,
            .compile_unit_text = cu_text,
        });
        return self.di_files.getPtr(file_id).?;
    }

    fn ensureDebugSubprogram(
        self: *MlirCodegen,
        f_id: tir.FuncId,
        func_name: []const u8,
        line: u32,
        file_id: u32,
        loc: tir.OptLocId,
    ) !*DebugSubprogramInfo {
        if (self.di_subprograms.getPtr(f_id)) |info| return info;

        const file_info = try self.ensureDebugFile(file_id);
        const func_name_attr = self.strAttr(func_name);
        const func_name_text = try self.ownedAttributeText(func_name_attr);
        defer self.gpa.free(func_name_text);

        const sp_text = try std.fmt.allocPrint(
            self.gpa,
            "#llvm.di_subprogram<id = distinct[{d}], compile_unit = {s}, scope = {s}, name = {s}, linkageName = {s}, file = {s}, line = {d}, scopeLine = {d}, type = #llvm.di_subroutine_type<types = !llvm.array<[]>>, spFlags = DIFlagDefinition>",
            .{
                self.nextDistinctId(),
                file_info.compile_unit_text,
                file_info.file_text,
                func_name_text,
                func_name_text,
                file_info.file_text,
                line,
                line,
            },
        );
        defer self.gpa.free(sp_text);

        const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(sp_text));
        if (attr.isNull()) return error.DebugAttrParseFailed;

        try self.di_subprograms.put(f_id, .{
            .attr = attr,
            .file_id = file_id,
            .line = line,
            .scope_line = line,
            .loc = loc,
        });
        return self.di_subprograms.getPtr(f_id).?;
    }

    fn attachTargetInfo(self: *MlirCodegen) void {
        const triple = self.strAttr("x86_64-unknown-linux-gnu");
        const dl = self.strAttr("e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128");
        var mod_op = self.module.getOperation();
        mod_op.setDiscardableAttributeByName(mlir.StringRef.from("llvm.target_triple"), triple);
        mod_op.setDiscardableAttributeByName(mlir.StringRef.from("llvm.data_layout"), dl);
    }

    fn ensureMetadataType(self: *MlirCodegen) !mlir.Type {
        if (!self.metadata_ty.isNull()) return self.metadata_ty;
        const ty = mlir.Type.parseGet(self.mlir_ctx, mlir.StringRef.from("!llvm.metadata"));
        if (ty.isNull()) return error.DebugAttrParseFailed;
        self.metadata_ty = ty;
        return ty;
    }

    fn ensureDINullTypeAttr(self: *MlirCodegen) !mlir.Attribute {
        if (!self.di_null_type_attr.isNull()) return self.di_null_type_attr;
        const attr = mlir.LLVMAttributes.getLLVMDINullTypeAttr(self.mlir_ctx);
        if (attr.isNull()) return error.DebugAttrParseFailed;
        self.di_null_type_attr = attr;
        return attr;
    }

    fn ensureEmptyDIExpression(self: *MlirCodegen) !mlir.Attribute {
        if (!self.di_empty_expr_attr.isNull()) return self.di_empty_expr_attr;
        const attr = mlir.LLVMAttributes.getLLVMDIExpressionAttr(self.mlir_ctx, &[_]mlir.Attribute{});
        if (attr.isNull()) return error.DebugAttrParseFailed;
        self.di_empty_expr_attr = attr;
        return attr;
    }

    fn metadataConstant(self: *MlirCodegen, attr: mlir.Attribute, ty: mlir.Type) mlir.Value {
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{ty})
            .add_attributes(&.{self.named("value", attr)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn emitParameterDebugInfo(
        self: *MlirCodegen,
        f_id: tir.FuncId,
        params: []const tir.ParamId,
        entry_block: mlir.Block,
        t: *const tir.TIR,
    ) !void {
        if (!enable_debug_info) return;
        const subp_ptr = self.di_subprograms.getPtr(f_id) orelse return;
        const subp = subp_ptr.*;

        var has_named = false;
        for (params) |pid| {
            const p = t.funcs.Param.get(pid);
            if (!p.name.isNone()) {
                has_named = true;
                break;
            }
        }
        if (!has_named) return;

        const file_info = self.ensureDebugFile(subp.file_id) catch return;
        const meta_ty = self.ensureMetadataType() catch return;
        const expr_attr = self.ensureEmptyDIExpression() catch return;
        const di_type = self.ensureDINullTypeAttr() catch return;

        const prev_loc = self.pushLocation(subp.loc);
        defer self.loc = prev_loc;

        const expr_value = self.metadataConstant(expr_attr, meta_ty);

        for (params, 0..) |pid, idx| {
            const p = t.funcs.Param.get(pid);
            if (p.name.isNone()) continue;
            const name = t.instrs.strs.get(p.name.unwrap());
            const var_attr = mlir.LLVMAttributes.getLLVMDILocalVariableAttr(
                self.mlir_ctx,
                subp.attr,
                self.strAttr(name),
                file_info.file_attr,
                subp.line,
                @intCast(idx + 1),
                0,
                di_type,
                0,
            );
            if (var_attr.isNull()) continue;

            const var_value = self.metadataConstant(var_attr, meta_ty);
            const arg_val = entry_block.getArgument(idx);
            var dbg = OpBuilder.init("llvm.intr.dbg.value", self.loc).builder()
                .add_operands(&.{ arg_val, var_value, expr_value })
                .build();
            self.append(dbg);
        }
    }

    // ----------------------------------------------------------------
    // Functions
    // ----------------------------------------------------------------

    fn emitExternDecls(self: *MlirCodegen, t: *const tir.TIR, store: *types.TypeStore) !void {
        const global_ids = t.funcs.global_pool.data.items;

        for (global_ids) |global_id| {
            const g = t.funcs.Global.get(global_id);
            const name = t.instrs.strs.get(g.name);

            if (store.getKind(g.ty) == .Function) {
                // If already present, return it.
                if (self.func_syms.contains(name)) continue;

                const fnty = store.get(.Function, g.ty);
                var params_sr = store.type_pool.slice(fnty.params);
                if (fnty.is_variadic)
                    params_sr = params_sr[0 .. params_sr.len - 1]; // drop trailing Any for varargs
                const ret_sr = fnty.result;

                // Build lowered param list & arg attributes
                var lowered_params = try self.gpa.alloc(mlir.Type, params_sr.len + 1); // +1 for possible sret
                defer self.gpa.free(lowered_params);
                var argAttrs = try self.gpa.alloc(mlir.Attribute, params_sr.len + 1);
                defer self.gpa.free(argAttrs);

                var n_args: usize = 0;

                // Return classification (may add leading sret)
                const retClass = abi.abiClassifyX64SysV(self, store, ret_sr, true);
                var ret_type: mlir.Type = self.void_ty;

                if (store.getKind(ret_sr) == .Void) {
                    ret_type = self.void_ty;
                } else switch (retClass.kind) {
                    .IndirectSRet => {
                        // leading ptr arg with { llvm.sret = type(T), llvm.align = K }
                        lowered_params[n_args] = self.llvm_ptr_ty;
                        const stTy = try self.llvmTypeOf(store, ret_sr);
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

                // Params
                for (params_sr) |psr| {
                    const cls = abi.abiClassifyX64SysV(self, store, psr, false);
                    switch (cls.kind) {
                        .IndirectByVal => {
                            lowered_params[n_args] = self.llvm_ptr_ty;
                            const stTy = try self.llvmTypeOf(store, psr);
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
                const fnop = OpBuilder.init("llvm.func", self.loc).builder()
                    .add_attributes(&attrs)
                    .add_regions(&.{region})
                    .build();
                var body = self.module.getBody();
                body.appendOwnedOperation(fnop);

                _ = try self.func_syms.put(name, .{
                    .op = fnop,
                    .is_variadic = fnty.is_variadic,
                    .n_formals = params_sr.len, // SR count, not lowered
                    .ret_type = ret_type,
                    .dbg_subprogram = null,
                });
            } else {
                // Handle global variables
                const var_mlir_ty = try self.llvmTypeOf(store, g.ty);

                var attr_buf: std.ArrayList(mlir.NamedAttribute) = .empty;
                defer attr_buf.deinit(self.gpa);

                try attr_buf.append(self.gpa, self.named("sym_name", self.strAttr(name)));
                try attr_buf.append(self.gpa, self.named("global_type", mlir.Attribute.typeAttrGet(var_mlir_ty)));
                try attr_buf.append(self.gpa, self.named("sym_visibility", self.strAttr("private")));
                try attr_buf.append(self.gpa, self.named(
                    "linkage",
                    mlir.LLVMAttributes.getLLVMLinkageAttr(self.mlir_ctx, mlir.LLVMLinkage.Internal),
                ));

                switch (g.init) {
                    .int => |val| {
                        const attr = mlir.Attribute.integerAttrGet(var_mlir_ty, val);
                        try attr_buf.append(self.gpa, self.named("value", attr));
                    },
                    .bool => |val| {
                        const attr = mlir.Attribute.integerAttrGet(var_mlir_ty, if (val) 1 else 0);
                        try attr_buf.append(self.gpa, self.named("value", attr));
                    },
                    else => {},
                }

                const attrs = attr_buf.items;
                // Likewise, synthesized globals are emitted with the module location
                // because they are not backed by user-written syntax.
                const global_op = OpBuilder.init("llvm.mlir.global", self.loc).builder()
                    .add_attributes(attrs)
                    .add_regions(&.{mlir.Region.create()})
                    .build();

                var body = self.module.getBody();
                body.appendOwnedOperation(global_op);
            }
        }
    }

    fn emitFunctionHeader(self: *MlirCodegen, f_id: tir.FuncId, t: *const tir.TIR, store: *types.TypeStore) !void {
        const f = t.funcs.Function.get(f_id);
        const params = t.funcs.param_pool.slice(f.params);

        var param_tys = try self.gpa.alloc(mlir.Type, params.len);
        defer self.gpa.free(param_tys);

        for (params, 0..) |p_id, i| {
            const p = t.funcs.Param.get(p_id);
            param_tys[i] = try self.llvmTypeOf(store, p.ty);
        }

        var results: [1]mlir.Type = undefined;
        const n_res: usize = if (store.getKind(f.result) == .Void) 0 else 1;
        if (n_res == 1) results[0] = try self.llvmTypeOf(store, f.result);

        const func_name = t.instrs.strs.get(f.name);
        if (self.func_syms.contains(func_name)) return;

        // NOTE: language-defined functions here are assumed non-variadic
        const fty = mlir.Type.getFunctionType(self.mlir_ctx, @intCast(param_tys.len), param_tys, @intCast(n_res), results[0..n_res]);

        var attrs: std.ArrayList(mlir.NamedAttribute) = .empty;
        defer attrs.deinit(self.gpa);

        try attrs.append(self.gpa, self.named("sym_name", self.strAttr(func_name)));
        try attrs.append(self.gpa, self.named("function_type", mlir.Attribute.typeAttrGet(fty)));
        try attrs.append(self.gpa, self.named("sym_visibility", self.strAttr("public")));

        const f_attrs = t.instrs.attribute_pool.slice(f.attrs);
        const emit_c_iface = t.instrs.strs.intern("llvm.emit_c_interface");
        for (f_attrs) |attr_id| {
            const attr = t.instrs.Attribute.get(attr_id);
            if (attr.name.eq(emit_c_iface)) {
                try attrs.append(self.gpa, self.named("llvm.emit_c_interface", mlir.Attribute.unitAttrGet(self.mlir_ctx)));
            }
        }

        const fn_loc = self.functionOptLoc(f_id, t);
        const prev_loc = self.pushLocation(fn_loc);
        const fn_mlir_loc = self.loc;
        self.loc = prev_loc;

        const region = mlir.Region.create();
        const fnop = OpBuilder.init("func.func", fn_mlir_loc).builder()
            .add_attributes(attrs.items)
            .add_regions(&.{region})
            .build();

        var body = self.module.getBody();
        body.appendOwnedOperation(fnop);

        const ret_mlir = if (n_res == 0) self.void_ty else results[0];
        var finfo: FuncInfo = .{
            .op = fnop,
            .is_variadic = false,
            .n_formals = params.len,
            .ret_type = ret_mlir,
            .dbg_subprogram = null,
        };

        if (enable_debug_info and !fn_loc.isNone()) {
            if (self.active_loc_store) |locs_store| {
                const loc_record = locs_store.get(fn_loc.unwrap());
                const src = self.getFileSource(loc_record.file_id) catch null;
                if (src) |src_text| {
                    const lc = computeLineCol(src_text, loc_record.start);
                    const line = @as(u32, @intCast(lc.line + 1));
                    const maybe_subp: ?*DebugSubprogramInfo = self.ensureDebugSubprogram(
                        f_id,
                        func_name,
                        line,
                        loc_record.file_id,
                        fn_loc,
                    ) catch null;
                    if (maybe_subp) |subp| {
                        fnop.setAttributeByName(mlir.StringRef.from("llvm.di.subprogram"), subp.attr);
                        finfo.dbg_subprogram = subp.attr;
                    }
                }
            }
        }

        _ = try self.func_syms.put(func_name, finfo);
    }

    fn emitFunctionBody(self: *MlirCodegen, f_id: tir.FuncId, t: *const tir.TIR, store: *types.TypeStore) !void {
        // reset per-function state
        self.block_map.clearRetainingCapacity();
        self.value_map.clearRetainingCapacity();
        self.val_types.clearRetainingCapacity();
        self.def_instr.clearRetainingCapacity();
        self.cur_region = null;
        self.cur_block = null;

        const f = t.funcs.Function.get(f_id);
        const fn_opt_loc = self.functionOptLoc(f_id, t);
        const func_name = t.instrs.strs.get(f.name);
        const finfo = self.func_syms.get(func_name).?;
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
            entry_arg_tys[i] = try self.llvmTypeOf(store, p.ty);
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
            self.emitParameterDebugInfo(f_id, params[0..n_formals], entry_block, t) catch {};
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
                    arg_tys[i] = try self.llvmTypeOf(store, bp.ty);
                    arg_locs[i] = block_mlir_loc;
                }

                const b = mlir.Block.create(arg_tys, arg_locs);
                region.appendOwnedBlock(b);
                try self.block_map.put(b_id, b);
            }
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
                const v = try self.emitInstr(ins_id, t, store);

                if (self.getInstrResultId(t, ins_id)) |rid| {
                    try self.value_map.put(rid, v);
                    if (self.instrResultSrType(t, ins_id)) |rt| {
                        try self.val_types.put(rid, rt);
                    }
                    try self.def_instr.put(rid, ins_id);
                }
            }

            // terminator
            try self.emitTerminator(bb.term, t, store);
        }
    }

    fn getInstrResultId(self: *MlirCodegen, t: *const tir.TIR, id: tir.InstrId) ?tir.ValueId {
        _ = self;
        const K = t.instrs.index.kinds.items[id.toRaw()];
        switch (K) {
            .RangeMake => return t.instrs.get(.RangeMake, id).result,
            .ConstInt => return t.instrs.get(.ConstInt, id).result,
            .ConstFloat => return t.instrs.get(.ConstFloat, id).result,
            .ConstBool => return t.instrs.get(.ConstBool, id).result,
            .ConstString => return t.instrs.get(.ConstString, id).result,
            .ConstNull => return t.instrs.get(.ConstNull, id).result,
            .ConstUndef => return t.instrs.get(.ConstUndef, id).result,
            inline .Add, .Sub, .Mul, .BinWrapAdd, .BinWrapSub, .BinWrapMul, .BinSatAdd, .BinSatSub, .BinSatMul, .BinSatShl, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe, .LogicalAnd, .LogicalOr => |k| return t.instrs.get(k, id).result,
            .LogicalNot => return t.instrs.get(.LogicalNot, id).result,
            inline .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => |k| return t.instrs.get(k, id).result,
            .Alloca => return t.instrs.get(.Alloca, id).result,
            .Load => return t.instrs.get(.Load, id).result,
            .Store => return null,
            .Gep => return t.instrs.get(.Gep, id).result,
            .GlobalAddr => return t.instrs.get(.GlobalAddr, id).result,
            .ComplexMake => return t.instrs.get(.ComplexMake, id).result,
            .TupleMake => return t.instrs.get(.TupleMake, id).result,
            .ArrayMake => return t.instrs.get(.ArrayMake, id).result,
            .StructMake => return t.instrs.get(.StructMake, id).result,
            .ExtractElem => return t.instrs.get(.ExtractElem, id).result,
            .InsertElem => return t.instrs.get(.InsertElem, id).result,
            .ExtractField => return t.instrs.get(.ExtractField, id).result,
            .InsertField => return t.instrs.get(.InsertField, id).result,
            .Index => return t.instrs.get(.Index, id).result,
            .AddressOf => return t.instrs.get(.AddressOf, id).result,
            .Select => return t.instrs.get(.Select, id).result,
            .Call => return t.instrs.get(.Call, id).result,
            .IndirectCall => return t.instrs.get(.IndirectCall, id).result,
            .VariantMake => return t.instrs.get(.VariantMake, id).result,
            .VariantTag => return t.instrs.get(.VariantTag, id).result,
            .VariantPayloadPtr => return t.instrs.get(.VariantPayloadPtr, id).result,
            .UnionMake => return t.instrs.get(.UnionMake, id).result,
            .UnionFieldPtr => return t.instrs.get(.UnionFieldPtr, id).result,
            .UnionField => return t.instrs.get(.UnionField, id).result,
            .MlirBlock => {
                const p = t.instrs.get(.MlirBlock, id);
                if (p.result.isNone()) return null;
                return p.result.unwrap();
            },
        }
    }

    fn instrResultSrType(self: *MlirCodegen, t: *const tir.TIR, id: tir.InstrId) ?types.TypeId {
        _ = self;
        const K = t.instrs.index.kinds.items[id.toRaw()];
        return switch (K) {
            .ConstInt => t.instrs.get(.ConstInt, id).ty,
            .ConstFloat => t.instrs.get(.ConstFloat, id).ty,
            .ConstBool => t.instrs.get(.ConstBool, id).ty,
            .ConstString => t.instrs.get(.ConstString, id).ty,
            .ConstNull => t.instrs.get(.ConstNull, id).ty,
            .ConstUndef => t.instrs.get(.ConstUndef, id).ty,
            inline .Add, .Sub, .Mul, .BinWrapAdd, .BinWrapSub, .BinWrapMul, .BinSatAdd, .BinSatSub, .BinSatMul, .BinSatShl, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe, .LogicalAnd, .LogicalOr => |k| t.instrs.get(k, id).ty,
            .LogicalNot => t.instrs.get(.LogicalNot, id).ty,
            inline .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => |k| t.instrs.get(k, id).ty,
            .Alloca => t.instrs.get(.Alloca, id).ty,
            .Load => t.instrs.get(.Load, id).ty,
            .Store => null,
            .Gep => t.instrs.get(.Gep, id).ty,
            .GlobalAddr => t.instrs.get(.GlobalAddr, id).ty,
            .ComplexMake => t.instrs.get(.ComplexMake, id).ty,
            .TupleMake => t.instrs.get(.TupleMake, id).ty,
            .ArrayMake => t.instrs.get(.ArrayMake, id).ty,
            .RangeMake => t.instrs.get(.RangeMake, id).ty,
            .StructMake => t.instrs.get(.StructMake, id).ty,
            .ExtractElem => t.instrs.get(.ExtractElem, id).ty,
            .InsertElem => t.instrs.get(.InsertElem, id).ty,
            .ExtractField => t.instrs.get(.ExtractField, id).ty,
            .InsertField => t.instrs.get(.InsertField, id).ty,
            .Index => t.instrs.get(.Index, id).ty,
            .AddressOf => t.instrs.get(.AddressOf, id).ty,
            .Select => t.instrs.get(.Select, id).ty,
            .Call => t.instrs.get(.Call, id).ty,
            .IndirectCall => t.instrs.get(.IndirectCall, id).ty,
            .VariantMake => t.instrs.get(.VariantMake, id).ty,
            .VariantTag => t.instrs.get(.VariantTag, id).ty,
            .VariantPayloadPtr => t.instrs.get(.VariantPayloadPtr, id).ty,
            .UnionMake => t.instrs.get(.UnionMake, id).ty,
            .UnionFieldPtr => t.instrs.get(.UnionFieldPtr, id).ty,
            .UnionField => t.instrs.get(.UnionField, id).ty,
            .MlirBlock => t.instrs.get(.MlirBlock, id).ty,
        };
    }

    fn ensureFuncDeclFromCall(self: *MlirCodegen, ins_id: tir.InstrId, t: *const tir.TIR, store: *types.TypeStore) !FuncInfo {
        const p = t.instrs.get(.Call, ins_id);
        const name = t.instrs.strs.get(p.callee);

        // If already present, return it.
        if (self.func_syms.get(name)) |fi| return fi;

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
            if (store.getKind(g.ty) != .Function) continue;
            if (!g.name.eq(p.callee)) continue;
            const fnty = store.get(.Function, g.ty);
            is_var = fnty.is_variadic;
            params_sr = store.type_pool.slice(fnty.params);
            ret_sr = fnty.result;
            found = true;
            break;
        }

        if (!found) {
            // Fallback: infer SR types from call operands/result.
            const args_slice = t.instrs.val_list_pool.slice(p.args);
            for (args_slice) |vid| try params_sr_list.append(self.srTypeOfValue(t, vid));
            ret_sr = p.ty;
            is_var = false; // unknown: assume non-variadic
        }
        params_sr = params_sr_list.items;

        // Lower with classifier: same logic as emitExternDecls
        var lowered_params = try self.gpa.alloc(mlir.Type, params_sr.len + 1);
        defer self.gpa.free(lowered_params);
        var argAttrs = try self.gpa.alloc(mlir.Attribute, params_sr.len + 1);
        defer self.gpa.free(argAttrs);
        var n_args: usize = 0;

        const retClass = abi.abiClassifyX64SysV(self, store, ret_sr, true);
        var ret_type: mlir.Type = self.void_ty;

        if (store.getKind(ret_sr) == .Void) {
            ret_type = self.void_ty;
        } else switch (retClass.kind) {
            .IndirectSRet => {
                lowered_params[n_args] = self.llvm_ptr_ty;
                const stTy = try self.llvmTypeOf(store, ret_sr);
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

        for (params_sr) |psr| {
            const cls = abi.abiClassifyX64SysV(self, store, psr, false);
            switch (cls.kind) {
                .IndirectByVal => {
                    lowered_params[n_args] = self.llvm_ptr_ty;
                    const stTy = try self.llvmTypeOf(store, psr);
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
        const fnop = OpBuilder.init("llvm.func", self.loc).builder()
            .add_attributes(&attrs)
            .add_regions(&.{region})
            .build();
        var body = self.module.getBody();
        body.appendOwnedOperation(fnop);

        const info: FuncInfo = .{
            .op = fnop,
            .is_variadic = is_var,
            .n_formals = params_sr.len,
            .ret_type = ret_type,
            .dbg_subprogram = null,
        };
        _ = try self.func_syms.put(name, info);
        return info;
    }

    // ----------------------------------------------------------------
    // Instructions
    // ----------------------------------------------------------------
    fn emitInstr(self: *MlirCodegen, ins_id: tir.InstrId, t: *const tir.TIR, store: *types.TypeStore) !mlir.Value {
        const kind = t.instrs.index.kinds.items[ins_id.toRaw()];
        return switch (kind) {
            // ------------- Constants -------------
            .ConstInt => blk: {
                const p = t.instrs.get(.ConstInt, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const ty = try self.llvmTypeOf(store, p.ty);
                break :blk self.constInt(ty, p.value);
            },
            .ConstFloat => blk: {
                const p = t.instrs.get(.ConstFloat, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const ty = try self.llvmTypeOf(store, p.ty);
                break :blk self.constFloat(ty, p.value);
            },
            .ConstBool => blk: {
                const p = t.instrs.get(.ConstBool, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                break :blk self.constBool(p.value);
            },
            .ConstNull => blk: {
                const p = t.instrs.get(.ConstNull, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const ty = try self.llvmTypeOf(store, p.ty);
                var zero = OpBuilder.init("llvm.mlir.zero", self.loc).builder()
                    .add_results(&.{ty}).build();
                self.append(zero);
                const flag = self.constBool(false);
                const v = self.insertAt(zero.getResult(0), flag, &.{0});
                break :blk v;
            },
            .ConstUndef => blk: {
                const p = t.instrs.get(.ConstUndef, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const ty = try self.llvmTypeOf(store, p.ty);
                var op = OpBuilder.init("llvm.mlir.undef", self.loc).builder()
                    .add_results(&.{ty}).build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .ConstString => blk: {
                const p = t.instrs.get(.ConstString, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const str_text = t.instrs.strs.get(p.text);
                var ptr_op = try self.constStringPtr(str_text);
                const ptr_val = ptr_op.getResult(0);
                const len_val = self.llvmConstI64(@intCast(str_text.len));

                const string_ty = try self.llvmTypeOf(store, p.ty);
                var agg = self.undefOf(string_ty);
                agg = self.insertAt(agg, ptr_val, &.{0});
                agg = self.insertAt(agg, len_val, &.{1});
                break :blk agg;
            },

            // ------------- Arithmetic / bitwise (now arith.*) -------------
            .Add => blk: {
                const p = t.instrs.get(.Add, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                // If result SR type is Complex, use complex.add
                if (store.getKind(p.ty) == .Complex) {
                    const lhs = self.value_map.get(p.lhs).?;
                    const rhs = self.value_map.get(p.rhs).?;
                    const cty = try self.llvmTypeOf(store, p.ty);
                    var op = OpBuilder.init("complex.add", self.loc).builder()
                        .add_operands(&.{ lhs, rhs })
                        .add_results(&.{cty}).build();
                    self.append(op);
                    break :blk op.getResult(0);
                }
                break :blk try self.binArith("llvm.add", "llvm.fadd", p, store);
            },
            .Sub => blk: {
                const p = t.instrs.get(.Sub, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                if (store.getKind(p.ty) == .Complex) {
                    const lhs = self.value_map.get(p.lhs).?;
                    const rhs = self.value_map.get(p.rhs).?;
                    const cty = try self.llvmTypeOf(store, p.ty);
                    var op = OpBuilder.init("complex.sub", self.loc).builder()
                        .add_operands(&.{ lhs, rhs })
                        .add_results(&.{cty}).build();
                    self.append(op);
                    break :blk op.getResult(0);
                }
                break :blk try self.binArith("llvm.sub", "llvm.fsub", p, store);
            },
            .Mul => blk: {
                const p = t.instrs.get(.Mul, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                if (store.getKind(p.ty) == .Complex) {
                    const lhs = self.value_map.get(p.lhs).?;
                    const rhs = self.value_map.get(p.rhs).?;
                    const cty = try self.llvmTypeOf(store, p.ty);
                    var op = OpBuilder.init("complex.mul", self.loc).builder()
                        .add_operands(&.{ lhs, rhs })
                        .add_results(&.{cty}).build();
                    self.append(op);
                    break :blk op.getResult(0);
                }
                break :blk try self.binArith("llvm.mul", "llvm.fmul", p, store);
            },
            .BinWrapAdd => try self.binArith("llvm.add", "llvm.fadd", t.instrs.get(.BinWrapAdd, ins_id), store),
            .BinWrapSub => try self.binArith("llvm.sub", "llvm.fsub", t.instrs.get(.BinWrapSub, ins_id), store),
            .BinWrapMul => try self.binArith("llvm.mul", "llvm.fmul", t.instrs.get(.BinWrapMul, ins_id), store),
            .BinSatAdd => blk: {
                const row = t.instrs.get(.BinSatAdd, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitSaturatingIntBinary(row, store, "arith.addi", true);
            },
            .BinSatSub => blk: {
                const row = t.instrs.get(.BinSatSub, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitSaturatingIntBinary(row, store, "arith.subi", true);
            },
            .BinSatMul => blk: {
                const row = t.instrs.get(.BinSatMul, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitSaturatingIntBinary(row, store, "arith.muli", true);
            },

            .Div => blk: {
                const p = t.instrs.get(.Div, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                if (store.getKind(p.ty) == .Complex) {
                    const lhs = self.value_map.get(p.lhs).?;
                    const rhs = self.value_map.get(p.rhs).?;
                    const cty = try self.llvmTypeOf(store, p.ty);
                    var op = OpBuilder.init("complex.div", self.loc).builder()
                        .add_operands(&.{ lhs, rhs })
                        .add_results(&.{cty}).build();
                    self.append(op);
                    break :blk op.getResult(0);
                }
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                const signed = !self.isUnsigned(store, self.srTypeOfValue(t, p.lhs));
                break :blk self.arithDiv(lhs, rhs, ty, signed);
            },

            .Mod => blk: {
                const p = t.instrs.get(.Mod, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                const signed = !self.isUnsigned(store, self.srTypeOfValue(t, p.lhs));
                break :blk self.arithRem(lhs, rhs, ty, signed);
            },

            .Shl => blk: {
                const p = t.instrs.get(.Shl, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                break :blk self.arithShl(lhs, rhs, ty);
            },
            .BinSatShl => blk: {
                const row = t.instrs.get(.BinSatShl, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitSaturatingIntBinary(row, store, "arith.shli", false);
            },
            .Shr => blk: {
                const p = t.instrs.get(.Shr, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                const signed = !self.isUnsigned(store, self.srTypeOfValue(t, p.lhs));
                break :blk self.arithShr(lhs, rhs, ty, signed);
            },

            .BitAnd => try self.binBit("llvm.and", t.instrs.get(.BitAnd, ins_id), store),
            .BitOr => try self.binBit("llvm.or", t.instrs.get(.BitOr, ins_id), store),
            .BitXor => try self.binBit("llvm.xor", t.instrs.get(.BitXor, ins_id), store),

            // ------------- Logical (arith.*) -------------
            .LogicalAnd => try self.binBit("llvm.and", t.instrs.get(.LogicalAnd, ins_id), store),
            .LogicalOr => try self.binBit("llvm.or", t.instrs.get(.LogicalOr, ins_id), store),
            .LogicalNot => blk: {
                const p = t.instrs.get(.LogicalNot, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const v = self.value_map.get(p.value).?;
                break :blk self.arithLogicalNotI1(v);
            },

            // ------------- Comparisons (keep LLVM for robust attrs) -------------
            .CmpEq => blk: {
                const row = t.instrs.get(.CmpEq, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitCmp("eq", "eq", "oeq", row, t, store);
            },
            .CmpNe => blk: {
                const row = t.instrs.get(.CmpNe, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitCmp("ne", "ne", "one", row, t, store);
            },
            .CmpLt => blk: {
                const row = t.instrs.get(.CmpLt, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitCmp("ult", "slt", "olt", row, t, store);
            },
            .CmpLe => blk: {
                const row = t.instrs.get(.CmpLe, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitCmp("ule", "sle", "ole", row, t, store);
            },
            .CmpGt => blk: {
                const row = t.instrs.get(.CmpGt, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitCmp("ugt", "sgt", "ogt", row, t, store);
            },
            .CmpGe => blk: {
                const row = t.instrs.get(.CmpGe, ins_id);
                const prev_loc = self.pushLocation(row.loc);
                defer self.loc = prev_loc;
                break :blk try self.emitCmp("uge", "sge", "oge", row, t, store);
            },

            // ------------- Casts -------------
            .CastBit => blk: {
                const p = t.instrs.get(.CastBit, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const to_ty = try self.llvmTypeOf(store, p.ty);
                const from_v = self.value_map.get(p.value).?;
                var op = OpBuilder.init("llvm.bitcast", self.loc).builder()
                    .add_operands(&.{from_v})
                    .add_results(&.{to_ty}).build();
                self.append(op);
                break :blk op.getResult(0);
            },

            .CastNormal => blk: {
                const p = t.instrs.get(.CastNormal, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const to_ty = try self.llvmTypeOf(store, p.ty);
                const from_v = self.value_map.get(p.value).?;
                const src_sr = self.srTypeOfValue(t, p.value);
                const val = try self.emitCastNormal(store, p.ty, to_ty, from_v, src_sr);
                break :blk val;
            },

            .CastSaturate => blk: {
                const p = t.instrs.get(.CastSaturate, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const from_v = self.value_map.get(p.value).?;
                const src_sr = self.srTypeOfValue(t, p.value);
                const val = try self.emitCast(.CastSaturate, store, p.ty, src_sr, from_v);
                break :blk val;
            },

            inline .CastWrap, .CastChecked => |x| blk: {
                const p = t.instrs.get(x, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const from_v = self.value_map.get(p.value).?;
                const src_sr = self.srTypeOfValue(t, p.value);
                const val = try self.emitCast(x, store, p.ty, src_sr, from_v);
                break :blk val;
            },

            // ------------- Memory -------------
            .Alloca => blk: {
                const p = t.instrs.get(.Alloca, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                var elem_ty: mlir.Type = self.i8_ty;
                switch (store.getKind(p.ty)) {
                    .Ptr => {
                        const ptr_row = store.get(.Ptr, p.ty);
                        // Use storage representation for memory: Complex -> {elem, elem}
                        if (store.getKind(ptr_row.elem) == .Complex) {
                            const c = store.get(.Complex, ptr_row.elem);
                            const ety = try self.llvmTypeOf(store, c.elem);
                            elem_ty = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ ety, ety }, false);
                        } else {
                            elem_ty = try self.llvmTypeOf(store, ptr_row.elem);
                        }
                    },
                    else => {},
                }
                const count_v: mlir.Value = if (!p.count.isNone())
                    self.value_map.get(p.count.unwrap()).?
                else
                    self.llvmConstI64(1);

                var attrs = [_]mlir.NamedAttribute{
                    self.named("elem_type", mlir.Attribute.typeAttrGet(elem_ty)),
                };
                var alloca = OpBuilder.init("llvm.alloca", self.loc).builder()
                    .add_operands(&.{count_v})
                    .add_results(&.{self.llvm_ptr_ty})
                    .add_attributes(&attrs).build();
                self.append(alloca);
                break :blk alloca.getResult(0);
            },

            .Load => blk: {
                const p = t.instrs.get(.Load, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                var ptr_val_opt = self.value_map.get(p.ptr);
                if (ptr_val_opt == null) {
                    // Try materializing or folding known-constant pointers directly to values as a last resort.
                    if (self.def_instr.get(p.ptr)) |pid| {
                        const kdef = t.instrs.index.kinds.items[pid.toRaw()];
                        const res_ty = try self.llvmTypeOf(store, p.ty);
                        switch (kdef) {
                            .ConstFloat => {
                                const rowf = t.instrs.get(.ConstFloat, pid);
                                const cf = self.constFloat(res_ty, rowf.value);
                                break :blk cf;
                            },
                            .ConstInt => {
                                const rowi = t.instrs.get(.ConstInt, pid);
                                const ci = self.constInt(res_ty, @intCast(rowi.value));
                                break :blk ci;
                            },
                            .ConstBool => {
                                const rowb = t.instrs.get(.ConstBool, pid);
                                const cb = self.constBool(rowb.value);
                                break :blk cb;
                            },
                            else => {},
                        }
                        // Otherwise, attempt on-demand emission
                        _ = try self.emitInstr(pid, t, store);
                        ptr_val_opt = self.value_map.get(p.ptr);
                    }
                    if (ptr_val_opt == null) {
                        // Last-resort: treat as value load and synthesize zero of result type.
                        const res_ty = try self.llvmTypeOf(store, p.ty);
                        break :blk self.zeroOf(res_ty);
                    }
                }
                const ptr = ptr_val_opt.?;
                if (store.getKind(p.ty) == .Complex) {
                    const c = store.get(.Complex, p.ty);
                    const elem_ty = try self.llvmTypeOf(store, c.elem);
                    const storage_ty = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ elem_ty, elem_ty }, false);
                    var ld = OpBuilder.init("llvm.load", self.loc).builder()
                        .add_operands(&.{ptr})
                        .add_results(&.{storage_ty}).build();
                    self.append(ld);
                    const agg = ld.getResult(0);
                    const re = self.extractAt(agg, elem_ty, &.{0});
                    const im = self.extractAt(agg, elem_ty, &.{1});
                    const res_ty = try self.llvmTypeOf(store, p.ty);
                    var mk = OpBuilder.init("complex.create", self.loc).builder()
                        .add_operands(&.{ re, im })
                        .add_results(&.{res_ty}).build();
                    self.append(mk);
                    break :blk mk.getResult(0);
                } else {
                    const res_ty = try self.llvmTypeOf(store, p.ty);
                    // If the operand is not a pointer (opaque ptr model), treat it as a value and coerce if needed.
                    if (!mlir.LLVM.isLLVMPointerType(ptr.getType())) {
                        // Pass-through/coerce
                        if (ptr.getType().equal(res_ty)) break :blk ptr;
                        const src_sr = self.srTypeOfValue(t, p.ptr);
                        const v = try self.coerceOnBranch(ptr, res_ty, p.ty, src_sr, store);
                        break :blk v;
                    }
                    var load = OpBuilder.init("llvm.load", self.loc).builder()
                        .add_operands(&.{ptr})
                        .add_results(&.{res_ty}).build();
                    self.append(load);
                    break :blk load.getResult(0);
                }
            },

            .Store => blk: {
                const p = t.instrs.get(.Store, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const v = self.value_map.get(p.value).?;
                const ptr_opt = self.value_map.get(p.ptr);
                if (ptr_opt == null) {
                    std.debug.print("MLIR Store missing ptr mapping: ins_id={} ptr_vid={}\n", .{ ins_id, p.ptr });
                    return error.CompileError;
                }
                const ptr = ptr_opt.?;
                const v_sr = self.srTypeOfValue(t, p.value);
                if (store.getKind(v_sr) == .Complex) {
                    const c = store.get(.Complex, v_sr);
                    const elem_ty = try self.llvmTypeOf(store, c.elem);
                    // Spill complex into {elem, elem}
                    var reop = OpBuilder.init("complex.re", self.loc).builder()
                        .add_operands(&.{v}).add_results(&.{elem_ty}).build();
                    self.append(reop);
                    var imop = OpBuilder.init("complex.im", self.loc).builder()
                        .add_operands(&.{v}).add_results(&.{elem_ty}).build();
                    self.append(imop);
                    const storage_ty = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ elem_ty, elem_ty }, false);
                    var acc = self.undefOf(storage_ty);
                    acc = self.insertAt(acc, reop.getResult(0), &.{0});
                    acc = self.insertAt(acc, imop.getResult(0), &.{1});
                    const st = OpBuilder.init("llvm.store", self.loc).builder()
                        .add_operands(&.{ acc, ptr }).build();
                    self.append(st);
                    break :blk mlir.Value.empty();
                } else {
                    const st = OpBuilder.init("llvm.store", self.loc).builder()
                        .add_operands(&.{ v, ptr }).build();
                    self.append(st);
                    break :blk mlir.Value.empty();
                }
            },

            .Gep => blk: {
                const p = t.instrs.get(.Gep, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const base = self.value_map.get(p.base).?;
                const pty_kind = store.getKind(p.ty);
                var elem_mlir: mlir.Type = undefined;
                if (pty_kind == .Ptr) {
                    const ptr_row = store.get(.Ptr, p.ty);
                    elem_mlir = try self.llvmTypeOf(store, ptr_row.elem);
                } else {
                    elem_mlir = self.i8_ty;
                }

                const index_ids = t.instrs.gep_pool.slice(p.indices);
                var indices_data = try self.gpa.alloc(tir.Rows.GepIndex, index_ids.len);
                defer self.gpa.free(indices_data);
                for (index_ids, 0..) |id, i| {
                    indices_data[i] = t.instrs.GepIndex.get(id);
                }
                const v = try self.emitGep(base, elem_mlir, indices_data);
                break :blk v;
            },
            .GlobalAddr => blk: {
                const p = t.instrs.get(.GlobalAddr, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const name = t.instrs.strs.get(p.name);
                const ty = try self.llvmTypeOf(store, p.ty);

                const gsym = mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(name));
                var addr = OpBuilder.init("llvm.mlir.addressof", self.loc).builder()
                    .add_results(&.{ty})
                    .add_attributes(&.{self.named("global_name", gsym)})
                    .build();
                self.append(addr);
                break :blk addr.getResult(0);
            },

            // ------------- Aggregates -------------
            .TupleMake => blk: {
                const p = t.instrs.get(.TupleMake, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const tup_ty = try self.llvmTypeOf(store, p.ty);
                var acc = self.zeroOf(tup_ty);
                // Tuple elements are stored in value_pool
                const elems = t.instrs.value_pool.slice(p.elems);
                for (elems, 0..) |vid, i| {
                    const v = self.value_map.get(vid).?;
                    acc = self.insertAt(acc, v, &.{@as(i64, @intCast(i))});
                }
                break :blk acc;
            },
            .RangeMake => blk: {
                const p = t.instrs.get(.RangeMake, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                // Materialize as struct<i64,i64> { start, end } (inclusive handled by consumers)
                const i64t = self.i64_ty;
                const pairTy = mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{ i64t, i64t }, false);
                var acc = self.zeroOf(pairTy);
                const s = self.value_map.get(p.start).?;
                const e = self.value_map.get(p.end).?;
                const s64 = try self.coerceOnBranch(s, i64t, store.tI64(), self.srTypeOfValue(t, p.start), store);
                const e64 = try self.coerceOnBranch(e, i64t, store.tI64(), self.srTypeOfValue(t, p.end), store);
                acc = self.insertAt(acc, s64, &.{0});
                acc = self.insertAt(acc, e64, &.{1});
                break :blk acc;
            },
            .ArrayMake => blk: {
                const p = t.instrs.get(.ArrayMake, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const arr_ty = try self.llvmTypeOf(store, p.ty);
                // Determine element MLIR type from SR array element
                const arr_sr = store.get(.Array, p.ty);
                const elem_mlir = try self.llvmTypeOf(store, arr_sr.elem);
                var acc = self.zeroOf(arr_ty);
                // Array elements are stored in value_pool
                const elems = t.instrs.value_pool.slice(p.elems);
                for (elems, 0..) |vid, i| {
                    var v = self.value_map.get(vid).?;
                    // Best-effort: coerce value to the array element type if it doesn't match
                    if (!v.getType().equal(elem_mlir)) {
                        v = try self.coerceOnBranch(v, elem_mlir, arr_sr.elem, self.srTypeOfValue(t, vid), store);
                    }
                    acc = self.insertAt(acc, v, &.{@as(i64, @intCast(i))});
                }
                break :blk acc;
            },
            .StructMake => blk: {
                const p = t.instrs.get(.StructMake, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const st_ty = try self.llvmTypeOf(store, p.ty);
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
                const cty = try self.llvmTypeOf(store, p.ty);
                const re = self.value_map.get(p.re).?;
                const im = self.value_map.get(p.im).?;
                var op = OpBuilder.init("complex.create", self.loc).builder()
                    .add_operands(&.{ re, im })
                    .add_results(&.{cty}).build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .ExtractElem => blk: {
                const p = t.instrs.get(.ExtractElem, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const agg = self.value_map.get(p.agg).?;
                const res_ty = try self.llvmTypeOf(store, p.ty);
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
                const res_ty = try self.llvmTypeOf(store, p.ty);
                // Special-case: Complex field access -> complex.re/complex.im
                const parent_sr = self.srTypeOfValue(t, p.agg);
                const parent_kind = store.getKind(parent_sr);
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
                        var op = OpBuilder.init(opname, self.loc).builder()
                            .add_operands(&.{agg})
                            .add_results(&.{res_ty}).build();
                        self.append(op);
                        break :blk op.getResult(0);
                    }
                }
                if (!p.name.isNone()) {
                    const field_name = t.instrs.strs.get(p.name.unwrap());
                    if (std.mem.eql(u8, field_name, "len")) {
                        const v = self.extractAt(agg, res_ty, &.{@as(i64, @intCast(1))});
                        break :blk v;
                    }
                }
                const v = self.extractAt(agg, res_ty, &.{@as(i64, @intCast(p.index))});
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
                const var_ty = try self.llvmTypeOf(store, p.ty);
                var acc = self.undefOf(var_ty);

                const tag_val = self.llvmConstI32(@intCast(p.tag));
                acc = self.insertAt(acc, tag_val, &.{0});

                if (!p.payload.isNone()) {
                    const payload_val_id = p.payload.unwrap();
                    const payload_val = self.value_map.get(payload_val_id).?;

                    const struct_ty = store.get(.Struct, p.ty);
                    const union_field = store.field_pool.slice(struct_ty.fields)[1];
                    const union_ty = store.Field.get(union_field).ty;
                    const union_mlir_ty = try self.llvmTypeOf(store, union_ty);

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
                const u_mlir = try self.llvmTypeOf(store, p.ty);

                // Figure out the chosen field type and coerce payload to it
                var payload = self.value_map.get(p.value).?;
                const urow = store.get(.Union, p.ty);
                const f_ids = store.field_pool.slice(urow.fields);
                const f_sr = store.Field.get(f_ids[@intCast(p.field_index)]).ty;
                const f_mlir = try self.llvmTypeOf(store, f_sr);
                if (!payload.getType().equal(f_mlir)) {
                    payload = try self.coerceOnBranch(payload, f_mlir, f_sr, self.srTypeOfValue(t, p.value), store);
                }

                // Materialize the union by writing the chosen field at offset 0
                const tmp = self.spillAgg(self.undefOf(u_mlir), u_mlir, 0);
                self.storeAt(tmp, payload, 0);

                var ld = OpBuilder.init("llvm.load", self.loc).builder()
                    .add_operands(&.{tmp})
                    .add_results(&.{u_mlir}).build();
                self.append(ld);
                break :blk ld.getResult(0);
            },
            .UnionField => blk: {
                const p = t.instrs.get(.UnionField, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;

                // Get a pointer to the union storage, even if we were given an SSA value.
                var base = self.value_map.get(p.base).?;
                var union_sr = self.srTypeOfValue(t, p.base);
                var storage_ptr = base;

                if (!self.isLlvmPtr(base.getType())) {
                    // SSA value: spill to memory to get a pointer
                    const u_mlir = try self.llvmTypeOf(store, union_sr);
                    storage_ptr = self.spillAgg(base, u_mlir, 0);
                } else if (store.getKind(union_sr) == .Ptr) {
                    union_sr = store.get(.Ptr, union_sr).elem; // peel pointee SR type
                }

                // Desired field type
                const urow = store.get(.Union, union_sr);
                const f_ids = store.field_pool.slice(urow.fields);
                const f_sr = store.Field.get(f_ids[@intCast(p.field_index)]).ty;
                const f_mlir = try self.llvmTypeOf(store, f_sr);

                // Reinterpret the same address as a pointer-to-field-type at offset 0.
                // With opaque pointers in MLIR, use a zero-index GEP with the desired element type.
                const idxs = [_]tir.Rows.GepIndex{.{ .Const = 0 }};
                const fptr = try self.emitGep(storage_ptr, f_mlir, &idxs);
                // load the field value from the pointer
                const load_op = OpBuilder.init("llvm.load", self.loc).builder()
                    .add_operands(&.{fptr})
                    .add_results(&.{f_mlir}).build();
                self.append(load_op);
                break :blk load_op.getResult(0);
            },

            .UnionFieldPtr => blk: {
                const p = t.instrs.get(.UnionFieldPtr, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;

                // Get a pointer to the union storage, even if we were given an SSA value.
                var base = self.value_map.get(p.base).?;
                var union_sr = self.srTypeOfValue(t, p.base);
                var storage_ptr = base;

                if (!self.isLlvmPtr(base.getType())) {
                    // SSA value: spill to memory to get a pointer
                    const u_mlir = try self.llvmTypeOf(store, union_sr);
                    storage_ptr = self.spillAgg(base, u_mlir, 0);
                } else if (store.getKind(union_sr) == .Ptr) {
                    union_sr = store.get(.Ptr, union_sr).elem; // peel pointee SR type
                }

                // Desired field type
                const urow = store.get(.Union, union_sr);
                const f_ids = store.field_pool.slice(urow.fields);
                const f_sr = store.Field.get(f_ids[@intCast(p.field_index)]).ty;
                const f_mlir = try self.llvmTypeOf(store, f_sr);

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

            .Index => blk: {
                const p = t.instrs.get(.Index, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const base = self.value_map.get(p.base).?;
                const res_ty = try self.llvmTypeOf(store, p.ty);
                const res_sr_kind = store.getKind(p.ty);
                const base_sr_ty = self.srTypeOfValue(t, p.base);

                // Slicing: result is a slice type ([]T). Build {ptr,len} from base + range.
                if (res_sr_kind == .Slice) {
                    // Peel optional CastNormal from the index to find builtin.range.make
                    var idx_vid: tir.ValueId = p.index;
                    if (self.def_instr.get(idx_vid)) |iid1| {
                        const k1 = t.instrs.index.kinds.items[iid1.toRaw()];
                        if (k1 == .CastNormal) {
                            const crow = t.instrs.get(.CastNormal, iid1);
                            idx_vid = crow.value;
                        }
                    }
                    var start_vid: tir.ValueId = undefined;
                    var end_vid: tir.ValueId = undefined;
                    var incl_vid: tir.ValueId = undefined;
                    if (self.def_instr.get(idx_vid)) |iid2| {
                        const k2 = t.instrs.index.kinds.items[iid2.toRaw()];
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
                                    const zero = self.zeroOf(res_ty);
                                    break :blk zero;
                                }
                            } else {
                                const zero = self.zeroOf(res_ty);
                                break :blk zero;
                            }
                        } else {
                            const zero = self.zeroOf(res_ty);
                            break :blk zero;
                        }
                    } else {
                        const zero = self.zeroOf(res_ty);
                        break :blk zero;
                    }

                    // Compute data pointer for the slice
                    var data_ptr: mlir.Value = undefined;
                    var elem_sr: types.TypeId = undefined;
                    switch (store.getKind(base_sr_ty)) {
                        .Array => {
                            const arr = store.get(.Array, base_sr_ty);
                            elem_sr = arr.elem;
                            const arr_mlir = try self.llvmTypeOf(store, base_sr_ty);
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
                            elem_sr = store.get(.Slice, base_sr_ty).elem;
                            const ptr0 = self.extractAt(base, self.llvm_ptr_ty, &.{0});
                            const idxs = [_]tir.Rows.GepIndex{.{ .Value = start_vid }};
                            const elem_mlir = try self.llvmTypeOf(store, elem_sr);
                            data_ptr = try self.emitGep(ptr0, elem_mlir, &idxs);
                        },
                        else => {
                            // Unsupported base; return zero slice
                            const zero = self.zeroOf(res_ty);
                            break :blk zero;
                        },
                    }

                    // Compute length: (end - start) + (inclusive ? 1 : 0)
                    const start_v = self.value_map.get(start_vid).?;
                    const end_v = self.value_map.get(end_vid).?;
                    const incl_v = self.value_map.get(incl_vid).?;
                    const i64t = self.i64_ty;
                    // Ensure operands are i64
                    const start64 = try self.coerceOnBranch(start_v, i64t, store.tI64(), self.srTypeOfValue(t, start_vid), store);
                    const end64 = try self.coerceOnBranch(end_v, i64t, store.tI64(), self.srTypeOfValue(t, end_vid), store);
                    var sub = OpBuilder.init("llvm.sub", self.loc).builder()
                        .add_operands(&.{ end64, start64 })
                        .add_results(&.{i64t}).build();
                    self.append(sub);
                    const diff = sub.getResult(0);
                    // zext bool to i64
                    var z = OpBuilder.init("llvm.zext", self.loc).builder()
                        .add_operands(&.{incl_v})
                        .add_results(&.{i64t}).build();
                    self.append(z);
                    var add = OpBuilder.init("llvm.add", self.loc).builder()
                        .add_operands(&.{ diff, z.getResult(0) })
                        .add_results(&.{i64t}).build();
                    self.append(add);
                    const len64 = add.getResult(0);

                    // Build slice {ptr,len}
                    var acc = self.zeroOf(res_ty);
                    acc = self.insertAt(acc, data_ptr, &.{0});
                    acc = self.insertAt(acc, len64, &.{1});
                    break :blk acc;
                }

                // Indexing into a slice value (in-SSA): extract ptr and load *(ptr+idx)
                if (!self.isLlvmPtr(base.getType()) and store.getKind(base_sr_ty) == .Slice and res_sr_kind != .Slice) {
                    const elem_mlir = res_ty; // result type is the element type
                    const ptr0 = self.extractAt(base, self.llvm_ptr_ty, &.{0});
                    const vptr = try self.emitGep(ptr0, elem_mlir, &.{.{ .Value = p.index }});
                    var ld = OpBuilder.init("llvm.load", self.loc).builder()
                        .add_operands(&.{vptr})
                        .add_results(&.{res_ty}).build();
                    self.append(ld);
                    break :blk ld.getResult(0);
                }

                if (self.isLlvmPtr(base.getType())) {
                    const vptr = try self.emitGep(base, res_ty, &.{.{ .Value = p.index }});
                    var ld = OpBuilder.init("llvm.load", self.loc).builder()
                        .add_operands(&.{vptr})
                        .add_results(&.{res_ty}).build();
                    self.append(ld);
                    break :blk ld.getResult(0);
                } else {
                    // Always spill aggregate to memory and use pointer indexing for arrays
                    const base_ty = base.getType();
                    const tmp_ptr = self.spillAgg(base, base_ty, 0);
                    const vptr = try self.emitGep(tmp_ptr, res_ty, &.{.{ .Value = p.index }});
                    var ld = OpBuilder.init("llvm.load", self.loc).builder()
                        .add_operands(&.{vptr})
                        .add_results(&.{res_ty}).build();
                    self.append(ld);
                    break :blk ld.getResult(0);
                }
            },

            // ------------- Data movement -------------
            .Select => blk: {
                const p = t.instrs.get(.Select, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const c = self.value_map.get(p.cond).?;
                const tv = self.value_map.get(p.then_value).?;
                const ev = self.value_map.get(p.else_value).?;
                const ty = try self.llvmTypeOf(store, p.ty);
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

                const ret_ty = try self.llvmTypeOf(store, p.ty);
                const has_res = !ret_ty.equal(self.void_ty);

                var callAttrsList = ArrayList(mlir.NamedAttribute).init(self.gpa);

                defer callAttrsList.deinit();

                try callAttrsList.append(self.named("operand_segment_sizes", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ @as(i32, @intCast(args_slice.len + 1)), 0 })));

                try callAttrsList.append(self.named("op_bundle_sizes", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{})));

                var call = OpBuilder.init("llvm.call", self.loc).builder()
                    .add_operands(ops)
                    .add_results(if (has_res) &.{ret_ty} else &.{}).add_attributes(callAttrsList.items)
                    .build();
                self.append(call);
                break :blk if (has_res) call.getResult(0) else mlir.Value.empty();
            },
            .Call => blk: {
                const p = t.instrs.get(.Call, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const callee_name = t.instrs.strs.get(p.callee);

                const finfo = self.func_syms.get(callee_name) orelse try self.ensureFuncDeclFromCall(ins_id, t, store);

                const isExternLL = std.mem.eql(u8, finfo.op.getName().str().toSlice(), "llvm.func");

                // Gather SR arg types and MLIR values
                const args_slice = t.instrs.val_list_pool.slice(p.args);
                var src_vals = try self.gpa.alloc(mlir.Value, args_slice.len);
                defer self.gpa.free(src_vals);
                var src_sr = try self.gpa.alloc(types.TypeId, args_slice.len);
                defer self.gpa.free(src_sr);
                for (args_slice, 0..) |vid, i| {
                    src_vals[i] = self.value_map.get(vid).?;
                    src_sr[i] = self.srTypeOfValue(t, vid);
                }

                const want_res_sr = p.ty;
                const want_res_mlir = try self.llvmTypeOf(store, want_res_sr);
                const want_has_res = !self.void_ty.equal(want_res_mlir);

                if (!isExternLL) {
                    // Internal call: unchanged (func.call)
                    const attrs = [_]mlir.NamedAttribute{
                        self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.StringRef.from(callee_name))),
                    };
                    var call = OpBuilder.init("func.call", self.loc).builder()
                        .add_operands(src_vals)
                        .add_results(if (want_has_res) &.{want_res_mlir} else &.{})
                        .add_attributes(&attrs)
                        .build();
                    self.append(call);
                    break :blk if (want_has_res) call.getResult(0) else mlir.Value.empty();
                }

                // ===== Extern C call via llvm.func (ABI-lowered) =====

                // Handle sret (if any): if return is IndirectSRet, first argument becomes out pointer.
                const retClass = abi.abiClassifyX64SysV(self, store, want_res_sr, true);

                var lowered_ops = ArrayList(mlir.Value).init(self.gpa);
                defer lowered_ops.deinit();

                var retbuf: mlir.Value = mlir.Value.empty();
                if (store.getKind(want_res_sr) != .Void and retClass.kind == .IndirectSRet) {
                    // allocate result, pass as first arg
                    retbuf = self.spillAgg(self.undefOf(want_res_mlir), want_res_mlir, @intCast(retClass.alignment));
                    // The alloca above created memory; but we stored undef just to materialize it.
                    // Overwrite with real result after the call; passing the pointer now:
                    lowered_ops.append(retbuf) catch unreachable;
                }

                // Lower each argument
                for (src_vals, 0..) |v, i| {
                    const sr = src_sr[i];
                    const cls = abi.abiClassifyX64SysV(self, store, sr, false);

                    switch (cls.kind) {
                        .IndirectByVal => {
                            // build a temp, store agg, pass pointer
                            const stTy = try self.llvmTypeOf(store, sr);
                            const tmp = self.spillAgg(v, stTy, cls.alignment);
                            lowered_ops.append(tmp) catch unreachable;
                        },
                        .DirectScalar => {
                            const stTy = try self.llvmTypeOf(store, sr);
                            // If already scalar of right type, pass as-is.
                            if (!stTy.isAInteger() and !stTy.isAFloat() and !stTy.isAVector()) {
                                // aggregate -> pack
                                const tmp = self.spillAgg(v, stTy, 1);
                                // load scalar type (int/float/vector)
                                if (cls.scalar0.?.isAInteger()) {
                                    const bits = cls.scalar0.?.getIntegerBitwidth();
                                    const packed_v = self.loadIntAt(tmp, bits, 0);
                                    lowered_ops.append(packed_v) catch unreachable;
                                } else if (cls.scalar0.?.isAFloat()) {
                                    var ld = OpBuilder.init("llvm.load", self.loc).builder()
                                        .add_operands(&.{tmp})
                                        .add_results(&.{cls.scalar0.?}).build();
                                    self.append(ld);
                                    lowered_ops.append(ld.getResult(0)) catch unreachable;
                                } else {
                                    // vector (e.g., <2 x float>)
                                    var ld = OpBuilder.init("llvm.load", self.loc).builder()
                                        .add_operands(&.{tmp})
                                        .add_results(&.{cls.scalar0.?}).build();
                                    self.append(ld);
                                    lowered_ops.append(ld.getResult(0)) catch unreachable;
                                }
                            } else {
                                // v is already scalar (or vector); cast if widths differ
                                var passv = v;
                                if (stTy.isAInteger() and cls.scalar0.?.isAInteger() and stTy.getIntegerBitwidth() != cls.scalar0.?.getIntegerBitwidth()) {
                                    // zext/trunc to exact width (unsigned ok for arg passing)
                                    const fw = stTy.getIntegerBitwidth();
                                    const tw = cls.scalar0.?.getIntegerBitwidth();
                                    if (fw > tw) {
                                        var tr = OpBuilder.init("llvm.trunc", self.loc).builder()
                                            .add_operands(&.{v}).add_results(&.{cls.scalar0.?}).build();
                                        self.append(tr);
                                        passv = tr.getResult(0);
                                    } else if (fw < tw) {
                                        var ex = OpBuilder.init("llvm.zext", self.loc).builder()
                                            .add_operands(&.{v}).add_results(&.{cls.scalar0.?}).build();
                                        self.append(ex);
                                        passv = ex.getResult(0);
                                    }
                                }
                                lowered_ops.append(passv) catch unreachable;
                            }
                        },
                        .DirectPair => {
                            // spill -> load lo i64, hi iN
                            const stTy = try self.llvmTypeOf(store, sr);
                            const tmp = self.spillAgg(v, stTy, 1);
                            const lo = self.loadIntAt(tmp, 64, 0);
                            const hibits = cls.scalar1.?.getIntegerBitwidth();
                            const hi = self.loadIntAt(tmp, hibits, 8);
                            lowered_ops.append(lo) catch unreachable;
                            lowered_ops.append(hi) catch unreachable;
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

                if (finfo.is_variadic) {
                    const func_ty = finfo.op.getInherentAttributeByName(mlir.StringRef.from("function_type"));
                    callAttrsList.append(self.named("var_callee_type", func_ty)) catch unreachable;
                }
                var call = OpBuilder.init("llvm.call", self.loc).builder()
                    .add_operands(lowered_ops.items)
                    .add_results(if (store.getKind(want_res_sr) == .Void or retClass.kind == .IndirectSRet)
                        &.{}
                    else
                        &.{finfo.ret_type})
                    .add_attributes(callAttrsList.items)
                    .build();
                self.append(call);

                // Reconstruct desired result (structural) from ABI return
                if (store.getKind(want_res_sr) == .Void) break :blk mlir.Value.empty();

                switch (retClass.kind) {
                    .IndirectSRet => {
                        // load structural result from retbuf
                        var ld = OpBuilder.init("llvm.load", self.loc).builder()
                            .add_operands(&.{retbuf})
                            .add_results(&.{want_res_mlir}).build();
                        self.append(ld);
                        break :blk ld.getResult(0);
                    },
                    .DirectScalar => {
                        const rv = call.getResult(0);
                        // If caller expects a scalar too, just return it
                        if (want_res_mlir.isAInteger() or want_res_mlir.isAFloat() or want_res_mlir.isAVector()) {
                            break :blk rv;
                        }
                        // Caller expects an aggregate: write scalar into buffer and reload as struct
                        const tmp = self.spillAgg(self.undefOf(want_res_mlir), want_res_mlir, 1);
                        self.storeAt(tmp, rv, 0);
                        var ld2 = OpBuilder.init("llvm.load", self.loc).builder()
                            .add_operands(&.{tmp})
                            .add_results(&.{want_res_mlir}).build();
                        self.append(ld2);
                        break :blk ld2.getResult(0);
                    },
                    .DirectPair => {
                        // Return value is a literal LLVM struct {lo,hi}
                        const rv = call.getResult(0);
                        const loTy = retClass.scalar0.?;
                        const hiTy = retClass.scalar1.?;
                        // extract pieces
                        var ex0 = OpBuilder.init("llvm.extractvalue", self.loc).builder()
                            .add_operands(&.{rv})
                            .add_results(&.{loTy})
                            .add_attributes(&.{self.named("position", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, &[_]i64{0}))})
                            .build();
                        self.append(ex0);
                        var ex1 = OpBuilder.init("llvm.extractvalue", self.loc).builder()
                            .add_operands(&.{rv})
                            .add_results(&.{hiTy})
                            .add_attributes(&.{self.named("position", mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, &[_]i64{1}))})
                            .build();
                        self.append(ex1);
                        // write into tmp at offsets 0 and 8, then reload as structural
                        const tmp = self.spillAgg(self.undefOf(want_res_mlir), want_res_mlir, 1);
                        self.storeAt(tmp, ex0.getResult(0), 0);
                        self.storeAt(tmp, ex1.getResult(0), 8);
                        var ld3 = OpBuilder.init("llvm.load", self.loc).builder()
                            .add_operands(&.{tmp})
                            .add_results(&.{want_res_mlir}).build();
                        self.append(ld3);
                        break :blk ld3.getResult(0);
                    },
                    else => unreachable,
                }
            },
            .MlirBlock => blk: {
                const p = t.instrs.get(.MlirBlock, ins_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const mlir_text_raw = t.instrs.strs.get(p.text);
                const mlir_kind = p.kind;

                // NEW: handle arguments
                const arg_vids = t.instrs.value_pool.slice(p.args);
                if (mlir_kind == .Operation) {
                    const result_ty = if (p.result.isNone()) self.void_ty else try self.llvmTypeOf(store, p.ty);
                    const value = try self.emitInlineMlirOperation(mlir_text_raw, arg_vids, result_ty);
                    if (p.result.isNone()) {
                        break :blk mlir.Value.empty();
                    } else {
                        break :blk value;
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

                        var str_buf: std.ArrayList(u8) = .empty;
                        defer str_buf.deinit(self.gpa);
                        var sink = PrintBuffer{ .list = &str_buf, .allocator = self.gpa };
                        mlir_val.print(printCallback, &sink);

                        const owned = try str_buf.toOwnedSlice(self.gpa);
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
                    while (i < mlir_text_raw.len) {
                        if (mlir_text_raw[i] == '%') {
                            var j = i + 1;
                            var num: u32 = 0;
                            var num_len: u32 = 0;
                            while (j < mlir_text_raw.len and std.ascii.isDigit(mlir_text_raw[j])) {
                                num = num * 10 + (mlir_text_raw[j] - '0');
                                num_len += 1;
                                j += 1;
                            }

                            if (num_len > 0 and num < arg_names.items.len) {
                                try writer.writeAll(arg_names.items[num]);
                                i += num_len + 1;
                            } else {
                                try writer.writeByte(mlir_text_raw[i]);
                                i += 1;
                            }
                        } else {
                            try writer.writeByte(mlir_text_raw[i]);
                            i += 1;
                        }
                    }
                } else {
                    try mlir_text_list.appendSlice(self.gpa, mlir_text_raw);
                }
                const mlir_text = mlir_text_list.items;

                switch (mlir_kind) {
                    else => unreachable,
                    .Module => {
                        var parsed_module = mlir.Module.createParse(
                            self.mlir_ctx,
                            mlir.StringRef.from(mlir_text), // No stripping of braces
                        );
                        if (parsed_module.isNull()) {
                            std.debug.print("Error parsing inline MLIR module: {s}\n", .{mlir_text});
                            return error.MlirParseError;
                        }
                        // Merge the parsed module into the current module
                        var parsed_module_body = parsed_module.getBody();
                        parsed_module_body.detach();
                        var current_op = parsed_module_body.getFirstOperation();
                        while (!current_op.isNull()) {
                            const next_op = current_op.getNextInBlock();

                            const op_name_ref = current_op.getName().str();
                            if (std.mem.eql(u8, op_name_ref.toSlice(), "func.func")) {
                                const sym_name_attr = current_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
                                if (!sym_name_attr.isNull()) {
                                    const sym_name = sym_name_attr.stringAttrGetValue().toSlice();
                                    if (!self.func_syms.contains(sym_name)) {
                                        const func_type_attr = current_op.getInherentAttributeByName(mlir.StringRef.from("function_type"));
                                        const func_type = func_type_attr.typeAttrGetValue();
                                        const n_formals = func_type.getFunctionNumInputs();
                                        const n_results = func_type.getFunctionNumResults();
                                        const ret_type = if (n_results == 1) func_type.getFunctionResult(0) else self.void_ty;

                                        const info = FuncInfo{
                                            .op = current_op,
                                            .is_variadic = false, // func.func is not variadic in this context
                                            .n_formals = @intCast(n_formals),
                                            .ret_type = ret_type,
                                            .dbg_subprogram = null,
                                        };
                                        _ = try self.func_syms.put(sym_name, info);
                                    }
                                }
                            }

                            current_op.removeFromParent();
                            var body = self.module.getBody();
                            body.appendOwnedOperation(current_op);
                            current_op = next_op;
                        }
                        parsed_module.destroy();
                        break :blk mlir.Value.empty();
                    },
                    .Type => {
                        // Parse the MLIR type
                        var parsed_type = mlir.Type.parseGet(self.mlir_ctx, mlir.StringRef.from(mlir_text));
                        if (parsed_type.isNull()) {
                            std.debug.print("Error parsing inline MLIR type: {s}\n", .{mlir_text});
                            return error.MlirParseError;
                        }
                        // Type declarations don't produce SSA values, so return empty.
                        break :blk mlir.Value.empty();
                    },
                    .Attribute => {
                        // Parse the MLIR attribute
                        var parsed_attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(mlir_text));
                        if (parsed_attr.isNull()) {
                            std.debug.print("Error parsing inline MLIR attribute: {s}\n", .{mlir_text});
                            return error.MlirParseError;
                        }
                        // Attribute declarations don't produce SSA values, so return empty.
                        break :blk mlir.Value.empty();
                    },
                }
            },
        };
    }

    fn emitInlineMlirOperation(
        self: *MlirCodegen,
        mlir_text_raw: []const u8,
        arg_vids: []const tir.ValueId,
        result_ty: mlir.Type,
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
            var type_str_buf: std.ArrayList(u8) = .empty;
            defer type_str_buf.deinit(self.gpa);
            var sink = PrintBuffer{ .list = &type_str_buf, .allocator = self.gpa };
            ty.print(printCallback, &sink);
            try writer.writeAll(type_str_buf.items);
        }
        try writer.writeAll(")");

        const has_result = !result_ty.equal(self.void_ty);
        if (has_result) {
            try writer.writeAll(" -> ");
            var type_str_buf: std.ArrayList(u8) = .empty;
            defer type_str_buf.deinit(self.gpa);
            var sink = PrintBuffer{ .list = &type_str_buf, .allocator = self.gpa };
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
            var type_str_buf: std.ArrayList(u8) = .empty;
            defer type_str_buf.deinit(self.gpa);
            var sink = PrintBuffer{ .list = &type_str_buf, .allocator = self.gpa };
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
            std.debug.print("Error parsing inline MLIR func: {s}\n", .{func_str.items});
            return error.MlirParseError;
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
        var call = OpBuilder.init("func.call", self.loc).builder()
            .add_operands(arg_values.items)
            .add_results(if (has_result) &.{result_ty} else &.{}) //
            .add_attributes(&attrs)
            .build();
        self.append(call);

        if (has_result) {
            return call.getResult(0);
        } else {
            return mlir.Value.empty();
        }
    }

    fn emitCmp(
        self: *MlirCodegen,
        pred_u: []const u8, // for unsigned ints (ult, ule, ugt, uge)
        pred_s: []const u8, // for signed ints   (slt, sle, sgt, sge)
        pred_f: []const u8, // for floats        (oeq, one, olt, ole, ogt, oge, ...)
        p: tir.Rows.Bin2,
        t: *const tir.TIR,
        store: *types.TypeStore,
    ) !mlir.Value {
        const lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;

        if (self.isFloat(lhs.getType())) {
            var op = OpBuilder.init("arith.cmpf", self.loc).builder()
                .add_operands(&.{ lhs, rhs })
                .add_results(&.{self.i1_ty})
                .add_attributes(&.{self.named("predicate", self.arithCmpFPredAttr(pred_f))})
                .build();
            self.append(op);
            return op.getResult(0);
        } else {
            // Integers (signless). Signedness is semantic and comes from SR type.
            const unsigned = self.isUnsigned(store, self.srTypeOfValue(t, p.lhs));
            const pred = if (unsigned) pred_u else pred_s;

            var op = OpBuilder.init("arith.cmpi", self.loc).builder()
                .add_operands(&.{ lhs, rhs })
                .add_results(&.{self.i1_ty})
                .add_attributes(&.{self.named("predicate", self.arithCmpIPredAttr(pred))})
                .build();
            self.append(op);
            return op.getResult(0);
        }
    }

    fn emitTerminator(self: *MlirCodegen, term_id: tir.TermId, t: *const tir.TIR, _: *types.TypeStore) !void {
        const kind = t.terms.index.kinds.items[term_id.toRaw()];

        switch (kind) {
            .Return => {
                const p = t.terms.get(.Return, term_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                var func_op = self.cur_block.?.getParentOperation();
                var name_attr = func_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
                const finfo = self.func_syms.get(name_attr.stringAttrGetValue().toSlice()).?;
                const ret_ty = finfo.ret_type;

                var retop: mlir.Operation = undefined;
                if (!p.value.isNone()) {
                    const maybe_v = self.value_map.get(p.value.unwrap());
                    const v = if (maybe_v) |mv| mv else self.zeroOf(ret_ty);
                    if (ret_ty.equal(self.void_ty)) {
                        retop = OpBuilder.init("func.return", self.loc).builder().build();
                    } else {
                        retop = OpBuilder.init("func.return", self.loc).builder()
                            .add_operands(&.{v}).build();
                    }
                } else {
                    if (!ret_ty.equal(self.void_ty)) {
                        // Synthesize a zero value to satisfy non-void return paths.
                        const z = self.zeroOf(ret_ty);
                        retop = OpBuilder.init("func.return", self.loc).builder()
                            .add_operands(&.{z}).build();
                    } else {
                        retop = OpBuilder.init("func.return", self.loc).builder().build();
                    }
                }
                self.append(retop);
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

                const br = OpBuilder.init("cf.br", self.loc).builder()
                    .add_operands(argv)
                    .add_successors(&.{dest})
                    .build();
                self.append(br);
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

                const br = OpBuilder.init("cf.cond_br", self.loc).builder()
                    .add_operands(ops)
                    .add_successors(&.{ tdest, edest })
                    .add_attributes(&.{self.named("operand_segment_sizes", seg)})
                    .build();
                self.append(br);
            },

            .SwitchInt => {
                std.debug.panic("Not Implemented, Switch Int", .{});
            },

            .Unreachable => {
                const p = t.terms.get(.Unreachable, term_id);
                const prev_loc = self.pushLocation(p.loc);
                defer self.loc = prev_loc;
                const op = OpBuilder.init("llvm.unreachable", self.loc).builder().build();
                self.append(op);
            },
        }
    }

    fn emitGep(
        self: *MlirCodegen,
        base: mlir.Value,
        elem_ty: mlir.Type,
        idxs: []const tir.Rows.GepIndex,
    ) !mlir.Value {
        const dyn_min = std.math.minInt(i32);
        var dyn = try self.gpa.alloc(mlir.Value, idxs.len);
        defer self.gpa.free(dyn);
        var raw = try self.gpa.alloc(i32, idxs.len);
        defer self.gpa.free(raw);

        var ndyn: usize = 0;
        for (idxs, 0..) |g, i| {
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

        ops[0] = base;
        for (dyn[0..ndyn], 0..) |v, i| ops[1 + i] = v;

        var op = OpBuilder.init("llvm.getelementptr", self.loc).builder()
            .add_operands(ops)
            .add_results(&.{self.llvm_ptr_ty})
            .add_attributes(&.{
                self.named("elem_type", mlir.Attribute.typeAttrGet(elem_ty)),

                self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, raw)),
            }).build();

        self.append(op);

        return op.getResult(0);
    }

    // ----------------------------------------------------------------
    // Helpers
    // ----------------------------------------------------------------
    fn isInt(self: *const MlirCodegen, t: mlir.Type) bool {
        _ = self;
        return t.isAInteger();
    }

    fn isFloat(self: *const MlirCodegen, t: mlir.Type) bool {
        _ = self;
        return t.isAFloat();
    }

    fn intBitWidth(t: mlir.Type) u32 {
        return t.getIntegerBitwidth();
    }

    // Pick signedness from SR type; default to signed if unknown.
    fn isSrcSigned(self: *MlirCodegen, store: *types.TypeStore, sr_ty: types.TypeId) bool {
        return self.isSignedInt(store, sr_ty);
    }
    fn arithCmpIPredAttr(self: *MlirCodegen, pred: []const u8) mlir.Attribute {
        const val: i64 = if (std.mem.eql(u8, pred, "eq")) 0 else if (std.mem.eql(u8, pred, "ne")) 1 else if (std.mem.eql(u8, pred, "slt")) 2 else if (std.mem.eql(u8, pred, "sle")) 3 else if (std.mem.eql(u8, pred, "sgt")) 4 else if (std.mem.eql(u8, pred, "sge")) 5 else if (std.mem.eql(u8, pred, "ult")) 6 else if (std.mem.eql(u8, pred, "ule")) 7 else if (std.mem.eql(u8, pred, "ugt")) 8 else if (std.mem.eql(u8, pred, "uge")) 9 else unreachable;
        return mlir.Attribute.integerAttrGet(self.i64_ty, val);
    }
    fn arithCmpFPredAttr(self: *MlirCodegen, pred: []const u8) mlir.Attribute {
        const val: i64 = if (std.mem.eql(u8, pred, "false")) 0 else if (std.mem.eql(u8, pred, "oeq"))
            1
        else if (std.mem.eql(u8, pred, "ogt")) 2 else if (std.mem.eql(u8, pred, "oge"))
            3
        else if (std.mem.eql(u8, pred, "olt")) 4 else if (std.mem.eql(u8, pred, "ole")) 5 else if (std.mem.eql(u8, pred, "one")) 6 else if (std.mem.eql(u8, pred, "ord")) 7 else if (std.mem.eql(u8, pred, "ueq")) 8 else if (std.mem.eql(u8, pred, "ugt")) 9 else if (std.mem.eql(u8, pred, "uge")) 10 else if (std.mem.eql(u8, pred, "ult"))
            11
        else if (std.mem.eql(u8, pred, "ule")) 12 else if (std.mem.eql(u8, pred, "une"))
            13
        else if (std.mem.eql(u8, pred, "uno")) 14 else if (std.mem.eql(u8, pred, "true")) 15 else unreachable;
        return mlir.Attribute.integerAttrGet(self.i64_ty, val);
    }
    fn append(self: *MlirCodegen, op: mlir.Operation) void {
        self.cur_block.?.appendOwnedOperation(op);
    }
    fn named(self: *const MlirCodegen, name: []const u8, attr: mlir.Attribute) mlir.NamedAttribute {
        return .{
            .inner = .{
                .name = mlir.c.mlirIdentifierGet(self.mlir_ctx.handle, mlir.StringRef.from(name).inner),
                .attribute = attr.handle,
            },
        };
    }
    fn strAttr(self: *const MlirCodegen, s: []const u8) mlir.Attribute {
        return mlir.Attribute.stringAttrGet(self.mlir_ctx, mlir.StringRef.from(s));
    }
    fn intAttr(self: *const MlirCodegen, ty: mlir.Type, val: i64) mlir.Attribute {
        _ = self;
        return mlir.Attribute.integerAttrGet(ty, val);
    }

    fn isLlvmPtr(self: *const MlirCodegen, ty: mlir.Type) bool {
        return ty.equal(self.llvm_ptr_ty);
    }

    fn zeroOf(self: *MlirCodegen, ty: mlir.Type) mlir.Value {
        var op = OpBuilder.init("llvm.mlir.zero", self.loc).builder()
            .add_results(&.{ty})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn llvmConstI64(self: *MlirCodegen, x: i64) mlir.Value {
        const val = mlir.Attribute.integerAttrGet(self.i64_ty, x);
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{self.i64_ty})
            .add_attributes(&.{self.named("value", val)}).build();
        self.append(op);
        return op.getResult(0);
    }
    fn llvmConstI32(self: *MlirCodegen, x: i32) mlir.Value {
        const ty = mlir.Type.getSignlessIntegerType(self.mlir_ctx, 32);
        const val = mlir.Attribute.integerAttrGet(ty, x);
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{ty})
            .add_attributes(&.{self.named("value", val)}).build();
        self.append(op);
        return op.getResult(0);
    }
    fn llvmNullPtr(self: *MlirCodegen) mlir.Value {
        // Create a null pointer via constant integer 0 casted to ptr
        const zero = self.llvmConstI64(0);
        var op = OpBuilder.init("llvm.inttoptr", self.loc).builder()
            .add_operands(&.{zero})
            .add_results(&.{self.llvm_ptr_ty}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn undefOf(self: *MlirCodegen, ty: mlir.Type) mlir.Value {
        var op = OpBuilder.init("llvm.mlir.undef", self.loc).builder()
            .add_results(&.{ty}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn insertAt(self: *MlirCodegen, agg: mlir.Value, val: mlir.Value, pos: []const i64) mlir.Value {
        const pos_attr = mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, pos);
        var op = OpBuilder.init("llvm.insertvalue", self.loc).builder()
            // Builder expects (container, value)
            .add_operands(&.{ agg, val })
            .add_results(&.{agg.getType()})
            .add_attributes(&.{self.named("position", pos_attr)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn extractAt(self: *MlirCodegen, agg: mlir.Value, res_ty: mlir.Type, pos: []const i64) mlir.Value {
        // If the source is a pointer, load the requested type directly. This avoids
        // invalid extractvalue-on-pointer and matches our opaque-pointer lowering model.
        if (mlir.LLVM.isLLVMPointerType(agg.getType())) {
            var ld = OpBuilder.init("llvm.load", self.loc).builder()
                .add_operands(&.{agg})
                .add_results(&.{res_ty})
                .build();
            self.append(ld);
            return ld.getResult(0);
        }
        const pos_attr = mlir.Attribute.denseI64ArrayGet(self.mlir_ctx, pos);
        var op = OpBuilder.init("llvm.extractvalue", self.loc).builder()
            .add_operands(&.{agg})
            .add_results(&.{res_ty})
            .add_attributes(&.{self.named("position", pos_attr)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    // Spill an aggregate SSA to memory (%tmp = alloca T ; store T %v, %tmp)
    fn spillAgg(self: *MlirCodegen, aggVal: mlir.Value, elemTy: mlir.Type, alignment: u32) mlir.Value {
        _ = alignment;
        var attrs = [_]mlir.NamedAttribute{
            self.named("elem_type", mlir.Attribute.typeAttrGet(elemTy)),
        };
        // one element
        var a = OpBuilder.init("llvm.alloca", self.loc).builder()
            .add_operands(&.{self.llvmConstI64(1)})
            .add_results(&.{self.llvm_ptr_ty})
            .add_attributes(&attrs).build();
        self.append(a);
        const st = OpBuilder.init("llvm.store", self.loc).builder()
            .add_operands(&.{ aggVal, a.getResult(0) }).build();
        self.append(st);
        return a.getResult(0);
    }

    // Load iN from ptr + offset
    fn loadIntAt(self: *MlirCodegen, base: mlir.Value, bits: u32, offset: usize) mlir.Value {
        const ity = mlir.Type.getSignlessIntegerType(self.mlir_ctx, bits);
        var p = base;
        if (offset != 0) {
            const offv = self.constInt(self.i64_ty, @intCast(offset));
            var gep = OpBuilder.init("llvm.getelementptr", self.loc).builder()
                .add_operands(&.{ base, offv })
                .add_results(&.{self.llvm_ptr_ty})
                .add_attributes(&.{
                    self.named("elem_type", mlir.Attribute.typeAttrGet(self.i8_ty)),
                    self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{std.math.minInt(i32)})),
                }) // byte-wise GEP with dynamic index marker
                .build();
            self.append(gep);
            p = gep.getResult(0);
        }
        var ld = OpBuilder.init("llvm.load", self.loc).builder()
            .add_operands(&.{p})
            .add_results(&.{ity}).build();
        self.append(ld);
        return ld.getResult(0);
    }

    // Store scalar at ptr + offset
    fn storeAt(self: *MlirCodegen, base: mlir.Value, val: mlir.Value, offset: usize) void {
        var p = base;
        if (offset != 0) {
            const offv = self.constInt(self.i64_ty, @intCast(offset));
            var gep = OpBuilder.init("llvm.getelementptr", self.loc).builder()
                .add_operands(&.{ base, offv })
                .add_results(&.{self.llvm_ptr_ty})
                .add_attributes(&.{
                    self.named("elem_type", mlir.Attribute.typeAttrGet(self.i8_ty)),
                    self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{std.math.minInt(i32)})),
                })
                .build();
            self.append(gep);
            p = gep.getResult(0);
        }
        const st = OpBuilder.init("llvm.store", self.loc).builder()
            .add_operands(&.{ val, p }).build();
        self.append(st);
    }

    fn constInt(self: *MlirCodegen, ty: mlir.Type, v: i128) mlir.Value {
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{ty})
            .add_attributes(&.{self.named("value", mlir.Attribute.integerAttrGet(ty, @intCast(v)))}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn constFloat(self: *MlirCodegen, ty: mlir.Type, v: f64) mlir.Value {
        const attr = mlir.Attribute.floatAttrDoubleGet(self.mlir_ctx, ty, v);
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{ty})
            .add_attributes(&.{self.named("value", attr)}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn constBool(self: *MlirCodegen, v: bool) mlir.Value {
        return self.constInt(self.i1_ty, if (v) 1 else 0);
    }

    fn isUnsigned(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) bool {
        _ = self;
        return switch (store.getKind(ty)) {
            .U8, .U16, .U32, .U64, .Usize => true,
            else => false,
        };
    }

    fn isFloatType(self: *MlirCodegen, t: mlir.Type) bool {
        _ = self;
        return t.isAFloat();
    }
    fn isIntType(self: *MlirCodegen, t: mlir.Type) bool {
        _ = self;
        return t.isAInteger();
    }

    fn intOrFloatWidth(t: mlir.Type) !u32 {
        if (t.isAInteger()) return t.getIntegerBitwidth();
        if (t.isAFloat()) return t.getFloatBitwidth();
        return error.NotIntOrFloat;
    }

    fn binArith(
        self: *MlirCodegen,
        intName: []const u8, // caller passes "llvm.add"|"llvm.sub"|"llvm.mul"
        floatName: []const u8, // caller passes "llvm.fadd"|"llvm.fsub"|"llvm.fmul"
        p: tir.Rows.Bin2,
        store: *types.TypeStore,
    ) !mlir.Value {
        const lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;
        const ty = try self.llvmTypeOf(store, p.ty);

        // Infer which of {add,sub,mul} from the names you already pass.
        const is_add = std.mem.eql(u8, intName, "llvm.add") and std.mem.eql(u8, floatName, "llvm.fadd");
        const is_sub = std.mem.eql(u8, intName, "llvm.sub") and std.mem.eql(u8, floatName, "llvm.fsub");
        // const is_mul = std.mem.eql(u8, intName, "llvm.mul") and std.mem.eql(u8, floatName, "llvm.fmul");
        //
        const op_name = if (lhs.getType().isAFloat())
            (if (is_add) "arith.addf" else if (is_sub) "arith.subf" else "arith.mulf")
        else
            (if (is_add) "arith.addi" else if (is_sub) "arith.subi" else "arith.muli");

        var op = OpBuilder.init(op_name, self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{ty})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn extendIntegerValue(self: *MlirCodegen, v: mlir.Value, signed: bool, to_ty: mlir.Type) mlir.Value {
        const from_ty = v.getType();
        const from_w = intOrFloatWidth(from_ty) catch 0;
        const to_w = intOrFloatWidth(to_ty) catch 0;
        if (from_w >= to_w) return v;
        const opname = if (signed) "arith.extsi" else "arith.extui";
        var op = OpBuilder.init(opname, self.loc).builder()
            .add_operands(&.{v})
            .add_results(&.{to_ty}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn emitSaturatingIntBinary(
        self: *MlirCodegen,
        p: tir.Rows.Bin2,
        store: *types.TypeStore,
        arith_name: []const u8,
        rhs_uses_lhs_sign: bool,
    ) !mlir.Value {
        const kind = store.getKind(p.ty);
        std.debug.assert(switch (kind) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
            else => false,
        });

        const lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;
        const res_ty = try self.llvmTypeOf(store, p.ty);
        const base_width = intOrFloatWidth(res_ty) catch unreachable;
        std.debug.assert(base_width > 0);
        const wide_width = base_width * 2;
        const ext_ty = mlir.Type.getSignlessIntegerType(self.mlir_ctx, @intCast(wide_width));

        const lhs_signed = self.isSignedInt(store, p.ty);
        const rhs_signed = if (rhs_uses_lhs_sign) lhs_signed else false;

        const lhs_ext = self.extendIntegerValue(lhs, lhs_signed, ext_ty);
        const rhs_ext = self.extendIntegerValue(rhs, rhs_signed, ext_ty);

        var op = OpBuilder.init(arith_name, self.loc).builder()
            .add_operands(&.{ lhs_ext, rhs_ext })
            .add_results(&.{ext_ty}).build();
        self.append(op);
        const wide = op.getResult(0);
        return self.saturateIntToInt(wide, lhs_signed, res_ty, lhs_signed);
    }

    fn binBit(
        self: *MlirCodegen,
        name_hint: []const u8, // caller passes "llvm.and"|"llvm.or"|"llvm.xor"
        p: tir.Rows.Bin2,
        store: *types.TypeStore,
    ) !mlir.Value {
        const lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;
        const ty = try self.llvmTypeOf(store, p.ty);

        const is_and = std.mem.eql(u8, name_hint, "llvm.and");
        const is_or = std.mem.eql(u8, name_hint, "llvm.or");
        const op_name = if (is_and) "arith.andi" else if (is_or) "arith.ori" else "arith.xori";

        var op = OpBuilder.init(op_name, self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{ty})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn arithDiv(self: *MlirCodegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type, signed: bool) mlir.Value {
        const op_name = if (lhs.getType().isAFloat()) "arith.divf" else (if (signed) "arith.divsi" else "arith.divui");
        var op = OpBuilder.init(op_name, self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{res_ty}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn arithRem(self: *MlirCodegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type, signed: bool) mlir.Value {
        const op_name = if (lhs.getType().isAFloat()) "arith.remf" else (if (signed) "arith.remsi" else "arith.remui");
        var op = OpBuilder.init(op_name, self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{res_ty}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn arithShl(self: *MlirCodegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type) mlir.Value {
        var op = OpBuilder.init("arith.shli", self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{res_ty}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn arithShr(self: *MlirCodegen, lhs: mlir.Value, rhs: mlir.Value, res_ty: mlir.Type, signed: bool) mlir.Value {
        const op_name = if (signed) "arith.shrsi" else "arith.shrui";
        var op = OpBuilder.init(op_name, self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{res_ty}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn arithLogicalNotI1(self: *MlirCodegen, v: mlir.Value) mlir.Value {
        // !v  ==  xori v, true
        var op = OpBuilder.init("arith.xori", self.loc).builder()
            .add_operands(&.{ v, self.constBool(true) })
            .add_results(&.{self.i1_ty}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn arithSelect(self: *MlirCodegen, c: mlir.Value, tv: mlir.Value, ev: mlir.Value, res_ty: mlir.Type) mlir.Value {
        var op = OpBuilder.init("arith.select", self.loc).builder()
            .add_operands(&.{ c, tv, ev })
            .add_results(&.{res_ty}).build();
        self.append(op);
        return op.getResult(0);
    }

    fn ensureDeclFromCall(self: *MlirCodegen, ins_id: tir.InstrId, t: *const tir.TIR, store: *types.TypeStore) !FuncInfo {
        const p = t.instrs.get(.Call, ins_id);
        const args_slice = t.instrs.val_list_pool.slice(p.args);
        var arg_tys = try self.gpa.alloc(mlir.Type, args_slice.len);
        defer self.gpa.free(arg_tys);
        for (args_slice, 0..) |vid, i| arg_tys[i] = self.value_map.get(vid).?.getType();
        const ret_ty = try self.llvmTypeOf(store, p.ty);
        const fn_ty = mlir.LLVM.getLLVMFunctionType(ret_ty, arg_tys, true);
        const name = t.instrs.strs.get(p.callee);

        if (std.mem.startsWith(u8, name, "m$")) {
            return .{
                .op = self.module.getOperation(),
                .is_variadic = false,
                .n_formals = arg_tys.len,
                .ret_type = ret_ty,
                .dbg_subprogram = null,
            };
        }

        const attrs = [_]mlir.NamedAttribute{
            self.named("sym_name", self.strAttr(name)),
            self.named("function_type", mlir.Attribute.typeAttrGet(fn_ty)),
            self.named("sym_visibility", self.strAttr("private")),
        };
        const region = mlir.Region.create();
        const func_op = OpBuilder.init("llvm.func", self.loc).builder()
            .add_attributes(&attrs)
            .add_regions(&.{region}).build();
        var body = self.module.getBody();
        body.appendOwnedOperation(func_op);

        const info: FuncInfo = .{
            .op = func_op,
            .is_variadic = false,
            .n_formals = arg_tys.len,
            .ret_type = ret_ty,
            .dbg_subprogram = null,
        };
        _ = try self.func_syms.put(name, info);
        return info;
    }

    fn constStringPtr(self: *MlirCodegen, text: []const u8) !mlir.Operation {
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

    fn addrOfFirstCharLen(self: *MlirCodegen, global_op: *mlir.Operation, n_bytes: usize) !mlir.Operation {
        // &@global
        const name_attr = global_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
        const gsym = mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.Attribute.stringAttrGetValue(name_attr));

        var addr = OpBuilder.init("llvm.mlir.addressof", self.loc).builder()
            .add_results(&.{self.llvm_ptr_ty})
            .add_attributes(&.{self.named("global_name", gsym)})
            .build();
        self.append(addr);

        // GEP 0,0 into [n x i8] to get pointer to first char
        const arr_ty = mlir.LLVM.getLLVMArrayType(self.i8_ty, @intCast(n_bytes));
        const gep = OpBuilder.init("llvm.getelementptr", self.loc).builder()
            .add_operands(&.{addr.getResult(0)})
            .add_results(&.{self.llvm_ptr_ty})
            .add_attributes(&.{
                self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.mlir_ctx, &[_]i32{ 0, 0 })),
                self.named("elem_type", mlir.Attribute.typeAttrGet(arr_ty)),
            })
            .build();
        self.append(gep);
        return gep;
    }

    fn escapeForMlirString(self: *MlirCodegen, s: []const u8) ![]u8 {
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

    fn typeIsAny(_: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) bool {
        return switch (store.getKind(ty)) {
            .Any => true,
            else => false,
        };
    }

    fn intWidth(_: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) u32 {
        return switch (store.getKind(ty)) {
            .I8, .U8 => 8,
            .I16, .U16 => 16,
            .I32, .U32 => 32,
            .I64, .U64 => 64,
            .Usize => 64, // TODO: target-specific
            else => 0,
        };
    }

    fn isSignedInt(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) bool {
        _ = self;
        return switch (store.getKind(ty)) {
            .I8, .I16, .I32, .I64 => true,
            else => false,
        };
    }

    fn srTypeOfValue(self: *MlirCodegen, t: *const tir.TIR, vid: tir.ValueId) types.TypeId {
        if (self.val_types.get(vid)) |ty| return ty;
        // fallback: if unknown, prefer signed behavior
        _ = t;
        return types.TypeId.fromRaw(0);
    }

    fn constIntOf(self: *MlirCodegen, t: *const tir.TIR, vid: tir.ValueId) ?u64 {
        if (self.def_instr.get(vid)) |iid| {
            const k = t.instrs.index.kinds.items[iid.toRaw()];
            if (k == .ConstInt) {
                const row = t.instrs.get(.ConstInt, iid);
                return row.value;
            }
        }
        return null;
    }

    const AggregateElemCoercer = fn (
        *MlirCodegen,
        *types.TypeStore,
        types.TypeId,
        mlir.Type,
        mlir.Value,
        types.TypeId,
    ) anyerror!mlir.Value;

    fn isAggregateKind(kind: types.TypeKind) bool {
        return switch (kind) {
            .Struct, .Tuple, .Array, .Optional, .Union, .ErrorSet, .Error => true,
            else => false,
        };
    }

    fn tryCopyAggregateValue(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
        elem_coercer: AggregateElemCoercer,
    ) anyerror!?mlir.Value {
        const dst_kind = store.getKind(dst_sr);
        const src_kind = store.getKind(src_sr);
        if (!isAggregateKind(dst_kind) or !isAggregateKind(src_kind)) return null;

        switch (dst_kind) {
            .Array => if (src_kind == .Array)
                return self.copyArrayAggregate(store, dst_sr, dst_ty, src_val, src_sr, elem_coercer),
            .Struct => if (src_kind == .Struct)
                return self.copyStructAggregate(store, dst_sr, dst_ty, src_val, src_sr, elem_coercer),
            .Tuple => if (src_kind == .Tuple)
                return self.copyTupleAggregate(store, dst_sr, dst_ty, src_val, src_sr, elem_coercer),
            .Optional => if (src_kind == .Optional)
                return self.copyOptionalAggregate(store, dst_sr, dst_ty, src_val, src_sr, elem_coercer),
            .Union => if (src_kind == .Union)
                return self.copyUnionAggregate(store, dst_sr, dst_ty, src_val, src_sr),
            .ErrorSet => if (src_kind == .ErrorSet)
                return self.copyErrorSetAggregate(store, dst_sr, dst_ty, src_val, src_sr, elem_coercer),
            .Error => if (src_kind == .ErrorSet)
                return self.copyErrorAggregate(store, dst_sr, dst_ty, src_val, src_sr, elem_coercer),
            else => {},
        }

        return null;
    }

    fn copyErrorAggregate(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
        elem_coercer: AggregateElemCoercer,
    ) anyerror!?mlir.Value {
        const dst_info = store.get(.Error, dst_sr);
        const src_info = store.get(.Error, src_sr);

        const dst_variants = store.field_pool.slice(dst_info.variants);
        const src_variants = store.field_pool.slice(src_info.variants);
        if (dst_variants.len != src_variants.len) return null;

        var dst_union_fields = try self.gpa.alloc(types.TypeStore.StructFieldArg, dst_variants.len);
        defer self.gpa.free(dst_union_fields);
        var src_union_fields = try self.gpa.alloc(types.TypeStore.StructFieldArg, src_variants.len);
        defer self.gpa.free(src_union_fields);

        for (dst_variants, 0..) |dst_field_id, i| {
            const src_field_id = src_variants[i];
            const dst_field = store.Field.get(dst_field_id);
            const src_field = store.Field.get(src_field_id);
            if (dst_field.name.toRaw() != src_field.name.toRaw()) return null;
            dst_union_fields[i] = .{ .name = dst_field.name, .ty = dst_field.ty };
            src_union_fields[i] = .{ .name = src_field.name, .ty = src_field.ty };
        }

        const dst_union_sr = store.mkUnion(dst_union_fields);
        const src_union_sr = store.mkUnion(src_union_fields);
        const dst_union_ty = try self.llvmTypeOf(store, dst_union_sr);
        const src_union_ty = try self.llvmTypeOf(store, src_union_sr);

        const tag = self.extractAt(src_val, self.i32_ty, &.{0});
        const src_payload = self.extractAt(src_val, src_union_ty, &.{1});

        var payload = try self.tryCopyAggregateValue(store, dst_union_sr, dst_union_ty, src_payload, src_union_sr, elem_coercer) orelse src_payload;
        if (!payload.getType().equal(dst_union_ty)) {
            payload = try elem_coercer(self, store, dst_union_sr, dst_union_ty, payload, src_union_sr);
        }

        var result = self.undefOf(dst_ty);
        result = self.insertAt(result, tag, &.{0});
        result = self.insertAt(result, payload, &.{1});
        return result;
    }

    fn copyArrayAggregate(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
        elem_coercer: AggregateElemCoercer,
    ) anyerror!?mlir.Value {
        const dst_info = store.get(.Array, dst_sr);
        const src_info = store.get(.Array, src_sr);
        if (dst_info.len != src_info.len) return null;

        const dst_elem_ty = try self.llvmTypeOf(store, dst_info.elem);
        const src_elem_ty = try self.llvmTypeOf(store, src_info.elem);

        var result = self.undefOf(dst_ty);
        var i: usize = 0;
        while (i < dst_info.len) : (i += 1) {
            const idx = [_]i64{@intCast(i)};
            const elem_val = self.extractAt(src_val, src_elem_ty, &idx);
            const coerced = try elem_coercer(self, store, dst_info.elem, dst_elem_ty, elem_val, src_info.elem);
            result = self.insertAt(result, coerced, &idx);
        }
        return result;
    }

    fn copyStructAggregate(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
        elem_coercer: AggregateElemCoercer,
    ) anyerror!?mlir.Value {
        const dst_info = store.get(.Struct, dst_sr);
        const src_info = store.get(.Struct, src_sr);
        if (dst_info.fields.len != src_info.fields.len) return null;

        const dst_fields = store.field_pool.slice(dst_info.fields);
        const src_fields = store.field_pool.slice(src_info.fields);

        var result = self.undefOf(dst_ty);
        for (dst_fields, 0..) |dst_field_id, i| {
            const src_field_id = src_fields[i];
            const dst_field = store.Field.get(dst_field_id);
            const src_field = store.Field.get(src_field_id);
            const dst_field_ty = try self.llvmTypeOf(store, dst_field.ty);
            const src_field_ty = try self.llvmTypeOf(store, src_field.ty);
            const idx = [_]i64{@intCast(i)};
            const field_val = self.extractAt(src_val, src_field_ty, &idx);
            const coerced = try elem_coercer(self, store, dst_field.ty, dst_field_ty, field_val, src_field.ty);
            result = self.insertAt(result, coerced, &idx);
        }
        return result;
    }

    fn copyTupleAggregate(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
        elem_coercer: AggregateElemCoercer,
    ) anyerror!?mlir.Value {
        const dst_info = store.get(.Tuple, dst_sr);
        const src_info = store.get(.Tuple, src_sr);
        if (dst_info.elems.len != src_info.elems.len) return null;

        const dst_elems = store.type_pool.slice(dst_info.elems);
        const src_elems = store.type_pool.slice(src_info.elems);

        var result = self.undefOf(dst_ty);
        for (dst_elems, 0..) |dst_elem_sr, i| {
            const src_elem_sr = src_elems[i];
            const dst_elem_ty = try self.llvmTypeOf(store, dst_elem_sr);
            const src_elem_ty = try self.llvmTypeOf(store, src_elem_sr);
            const idx = [_]i64{@intCast(i)};
            const elem_val = self.extractAt(src_val, src_elem_ty, &idx);
            const coerced = try elem_coercer(self, store, dst_elem_sr, dst_elem_ty, elem_val, src_elem_sr);
            result = self.insertAt(result, coerced, &idx);
        }
        return result;
    }

    fn copyOptionalAggregate(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
        elem_coercer: AggregateElemCoercer,
    ) anyerror!?mlir.Value {
        const dst_info = store.get(.Optional, dst_sr);
        const src_info = store.get(.Optional, src_sr);
        const dst_payload_ty = try self.llvmTypeOf(store, dst_info.elem);
        const src_payload_ty = try self.llvmTypeOf(store, src_info.elem);

        const tag = self.extractAt(src_val, self.i1_ty, &.{0});
        const src_payload = self.extractAt(src_val, src_payload_ty, &.{1});
        const coerced_payload = try elem_coercer(self, store, dst_info.elem, dst_payload_ty, src_payload, src_info.elem);

        var result = self.undefOf(dst_ty);
        result = self.insertAt(result, tag, &.{0});
        result = self.insertAt(result, coerced_payload, &.{1});
        return result;
    }

    fn copyUnionAggregate(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
    ) anyerror!?mlir.Value {
        const dst_size = abi.abiSizeAlign(self, store, dst_sr).size;
        const src_size = abi.abiSizeAlign(self, store, src_sr).size;
        if (dst_size != src_size) return null;

        var result = self.undefOf(dst_ty);
        var i: usize = 0;
        while (i < dst_size) : (i += 1) {
            const idx = [_]i64{@intCast(i)};
            const byte_val = self.extractAt(src_val, self.i8_ty, &idx);
            result = self.insertAt(result, byte_val, &idx);
        }
        return result;
    }

    fn copyErrorSetAggregate(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
        elem_coercer: AggregateElemCoercer,
    ) anyerror!?mlir.Value {
        const dst_info = store.get(.ErrorSet, dst_sr);
        const src_info = store.get(.ErrorSet, src_sr);

        const ok_name = store.strs.intern("Ok");
        const err_name = store.strs.intern("Err");

        var dst_union_fields = [_]types.TypeStore.StructFieldArg{
            .{ .name = ok_name, .ty = dst_info.value_ty },
            .{ .name = err_name, .ty = dst_info.error_ty },
        };
        var src_union_fields = [_]types.TypeStore.StructFieldArg{
            .{ .name = ok_name, .ty = src_info.value_ty },
            .{ .name = err_name, .ty = src_info.error_ty },
        };

        const dst_union_sr = store.mkUnion(&dst_union_fields);
        const src_union_sr = store.mkUnion(&src_union_fields);
        const dst_union_ty = try self.llvmTypeOf(store, dst_union_sr);
        const src_union_ty = try self.llvmTypeOf(store, src_union_sr);

        const tag = self.extractAt(src_val, self.i32_ty, &.{0});
        const src_payload = self.extractAt(src_val, src_union_ty, &.{1});
        const coerced_payload = try self.tryCopyAggregateValue(store, dst_union_sr, dst_union_ty, src_payload, src_union_sr, elem_coercer) orelse src_payload;

        var result = self.undefOf(dst_ty);
        result = self.insertAt(result, tag, &.{0});
        result = self.insertAt(result, coerced_payload, &.{1});
        return result;
    }

    fn reinterpretAggregateViaSpill(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
    ) anyerror!?mlir.Value {
        if (dst_sr.toRaw() == 0 or src_sr.toRaw() == 0) return null;

        const dst_kind = store.getKind(dst_sr);
        const src_kind = store.getKind(src_sr);
        if (!isAggregateKind(dst_kind) and !isAggregateKind(src_kind)) return null;

        const dst_layout = abi.abiSizeAlign(self, store, dst_sr);
        const src_layout = abi.abiSizeAlign(self, store, src_sr);

        const src_ptr = self.spillAgg(src_val, src_val.getType(), 0);
        const dst_init = self.zeroOf(dst_ty);
        const dst_ptr = self.spillAgg(dst_init, dst_ty, 0);

        const copy_len = if (dst_layout.size < src_layout.size) dst_layout.size else src_layout.size;
        var i: usize = 0;
        while (i < copy_len) : (i += 1) {
            const byte = self.loadIntAt(src_ptr, 8, i);
            self.storeAt(dst_ptr, byte, i);
        }

        var ld = OpBuilder.init("llvm.load", self.loc).builder()
            .add_operands(&.{dst_ptr}).add_results(&.{dst_ty}).build();
        self.append(ld);
        return ld.getResult(0);
    }

    fn coerceAggregateElementOnBranch(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
    ) anyerror!mlir.Value {
        return self.coerceOnBranch(src_val, dst_ty, dst_sr, src_sr, store);
    }

    fn emitCastAggregateElement(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_sr: types.TypeId,
        dst_ty: mlir.Type,
        src_val: mlir.Value,
        src_sr: types.TypeId,
    ) anyerror!mlir.Value {
        return self.emitCastNormal(store, dst_sr, dst_ty, src_val, src_sr);
    }

    fn coerceOnBranch(
        self: *MlirCodegen,
        v: mlir.Value,
        want: mlir.Type,
        dst_sr_ty: types.TypeId,
        src_sr_ty: types.TypeId,
        store: *types.TypeStore,
    ) !mlir.Value {
        if (v.getType().equal(want)) return v;

        // ptr <-> ptr : bitcast
        if (mlir.LLVM.isLLVMPointerType(v.getType()) and mlir.LLVM.isLLVMPointerType(want)) {
            var bc = OpBuilder.init("llvm.bitcast", self.loc).builder()
                .add_operands(&.{v}).add_results(&.{want}).build();
            self.append(bc);
            return bc.getResult(0);
        }

        // ptr -> int : ptrtoint
        if (mlir.LLVM.isLLVMPointerType(v.getType()) and want.isAInteger()) {
            var op = OpBuilder.init("llvm.ptrtoint", self.loc).builder()
                .add_operands(&.{v}).add_results(&.{want}).build();
            self.append(op);
            return op.getResult(0);
        }

        // int -> ptr : inttoptr
        if (v.getType().isAInteger() and mlir.LLVM.isLLVMPointerType(want)) {
            var op = OpBuilder.init("llvm.inttoptr", self.loc).builder()
                .add_operands(&.{v}).add_results(&.{want}).build();
            self.append(op);
            return op.getResult(0);
        }

        // ints: zext/sext/trunc
        if (v.getType().isAInteger() and want.isAInteger()) {
            const fw = try intOrFloatWidth(v.getType());
            const tw = try intOrFloatWidth(want);
            if (fw == tw) return v;
            if (fw > tw) {
                var tr = OpBuilder.init("llvm.trunc", self.loc).builder()
                    .add_operands(&.{v}).add_results(&.{want}).build();
                self.append(tr);
                return tr.getResult(0);
            } else {
                const from_signed = self.isSignedInt(store, src_sr_ty);
                var ex = OpBuilder.init(if (from_signed) "llvm.sext" else "llvm.zext", self.loc).builder()
                    .add_operands(&.{v}).add_results(&.{want}).build();
                self.append(ex);
                return ex.getResult(0);
            }
        }

        // floats: fpext/fptrunc
        if (v.getType().isAFloat() and want.isAFloat()) {
            const fw = try intOrFloatWidth(v.getType());
            const tw = try intOrFloatWidth(want);
            if (fw == tw) return v;
            if (fw > tw) {
                var tr = OpBuilder.init("llvm.fptrunc", self.loc).builder()
                    .add_operands(&.{v}).add_results(&.{want}).build();
                self.append(tr);
                return tr.getResult(0);
            } else {
                var ex = OpBuilder.init("llvm.fpext", self.loc).builder()
                    .add_operands(&.{v}).add_results(&.{want}).build();
                self.append(ex);
                return ex.getResult(0);
            }
        }

        // int<->float (rare here): use normal cast rules to avoid crashes
        if (v.getType().isAInteger() and want.isAFloat()) {
            const from_signed = true; // branch-time info thin; assume signed
            var op = OpBuilder.init(if (from_signed) "llvm.sitofp" else "llvm.uitofp", self.loc).builder()
                .add_operands(&.{v}).add_results(&.{want}).build();
            self.append(op);
            return op.getResult(0);
        }
        if (v.getType().isAFloat() and want.isAInteger()) {
            // pick signed based on 'want' SR type if you pass it; here default signed
            var op = OpBuilder.init("llvm.fptosi", self.loc).builder()
                .add_operands(&.{v}).add_results(&.{want}).build();
            self.append(op);
            return op.getResult(0);
        }

        if (dst_sr_ty.toRaw() != 0 and src_sr_ty.toRaw() != 0) {
            const dst_kind = store.getKind(dst_sr_ty);
            const src_kind = store.getKind(src_sr_ty);

            if (dst_kind == .Error and src_kind == .ErrorSet) {
                return try self.errorSetToError(store, dst_sr_ty, want, src_sr_ty, v);
            }
        }

        if (try self.tryCopyAggregateValue(store, dst_sr_ty, want, v, src_sr_ty, coerceAggregateElementOnBranch)) |agg|
            return agg;

        if (try self.reinterpretAggregateViaSpill(store, dst_sr_ty, want, v, src_sr_ty)) |agg|
            return agg;

        // last resort (should be rare): bitcast
        var bc = OpBuilder.init("llvm.bitcast", self.loc).builder()
            .add_operands(&.{v}).add_results(&.{want}).build();
        self.append(bc);
        return bc.getResult(0);
    }

    fn errorSetToError(
        self: *MlirCodegen,
        store: *types.TypeStore,
        dst_err_sr: types.TypeId,
        dst_err_ty: mlir.Type,
        src_errset_sr: types.TypeId,
        src_val: mlir.Value,
    ) anyerror!mlir.Value {
        const es = store.get(.ErrorSet, src_errset_sr);

        const ok_name = store.strs.intern("Ok");
        const err_name = store.strs.intern("Err");
        var union_fields = [_]types.TypeStore.StructFieldArg{
            .{ .name = ok_name, .ty = es.value_ty },
            .{ .name = err_name, .ty = es.error_ty },
        };

        const union_sr = store.mkUnion(&union_fields);
        const union_ty = try self.llvmTypeOf(store, union_sr);
        const payload = self.extractAt(src_val, union_ty, &.{1});

        const err_mlir = try self.llvmTypeOf(store, es.error_ty);
        const union_ptr = self.spillAgg(payload, union_ty, 0);
        const idxs = [_]tir.Rows.GepIndex{.{ .Const = 0 }};
        const err_ptr = try self.emitGep(union_ptr, err_mlir, &idxs);
        var load_op = OpBuilder.init("llvm.load", self.loc).builder()
            .add_operands(&.{err_ptr}).add_results(&.{err_mlir}).build();
        self.append(load_op);

        var err_val = load_op.getResult(0);
        if (!err_mlir.equal(dst_err_ty)) {
            err_val = try self.coerceOnBranch(err_val, dst_err_ty, dst_err_sr, es.error_ty, store);
        }

        return err_val;
    }

    fn sameType(a: mlir.Type, b: mlir.Type) bool {
        return a.equal(b);
    }

    fn isLLVMPtr(ty: mlir.Type) bool {
        return mlir.LLVM.isLLVMPointerType(ty);
    }

    fn appendIfHasResult(self: *MlirCodegen, op: mlir.Operation) mlir.Value {
        if (op.getNumResults() == 0) return mlir.Value.empty();
        self.append(op);
        return op.getResult(0);
    }

    // arith.cmpi predicates (MLIR enum values)
    const CMP_EQ: i64 = 0;
    const CMP_NE: i64 = 1;
    const CMP_SLT: i64 = 2;
    const CMP_SGT: i64 = 4;
    const CMP_ULT: i64 = 6;
    const CMP_UGT: i64 = 8;

    // arith.cmpf predicates (MLIR enum values)
    const F_CMP_OEQ: i64 = 1;
    const F_CMP_OGT: i64 = 2;
    const F_CMP_OLT: i64 = 4;
    const F_CMP_UNO: i64 = 14;

    // boolean ops
    fn boolOr(self: *MlirCodegen, a: mlir.Value, b: mlir.Value) mlir.Value {
        const op = OpBuilder.init("arith.ori", self.loc).builder()
            .add_operands(&.{ a, b }).add_results(&.{self.i1_ty}).build();
        return appendIfHasResult(self, op);
    }
    fn boolAnd(self: *MlirCodegen, a: mlir.Value, b: mlir.Value) mlir.Value {
        const op = OpBuilder.init("arith.andi", self.loc).builder()
            .add_operands(&.{ a, b }).add_results(&.{self.i1_ty}).build();
        return appendIfHasResult(self, op);
    }
    fn boolNot(self: *MlirCodegen, a: mlir.Value) mlir.Value {
        const t = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_attributes(&.{self.named("value", mlir.Attribute.integerAttrGet(self.i1_ty, 1))})
            .add_results(&.{self.i1_ty}).build();
        self.append(t);
        const op = OpBuilder.init("arith.xori", self.loc).builder()
            .add_operands(&.{ a, t.getResult(0) }).add_results(&.{self.i1_ty}).build();
        return appendIfHasResult(self, op);
    }

    // call the lowered @assert(bool)
    fn emitAssertCall(self: *MlirCodegen, cond: mlir.Value) void {
        _ = appendIfHasResult(self, OpBuilder.init("func.call", self.loc).builder()
            .add_operands(&.{cond})
            .add_attributes(&.{
                self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.mlir_ctx, mlir.Attribute.stringAttrGetValue(self.strAttr("assert")))),
                self.named("sym_visibility", self.strAttr("private")),
                self.named("function_type", mlir.Attribute.typeAttrGet(mlir.LLVM.getLLVMFunctionType(self.i1_ty, &.{self.i1_ty}, false))),
            })
            // .add_attr("callee", @as(mlir.Attribute, mlir.FlatSymbolRefAttr.get(self.ctx, "assert")))
            .build());
    }

    // --- Complex helpers ---

    fn complexRe(self: *MlirCodegen, v: mlir.Value, elem_ty: mlir.Type) mlir.Value {
        const op = OpBuilder.init("complex.re", self.loc).builder()
            .add_operands(&.{v}).add_results(&.{elem_ty}).build();
        return appendIfHasResult(self, op);
    }

    fn complexIm(self: *MlirCodegen, v: mlir.Value, elem_ty: mlir.Type) mlir.Value {
        const op = OpBuilder.init("complex.im", self.loc).builder()
            .add_operands(&.{v}).add_results(&.{elem_ty}).build();
        return appendIfHasResult(self, op);
    }

    fn complexFromParts(self: *MlirCodegen, re: mlir.Value, im: mlir.Value, complex_ty: mlir.Type) mlir.Value {
        const make = OpBuilder.init("complex.create", self.loc).builder()
            .add_operands(&.{ re, im }).add_results(&.{complex_ty}).build();
        self.append(make);
        return make.getResult(0);
    }

    // --- Scalar cast helpers ---

    fn castPtrToPtr(self: *MlirCodegen, v: mlir.Value, to_ty: mlir.Type) mlir.Value {
        const op = OpBuilder.init("llvm.bitcast", self.loc).builder()
            .add_operands(&.{v}).add_results(&.{to_ty}).build();
        return appendIfHasResult(self, op);
    }
    fn castPtrToInt(self: *MlirCodegen, v: mlir.Value, to_ty: mlir.Type) mlir.Value {
        const op = OpBuilder.init("llvm.ptrtoint", self.loc).builder()
            .add_operands(&.{v}).add_results(&.{to_ty}).build();
        return appendIfHasResult(self, op);
    }
    fn castIntToPtr(self: *MlirCodegen, v: mlir.Value, to_ty: mlir.Type) mlir.Value {
        const op = OpBuilder.init("llvm.inttoptr", self.loc).builder()
            .add_operands(&.{v}).add_results(&.{to_ty}).build();
        return appendIfHasResult(self, op);
    }

    fn castIntToInt(self: *MlirCodegen, from_v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type, signed_from: bool) mlir.Value {
        const fw = intOrFloatWidth(from_ty) catch 0;
        const tw = intOrFloatWidth(to_ty) catch 0;
        if (fw == tw) return from_v;
        if (fw > tw) {
            const op = OpBuilder.init("llvm.trunc", self.loc).builder()
                .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
            return appendIfHasResult(self, op);
        }
        const opname = if (signed_from) "llvm.sext" else "llvm.zext";
        const op = OpBuilder.init(opname, self.loc).builder()
            .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
        return appendIfHasResult(self, op);
    }

    fn castIntToFloat(self: *MlirCodegen, v: mlir.Value, to_ty: mlir.Type, signed_from: bool) mlir.Value {
        const op = OpBuilder.init(if (signed_from) "llvm.sitofp" else "llvm.uitofp", self.loc).builder()
            .add_operands(&.{v}).add_results(&.{to_ty}).build();
        return appendIfHasResult(self, op);
    }

    fn castFloatToInt(self: *MlirCodegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
        const op = OpBuilder.init(if (signed_to) "llvm.fptosi" else "llvm.fptoui", self.loc).builder()
            .add_operands(&.{v}).add_results(&.{to_ty}).build();
        return appendIfHasResult(self, op);
    }

    fn resizeFloat(self: *MlirCodegen, v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type) mlir.Value {
        const fw = intOrFloatWidth(from_ty) catch 0;
        const tw = intOrFloatWidth(to_ty) catch 0;
        if (fw == tw) return v;
        const opname = if (fw > tw) "llvm.fptrunc" else "llvm.fpext";
        const op = OpBuilder.init(opname, self.loc).builder()
            .add_operands(&.{v}).add_results(&.{to_ty}).build();
        return appendIfHasResult(self, op);
    }

    // --- Integer limits as MLIR constants (destination type) ---
    fn intMinMax(self: *MlirCodegen, to_ty: mlir.Type, signed_to: bool) struct { min: mlir.Value, max: mlir.Value } {
        const w: u32 = intOrFloatWidth(to_ty) catch 1;
        if (signed_to) {
            return switch (w) {
                inline 1, 8, 16, 32, 64 => |x| blk: {
                    const Int = @Type(.{ .int = .{ .bits = x, .signedness = .signed } });
                    break :blk .{
                        .min = self.constInt(to_ty, std.math.minInt(Int)),
                        .max = self.constInt(to_ty, std.math.maxInt(Int)),
                    };
                },
                else => .{
                    .min = self.constInt(to_ty, std.math.minInt(i64)),
                    .max = self.constInt(to_ty, std.math.maxInt(i64)),
                },
            };
        } else {
            return switch (w) {
                inline 1, 8, 16, 32, 64 => |x| blk: {
                    const Int = @Type(.{ .int = .{ .bits = x, .signedness = .unsigned } });
                    break :blk .{
                        .min = self.constInt(to_ty, 0),
                        .max = self.constInt(to_ty, std.math.maxInt(Int)),
                    };
                },
                else => .{
                    .min = self.constInt(to_ty, 0),
                    .max = self.constInt(to_ty, std.math.maxInt(u64)),
                },
            };
        }
    }

    // --- Saturating helpers ---

    fn saturateIntToInt(self: *MlirCodegen, v: mlir.Value, from_signed: bool, to_ty: mlir.Type, to_signed: bool) mlir.Value {
        // Compare in source domain: extend to_ty limits up to source type
        const lim = self.intMinMax(to_ty, to_signed);
        const from_ty = v.getType();
        const ext_opname = if (from_signed) "llvm.sext" else "llvm.zext";
        const min_in_from = appendIfHasResult(self, OpBuilder.init(ext_opname, self.loc).builder()
            .add_operands(&.{lim.min}).add_results(&.{from_ty}).build());
        const max_in_from = appendIfHasResult(self, OpBuilder.init(ext_opname, self.loc).builder()
            .add_operands(&.{lim.max}).add_results(&.{from_ty}).build());

        const pred_lt: i64 = if (from_signed) CMP_SLT else CMP_ULT;
        const pred_gt: i64 = if (from_signed) CMP_SGT else CMP_UGT;

        const lt = OpBuilder.init("arith.cmpi", self.loc).builder()
            .add_operands(&.{ v, min_in_from })
            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, pred_lt))})
            .add_results(&.{self.i1_ty}).build();
        const gt = OpBuilder.init("arith.cmpi", self.loc).builder()
            .add_operands(&.{ v, max_in_from })
            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, pred_gt))})
            .add_results(&.{self.i1_ty}).build();
        self.append(lt);
        self.append(gt);

        // select low/high in source domain
        const sel_low = OpBuilder.init("arith.select", self.loc).builder()
            .add_operands(&.{ lt.getResult(0), min_in_from, v }).add_results(&.{from_ty}).build();
        self.append(sel_low);
        const sel_hi = OpBuilder.init("arith.select", self.loc).builder()
            .add_operands(&.{ gt.getResult(0), max_in_from, sel_low.getResult(0) }).add_results(&.{from_ty}).build();
        self.append(sel_hi);

        // Final convert to destination width
        return self.castIntToInt(sel_hi.getResult(0), from_ty, to_ty, from_signed);
    }

    fn saturateFloatToInt(self: *MlirCodegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
        const lim = self.intMinMax(to_ty, signed_to);
        const ft = v.getType();
        const min_f = self.castIntToFloat(lim.min, ft, signed_to);
        const max_f = self.castIntToFloat(lim.max, ft, signed_to);

        const lt = OpBuilder.init("arith.cmpf", self.loc).builder()
            .add_operands(&.{ v, min_f })
            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OLT))})
            .add_results(&.{self.i1_ty}).build();
        const gt = OpBuilder.init("arith.cmpf", self.loc).builder()
            .add_operands(&.{ v, max_f })
            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OGT))})
            .add_results(&.{self.i1_ty}).build();
        const isnan = OpBuilder.init("arith.cmpf", self.loc).builder()
            .add_operands(&.{ v, v })
            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_UNO))})
            .add_results(&.{self.i1_ty}).build();
        self.append(lt);
        self.append(gt);
        self.append(isnan);

        var fail = self.boolOr(lt.getResult(0), gt.getResult(0));
        fail = self.boolOr(fail, isnan.getResult(0));

        // clamp
        const sel_low = OpBuilder.init("arith.select", self.loc).builder()
            .add_operands(&.{ lt.getResult(0), min_f, v }).add_results(&.{ft}).build();
        self.append(sel_low);
        const sel_hi = OpBuilder.init("arith.select", self.loc).builder()
            .add_operands(&.{ gt.getResult(0), max_f, sel_low.getResult(0) }).add_results(&.{ft}).build();
        self.append(sel_hi);

        return self.castFloatToInt(sel_hi.getResult(0), to_ty, signed_to);
    }

    // --- Checked helpers ---

    fn checkedIntToInt(self: *MlirCodegen, v: mlir.Value, from_ty: mlir.Type, to_ty: mlir.Type, from_signed: bool) mlir.Value {
        // Convert normally (trunc/extend)
        const narrowed = self.castIntToInt(v, from_ty, to_ty, from_signed);

        // Re-extend to source width and compare equality (round-trip check)
        const widened = appendIfHasResult(self, OpBuilder.init(if (from_signed) "llvm.sext" else "llvm.zext", self.loc).builder()
            .add_operands(&.{narrowed}).add_results(&.{from_ty}).build());

        const ok = OpBuilder.init("arith.cmpi", self.loc).builder()
            .add_operands(&.{ v, widened })
            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, CMP_EQ))})
            .add_results(&.{self.i1_ty}).build();
        self.append(ok);
        self.emitAssertCall(ok.getResult(0)); // trap if overflow

        return narrowed;
    }

    fn checkedFloatToInt(self: *MlirCodegen, v: mlir.Value, to_ty: mlir.Type, signed_to: bool) mlir.Value {
        const lim = self.intMinMax(to_ty, signed_to);
        const ft = v.getType();
        const min_f = self.castIntToFloat(lim.min, ft, signed_to);
        const max_f = self.castIntToFloat(lim.max, ft, signed_to);

        const lt = OpBuilder.init("arith.cmpf", self.loc).builder()
            .add_operands(&.{ v, min_f })
            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OLT))})
            .add_results(&.{self.i1_ty}).build();
        const gt = OpBuilder.init("arith.cmpf", self.loc).builder()
            .add_operands(&.{ v, max_f })
            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OGT))})
            .add_results(&.{self.i1_ty}).build();
        const isnan = OpBuilder.init("arith.cmpf", self.loc).builder()
            .add_operands(&.{ v, v })
            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_UNO))})
            .add_results(&.{self.i1_ty}).build();
        self.append(lt);
        self.append(gt);
        self.append(isnan);

        var bad = self.boolOr(lt.getResult(0), gt.getResult(0));
        bad = self.boolOr(bad, isnan.getResult(0));

        // assert(!bad)
        const ok = self.boolNot(bad);
        self.emitAssertCall(ok);

        return self.castFloatToInt(v, to_ty, signed_to);
    }

    // --- The normalized "normal cast" (includes Complex + slice→int quirk) ---

    fn emitCastNormal(self: *MlirCodegen, store: *types.TypeStore, dst_sr: types.TypeId, to_ty: mlir.Type, from_v: mlir.Value, src_sr: types.TypeId) !mlir.Value {
        var from_ty = from_v.getType();

        // Complex target?
        if (store.getKind(dst_sr) == .Complex) {
            const tgt = store.get(.Complex, dst_sr);
            const elem_ty = self.llvmTypeOf(store, tgt.elem) catch unreachable;

            const src_kind = store.getKind(src_sr);
            if (src_kind == .Complex) {
                const src_c = store.get(.Complex, src_sr);
                const src_elem_ty = self.llvmTypeOf(store, src_c.elem) catch unreachable;
                if (sameType(src_elem_ty, elem_ty)) return from_v;

                const re0 = self.complexRe(from_v, src_elem_ty);
                const im0 = self.complexIm(from_v, src_elem_ty);
                const re = self.resizeFloat(re0, src_elem_ty, elem_ty);
                const im = self.resizeFloat(im0, src_elem_ty, elem_ty);
                return self.complexFromParts(re, im, to_ty);
            } else {
                // scalar -> complex
                const from_is_int = from_ty.isAInteger();
                const from_is_f = from_ty.isAFloat();
                var re_val: mlir.Value = from_v;
                if (from_is_int and elem_ty.isAFloat()) {
                    const signed_from = self.isSignedInt(store, src_sr);
                    re_val = self.castIntToFloat(from_v, elem_ty, signed_from);
                } else if (from_is_f and elem_ty.isAFloat()) {
                    re_val = self.resizeFloat(from_v, from_ty, elem_ty);
                }
                const im_val = self.constFloat(elem_ty, 0.0);
                return self.complexFromParts(re_val, im_val, to_ty);
            }
        }

        // Special-case slice -> int coercion artifact
        if (store.getKind(src_sr) == .Slice and to_ty.isAInteger()) {
            return self.constInt(to_ty, 0);
        }

        // Scalars & pointers
        const from_is_int = from_ty.isAInteger();
        const to_is_int = to_ty.isAInteger();
        const from_is_f = from_ty.isAFloat();
        const to_is_f = to_ty.isAFloat();
        const from_is_ptr = isLLVMPtr(from_ty);
        const to_is_ptr = isLLVMPtr(to_ty);

        if (from_is_ptr and to_is_ptr) return self.castPtrToPtr(from_v, to_ty);
        if (from_is_ptr and to_is_int) return self.castPtrToInt(from_v, to_ty);
        if (from_is_int and to_is_ptr) return self.castIntToPtr(from_v, to_ty);

        if (from_is_int and to_is_int) return self.castIntToInt(from_v, from_ty, to_ty, self.isSignedInt(store, src_sr));
        if (from_is_int and to_is_f) return self.castIntToFloat(from_v, to_ty, self.isSignedInt(store, src_sr));
        if (from_is_f and to_is_int) return self.castFloatToInt(from_v, to_ty, self.isSignedInt(store, dst_sr));
        if (from_is_f and to_is_f) return self.resizeFloat(from_v, from_ty, to_ty);

        if (try self.tryCopyAggregateValue(store, dst_sr, to_ty, from_v, src_sr, emitCastAggregateElement)) |agg|
            return agg;

        if (try self.reinterpretAggregateViaSpill(store, dst_sr, to_ty, from_v, src_sr)) |agg|
            return agg;

        // Fallback: bitcast (ensure size match upstream)
        const op = OpBuilder.init("llvm.bitcast", self.loc).builder()
            .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
        return appendIfHasResult(self, op);
    }

    // --- Public dispatcher for all cast kinds ---

    fn emitCast(self: *MlirCodegen, kind: tir.OpKind, store: *types.TypeStore, dst_sr: types.TypeId, src_sr: types.TypeId, from_v: mlir.Value) !mlir.Value {
        const to_ty = try self.llvmTypeOf(store, dst_sr);
        const from_ty = from_v.getType();

        switch (kind) {
            else => unreachable, // not a cast
            .CastNormal => return self.emitCastNormal(store, dst_sr, to_ty, from_v, src_sr),

            .CastWrap => {
                if (from_ty.isAInteger() and to_ty.isAInteger()) {
                    return self.castIntToInt(from_v, from_ty, to_ty, self.isSignedInt(store, src_sr)); // wrap == modular
                }
                // others: same as normal
                return self.emitCastNormal(store, dst_sr, to_ty, from_v, src_sr);
            },

            .CastSaturate => {
                if (from_ty.isAInteger() and to_ty.isAInteger()) {
                    return self.saturateIntToInt(from_v, self.isSignedInt(store, src_sr), to_ty, self.isSignedInt(store, dst_sr));
                }
                if (from_ty.isAFloat() and to_ty.isAInteger()) {
                    return self.saturateFloatToInt(from_v, to_ty, self.isSignedInt(store, dst_sr));
                }
                // others: normal behavior
                return self.emitCastNormal(store, dst_sr, to_ty, from_v, src_sr);
            },

            .CastChecked => {
                // const to_ty_mlir = to_ty;
                const from_ty_mlir = from_v.getType();

                // The result of a checked cast is always an Optional type.
                const optional_sr = store.get(.Optional, dst_sr);
                const optional_mlir_ty = try self.llvmTypeOf(store, dst_sr);
                const optional_elem_mlir_ty = try self.llvmTypeOf(store, optional_sr.elem);
                const optional_elem_is_signed = self.isSignedInt(store, optional_sr.elem);

                var cast_ok: mlir.Value = self.constBool(true);
                var casted_val: mlir.Value = undefined;

                if (from_ty_mlir.isAInteger() and optional_elem_mlir_ty.isAInteger()) {
                    // Integer to Integer checked cast
                    const fw = try intOrFloatWidth(from_ty_mlir);
                    const tw = try intOrFloatWidth(optional_elem_mlir_ty);
                    const from_signed = self.isSignedInt(store, src_sr);
                    // const to_signed = self.isSignedInt(store, store.get(.Optional, dst_sr).elem);

                    if (fw == tw) {
                        casted_val = from_v;
                    } else if (fw > tw) {
                        // Truncation: check for overflow
                        const narrowed = self.castIntToInt(from_v, from_ty_mlir, optional_elem_mlir_ty, from_signed);
                        const widened = appendIfHasResult(self, OpBuilder.init(if (from_signed) "llvm.sext" else "llvm.zext", self.loc).builder()
                            .add_operands(&.{narrowed}).add_results(&.{from_ty_mlir}).build());
                        cast_ok = appendIfHasResult(self, OpBuilder.init("arith.cmpi", self.loc).builder()
                            .add_operands(&.{ from_v, widened })
                            .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, CMP_EQ))})
                            .add_results(&.{self.i1_ty}).build());
                        casted_val = narrowed;
                    } else {
                        // Extension: always succeeds
                        casted_val = self.castIntToInt(from_v, from_ty_mlir, optional_elem_mlir_ty, from_signed);
                    }
                } else if (from_ty_mlir.isAFloat() and optional_elem_mlir_ty.isAInteger()) {
                    // Float to Integer checked cast
                    const lim = self.intMinMax(optional_elem_mlir_ty, optional_elem_is_signed);
                    const ft = from_ty_mlir;
                    const min_f = self.castIntToFloat(lim.min, ft, optional_elem_is_signed);
                    const max_f = self.castIntToFloat(lim.max, ft, optional_elem_is_signed);

                    const lt = appendIfHasResult(self, OpBuilder.init("arith.cmpf", self.loc).builder()
                        .add_operands(&.{ from_v, min_f })
                        .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OLT))})
                        .add_results(&.{self.i1_ty}).build());
                    const gt = appendIfHasResult(self, OpBuilder.init("arith.cmpf", self.loc).builder()
                        .add_operands(&.{ from_v, max_f })
                        .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OGT))})
                        .add_results(&.{self.i1_ty}).build());
                    const isnan = appendIfHasResult(self, OpBuilder.init("arith.cmpf", self.loc).builder()
                        .add_operands(&.{ from_v, from_v })
                        .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_UNO))})
                        .add_results(&.{self.i1_ty}).build());

                    var bad = self.boolOr(lt, gt);
                    bad = self.boolOr(bad, isnan);
                    cast_ok = self.boolNot(bad);

                    // Clamp the source value into the integer domain (or a benign value for NaN)
                    const clamped_low = appendIfHasResult(self, OpBuilder.init("arith.select", self.loc).builder()
                        .add_operands(&.{ lt, min_f, from_v }).add_results(&.{ft}).build());
                    const clamped_high = appendIfHasResult(self, OpBuilder.init("arith.select", self.loc).builder()
                        .add_operands(&.{ gt, max_f, clamped_low }).add_results(&.{ft}).build());
                    const zero = self.constFloat(ft, 0.0);
                    const sanitized = appendIfHasResult(self, OpBuilder.init("arith.select", self.loc).builder()
                        .add_operands(&.{ isnan, zero, clamped_high }).add_results(&.{ft}).build());

                    casted_val = self.castFloatToInt(sanitized, optional_elem_mlir_ty, optional_elem_is_signed);

                    // Verify round-trip back to float to catch fractional values.
                    const roundtrip = self.castIntToFloat(casted_val, ft, optional_elem_is_signed);
                    const same = appendIfHasResult(self, OpBuilder.init("arith.cmpf", self.loc).builder()
                        .add_operands(&.{ from_v, roundtrip })
                        .add_attributes(&.{self.named("predicate", mlir.Attribute.integerAttrGet(self.i64_ty, F_CMP_OEQ))})
                        .add_results(&.{self.i1_ty}).build());
                    cast_ok = self.boolAnd(cast_ok, same);
                } else {
                    // For other types (ptr<->int, float<->float), treat as normal cast for now.
                    // If it's a normal cast that would fail, then the checked cast should produce None.
                    // This is a simplification; a more robust solution would involve more specific checks.
                    casted_val = try self.emitCastNormal(store, optional_sr.elem, optional_elem_mlir_ty, from_v, src_sr);
                    // Assume success for now, or add more complex checks if needed.
                    cast_ok = self.constBool(true);
                }

                // Construct the Optional struct
                var result_optional = self.undefOf(optional_mlir_ty);
                result_optional = self.insertAt(result_optional, cast_ok, &.{0});
                result_optional = self.insertAt(result_optional, casted_val, &.{1});
                return result_optional;
            },
        }
    }

    fn llvmTypeOf(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) !mlir.Type {
        return switch (store.getKind(ty)) {
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

            .Any => self.llvm_ptr_ty,
            .Function => self.llvm_ptr_ty,
            .Ptr => self.llvm_ptr_ty,

            .String, .Slice => blk: {
                // { ptr, len } (opaque ptr for data)
                const fields = [_]mlir.Type{ self.llvm_ptr_ty, self.i64_ty };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
            },

            .Array => blk: {
                const arr_ty = store.get(.Array, ty);
                const e = try self.llvmTypeOf(store, arr_ty.elem);
                break :blk mlir.LLVM.getLLVMArrayType(e, @intCast(arr_ty.len));
            },
            .Complex => blk: {
                const c = store.get(.Complex, ty);
                const elem = try self.llvmTypeOf(store, c.elem);
                break :blk mlir.Type.getComplexType(elem);
            },

            .Optional => blk: {
                const opt_ty = store.get(.Optional, ty);
                const inner = try self.llvmTypeOf(store, opt_ty.elem);
                const fields = [_]mlir.Type{ self.i1_ty, inner };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
            },

            .ErrorSet => blk: {
                const es = store.get(.ErrorSet, ty);
                const ok_name = store.strs.intern("Ok");
                const err_name = store.strs.intern("Err");
                var union_fields = [_]types.TypeStore.StructFieldArg{
                    .{ .name = ok_name, .ty = es.value_ty },
                    .{ .name = err_name, .ty = es.error_ty },
                };
                const payload_union = store.mkUnion(&union_fields);
                const payload_mlir = try self.llvmTypeOf(store, payload_union);
                const parts = [_]mlir.Type{ self.i32_ty, payload_mlir };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &parts, false);
            },

            .Tuple => blk: {
                const tup_ty = store.get(.Tuple, ty);
                const n = tup_ty.elems.len;
                var buf = try self.gpa.alloc(mlir.Type, n);
                defer self.gpa.free(buf);
                const elems = store.type_pool.slice(tup_ty.elems);
                for (elems, 0..) |eid, i| buf[i] = try self.llvmTypeOf(store, eid);
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, buf, false);
            },

            .Struct => blk: {
                const st_ty = store.get(.Struct, ty);
                const n = st_ty.fields.len;
                var buf = try self.gpa.alloc(mlir.Type, n);
                defer self.gpa.free(buf);
                const fields = store.field_pool.slice(st_ty.fields);
                for (fields, 0..) |f, i| {
                    const field = store.Field.get(f);
                    buf[i] = try self.llvmTypeOf(store, field.ty);
                }
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, buf, false);
            },

            .Enum => blk: {
                // TODO: usee backing integer type if specified
                break :blk mlir.Type.getSignlessIntegerType(self.mlir_ctx, 32);
            },

            .Union => blk: {
                const un_ty = store.get(.Union, ty);
                const n = un_ty.fields.len;
                if (n == 0) break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &[_]mlir.Type{}, false);

                var max_size: u64 = 0;

                const fields = store.field_pool.slice(un_ty.fields);
                for (fields) |f| {
                    const field = store.Field.get(f);
                    const sa = abi.abiSizeAlign(self, store, field.ty);
                    if (sa.size > max_size) {
                        max_size = sa.size;
                    }
                }

                break :blk mlir.LLVM.getLLVMArrayType(self.i8_ty, @intCast(max_size));
            },

            .Error => blk: {
                const e_ty = store.get(.Error, ty);
                const fields = store.field_pool.slice(e_ty.variants);
                if (fields.len == 0) {
                    const parts = [_]mlir.Type{self.i32_ty};
                    break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &parts, false);
                }

                var payload_types = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                defer self.gpa.free(payload_types);
                for (fields, 0..) |f, i| {
                    const field = store.Field.get(f);
                    payload_types[i] = .{ .name = field.name, .ty = field.ty };
                }
                const union_ty = store.mkUnion(payload_types);
                const union_mlir_ty = try self.llvmTypeOf(store, union_ty);

                const parts = [_]mlir.Type{ self.i32_ty, union_mlir_ty };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &parts, false);
            },

            .Variant => blk: {
                const v_ty = store.get(.Variant, ty);
                const n = v_ty.variants.len;
                var payload_types = try self.gpa.alloc(types.TypeStore.StructFieldArg, n);
                defer self.gpa.free(payload_types);

                const fields = store.field_pool.slice(v_ty.variants);
                for (fields, 0..) |f, i| {
                    const field = store.Field.get(f);
                    payload_types[i] = .{ .name = field.name, .ty = field.ty };
                }

                const union_ty = store.mkUnion(payload_types);
                const union_mlir_ty = try self.llvmTypeOf(store, union_ty);

                const fields_mlir = [_]mlir.Type{ self.i32_ty, union_mlir_ty };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields_mlir, false);
            },

            .TypeType => return self.llvm_ptr_ty,
            else => std.debug.panic("unhandled type: {}", .{store.getKind(ty)}),
        };
    }
};
