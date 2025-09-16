const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir_v2.zig");
const types = @import("types_v2.zig");

const Allocator = std.mem.Allocator;
const ArrayList = std.array_list.Managed;

pub const TirLlvmGenV2 = struct {
    gpa: Allocator,
    ctx: mlir.Context,
    loc: mlir.Location,
    module: mlir.Module,

    // common LLVM/arith types
    void_ty: mlir.Type,
    i1_ty: mlir.Type,
    i8_ty: mlir.Type,
    i32_ty: mlir.Type,
    i64_ty: mlir.Type,
    f32_ty: mlir.Type,
    f64_ty: mlir.Type,
    llvm_ptr_ty: mlir.Type,

    // per-module caches
    func_syms: std.StringHashMap(FuncInfo),
    str_pool: std.StringHashMap(mlir.Operation),

    // per-function state (value and block maps keyed by v2 ids)
    cur_region: ?mlir.Region = null,
    cur_block: ?mlir.Block = null,
    block_map: std.AutoHashMap(tir.BlockId, mlir.Block),
    value_map: std.AutoHashMap(tir.ValueId, mlir.Value),

    pub const FuncInfo = struct { op: mlir.Operation, is_variadic: bool, n_formals: usize };

    const OpBuilder = struct {
        operands: ?[]const mlir.Value = null,
        results: ?[]const mlir.Type = null,
        attributes: ?[]const mlir.NamedAttribute = null,
        regions: ?[]const mlir.Region = null,
        successors: ?[]const mlir.Block = null,
        name: []const u8,
        loc: mlir.Location,
        pub fn init(name: []const u8, loc: mlir.Location) OpBuilder { return .{ .name = name, .loc = loc }; }
        pub fn builder(self: *const OpBuilder) *OpBuilder { return @constCast(self); }
        pub fn add_operands(self: *OpBuilder, ops: []const mlir.Value) *OpBuilder { self.operands = ops; return self; }
        pub fn add_results(self: *OpBuilder, tys: []const mlir.Type) *OpBuilder { self.results = tys; return self; }
        pub fn add_attributes(self: *OpBuilder, attrs: []const mlir.NamedAttribute) *OpBuilder { self.attributes = attrs; return self; }
        pub fn add_regions(self: *OpBuilder, regs: []const mlir.Region) *OpBuilder { self.regions = regs; return self; }
        pub fn add_successors(self: *OpBuilder, succs: []const mlir.Block) *OpBuilder { self.successors = succs; return self; }
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

    pub fn init(gpa: Allocator) TirLlvmGenV2 {
        const ctx = initMLIR(gpa);
        const loc = mlir.Location.unknownGet(ctx);
        const module = mlir.Module.createEmpty(loc);
        const void_ty = mlir.Type{ .handle = mlir.c.mlirLLVMVoidTypeGet(ctx.handle) };
        return .{
            .gpa = gpa,
            .ctx = ctx,
            .loc = loc,
            .module = module,
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
        };
    }

    fn initMLIR(alloc: std.mem.Allocator) mlir.Context {
        mlir.setGlobalAlloc(alloc);
        var mlir_context = mlir.Context.create();
        const registry = mlir.DialectRegistry.create();
        mlir.registerAllDialects(registry);
        mlir.registerAllPasses();
        mlir.registerAllLLVMTranslations(mlir_context);
        mlir_context.appendDialectRegistry(registry);
        mlir_context.loadAllAvailableDialects();
        return mlir_context;
    }

    pub fn deinit(self: *TirLlvmGenV2) void {
        self.func_syms.deinit();
        self.str_pool.deinit();
        self.block_map.deinit();
        self.value_map.deinit();
        self.module.destroy();
        self.ctx.destroy();
    }

    // Entry: emit module from v2 TIR
    pub fn emitModule(self: *TirLlvmGenV2, t: *const tir.TIR, store: *types.TypeStore) !mlir.Module {
        // TODO: walk t.funcs.Function to declare/define; for now return empty module to establish wiring
        _ = t; _ = store;
        return self.module;
    }

    // Helpers mirrored from v1 codegen (to be ported progressively)
    fn named(self: *TirLlvmGenV2, name: []const u8, attr: mlir.Attribute) mlir.NamedAttribute {
        return mlir.NamedAttribute.get(self.ctx, mlir.StringRef.from(name), attr);
    }
    fn strAttr(self: *TirLlvmGenV2, s: []const u8) mlir.Attribute { return mlir.Attribute.stringAttrGet(self.ctx, mlir.StringRef.from(s)); }
    fn append(self: *TirLlvmGenV2, op: mlir.Operation) void { self.cur_block.?.appendOwnedOperation(op); }
};

