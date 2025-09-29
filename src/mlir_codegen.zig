const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const compile = @import("compile.zig");
const types = @import("types.zig");
const abi = @import("abi.zig");

const Allocator = std.mem.Allocator;
const ArrayList = std.array_list.Managed;

pub const MlirCodegen = struct {
    gpa: Allocator,
    context: *compile.Context,
    mlir_ctx: mlir.Context,
    loc: mlir.Location,
    module: mlir.Module,

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

    pub const FuncInfo = struct {
        op: mlir.Operation,
        is_variadic: bool,
        n_formals: usize, // MLIR visible formals after dropping trailing Any
        ret_type: mlir.Type,
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
        self.func_syms.deinit();
        self.str_pool.deinit();
        self.block_map.deinit();
        self.value_map.deinit();
        self.val_types.deinit();
        self.def_instr.deinit();
        self.module.destroy();
    }

    // ----------------------------------------------------------------
    // Public entry
    // ----------------------------------------------------------------
    pub fn emitModule(self: *MlirCodegen, t: *const tir.TIR, context: *compile.Context) !mlir.Module {
        self.attachTargetInfo();
        try self.emitExternDecls(t, &context.type_store);

        const func_ids = t.funcs.func_pool.data.items;
        for (func_ids) |fid| try self.emitFunctionHeader(fid, t, &context.type_store);
        for (func_ids) |fid| {
            const row = t.funcs.Function.get(fid.toRaw());
            const blocks = t.funcs.block_pool.slice(row.blocks);
            if (blocks.len > 0) try self.emitFunctionBody(fid, t, &context.type_store);
        }
        return self.module;
    }

    fn attachTargetInfo(self: *MlirCodegen) void {
        const triple = self.strAttr("x86_64-unknown-linux-gnu");
        const dl = self.strAttr("e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128");
        var mod_op = self.module.getOperation();
        mod_op.setDiscardableAttributeByName(mlir.StringRef.from("llvm.target_triple"), triple);
        mod_op.setDiscardableAttributeByName(mlir.StringRef.from("llvm.data_layout"), dl);
    }

    // ----------------------------------------------------------------
    // Functions
    // ----------------------------------------------------------------

    fn emitExternDecls(self: *MlirCodegen, t: *const tir.TIR, store: *types.TypeStore) !void {
        const global_ids = t.funcs.global_pool.data.items;

        for (global_ids) |global_id| {
            const g = t.funcs.Global.get(global_id.toRaw());
            if (store.getKind(g.ty) != .Function) continue;

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
            const name = t.instrs.strs.get(g.name);

            if (self.func_syms.contains(name)) continue;

            const argAttrsArray = mlir.Attribute.arrayAttrGet(self.mlir_ctx, argAttrs[0..n_args]);
            const attrs = [_]mlir.NamedAttribute{
                self.named("sym_name", self.strAttr(name)),
                self.named("function_type", mlir.Attribute.typeAttrGet(fty)),
                self.named("arg_attrs", argAttrsArray),
                self.named("sym_visibility", self.strAttr("private")),
            };
            const region = mlir.Region.create(); // extern: no body
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
            });
        }
    }

    fn emitFunctionHeader(self: *MlirCodegen, f_id: tir.FuncId, t: *const tir.TIR, store: *types.TypeStore) !void {
        const f = t.funcs.Function.get(f_id.toRaw());
        const params = t.funcs.param_pool.slice(f.params);

        var param_tys = try self.gpa.alloc(mlir.Type, params.len);
        defer self.gpa.free(param_tys);

        for (params, 0..) |p_id, i| {
            const p = t.funcs.Param.get(p_id.toRaw());
            param_tys[i] = try self.llvmTypeOf(store, p.ty);
        }

        var results: [1]mlir.Type = undefined;
        const n_res: usize = if (store.getKind(f.result) == .Void) 0 else 1;
        if (n_res == 1) results[0] = try self.llvmTypeOf(store, f.result);

        const func_name = t.instrs.strs.get(f.name);
        if (self.func_syms.contains(func_name)) return;

        // NOTE: language-defined functions here are assumed non-variadic
        const fty = mlir.Type.getFunctionType(self.mlir_ctx, @intCast(param_tys.len), param_tys, @intCast(n_res), results[0..n_res]);
        const attrs = [_]mlir.NamedAttribute{
            self.named("sym_name", self.strAttr(func_name)),
            self.named("function_type", mlir.Attribute.typeAttrGet(fty)),
        };
        const region = mlir.Region.create();
        const fnop = OpBuilder.init("func.func", self.loc).builder()
            .add_attributes(&attrs)
            .add_regions(&.{region})
            .build();

        var body = self.module.getBody();
        body.appendOwnedOperation(fnop);

        const ret_mlir = if (n_res == 0) self.void_ty else results[0];
        _ = try self.func_syms.put(func_name, .{
            .op = fnop,
            .is_variadic = false,
            .n_formals = params.len,
            .ret_type = ret_mlir,
        });
    }

    fn emitFunctionBody(self: *MlirCodegen, f_id: tir.FuncId, t: *const tir.TIR, store: *types.TypeStore) !void {
        // reset per-function state
        self.block_map.clearRetainingCapacity();
        self.value_map.clearRetainingCapacity();
        self.val_types.clearRetainingCapacity();
        self.def_instr.clearRetainingCapacity();
        self.cur_region = null;
        self.cur_block = null;

        const f = t.funcs.Function.get(f_id.toRaw());
        const func_name = t.instrs.strs.get(f.name);
        const finfo = self.func_syms.get(func_name).?;
        var func_op = finfo.op;
        var region = func_op.getRegion(0);

        const n_formals = finfo.n_formals;
        const params = t.funcs.param_pool.slice(f.params);

        // entry block arg types
        var entry_arg_tys = try self.gpa.alloc(mlir.Type, n_formals);
        defer self.gpa.free(entry_arg_tys);
        for (params[0..n_formals], 0..) |p_id, i| {
            const p = t.funcs.Param.get(p_id.toRaw());
            entry_arg_tys[i] = try self.llvmTypeOf(store, p.ty);
        }
        const entry_locs = try self.gpa.alloc(mlir.Location, n_formals);
        defer self.gpa.free(entry_locs);
        for (entry_locs) |*L| L.* = self.loc;

        var entry_block = mlir.Block.create(entry_arg_tys, entry_locs);
        region.appendOwnedBlock(entry_block);
        self.cur_region = region;
        self.cur_block = entry_block;

        const blocks = t.funcs.block_pool.slice(f.blocks);

        if (blocks.len > 0) {
            const entry_bid = blocks[0];
            try self.block_map.put(entry_bid, entry_block);
        }

        // seed param SSA values + SR types
        try self.value_map.ensureTotalCapacity(@intCast(n_formals));
        try self.val_types.ensureTotalCapacity(@intCast(n_formals));
        for (params[0..n_formals], 0..) |p_id, i| {
            const p = t.funcs.Param.get(p_id.toRaw());
            const v = entry_block.getArgument(i);
            try self.value_map.put(p.value, v);
            try self.val_types.put(p.value, p.ty);
        }

        // pre-create remaining blocks and map their params + SR types
        if (blocks.len > 1) {
            for (blocks[1..]) |b_id| {
                const bb = t.funcs.Block.get(b_id.toRaw());
                const b_params = t.funcs.param_pool.slice(bb.params);
                const m = b_params.len;

                var arg_tys = try self.gpa.alloc(mlir.Type, m);
                defer self.gpa.free(arg_tys);
                var arg_locs = try self.gpa.alloc(mlir.Location, m);
                defer self.gpa.free(arg_locs);
                for (b_params, 0..) |bp_id, i| {
                    const bp = t.funcs.Param.get(bp_id.toRaw());
                    arg_tys[i] = try self.llvmTypeOf(store, bp.ty);
                    arg_locs[i] = self.loc;
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
            const bb = t.funcs.Block.get(b_id.toRaw());

            // map block params to SSA + SR types
            const b_params = t.funcs.param_pool.slice(bb.params);
            for (b_params, 0..) |bp_id, i| {
                const bp = t.funcs.Param.get(bp_id.toRaw());
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
            .ConstInt => return t.instrs.get(.ConstInt, id).result,
            .ConstFloat => return t.instrs.get(.ConstFloat, id).result,
            .ConstBool => return t.instrs.get(.ConstBool, id).result,
            .ConstString => return t.instrs.get(.ConstString, id).result,
            .ConstNull => return t.instrs.get(.ConstNull, id).result,
            .ConstUndef => return t.instrs.get(.ConstUndef, id).result,
            inline .Add, .Sub, .Mul, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe => |k| return t.instrs.get(k, id).result,
            .LogicalNot => return t.instrs.get(.LogicalNot, id).result,
            inline .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => |k| return t.instrs.get(k, id).result,
            .Alloca => return t.instrs.get(.Alloca, id).result,
            .Load => return t.instrs.get(.Load, id).result,
            .Store => return null,
            .Gep => return t.instrs.get(.Gep, id).result,
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
            else => std.debug.panic("unhandled instruction kind, {}\n", .{K}),
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
            inline .Add, .Sub, .Mul, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe => |k| t.instrs.get(k, id).ty,
            .LogicalNot => t.instrs.get(.LogicalNot, id).ty,
            inline .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => |k| t.instrs.get(k, id).ty,
            .Alloca => t.instrs.get(.Alloca, id).ty,
            .Load => t.instrs.get(.Load, id).ty,
            .Store => null,
            .Gep => t.instrs.get(.Gep, id).ty,
            .TupleMake => t.instrs.get(.TupleMake, id).ty,
            .ArrayMake => t.instrs.get(.ArrayMake, id).ty,
            .StructMake => t.instrs.get(.StructMake, id).ty,
            .ExtractElem => t.instrs.get(.ExtractElem, id).ty,
            .InsertElem => t.instrs.get(.InsertElem, id).ty,
            .ExtractField => t.instrs.get(.ExtractField, id).ty,
            .InsertField => t.instrs.get(.InsertField, id).ty,
            .Index => t.instrs.get(.Index, id).ty,
            .AddressOf => t.instrs.get(.AddressOf, id).ty,
            .Select => t.instrs.get(.Select, id).ty,
            .Call => t.instrs.get(.Call, id).ty,
            else => std.debug.panic("unhandled instruction kind, {}\n", .{K}),
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
            const g = t.funcs.Global.get(gid.toRaw());
            if (store.getKind(g.ty) != .Function) continue;
            const sym = t.instrs.strs.get(g.name);
            if (!std.mem.eql(u8, sym, name)) continue;
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

        const info: FuncInfo = .{ .op = fnop, .is_variadic = is_var, .n_formals = params_sr.len, .ret_type = ret_type };
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
                const ty = try self.llvmTypeOf(store, p.ty);
                break :blk self.constInt(ty, p.value);
            },
            .ConstFloat => blk: {
                const p = t.instrs.get(.ConstFloat, ins_id);
                const ty = try self.llvmTypeOf(store, p.ty);
                break :blk self.constFloat(ty, p.value);
            },
            .ConstBool => blk: {
                const p = t.instrs.get(.ConstBool, ins_id);
                break :blk self.constBool(p.value);
            },
            .ConstNull => blk: {
                const p = t.instrs.get(.ConstNull, ins_id);
                const ty = try self.llvmTypeOf(store, p.ty);
                var op = OpBuilder.init("llvm.mlir.null", self.loc).builder()
                    .add_results(&.{ty}).build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .ConstUndef => blk: {
                const p = t.instrs.get(.ConstUndef, ins_id);
                const ty = try self.llvmTypeOf(store, p.ty);
                var op = OpBuilder.init("llvm.mlir.undef", self.loc).builder()
                    .add_results(&.{ty}).build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .ConstString => blk: {
                const p = t.instrs.get(.ConstString, ins_id);
                const str_text = t.instrs.strs.get(p.text);
                var op = try self.constStringPtr(str_text);
                break :blk op.getResult(0);
            },

            // ------------- Arithmetic / bitwise (now arith.*) -------------
            .Add => try self.binArith("llvm.add", "llvm.fadd", t.instrs.get(.Add, ins_id), store),
            .Sub => try self.binArith("llvm.sub", "llvm.fsub", t.instrs.get(.Sub, ins_id), store),
            .Mul => try self.binArith("llvm.mul", "llvm.fmul", t.instrs.get(.Mul, ins_id), store),

            .Div => blk: {
                const p = t.instrs.get(.Div, ins_id);
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                const signed = !self.isUnsigned(store, self.srTypeOfValue(t, p.lhs));
                break :blk self.arithDiv(lhs, rhs, ty, signed);
            },

            .Mod => blk: {
                const p = t.instrs.get(.Mod, ins_id);
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                const signed = !self.isUnsigned(store, self.srTypeOfValue(t, p.lhs));
                break :blk self.arithRem(lhs, rhs, ty, signed);
            },

            .Shl => blk: {
                const p = t.instrs.get(.Shl, ins_id);
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                break :blk self.arithShl(lhs, rhs, ty);
            },
            .Shr => blk: {
                const p = t.instrs.get(.Shr, ins_id);
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
                const v = self.value_map.get(p.value).?;
                break :blk self.arithLogicalNotI1(v);
            },

            // ------------- Comparisons (keep LLVM for robust attrs) -------------
            .CmpEq => try self.emitCmp("eq", "eq", "oeq", t.instrs.get(.CmpEq, ins_id), t, store),
            .CmpNe => try self.emitCmp("ne", "ne", "one", t.instrs.get(.CmpNe, ins_id), t, store),
            .CmpLt => try self.emitCmp("ult", "slt", "olt", t.instrs.get(.CmpLt, ins_id), t, store),
            .CmpLe => try self.emitCmp("ule", "sle", "ole", t.instrs.get(.CmpLe, ins_id), t, store),
            .CmpGt => try self.emitCmp("ugt", "sgt", "ogt", t.instrs.get(.CmpGt, ins_id), t, store),
            .CmpGe => try self.emitCmp("uge", "sge", "oge", t.instrs.get(.CmpGe, ins_id), t, store),

            // ------------- Casts -------------
            .CastBit => blk: {
                const p = t.instrs.get(.CastBit, ins_id);
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
                const to_ty = try self.llvmTypeOf(store, p.ty);
                var from_v = self.value_map.get(p.value).?;
                var from_ty = from_v.getType();

                const from_is_int = from_ty.isAInteger();
                const to_is_int = to_ty.isAInteger();
                const from_is_f = from_ty.isAFloat();
                const to_is_f = to_ty.isAFloat();
                const from_is_ptr = mlir.LLVM.isLLVMPointerType(from_ty);
                const to_is_ptr = mlir.LLVM.isLLVMPointerType(to_ty);

                const fw = intOrFloatWidth(from_ty) catch 0;
                const tw = intOrFloatWidth(to_ty) catch 0;

                var op: mlir.Operation = undefined;

                if (from_is_ptr and to_is_ptr) {
                    op = OpBuilder.init("llvm.bitcast", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                } else if (from_is_ptr and to_is_int) {
                    op = OpBuilder.init("llvm.ptrtoint", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                } else if (from_is_int and to_is_ptr) {
                    op = OpBuilder.init("llvm.inttoptr", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                } else if (from_is_int and to_is_int) {
                    if (fw == tw) {
                        break :blk from_v;
                    } else if (fw > tw) {
                        op = OpBuilder.init("llvm.trunc", self.loc).builder()
                            .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                    } else {
                        const from_signed = self.isSignedInt(store, self.srTypeOfValue(t, p.value));
                        op = OpBuilder.init(if (from_signed) "llvm.sext" else "llvm.zext", self.loc).builder()
                            .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                    }
                } else if (from_is_int and to_is_f) {
                    const from_signed = self.isSignedInt(store, self.srTypeOfValue(t, p.value));
                    op = OpBuilder.init(if (from_signed) "llvm.sitofp" else "llvm.uitofp", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                } else if (from_is_f and to_is_int) {
                    const to_signed = self.isSignedInt(store, p.ty);
                    op = OpBuilder.init(if (to_signed) "llvm.fptosi" else "llvm.fptoui", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                } else if (from_is_f and to_is_f) {
                    if (fw == tw) {
                        break :blk from_v;
                    } else if (fw > tw) {
                        op = OpBuilder.init("llvm.fptrunc", self.loc).builder()
                            .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                    } else {
                        op = OpBuilder.init("llvm.fpext", self.loc).builder()
                            .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                    }
                } else {
                    op = OpBuilder.init("llvm.bitcast", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                }
                self.append(op);
                break :blk op.getResult(0);
            },
            .CastSaturate, .CastWrap, .CastChecked => return error.NotImplemented,

            // ------------- Memory -------------
            .Alloca => blk: {
                const p = t.instrs.get(.Alloca, ins_id);
                var elem_ty: mlir.Type = self.i8_ty;
                switch (store.getKind(p.ty)) {
                    .Ptr => {
                        const ptr_row = store.get(.Ptr, p.ty);
                        elem_ty = try self.llvmTypeOf(store, ptr_row.elem);
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
                const ptr = self.value_map.get(p.ptr).?;
                const res_ty = try self.llvmTypeOf(store, p.ty);
                var load = OpBuilder.init("llvm.load", self.loc).builder()
                    .add_operands(&.{ptr})
                    .add_results(&.{res_ty}).build();
                self.append(load);
                break :blk load.getResult(0);
            },

            .Store => blk: {
                const p = t.instrs.get(.Store, ins_id);
                const v = self.value_map.get(p.value).?;
                const ptr = self.value_map.get(p.ptr).?;
                const st = OpBuilder.init("llvm.store", self.loc).builder()
                    .add_operands(&.{ v, ptr }).build();
                self.append(st);
                break :blk mlir.Value.empty();
            },

            .Gep => blk: {
                const p = t.instrs.get(.Gep, ins_id);
                const base = self.value_map.get(p.base).?;
                const res_ty_row = store.type_pool.data.items[p.ty.toRaw()];
                if (store.getKind(res_ty_row) != .Ptr) return error.CompileError;
                const ptr_row = store.get(.Ptr, p.ty);
                const elem_mlir = try self.llvmTypeOf(store, ptr_row.elem);

                const index_ids = t.instrs.gep_pool.slice(p.indices);
                var indices_data = try self.gpa.alloc(tir.Rows.GepIndex, index_ids.len);
                defer self.gpa.free(indices_data);
                for (index_ids, 0..) |id, i| {
                    indices_data[i] = t.instrs.GepIndex.get(id.toRaw());
                }
                const v = try self.emitGep(base, elem_mlir, indices_data, t);
                break :blk v;
            },

            // ------------- Aggregates -------------
            .TupleMake => blk: {
                const p = t.instrs.get(.TupleMake, ins_id);
                const tup_ty = try self.llvmTypeOf(store, p.ty);
                var acc = self.zeroOf(tup_ty);
                const elems = t.instrs.val_list_pool.slice(p.elems);
                for (elems, 0..) |vid, i| {
                    const v = self.value_map.get(vid).?;
                    acc = self.insertAt(acc, v, &.{@as(i64, @intCast(i))});
                }
                break :blk acc;
            },
            .ArrayMake => blk: {
                const p = t.instrs.get(.ArrayMake, ins_id);
                const arr_ty = try self.llvmTypeOf(store, p.ty);
                var acc = self.zeroOf(arr_ty);
                const elems = t.instrs.val_list_pool.slice(p.elems);
                for (elems, 0..) |vid, i| {
                    const v = self.value_map.get(vid).?;
                    acc = self.insertAt(acc, v, &.{@as(i64, @intCast(i))});
                }
                break :blk acc;
            },
            .StructMake => blk: {
                const p = t.instrs.get(.StructMake, ins_id);
                const st_ty = try self.llvmTypeOf(store, p.ty);
                var acc = self.zeroOf(st_ty);
                const fields = t.instrs.sfi_pool.slice(p.fields);
                for (fields) |f_id| {
                    const f = t.instrs.StructFieldInit.get(f_id.toRaw());
                    const v = self.value_map.get(f.value).?;
                    acc = self.insertAt(acc, v, &.{@as(i64, @intCast(f.index))});
                }
                break :blk acc;
            },
            .ExtractElem => blk: {
                const p = t.instrs.get(.ExtractElem, ins_id);
                const agg = self.value_map.get(p.agg).?;
                const res_ty = try self.llvmTypeOf(store, p.ty);
                const v = self.extractAt(agg, res_ty, &.{@as(i64, @intCast(p.index))});
                break :blk v;
            },

            .InsertElem => blk: {
                const p = t.instrs.get(.InsertElem, ins_id);
                const agg = self.value_map.get(p.agg).?;
                const val = self.value_map.get(p.value).?;
                const v = self.insertAt(agg, val, &.{@as(i64, @intCast(p.index))});
                break :blk v;
            },

            .ExtractField => blk: {
                const p = t.instrs.get(.ExtractField, ins_id);
                const agg = self.value_map.get(p.agg).?;
                const res_ty = try self.llvmTypeOf(store, p.ty);
                const v = self.extractAt(agg, res_ty, &.{@as(i64, @intCast(p.index))});
                break :blk v;
            },

            .InsertField => blk: {
                const p = t.instrs.get(.InsertField, ins_id);
                const agg = self.value_map.get(p.agg).?;
                const val = self.value_map.get(p.value).?;
                const v = self.insertAt(agg, val, &.{@as(i64, @intCast(p.index))});
                break :blk v;
            },

            // ------------- Pointers/Indexing -------------
            .AddressOf => blk: {
                const p = t.instrs.get(.AddressOf, ins_id);
                const v = self.value_map.get(p.value).?;
                if (mlir.LLVM.isLLVMPointerType(v.getType())) break :blk v;
                return error.NotImplemented;
            },

            .Index => blk: {
                const p = t.instrs.get(.Index, ins_id);
                const base = self.value_map.get(p.base).?;
                const res_ty = try self.llvmTypeOf(store, p.ty);

                if (self.isLlvmPtr(base.getType())) {
                    const vptr = try self.emitGep(base, res_ty, &.{.{ .Value = p.index }}, t);
                    var ld = OpBuilder.init("llvm.load", self.loc).builder()
                        .add_operands(&.{vptr})
                        .add_results(&.{res_ty}).build();
                    self.append(ld);
                    break :blk ld.getResult(0);
                } else {
                    if (self.constIntOf(t, p.index)) |cval| {
                        const v = self.extractAt(base, res_ty, &.{@as(i64, @intCast(cval))});
                        break :blk v;
                    } else {
                        return error.NotImplemented; // dynamic index into in-SSA aggregate
                    }
                }
            },

            // ------------- Data movement -------------
            .Select => blk: {
                const p = t.instrs.get(.Select, ins_id);
                const c = self.value_map.get(p.cond).?;
                const tv = self.value_map.get(p.then_value).?;
                const ev = self.value_map.get(p.else_value).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                break :blk self.arithSelect(c, tv, ev, ty);
            },

            .Call => blk: {
                const p = t.instrs.get(.Call, ins_id);
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
        };
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
                var func_op = self.cur_block.?.getParentOperation();
                var name_attr = func_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
                const finfo = self.func_syms.get(name_attr.stringAttrGetValue().toSlice()).?;
                const ret_ty = finfo.ret_type;

                var retop: mlir.Operation = undefined;
                if (!p.value.isNone()) {
                    const v = self.value_map.get(p.value.unwrap()).?;
                    if (ret_ty.equal(self.void_ty)) {
                        retop = OpBuilder.init("func.return", self.loc).builder().build();
                    } else {
                        retop = OpBuilder.init("func.return", self.loc).builder()
                            .add_operands(&.{v}).build();
                    }
                } else {
                    if (!ret_ty.equal(self.void_ty)) {
                        std.debug.panic("Function with non-void return type has a void return", .{});
                    }
                    retop = OpBuilder.init("func.return", self.loc).builder().build();
                }
                self.append(retop);
            },

            .Br => {
                const p = t.terms.get(.Br, term_id);
                const edge = t.terms.Edge.get(p.edge.toRaw());
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
                const cond = self.value_map.get(p.cond).?;

                const tedge = t.terms.Edge.get(p.then_edge.toRaw());
                const eedge = t.terms.Edge.get(p.else_edge.toRaw());
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
        t: *const tir.TIR,
    ) !mlir.Value {
        _ = t;
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
        return self.strAttr(pred);
    }
    fn arithCmpFPredAttr(self: *MlirCodegen, pred: []const u8) mlir.Attribute {
        return self.strAttr(pred);
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
                .add_attributes(&.{self.named("elem_type", mlir.Attribute.typeAttrGet(self.i8_ty))}) // byte-wise GEP
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
                .add_attributes(&.{self.named("elem_type", mlir.Attribute.typeAttrGet(self.i8_ty))})
                .build();
            self.append(gep);
            p = gep.getResult(0);
        }
        const st = OpBuilder.init("llvm.store", self.loc).builder()
            .add_operands(&.{ val, p }).build();
        self.append(st);
    }

    fn constInt(self: *MlirCodegen, ty: mlir.Type, v: u64) mlir.Value {
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
            return .{ .op = self.module.getOperation(), .is_variadic = false, .n_formals = arg_tys.len, .ret_type = ret_ty };
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

        const info: FuncInfo = .{ .op = func_op, .is_variadic = false, .n_formals = arg_tys.len, .ret_type = ret_ty };
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

    fn coerceOnBranch(
        self: *MlirCodegen,
        v: mlir.Value,
        want: mlir.Type,
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

        // last resort (should be rare): bitcast
        var bc = OpBuilder.init("llvm.bitcast", self.loc).builder()
            .add_operands(&.{v}).add_results(&.{want}).build();
        self.append(bc);
        return bc.getResult(0);
    }

    fn llvmTypeOf(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) !mlir.Type {
        return switch (store.getKind(ty)) {
            .Void => self.void_ty,
            .Bool => self.i1_ty,

            .I8, .U8 => mlir.Type.getSignlessIntegerType(self.mlir_ctx, 8),
            .I16, .U16 => mlir.Type.getSignlessIntegerType(self.mlir_ctx, 16),
            .I32, .U32 => mlir.Type.getSignlessIntegerType(self.mlir_ctx, 32),
            .I64, .U64 => mlir.Type.getSignlessIntegerType(self.mlir_ctx, 64),

            .F32 => self.f32_ty,
            .F64 => self.f64_ty,
            .Usize => self.i64_ty,

            .String => self.llvm_ptr_ty,
            .Any => self.llvm_ptr_ty,
            .Function => self.llvm_ptr_ty,
            .Ptr => self.llvm_ptr_ty,

            .Slice => blk: {
                // { ptr, len } (opaque ptr for data)
                const fields = [_]mlir.Type{ self.llvm_ptr_ty, self.i64_ty };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
            },

            .Array => blk: {
                const arr_ty = store.get(.Array, ty);
                const e = try self.llvmTypeOf(store, arr_ty.elem);
                break :blk mlir.LLVM.getLLVMArrayType(e, @intCast(arr_ty.len));
            },

            .Optional => blk: {
                const opt_ty = store.get(.Optional, ty);
                const inner = try self.llvmTypeOf(store, opt_ty.elem);
                const fields = [_]mlir.Type{ self.i1_ty, inner };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
            },

            .ErrorSet => blk: {
                const es = store.get(.ErrorSet, ty);
                const val = try self.llvmTypeOf(store, es.value_ty);
                const fields = [_]mlir.Type{ self.i1_ty, val };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, &fields, false);
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
                    const field = store.Field.get(f.toRaw());
                    buf[i] = try self.llvmTypeOf(store, field.ty);
                }
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.mlir_ctx, buf, false);
            },

            else => std.debug.panic("unhandled type: {}", .{ty}),
        };
    }
};
