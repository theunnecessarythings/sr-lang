const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const compile = @import("compile.zig");
const types = @import("types.zig");

const Allocator = std.mem.Allocator;
const ArrayList = std.array_list.Managed;

pub const MlirCodegen = struct {
    gpa: Allocator,
    ctx: mlir.Context,
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
    llvm_ptr_ty: mlir.Type, // opaque: !llvm.ptr

    // per-module caches
    func_syms: std.StringHashMap(FuncInfo),
    str_pool: std.StringHashMap(mlir.Operation), // text -> llvm.mlir.global op

    // per-function state
    cur_region: ?mlir.Region = null,
    cur_block: ?mlir.Block = null,
    block_map: std.AutoHashMap(tir.BlockId, mlir.Block),
    value_map: std.AutoHashMap(tir.ValueId, mlir.Value),

    pub const FuncInfo = struct {
        op: mlir.Operation,
        is_variadic: bool,
        n_formals: usize, // number of MLIR formals actually in the type (after dropping tail any)
        ret_type: mlir.Type,
    };

    // ------------------------------------------------------------
    // Lightweight Op builder (same style as your sample)
    // ------------------------------------------------------------
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

    // ------------------------------------------------------------
    // Init / Deinit
    // ------------------------------------------------------------
    pub fn init(gpa: Allocator, ctx: mlir.Context) MlirCodegen {
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

    pub fn deinit(self: *MlirCodegen) void {
        self.func_syms.deinit();
        self.str_pool.deinit();
        self.block_map.deinit();
        self.value_map.deinit();
        self.module.destroy();
    }

    // ------------------------------------------------------------
    // Public entry
    // ------------------------------------------------------------
    pub fn emitModule(self: *MlirCodegen, t: *const tir.TIR, store: *types.TypeStore) !mlir.Module {
        const func_ids = t.funcs.func_pool.data.items;
        // Declare/define functions
        for (func_ids) |func_id| {
            try self.emitFunctionHeader(func_id, t, store);
        }
        for (func_ids) |func_id| {
            const func_row = t.funcs.Function.get(func_id.toRaw());
            const block_ids = t.funcs.block_pool.slice(func_row.blocks);
            if (block_ids.len > 0) {
                try self.emitFunctionBody(func_id, t, store);
            }
        }
        return self.module;
    }

    // ------------------------------------------------------------
    // Functions
    // ------------------------------------------------------------
    fn emitFunctionHeader(self: *MlirCodegen, f_id: tir.FuncId, t: *const tir.TIR, store: *types.TypeStore) !void {
        const f = t.funcs.Function.get(f_id.toRaw());
        const params = t.funcs.param_pool.slice(f.params);

        // Build LLVM function type. If last TIR param is `Any`, drop it from MLIR type and set vararg=true.
        var param_tys = try self.gpa.alloc(mlir.Type, params.len);
        defer self.gpa.free(param_tys);
        var mlir_n_formals: usize = 0;
        var is_variadic = false;

        if (params.len > 0) {
            const last_param_row = t.funcs.Param.get(params[params.len - 1].toRaw());
            const last_ty = last_param_row.ty;
            if (self.typeIsAny(store, last_ty)) {
                is_variadic = true;
                // copy all but last
                for (params[0 .. params.len - 1], 0..) |p_id, i| {
                    const p = t.funcs.Param.get(p_id.toRaw());
                    param_tys[i] = try self.llvmTypeOf(store, p.ty);
                }
                mlir_n_formals = params.len - 1;
            } else {
                for (params, 0..) |p_id, i| {
                    const p = t.funcs.Param.get(p_id.toRaw());
                    param_tys[i] = try self.llvmTypeOf(store, p.ty);
                }
                mlir_n_formals = params.len;
            }
        }
        const ret_ty = try self.llvmTypeOf(store, f.result);
        const fn_ty = mlir.LLVM.getLLVMFunctionType(ret_ty, param_tys[0..mlir_n_formals], is_variadic);

        const func_name = t.instrs.strs.get(f.name);
        // If already declared (e.g., from a prior call site), skip redeclaration
        if (self.func_syms.contains(func_name)) return;

        // Create llvm.func @name
        const attrs = [_]mlir.NamedAttribute{
            self.named("sym_name", self.strAttr(func_name)),
            self.named("function_type", mlir.Attribute.typeAttrGet(fn_ty)),
        };
        const region = mlir.Region.create(); // empty now; body added later if defined
        const func_op = OpBuilder.init("llvm.func", self.loc).builder()
            .add_attributes(&attrs)
            .add_regions(&.{region})
            .build();
        var body = self.module.getBody();
        body.appendOwnedOperation(func_op);
        _ = try self.func_syms.put(func_name, .{ .op = func_op, .is_variadic = is_variadic, .n_formals = mlir_n_formals, .ret_type = ret_ty });
    }

    fn emitFunctionBody(self: *MlirCodegen, f_id: tir.FuncId, t: *const tir.TIR, store: *types.TypeStore) !void {
        // ---- reset per-function state
        self.block_map.clearRetainingCapacity();
        self.value_map.clearRetainingCapacity();
        self.cur_region = null;
        self.cur_block = null;

        const f = t.funcs.Function.get(f_id.toRaw());
        const func_name = t.instrs.strs.get(f.name);
        const finfo = self.func_syms.get(func_name).?;
        var func_op = finfo.op;
        var region = func_op.getRegion(0);

        const n_formals = finfo.n_formals;
        const params = t.funcs.param_pool.slice(f.params);

        // ---- entry block arg types come from the *function params* (drop trailing Any)
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

        // ---- map the real entry block id
        if (blocks.len > 0) {
            const entry_bid = blocks[0];
            try self.block_map.put(entry_bid, entry_block);
        }

        // ---- seed value_map with *param ValueIds* -> MLIR entry args
        try self.value_map.ensureTotalCapacity(@intCast(n_formals));
        for (params[0..n_formals], 0..) |p_id, i| {
            const p = t.funcs.Param.get(p_id.toRaw());
            try self.value_map.put(p.value, entry_block.getArgument(i));
        }

        // ---- create remaining MLIR blocks with their block params (if any)
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

        // ---- emit each TIR block
        for (blocks) |b_id| {
            var mblock = self.block_map.get(b_id).?;
            self.cur_block = mblock;
            const bb = t.funcs.Block.get(b_id.toRaw());

            // map block params (if any) for this block
            const b_params = t.funcs.param_pool.slice(bb.params);
            for (b_params, 0..) |bp_id, i| {
                const bp = t.funcs.Param.get(bp_id.toRaw());
                try self.value_map.put(bp.value, mblock.getArgument(i));
            }

            // non-terminator instructions
            const instrs = t.instrs.instr_pool.slice(bb.instrs);
            for (instrs) |ins_id| {
                const v = try self.emitInstr(ins_id, t, store);
                const result_id = self.getInstrResultId(t, ins_id);
                if (result_id) |rid| {
                    try self.value_map.put(rid, v);
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
            inline .Add, .Sub, .Mul, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .LogicalAnd, .LogicalOr, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe => |k| return t.instrs.get(k, id).result,
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
        }
    }

    // ------------------------------------------------------------
    // Instructions
    // ------------------------------------------------------------
    fn emitInstr(self: *MlirCodegen, ins_id: tir.InstrId, t: *const tir.TIR, store: *types.TypeStore) !mlir.Value {
        const kind = t.instrs.index.kinds.items[ins_id.toRaw()];
        return switch (kind) {
            // -------------------- Constants --------------------
            .ConstInt => blk: {
                const p = t.instrs.get(.ConstInt, ins_id);
                const ty = try self.llvmTypeOf(store, p.ty);
                const v = self.constInt(ty, p.value);
                break :blk v;
            },
            .ConstFloat => blk: {
                const p = t.instrs.get(.ConstFloat, ins_id);
                const ty = try self.llvmTypeOf(store, p.ty);
                const v = self.constFloat(ty, p.value);
                break :blk v;
            },
            .ConstBool => blk: {
                const p = t.instrs.get(.ConstBool, ins_id);
                const v = self.constBool(p.value);
                break :blk v;
            },
            .ConstNull => blk: {
                const p = t.instrs.get(.ConstNull, ins_id);
                const ty = try self.llvmTypeOf(store, p.ty); // should be !llvm.ptr
                var op = OpBuilder.init("llvm.mlir.null", self.loc).builder()
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .ConstUndef => blk: {
                const p = t.instrs.get(.ConstUndef, ins_id);
                const ty = try self.llvmTypeOf(store, p.ty);
                var op = OpBuilder.init("llvm.mlir.undef", self.loc).builder()
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .ConstString => blk: {
                const p = t.instrs.get(.ConstString, ins_id);
                const str_text = t.instrs.strs.get(p.text);
                var op = try self.constStringPtr(str_text);
                break :blk op.getResult(0);
            },

            // -------------------- Arithmetic / Bitwise --------------------
            .Add => try self.binArith("llvm.add", "llvm.fadd", t.instrs.get(.Add, ins_id), store),
            .Sub => try self.binArith("llvm.sub", "llvm.fsub", t.instrs.get(.Sub, ins_id), store),
            .Mul => try self.binArith("llvm.mul", "llvm.fmul", t.instrs.get(.Mul, ins_id), store),
            .Div => blk: {
                const p = t.instrs.get(.Div, ins_id);
                var lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                const name = if (self.isFloatType(lhs.getType())) "llvm.fdiv" else if (self.isUnsigned(store, p.ty)) "llvm.udiv" else "llvm.sdiv";
                var op = OpBuilder.init(name, self.loc).builder()
                    .add_operands(&.{ lhs, rhs })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },

            .Mod => blk: {
                const p = t.instrs.get(.Mod, ins_id);
                var lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                const name = if (self.isFloatType(lhs.getType())) "llvm.frem" else if (self.isUnsigned(store, p.ty)) "llvm.urem" else "llvm.srem";
                var op = OpBuilder.init(name, self.loc).builder()
                    .add_operands(&.{ lhs, rhs })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },

            .Shl => blk: {
                const p = t.instrs.get(.Shl, ins_id);
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                var op = OpBuilder.init("llvm.shl", self.loc).builder()
                    .add_operands(&.{ lhs, rhs })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .Shr => blk: {
                const p = t.instrs.get(.Shr, ins_id);
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                const name = if (self.isUnsigned(store, p.ty)) "llvm.lshr" else "llvm.ashr";
                var op = OpBuilder.init(name, self.loc).builder()
                    .add_operands(&.{ lhs, rhs })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },

            .BitAnd => try self.binBit("llvm.and", t.instrs.get(.BitAnd, ins_id), store),
            .BitOr => try self.binBit("llvm.or", t.instrs.get(.BitOr, ins_id), store),
            .BitXor => try self.binBit("llvm.xor", t.instrs.get(.BitXor, ins_id), store),

            // -------------------- Logical --------------------
            .LogicalAnd => try self.binBit("llvm.and", t.instrs.get(.LogicalAnd, ins_id), store),
            .LogicalOr => try self.binBit("llvm.or", t.instrs.get(.LogicalOr, ins_id), store),
            .LogicalNot => blk: {
                const p = t.instrs.get(.LogicalNot, ins_id);
                const v = self.value_map.get(p.value).?;
                const one = self.constBool(true);
                var op = OpBuilder.init("llvm.xor", self.loc).builder()
                    .add_operands(&.{ v, one })
                    .add_results(&.{self.i1_ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },

            // -------------------- Comparisons --------------------
            .CmpEq => try self.emitCmp("eq", "eq", "oeq", t.instrs.get(.CmpEq, ins_id)),
            .CmpNe => try self.emitCmp("ne", "ne", "one", t.instrs.get(.CmpNe, ins_id)),
            .CmpLt => try self.emitCmp("ult", "slt", "olt", t.instrs.get(.CmpLt, ins_id)),
            .CmpLe => try self.emitCmp("ule", "sle", "ole", t.instrs.get(.CmpLe, ins_id)),
            .CmpGt => try self.emitCmp("ugt", "sgt", "ogt", t.instrs.get(.CmpGt, ins_id)),
            .CmpGe => try self.emitCmp("uge", "sge", "oge", t.instrs.get(.CmpGe, ins_id)),

            // -------------------- Casts (minimal) --------------------
            .CastBit => blk: {
                const p = t.instrs.get(.CastBit, ins_id);
                const to_ty = try self.llvmTypeOf(store, p.ty);
                const from_v = self.value_map.get(p.value).?;
                var op = OpBuilder.init("llvm.bitcast", self.loc).builder()
                    .add_operands(&.{from_v})
                    .add_results(&.{to_ty})
                    .build();
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

                var op =
                    if (from_is_ptr and to_is_ptr) OpBuilder.init("llvm.bitcast", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build() else if (from_is_ptr and to_is_int) OpBuilder.init("llvm.ptrtoint", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build() else if (from_is_int and to_is_ptr) OpBuilder.init("llvm.inttoptr", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build() else if (from_is_int and to_is_int)
                    blk2: {
                        const fw = try intOrFloatWidth(from_ty);
                        const tw = try intOrFloatWidth(to_ty);
                        break :blk2 if (fw == tw)
                            OpBuilder.init("llvm.bitcast", self.loc).builder()
                                .add_operands(&.{from_v}).add_results(&.{to_ty}).build()
                        else if (fw > tw)
                            OpBuilder.init("llvm.trunc", self.loc).builder()
                                .add_operands(&.{from_v}).add_results(&.{to_ty}).build()
                        else if (self.isSignedInt(store, p.ty))
                            OpBuilder.init("llvm.sext", self.loc).builder()
                                .add_operands(&.{from_v}).add_results(&.{to_ty}).build()
                        else
                            OpBuilder.init("llvm.zext", self.loc).builder()
                                .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                    } else if (from_is_int and to_is_f)
                        OpBuilder.init(if (self.isSignedInt(store, p.ty)) "llvm.sitofp" else "llvm.uitofp", self.loc).builder()
                            .add_operands(&.{from_v}).add_results(&.{to_ty}).build()
                    else if (from_is_f and to_is_int)
                        OpBuilder.init(if (self.isSignedInt(store, p.ty)) "llvm.fptosi" else "llvm.fptoui", self.loc).builder()
                            .add_operands(&.{from_v}).add_results(&.{to_ty}).build()
                    else if (from_is_f and to_is_f) blk3: {
                        const fw = try intOrFloatWidth(from_ty);
                        const tw = try intOrFloatWidth(to_ty);
                        break :blk3 if (fw == tw)
                            OpBuilder.init("llvm.bitcast", self.loc).builder()
                                .add_operands(&.{from_v}).add_results(&.{to_ty}).build()
                        else if (fw > tw)
                            OpBuilder.init("llvm.fptrunc", self.loc).builder()
                                .add_operands(&.{from_v}).add_results(&.{to_ty}).build()
                        else
                            OpBuilder.init("llvm.fpext", self.loc).builder()
                                .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                    } else OpBuilder.init("llvm.bitcast", self.loc).builder()
                        .add_operands(&.{from_v}).add_results(&.{to_ty}).build();

                self.append(op);
                break :blk op.getResult(0);
            },
            .CastSaturate, .CastWrap, .CastChecked => return error.NotImplemented,

            // -------------------- Memory --------------------
            .Alloca => blk: {
                const p = t.instrs.get(.Alloca, ins_id);
                // TIR: result type is a pointer; elem type = pointee
                const resT = self.llvmTypeOf(store, p.ty) catch self.llvm_ptr_ty;
                _ = resT;

                // Find pointee type for elem_type attribute
                var elem_ty: mlir.Type = self.i8_ty;
                switch (store.getKind(p.ty)) {
                    .Ptr => {
                        const ptr_ty = store.get(.Ptr, p.ty);
                        elem_ty = try self.llvmTypeOf(store, ptr_ty.elem);
                    },
                    else => {}, // fallback; shouldn't really happen for Alloca
                }

                // Count operand: use provided value or default to 1
                var count_v: mlir.Value = undefined;
                if (!p.count.isNone()) {
                    count_v = self.value_map.get(p.count.unwrap()).?;
                } else {
                    count_v = self.llvmConstI64(1);
                }

                var attrs = [_]mlir.NamedAttribute{
                    self.named("elem_type", mlir.Attribute.typeAttrGet(elem_ty)),
                };

                var alloca = OpBuilder.init("llvm.alloca", self.loc).builder()
                    .add_operands(&.{count_v}) // REQUIRED operand
                    .add_results(&.{self.llvm_ptr_ty}) // result is !llvm.ptr
                    .add_attributes(&attrs)
                    .build();
                self.append(alloca);
                break :blk alloca.getResult(0);
            },

            .Load => blk: {
                const p = t.instrs.get(.Load, ins_id);
                const ptr = self.value_map.get(p.ptr).?;
                const res_ty = try self.llvmTypeOf(store, p.ty);
                var load = OpBuilder.init("llvm.load", self.loc).builder()
                    .add_operands(&.{ptr}) // address
                    .add_results(&.{res_ty}) // loaded value type
                    .build();
                self.append(load);
                break :blk load.getResult(0);
            },

            .Store => blk: {
                const p = t.instrs.get(.Store, ins_id);
                const v = self.value_map.get(p.value).?;
                const ptr = self.value_map.get(p.ptr).?;
                const st = OpBuilder.init("llvm.store", self.loc).builder()
                    .add_operands(&.{ v, ptr }) // (value, address)
                    .build();
                self.append(st);
                break :blk mlir.Value.empty();
            },
            .Gep => blk: {
                const p = t.instrs.get(.Gep, ins_id);
                const base = self.value_map.get(p.base).?;
                const resT = store.type_pool.data.items[p.ty.toRaw()];
                if (store.getKind(resT) != .Ptr) return error.CompileError;
                const res_ty = store.get(.Ptr, p.ty);
                const elem_mlir = try self.llvmTypeOf(store, res_ty.elem);
                const index_ids = t.instrs.gep_pool.slice(p.indices);
                var indices_data = try self.gpa.alloc(tir.Rows.GepIndex, index_ids.len);
                defer self.gpa.free(indices_data);

                for (index_ids, 0..) |id, i| {
                    indices_data[i] = t.instrs.GepIndex.get(id.toRaw());
                }

                const v = try self.emitGep(base, elem_mlir, indices_data, t);
                break :blk v;
            },

            // -------------------- Aggregates --------------------
            .TupleMake => blk: {
                const p = t.instrs.get(.TupleMake, ins_id);
                const tup_ty = try self.llvmTypeOf(store, p.ty);
                var acc = self.undefOf(tup_ty);
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
                var acc = self.undefOf(arr_ty);
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
                var acc = self.undefOf(st_ty);
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

            // -------------------- Pointers/Indexing --------------------
            .AddressOf => blk: {
                const p = t.instrs.get(.AddressOf, ins_id);
                var v = self.value_map.get(p.value).?;
                if (mlir.LLVM.isLLVMPointerType(v.getType())) break :blk v;
                return error.NotImplemented;
            },
            .Index => blk: {
                const p = t.instrs.get(.Index, ins_id);
                const base = self.value_map.get(p.base).?;
                const gep_type_kind = store.index.kinds.items[p.ty.toRaw()];
                if (gep_type_kind != .Ptr) return error.CompileError;
                const ptr_row = store.get(.Ptr, p.ty);
                const elem_mlir = try self.llvmTypeOf(store, ptr_row.elem);

                const v = try self.emitGep(base, elem_mlir, &.{.{ .Value = p.index }}, t);
                break :blk v;
            },

            // -------------------- Control/Data --------------------
            .Select => blk: {
                const p = t.instrs.get(.Select, ins_id);
                const c = self.value_map.get(p.cond).?;
                const tv = self.value_map.get(p.then_value).?;
                const ev = self.value_map.get(p.else_value).?;
                const ty = try self.llvmTypeOf(store, p.ty);
                var op = OpBuilder.init("llvm.select", self.loc).builder()
                    .add_operands(&.{ c, tv, ev })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .Call => blk: {
                const p = t.instrs.get(.Call, ins_id);
                const callee_name = t.instrs.strs.get(p.callee);
                const finfo = self.func_syms.get(callee_name) orelse try self.ensureDeclFromCall(ins_id, t, store);

                const args_slice = t.instrs.val_list_pool.slice(p.args);
                var args = try self.gpa.alloc(mlir.Value, args_slice.len);
                defer self.gpa.free(args);
                for (args_slice, 0..) |vid, i| args[i] = self.value_map.get(vid).?;

                const ret_ty = try self.llvmTypeOf(store, p.ty);

                var attrs = ArrayList(mlir.NamedAttribute).init(self.gpa);
                defer attrs.deinit();

                try attrs.append(self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.ctx, mlir.StringRef.from(callee_name))));
                const seg = mlir.Attribute.denseI32ArrayGet(self.ctx, &[_]i32{ @intCast(args.len), 0 });
                try attrs.append(self.named("operandSegmentSizes", seg));
                const empty_bundles = mlir.Attribute.denseI32ArrayGet(self.ctx, &[_]i32{});
                try attrs.append(self.named("op_bundle_sizes", empty_bundles));

                if (finfo.is_variadic) {
                    var arg_tys = try self.gpa.alloc(mlir.Type, args.len);
                    defer self.gpa.free(arg_tys);
                    for (args, 0..) |*a, i| arg_tys[i] = a.getType();
                    const var_fty = mlir.LLVM.getLLVMFunctionType(ret_ty, arg_tys, true);
                    try attrs.append(self.named("var_callee_type", mlir.Attribute.typeAttrGet(var_fty)));
                }

                var call = OpBuilder.init("llvm.call", self.loc).builder()
                    .add_operands(args)
                    .add_results(if (self.void_ty.equal(ret_ty)) &.{} else &.{ret_ty})
                    .add_attributes(attrs.items)
                    .build();

                self.append(call);
                break :blk if (call.getNumResults() == 0) mlir.Value.empty() else call.getResult(0);
            },
        };
    }

    fn emitCmp(self: *MlirCodegen, pred_u: []const u8, pred_s: []const u8, pred_f: []const u8, p: tir.Rows.Bin2) !mlir.Value {
        var lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;

        const lty = lhs.getType();
        const is_float = lty.isAFloat();

        if (is_float) {
            var op = OpBuilder.init("llvm.fcmp", self.loc).builder()
                .add_operands(&.{ lhs, rhs })
                .add_results(&.{self.i1_ty})
                .add_attributes(&.{self.named("predicate", self.strAttr(pred_f))})
                .build();
            self.append(op);
            return op.getResult(0);
        } else {
            const unsigned = true;
            const pred = if (unsigned) pred_u else pred_s;
            var op = OpBuilder.init("llvm.icmp", self.loc).builder()
                .add_operands(&.{ lhs, rhs })
                .add_results(&.{self.i1_ty})
                .add_attributes(&.{self.named("predicate", self.strAttr(pred))})
                .build();
            self.append(op);
            return op.getResult(0);
        }
    }

    fn emitTerminator(self: *MlirCodegen, term_id: tir.TermId, t: *const tir.TIR, store: *types.TypeStore) !void {
        _ = store;
        const kind = t.terms.index.kinds.items[term_id.toRaw()];
        switch (kind) {
            .Return => {
                const p = t.terms.get(.Return, term_id);
                var func_op = self.cur_block.?.getParentOperation();
                const func_name_attr = func_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
                var func_name_ref = func_name_attr.stringAttrGetValue();
                const func_name = func_name_ref.toSlice();
                const finfo = self.func_syms.get(func_name).?;
                const ret_mlir_type = finfo.ret_type;

                const op = if (!p.value.isNone()) blk: {
                    const v_opt = self.value_map.get(p.value.unwrap());
                    var v: mlir.Value = undefined;
                    if (v_opt) |vv| {
                        v = vv;
                    } else {
                        // Fallback: if the return value is a block param and wasn't mapped, use the first block argument
                        // (common for join blocks with a single result parameter)
                        const argc = self.cur_block.?.getNumArguments();
                        std.debug.assert(argc > 0);
                        v = self.cur_block.?.getArgument(0);
                    }
                    if (ret_mlir_type.equal(self.void_ty)) {
                        // Function returns void, but TIR has a value. This indicates an inconsistency.
                        // For now, we\'ll generate a void return, but this should ideally be caught earlier.
                        std.debug.print("Warning: Function with void return type has a return instruction with a value. Ignoring the value.\n", .{});
                        break :blk OpBuilder.init("llvm.return", self.loc).builder().add_results(&.{}).build();
                    } else {
                        break :blk OpBuilder.init("llvm.return", self.loc).builder()
                            .add_operands(&.{v})
                            .add_results(&.{}) // Explicitly no results
                            .build();
                    }
                } else blk: {
                    if (!ret_mlir_type.equal(self.void_ty)) {
                        // Function has a non-void return type but TIR return instruction has no value.
                        // This is an error.
                        std.debug.panic("Function with non-void return type has a return instruction with no value", .{});
                    }
                    break :blk OpBuilder.init("llvm.return", self.loc).builder().add_results(&.{}).build();
                };
                self.append(op);
            },

            .Br => |edge_p| {
                _ = edge_p;
                const p = t.terms.get(.Br, term_id);
                const edge = t.terms.Edge.get(p.edge.toRaw());
                var dest = self.block_map.get(edge.dest).?;
                const args = t.instrs.value_pool.slice(edge.args);
                std.debug.assert(dest.getNumArguments() == args.len);

                var small: [4]mlir.Value = undefined;
                var argv: []mlir.Value = if (args.len <= small.len) small[0..args.len] else try self.gpa.alloc(mlir.Value, args.len);
                defer if (argv.ptr != &small) self.gpa.free(argv);

                for (args, 0..) |avid, i| {
                    var v = self.value_map.get(avid).?;
                    var want_arg = dest.getArgument(i);
                    const want = want_arg.getType();
                    if (!v.getType().equal(want)) {
                        if (self.isLlvmPtr(v.getType()) and self.isLlvmPtr(want)) {
                            var bc = OpBuilder.init("llvm.bitcast", self.loc).builder()
                                .add_operands(&.{v})
                                .add_results(&.{want})
                                .build();
                            self.append(bc);
                            v = bc.getResult(0);
                        } else {
                            @panic("branch arg type mismatch");
                        }
                    }
                    argv[i] = v;
                }

                const br = OpBuilder.init("llvm.br", self.loc).builder()
                    .add_operands(argv)
                    .add_successors(&.{dest})
                    .build();
                self.append(br);
            },

            .CondBr => |cb_p| {
                _ = cb_p;
                const p = t.terms.get(.CondBr, term_id);
                const cond = self.value_map.get(p.cond).?;
                const then_edge = t.terms.Edge.get(p.then_edge.toRaw());
                const else_edge = t.terms.Edge.get(p.else_edge.toRaw());
                const tdest = self.block_map.get(then_edge.dest).?;
                const edest = self.block_map.get(else_edge.dest).?;

                const then_args = t.instrs.value_pool.slice(then_edge.args);
                const else_args = t.instrs.value_pool.slice(else_edge.args);

                const n_then = then_args.len;
                const n_else = else_args.len;
                const total = 1 + n_then + n_else;

                var ops = try self.gpa.alloc(mlir.Value, total);
                defer self.gpa.free(ops);
                ops[0] = cond;

                var k: usize = 1;
                for (then_args) |vid| {
                    ops[k] = self.value_map.get(vid).?;
                    k += 1;
                }
                for (else_args) |vid| {
                    ops[k] = self.value_map.get(vid).?;
                    k += 1;
                }

                const seg = mlir.Attribute.denseI32ArrayGet(self.ctx, &[_]i32{
                    1, @intCast(n_then), @intCast(n_else),
                });

                const br = OpBuilder.init("llvm.cond_br", self.loc).builder()
                    .add_operands(ops)
                    .add_successors(&.{ tdest, edest })
                    .add_attributes(&.{self.named("operandSegmentSizes", seg)})
                    .build();
                self.append(br);
            },

            .SwitchInt => |sw_p| {
                _ = sw_p;
                const p = t.terms.get(.SwitchInt, term_id);
                var scrut = self.value_map.get(p.scrut).?;
                const default_edge = t.terms.Edge.get(p.default_edge.toRaw());
                const default_dest = self.block_map.get(default_edge.dest).?;
                const default_args = t.instrs.value_pool.slice(default_edge.args);

                const ndef = default_args.len;
                const def_ops = if (ndef == 0) &[_]mlir.Value{} else blk: {
                    const buf = try self.gpa.alloc(mlir.Value, ndef);
                    for (default_args, 0..) |vid, i| buf[i] = self.value_map.get(vid).?;
                    break :blk buf;
                };
                defer if (ndef > 0) self.gpa.free(def_ops);

                const cases = t.terms.case_pool.slice(p.cases);
                if (cases.len == 0) {
                    const br = OpBuilder.init("llvm.br", self.loc).builder()
                        .add_operands(def_ops)
                        .add_successors(&.{default_dest})
                        .build();
                    self.append(br);
                    return;
                }

                var next_block: ?mlir.Block = null;

                for (cases, 0..) |c_id, idx| {
                    if (idx != 0) {
                        const nb = mlir.Block.create(&.{}, &.{});
                        self.cur_region.?.appendOwnedBlock(nb);
                        _ = next_block.?;
                        self.cur_block = nb;
                        next_block = nb;
                    } else {
                        next_block = self.cur_block.?;
                    }

                    const c = t.terms.Case.get(c_id.toRaw());
                    const c_ty = scrut.getType();
                    const case_val = self.constInt(c_ty, @bitCast(c.value));

                    var icmp = OpBuilder.init("llvm.icmp", self.loc).builder()
                        .add_operands(&.{ scrut, case_val })
                        .add_results(&.{self.i1_ty})
                        .add_attributes(&.{self.named("predicate", self.strAttr("eq"))})
                        .build();
                    self.append(icmp);

                    const case_edge = t.terms.Edge.get(c.edge.toRaw());
                    const case_args = t.instrs.value_pool.slice(case_edge.args);
                    const nt = case_args.len;
                    const t_ops = if (nt == 0) &[_]mlir.Value{} else blk: {
                        const buf = try self.gpa.alloc(mlir.Value, nt);
                        for (case_args, 0..) |vid, i| buf[i] = self.value_map.get(vid).?;
                        break :blk buf;
                    };
                    defer if (nt > 0) self.gpa.free(t_ops);

                    const false_is_last = (idx + 1 == cases.len);
                    const false_dest = if (false_is_last) default_dest else blk: {
                        const nb = mlir.Block.create(&.{}, &.{});
                        self.cur_region.?.appendOwnedBlock(nb);
                        break :blk nb;
                    };

                    const total = 1 + nt + (if (false_is_last) ndef else 0);
                    var ops = try self.gpa.alloc(mlir.Value, total);
                    defer self.gpa.free(ops);
                    ops[0] = icmp.getResult(0);
                    var k: usize = 1;
                    for (t_ops) |v| {
                        ops[k] = v;
                        k += 1;
                    }
                    if (false_is_last) {
                        for (def_ops) |v| {
                            ops[k] = v;
                            k += 1;
                        }
                    }

                    const seg = mlir.Attribute.denseI32ArrayGet(self.ctx, &[_]i32{
                        1, @intCast(nt), @intCast(if (false_is_last) ndef else 0),
                    });
                    const tdest = self.block_map.get(case_edge.dest).?;
                    const condbr = OpBuilder.init("llvm.cond_br", self.loc).builder()
                        .add_operands(ops)
                        .add_successors(&.{ tdest, false_dest })
                        .add_attributes(&.{self.named("operandSegmentSizes", seg)})
                        .build();
                    self.append(condbr);

                    if (!false_is_last) {
                        self.cur_block = false_dest;
                        next_block = false_dest;
                    }
                }
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
                self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.ctx, raw)),
            })
            .build();
        self.append(op);
        return op.getResult(0);
    }

    // ------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------
    fn append(self: *MlirCodegen, op: mlir.Operation) void {
        self.cur_block.?.appendOwnedOperation(op);
    }
    fn named(self: *const MlirCodegen, name: []const u8, attr: mlir.Attribute) mlir.NamedAttribute {
        return .{
            .inner = .{
                .name = mlir.c.mlirIdentifierGet(self.ctx.handle, mlir.StringRef.from(name).inner),
                .attribute = attr.handle,
            },
        };
    }
    fn strAttr(self: *const MlirCodegen, s: []const u8) mlir.Attribute {
        return mlir.Attribute.stringAttrGet(self.ctx, mlir.StringRef.from(s));
    }
    fn intAttr(self: *const MlirCodegen, ty: mlir.Type, val: i64) mlir.Attribute {
        _ = self;
        return mlir.Attribute.integerAttrGet(ty, val);
    }

    fn isLlvmPtr(self: *const MlirCodegen, ty: mlir.Type) bool {
        return ty.equal(self.llvm_ptr_ty);
    }

    fn llvmConstI64(self: *MlirCodegen, x: i64) mlir.Value {
        const val = mlir.Attribute.integerAttrGet(self.i64_ty, x);
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{self.i64_ty})
            .add_attributes(&.{self.named("value", val)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn undefOf(self: *MlirCodegen, ty: mlir.Type) mlir.Value {
        var op = OpBuilder.init("llvm.mlir.undef", self.loc).builder()
            .add_results(&.{ty})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn insertAt(self: *MlirCodegen, agg: mlir.Value, val: mlir.Value, pos: []const i64) mlir.Value {
        var agg_l = agg;
        const pos_attr = mlir.Attribute.denseI64ArrayGet(self.ctx, pos);
        var op = OpBuilder.init("llvm.insertvalue", self.loc).builder()
            .add_operands(&.{ agg, val })
            .add_results(&.{agg_l.getType()})
            .add_attributes(&.{self.named("position", pos_attr)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn extractAt(self: *MlirCodegen, agg: mlir.Value, res_ty: mlir.Type, pos: []const i64) mlir.Value {
        const pos_attr = mlir.Attribute.denseI64ArrayGet(self.ctx, pos);
        var op = OpBuilder.init("llvm.extractvalue", self.loc).builder()
            .add_operands(&.{agg})
            .add_results(&.{res_ty})
            .add_attributes(&.{self.named("position", pos_attr)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn constInt(self: *MlirCodegen, ty: mlir.Type, v: i64) mlir.Value {
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{ty})
            .add_attributes(&.{self.named("value", mlir.Attribute.integerAttrGet(ty, v))})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn constFloat(self: *MlirCodegen, ty: mlir.Type, v: f64) mlir.Value {
        const attr = mlir.Attribute.floatAttrDoubleGet(self.ctx, ty, v);
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{ty})
            .add_attributes(&.{self.named("value", attr)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn constBool(self: *MlirCodegen, v: bool) mlir.Value {
        return self.constInt(self.i1_ty, if (v) 1 else 0);
    }

    fn isUnsigned(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) bool {
        _ = self;
        return switch (store.getKind(ty)) {
            .Usize => true,
            .U32, .U64 => true,
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

    fn binBit(self: *MlirCodegen, name: []const u8, p: tir.Rows.Bin2, store: *types.TypeStore) !mlir.Value {
        const lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;
        const ty = try self.llvmTypeOf(store, p.ty);
        var op = OpBuilder.init(name, self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{ty})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn binArith(self: *MlirCodegen, intName: []const u8, floatName: []const u8, p: tir.Rows.Bin2, store: *types.TypeStore) !mlir.Value {
        var lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;
        const ty = try self.llvmTypeOf(store, p.ty);
        const name = if (self.isFloatType(lhs.getType())) floatName else intName;
        var op = OpBuilder.init(name, self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{ty})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn ensureDeclFromCall(self: *MlirCodegen, ins_id: tir.InstrId, t: *const tir.TIR, store: *types.TypeStore) !FuncInfo {
        const p = t.instrs.get(.Call, ins_id);
        const args_slice = t.instrs.val_list_pool.slice(p.args);
        var args = try self.gpa.alloc(mlir.Value, args_slice.len);
        defer self.gpa.free(args);
        var arg_tys = try self.gpa.alloc(mlir.Type, args_slice.len);
        defer self.gpa.free(arg_tys);
        for (args_slice, 0..) |vid, i| {
            var v = self.value_map.get(vid).?;
            args[i] = v;
            arg_tys[i] = v.getType();
        }
        const ret_ty = try self.llvmTypeOf(store, p.ty);
        const fn_ty = mlir.LLVM.getLLVMFunctionType(ret_ty, arg_tys, true);
        const name = t.instrs.strs.get(p.callee);
        // If the callee name is a mangled imported function (m$...), it will be defined later
        // when that module is emitted. Avoid emitting a provisional declaration with a mismatched
        // signature; just return a lightweight FuncInfo for call attribute decisions.
        if (std.mem.startsWith(u8, name, "m$")) {
            return .{ .op = self.module.getOperation(), .is_variadic = false, .n_formals = args_slice.len, .ret_type = ret_ty };
        }
        const attrs = [_]mlir.NamedAttribute{
            self.named("sym_name", self.strAttr(name)),
            self.named("function_type", mlir.Attribute.typeAttrGet(fn_ty)),
        };
        const region = mlir.Region.create();
        const func_op = OpBuilder.init("llvm.func", self.loc).builder()
            .add_attributes(&attrs)
            .add_regions(&.{region})
            .build();
        var body = self.module.getBody();
        body.appendOwnedOperation(func_op);
        const info: FuncInfo = .{ .op = func_op, .is_variadic = true, .n_formals = arg_tys.len, .ret_type = ret_ty };
        _ = try self.func_syms.put(name, info);
        return info;
    }

    fn constStringPtr(self: *MlirCodegen, text: []const u8) !mlir.Operation {
        if (self.str_pool.get(text)) |*g| {
            return self.addrOfFirstChar(@constCast(g));
        }
        const esc = try self.escapeForMlirString(text);
        defer self.gpa.free(esc);
        const name = try std.fmt.allocPrint(self.gpa, "str_{d}", .{self.str_pool.count()});
        defer self.gpa.free(name);
        const glb_src = try std.fmt.allocPrint(
            self.gpa,
            "llvm.mlir.global internal constant @{s}(\"{s}\\00\") {{addr_space = 0:i32}}",
            .{ name, esc },
        );
        defer self.gpa.free(glb_src);
        var global_op = mlir.Operation.createParse(self.ctx, mlir.StringRef.from(glb_src), mlir.StringRef.from("llvm.mlir.global"));
        var body = self.module.getBody();
        body.appendOwnedOperation(global_op);
        _ = try self.str_pool.put(text, global_op);
        return self.addrOfFirstChar(&global_op);
    }

    fn addrOfFirstChar(self: *MlirCodegen, global_op: *mlir.Operation) !mlir.Operation {
        const name_attr = global_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
        const gsym = mlir.Attribute.flatSymbolRefAttrGet(self.ctx, mlir.Attribute.stringAttrGetValue(name_attr));
        var addr = OpBuilder.init("llvm.mlir.addressof", self.loc).builder()
            .add_results(&.{self.llvm_ptr_ty})
            .add_attributes(&.{self.named("global_name", gsym)})
            .build();
        self.append(addr);
        const value_attr = global_op.getInherentAttributeByName(mlir.StringRef.from("value"));
        var lit = mlir.Attribute.stringAttrGetValue(value_attr);
        const n: usize = lit.length() + 1; // +1 nul
        const arr_ty = mlir.LLVM.getLLVMArrayType(self.i8_ty, @intCast(n));
        const gep = OpBuilder.init("llvm.getelementptr", self.loc).builder()
            .add_operands(&.{addr.getResult(0)})
            .add_results(&.{self.llvm_ptr_ty})
            .add_attributes(&.{
                self.named("rawConstantIndices", mlir.Attribute.denseI32ArrayGet(self.ctx, &[_]i32{ 0, 0 })),
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

    fn typeIsAny(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) bool {
        _ = self;
        return switch (store.getKind(ty)) {
            .Any => true,
            else => false,
        };
    }

    fn intWidth(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) u32 {
        _ = self;
        return switch (store.getKind(ty)) {
            .I8, .U8 => 8,
            .I16, .U16 => 16,
            .I32, .U32 => 32,
            .I64, .U64 => 64,
            .Usize => 64, // TODO: target bits
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

    fn llvmTypeOf(self: *MlirCodegen, store: *types.TypeStore, ty: types.TypeId) !mlir.Type {
        return switch (store.getKind(ty)) {
            .Void => self.void_ty,
            .Bool => self.i1_ty,

            .I8, .U8 => mlir.Type.getSignlessIntegerType(self.ctx, 8),
            .I16, .U16 => mlir.Type.getSignlessIntegerType(self.ctx, 16),
            .I32, .U32 => mlir.Type.getSignlessIntegerType(self.ctx, 32),
            .I64, .U64 => mlir.Type.getSignlessIntegerType(self.ctx, 64),

            .F32 => self.f32_ty,
            .F64 => self.f64_ty,
            .Usize => self.i64_ty,

            .String => self.llvm_ptr_ty,

            .Any => self.llvm_ptr_ty,

            .Ptr => self.llvm_ptr_ty,

            .Slice => blk: {
                const slice_ty = store.get(.Slice, ty);
                const elem_ty = try self.llvmTypeOf(store, slice_ty.elem);
                _ = elem_ty;
                const fields = [_]mlir.Type{ self.llvm_ptr_ty, self.i64_ty };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.ctx, &fields, false);
            },

            .Array => blk: {
                const arr_ty = store.get(.Array, ty);
                const e = try self.llvmTypeOf(store, arr_ty.elem);
                const len = self.intWidth(store, arr_ty.elem);
                break :blk mlir.LLVM.getLLVMArrayType(e, len);
            },

            .Optional => blk: {
                const opt_ty = store.get(.Optional, ty);
                const inner = try self.llvmTypeOf(store, opt_ty.elem);
                const fields = [_]mlir.Type{ self.i1_ty, inner };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.ctx, &fields, false);
            },

            .ErrorSet => blk: {
                const es = store.get(.ErrorSet, ty);
                const val = try self.llvmTypeOf(store, es.value_ty);
                const fields = [_]mlir.Type{ self.i1_ty, val };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.ctx, &fields, false);
            },

            .Tuple => blk: {
                const tup_ty = store.get(.Tuple, ty);
                const n = tup_ty.elems.len;
                var buf = try self.gpa.alloc(mlir.Type, n);
                defer self.gpa.free(buf);
                const elems = store.type_pool.slice(tup_ty.elems);
                for (elems, 0..) |eid, i| buf[i] = try self.llvmTypeOf(store, eid);
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.ctx, buf, false);
            },

            .Function => self.llvm_ptr_ty,

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
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.ctx, buf, false);
            },
            else => std.debug.panic("unhandled type: {}", .{ty}),
        };
    }
};
