const std = @import("std");
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");

const Allocator = std.mem.Allocator;
const ArrayList = std.array_list.Managed;

pub const TirLlvmGen = struct {
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
    llvm_ptr_ty: mlir.Type, // opaque: !llvm.ptr<0>

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
    pub fn init(gpa: Allocator) TirLlvmGen {
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

    pub fn deinit(self: *TirLlvmGen) void {
        self.func_syms.deinit();
        self.str_pool.deinit();
        self.block_map.deinit();
        self.value_map.deinit();
        self.module.destroy();
        self.ctx.destroy();
    }

    // ------------------------------------------------------------
    // Public entry
    // ------------------------------------------------------------
    pub fn emitModule(self: *TirLlvmGen, tm: *const tir.Module, arena: *types.TypeArena) !mlir.Module {
        // Declare/define functions
        for (tm.functions.items) |*f| {
            try self.emitFunctionHeader(f, arena);
        }
        for (tm.functions.items) |*f| {
            if (f.blocks.items.len != 0) {
                try self.emitFunctionBody(f, arena);
            }
        }
        return self.module;
    }

    // ------------------------------------------------------------
    // Functions
    // ------------------------------------------------------------
    fn emitFunctionHeader(self: *TirLlvmGen, f: *const tir.Function, arena: *types.TypeArena) !void {
        // Build LLVM function type. If last TIR param is `Any`, drop it from MLIR type and set vararg=true.
        var param_tys = try self.gpa.alloc(mlir.Type, f.params.items.len);
        defer self.gpa.free(param_tys);
        var mlir_n_formals: usize = 0;
        var is_variadic = false;

        if (f.params.items.len > 0) {
            const last_ty = f.params.items[f.params.items.len - 1].ty;
            if (self.typeIsAny(arena, last_ty)) {
                is_variadic = true;
                // copy all but last
                for (f.params.items[0 .. f.params.items.len - 1], 0..) |p, i| {
                    param_tys[i] = try self.llvmTypeOf(arena, p.ty);
                }
                mlir_n_formals = f.params.items.len - 1;
            } else {
                for (f.params.items, 0..) |p, i| {
                    param_tys[i] = try self.llvmTypeOf(arena, p.ty);
                }
                mlir_n_formals = f.params.items.len;
            }
        }
        const ret_ty = try self.llvmTypeOf(arena, f.result);
        const fn_ty = mlir.LLVM.getLLVMFunctionType(ret_ty, param_tys[0..mlir_n_formals], is_variadic);

        // Create llvm.func @name
        const attrs = [_]mlir.NamedAttribute{
            self.named("sym_name", self.strAttr(f.name)),
            self.named("function_type", mlir.Attribute.typeAttrGet(fn_ty)),
        };
        const region = mlir.Region.create(); // empty now; body added later if defined
        const func_op = OpBuilder.init("llvm.func", self.loc).builder()
            .add_attributes(&attrs)
            .add_regions(&.{region})
            .build();
        var body = self.module.getBody();
        body.appendOwnedOperation(func_op);
        _ = try self.func_syms.put(f.name, .{ .op = func_op, .is_variadic = is_variadic, .n_formals = mlir_n_formals });
    }

    fn emitFunctionBody(self: *TirLlvmGen, f: *const tir.Function, arena: *types.TypeArena) !void {
        // ---- reset per-function state
        self.block_map.clearRetainingCapacity();
        self.value_map.clearRetainingCapacity();
        self.cur_region = null;
        self.cur_block = null;

        const finfo = self.func_syms.get(f.name).?;
        var func_op = finfo.op;
        var region = func_op.getRegion(0);

        const n_formals = finfo.n_formals;

        // ---- entry block arg types come from the *function params* (drop trailing Any)
        var entry_arg_tys = try self.gpa.alloc(mlir.Type, n_formals);
        defer self.gpa.free(entry_arg_tys);
        for (f.params.items[0..n_formals], 0..) |p, i| {
            entry_arg_tys[i] = try self.llvmTypeOf(arena, p.ty);
        }

        const entry_locs = try self.gpa.alloc(mlir.Location, n_formals);
        defer self.gpa.free(entry_locs);
        for (entry_locs) |*L| L.* = self.loc;

        var entry_block = mlir.Block.create(entry_arg_tys, entry_locs);
        region.appendOwnedBlock(entry_block);
        self.cur_region = region;
        self.cur_block = entry_block;

        // ---- map the real entry block id
        if (f.blocks.items.len > 0) {
            const entry_bid = f.blocks.items[0].id;
            try self.block_map.put(entry_bid, entry_block);
        }

        // ---- seed value_map with *param ValueIds* -> MLIR entry args
        try self.value_map.ensureTotalCapacity(@intCast(n_formals));
        for (f.params.items[0..n_formals], 0..) |p, i| {
            try self.value_map.put(p.id, entry_block.getArgument(i));
        }

        // ---- create remaining MLIR blocks with their block params (if any)
        if (f.blocks.items.len > 1) {
            for (f.blocks.items[1..]) |*bb| {
                const m = bb.params.items.len;
                var arg_tys = try self.gpa.alloc(mlir.Type, m);
                defer self.gpa.free(arg_tys);
                var arg_locs = try self.gpa.alloc(mlir.Location, m);
                defer self.gpa.free(arg_locs);

                for (bb.params.items, 0..) |bp, i| {
                    arg_tys[i] = try self.llvmTypeOf(arena, bp.ty);
                    arg_locs[i] = self.loc;
                }

                const b = mlir.Block.create(arg_tys, arg_locs);
                region.appendOwnedBlock(b);
                try self.block_map.put(bb.id, b);
            }
        }

        // ---- emit each TIR block
        for (f.blocks.items) |*bb| {
            var mblock = self.block_map.get(bb.id).?;
            self.cur_block = mblock;

            // map block params (if any) for this block
            for (bb.params.items, 0..) |bp, i| {
                try self.value_map.put(bp.id, mblock.getArgument(i));
            }

            // non-terminator instructions
            for (bb.instrs.items) |*ins| {
                const v = try self.emitInstr(ins, arena);
                try self.value_map.put(ins.result, v);
            }

            // terminator
            if (bb.term) |t| try self.emitTerminator(&t);
        }
    }

    // ------------------------------------------------------------
    // Instructions
    // ------------------------------------------------------------
    fn emitInstr(self: *TirLlvmGen, ins: *const tir.Instr, arena: *types.TypeArena) !mlir.Value {
        return switch (ins.tag) {

            // -------------------- Constants --------------------
            .ConstInt => blk: {
                const ty = try self.llvmTypeOf(arena, ins.ty);
                const v = self.constInt(ty, ins.payload.ConstInt);
                break :blk v;
            },
            .ConstFloat => blk: {
                const ty = try self.llvmTypeOf(arena, ins.ty);
                const v = self.constFloat(ty, ins.payload.ConstFloat);
                break :blk v;
            },
            .ConstBool => blk: {
                const v = self.constBool(ins.payload.ConstBool);
                break :blk v;
            },
            .ConstNull => blk: {
                const ty = try self.llvmTypeOf(arena, ins.ty); // should be !llvm.ptr
                var op = OpBuilder.init("llvm.mlir.null", self.loc).builder()
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .ConstUndef => blk: {
                const ty = try self.llvmTypeOf(arena, ins.ty);
                var op = OpBuilder.init("llvm.mlir.undef", self.loc).builder()
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .ConstString => blk: {
                var op = try self.constStringPtr(ins.payload.ConstString);
                break :blk op.getResult(0);
            },

            // -------------------- Arithmetic / Bitwise --------------------
            .Add => try self.binArith("llvm.add", "llvm.fadd", ins.payload.Add, ins, arena),
            .Sub => try self.binArith("llvm.sub", "llvm.fsub", ins.payload.Sub, ins, arena),
            .Mul => try self.binArith("llvm.mul", "llvm.fmul", ins.payload.Mul, ins, arena),
            .Div => blk: {
                var lhs = self.value_map.get(ins.payload.Div.lhs).?;
                const rhs = self.value_map.get(ins.payload.Div.rhs).?;
                const ty = try self.llvmTypeOf(arena, ins.ty);
                const name = if (self.isFloatType(lhs.getType())) "llvm.fdiv" else if (self.isUnsigned(arena, ins.ty)) "llvm.udiv" else "llvm.sdiv";
                var op = OpBuilder.init(name, self.loc).builder()
                    .add_operands(&.{ lhs, rhs })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },

            .Mod => blk: {
                var lhs = self.value_map.get(ins.payload.Mod.lhs).?;
                const rhs = self.value_map.get(ins.payload.Mod.rhs).?;
                const ty = try self.llvmTypeOf(arena, ins.ty);
                const name = if (self.isFloatType(lhs.getType())) "llvm.frem" else if (self.isUnsigned(arena, ins.ty)) "llvm.urem" else "llvm.srem";
                var op = OpBuilder.init(name, self.loc).builder()
                    .add_operands(&.{ lhs, rhs })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },

            .Shl => blk: {
                const p = ins.payload.Shl;
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(arena, ins.ty);
                var op = OpBuilder.init("llvm.shl", self.loc).builder()
                    .add_operands(&.{ lhs, rhs })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .Shr => blk: {
                const p = ins.payload.Shr;
                const lhs = self.value_map.get(p.lhs).?;
                const rhs = self.value_map.get(p.rhs).?;
                const ty = try self.llvmTypeOf(arena, ins.ty);
                const name = if (self.isUnsigned(arena, ins.ty)) "llvm.lshr" else "llvm.ashr";
                var op = OpBuilder.init(name, self.loc).builder()
                    .add_operands(&.{ lhs, rhs })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },

            .BitAnd => try self.binBit("llvm.and", ins.payload.BitAnd, ins, arena),
            .BitOr => try self.binBit("llvm.or", ins.payload.BitOr, ins, arena),
            .BitXor => try self.binBit("llvm.xor", ins.payload.BitXor, ins, arena),

            // -------------------- Logical --------------------
            .LogicalAnd => try self.binBit("llvm.and", ins.payload.LogicalAnd, ins, arena),
            .LogicalOr => try self.binBit("llvm.or", ins.payload.LogicalOr, ins, arena),
            .LogicalNot => blk: {
                const v = self.value_map.get(ins.payload.LogicalNot.value).?;
                const one = self.constBool(true);
                var op = OpBuilder.init("llvm.xor", self.loc).builder()
                    .add_operands(&.{ v, one })
                    .add_results(&.{self.i1_ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },

            // -------------------- Comparisons --------------------
            .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe => try self.emitCmp(ins, arena),

            // -------------------- Casts (minimal) --------------------
            .CastBit => blk: {
                const to_ty = try self.llvmTypeOf(arena, ins.ty);
                const from_v = self.value_map.get(ins.payload.CastBit.value).?;
                var op = OpBuilder.init("llvm.bitcast", self.loc).builder()
                    .add_operands(&.{from_v})
                    .add_results(&.{to_ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },

            .CastNormal => blk: {
                const to_ty = try self.llvmTypeOf(arena, ins.ty);
                var from_v = self.value_map.get(ins.payload.CastNormal.value).?;
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
                        else if (self.isSignedInt(arena, ins.ty))
                            OpBuilder.init("llvm.sext", self.loc).builder()
                                .add_operands(&.{from_v}).add_results(&.{to_ty}).build()
                        else
                            OpBuilder.init("llvm.zext", self.loc).builder()
                                .add_operands(&.{from_v}).add_results(&.{to_ty}).build();
                    } else if (from_is_int and to_is_f)
                        OpBuilder.init(if (self.isSignedInt(arena, ins.ty)) "llvm.sitofp" else "llvm.uitofp", self.loc).builder()
                            .add_operands(&.{from_v}).add_results(&.{to_ty}).build()
                    else if (from_is_f and to_is_int)
                        OpBuilder.init(if (self.isSignedInt(arena, ins.ty)) "llvm.fptosi" else "llvm.fptoui", self.loc).builder()
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
                // TIR: result type is a pointer; elem type = pointee
                const resT = self.llvmTypeOf(arena, ins.ty) catch self.llvm_ptr_ty;
                _ = resT;

                // Find pointee type for elem_type attribute
                var elem_ty: mlir.Type = self.i8_ty;
                switch (arena.get(ins.ty)) {
                    .Ptr => |p| elem_ty = try self.llvmTypeOf(arena, p.elem),
                    else => {}, // fallback; shouldn't really happen for Alloca
                }

                // Count operand: use provided value or default to 1
                var count_v: mlir.Value = undefined;
                if (ins.payload.Alloca.count) |cvid| {
                    count_v = self.value_map.get(cvid).?;
                } else {
                    count_v = self.llvmConstI64(1);
                }

                var attrs = [_]mlir.NamedAttribute{
                    self.named("elem_type", mlir.Attribute.typeAttrGet(elem_ty)),
                };

                // Optional alignment attribute if you want it:
                // if (ins.payload.Alloca.@"align" != 0) {
                //     const a = mlir.Attribute.integerAttrGet(self.i64_ty, ins.payload.Alloca.@"align");
                //     // You'll need a small DynamicArray if you add attrs dynamically.
                // }

                var alloca = OpBuilder.init("llvm.alloca", self.loc).builder()
                    .add_operands(&.{count_v}) // REQUIRED operand
                    .add_results(&.{self.llvm_ptr_ty}) // result is !llvm.ptr
                    .add_attributes(&attrs)
                    .build();
                self.append(alloca);
                break :blk alloca.getResult(0);
            },

            .Load => blk: {
                const ptr = self.value_map.get(ins.payload.Load.ptr).?;
                const res_ty = try self.llvmTypeOf(arena, ins.ty);
                var load = OpBuilder.init("llvm.load", self.loc).builder()
                    .add_operands(&.{ptr}) // address
                    .add_results(&.{res_ty}) // loaded value type
                    .build();
                self.append(load);
                break :blk load.getResult(0);
            },

            .Store => blk: {
                const v = self.value_map.get(ins.payload.Store.value).?;
                const ptr = self.value_map.get(ins.payload.Store.ptr).?;
                const st = OpBuilder.init("llvm.store", self.loc).builder()
                    .add_operands(&.{ v, ptr }) // (value, address)
                    .build();
                self.append(st);
                break :blk mlir.Value.empty();
            },
            .Gep => blk: {
                const p = ins.payload.Gep;
                const base = self.value_map.get(p.base).?;
                // base type must be Ptr{elem = E}
                const base_tid = blk2: {
                    // Find TIR type of base value through `ins.ty`? (GEP result is also a ptr)
                    // We need pointee from the *base* value; carry it via arena.get(..)
                    // If you can’t read the base type directly here, you likely recorded it in TIR.
                    // Assuming base’s type is Ptr{elem=E}: use E below.
                    // If you don’t have a side-table for ValueId->TypeId, add one; for now:
                    break :blk2 null;
                };
                _ = base_tid;
                // If you *do* have ValueId -> TypeId side table, use it.
                // For now we derive element type from the result pointer (ins.ty == Ptr<something>)
                const resT = arena.get(ins.ty);
                if (@as(types.TypeKind, resT) != .Ptr) return error.CompileError;
                // op needs the *base* elem_type, not the final one; safest is to walk backwards:
                // However, for most common patterns it’s OK to use the base’s pointee.
                // If you can’t read base’s pointee, using result’s pointee also works in many cases.
                const elem_mlir = try self.llvmTypeOf(arena, resT.Ptr.elem);

                const v = try self.emitGep(base, elem_mlir, p.indices);
                break :blk v;
            },

            // -------------------- Aggregates --------------------
            .TupleMake => blk: {
                const tup_ty = try self.llvmTypeOf(arena, ins.ty);
                var acc = self.undefOf(tup_ty);
                for (ins.payload.TupleMake.elems, 0..) |vid, i| {
                    const v = self.value_map.get(vid).?;
                    acc = self.insertAt(acc, v, &.{@as(i64, @intCast(i))});
                }
                break :blk acc;
            },

            .ArrayMake => blk: {
                const arr_ty = try self.llvmTypeOf(arena, ins.ty);
                var acc = self.undefOf(arr_ty);
                for (ins.payload.ArrayMake.elems, 0..) |vid, i| {
                    const v = self.value_map.get(vid).?;
                    acc = self.insertAt(acc, v, &.{@as(i64, @intCast(i))});
                }
                break :blk acc;
            },

            .StructMake => blk: {
                const st_ty = try self.llvmTypeOf(arena, ins.ty);
                var acc = self.undefOf(st_ty);
                for (ins.payload.StructMake.fields) |f| {
                    const v = self.value_map.get(f.value).?;
                    acc = self.insertAt(acc, v, &.{@as(i64, @intCast(f.index))});
                }
                break :blk acc;
            },

            .ExtractElem => blk: {
                const p = ins.payload.ExtractElem;
                const agg = self.value_map.get(p.agg).?;
                const res_ty = try self.llvmTypeOf(arena, ins.ty);
                const v = self.extractAt(agg, res_ty, &.{@as(i64, @intCast(p.index))});
                break :blk v;
            },

            .InsertElem => blk: {
                const p = ins.payload.InsertElem;
                const agg = self.value_map.get(p.agg).?;
                const val = self.value_map.get(p.value).?;
                const v = self.insertAt(agg, val, &.{@as(i64, @intCast(p.index))});
                break :blk v;
            },

            .ExtractField => blk: {
                const p = ins.payload.ExtractField;
                const agg = self.value_map.get(p.agg).?;
                const res_ty = try self.llvmTypeOf(arena, ins.ty);
                const v = self.extractAt(agg, res_ty, &.{@as(i64, @intCast(p.index))});
                break :blk v;
            },

            .InsertField => blk: {
                const p = ins.payload.InsertField;
                const agg = self.value_map.get(p.agg).?;
                const val = self.value_map.get(p.value).?;
                const v = self.insertAt(agg, val, &.{@as(i64, @intCast(p.index))});
                break :blk v;
            },

            // -------------------- Pointers/Indexing --------------------
            .AddressOf => blk: {
                var v = self.value_map.get(ins.payload.AddressOf.value).?;
                // If it is already a pointer, just forward it.
                if (mlir.LLVM.isLLVMPointerType(v.getType())) break :blk v;
                return error.NotImplemented; // taking address of SSA value needs an alloca+store lowering
            },
            .Index => blk: {
                const idx = ins.payload.Index;
                const base = self.value_map.get(idx.base).?;
                const iv = self.value_map.get(idx.index).?;
                _ = iv;
                // Result is Ptr<elem>; elem_type should be the pointee of base
                // Use result’s pointee — matches Ptr<elem> in TIR
                const resT = arena.get(ins.ty);
                if (@as(types.TypeKind, resT) != .Ptr) return error.CompileError;
                const elem_mlir = try self.llvmTypeOf(arena, resT.Ptr.elem);

                // single dynamic index
                const v = try self.emitGep(base, elem_mlir, &.{.{ .Value = idx.index }});
                break :blk v;
            },

            // -------------------- Control/Data --------------------
            .Select => blk: {
                const p = ins.payload.Select;
                const c = self.value_map.get(p.cond).?;
                const t = self.value_map.get(p.then_value).?;
                const e = self.value_map.get(p.else_value).?;
                const ty = try self.llvmTypeOf(arena, ins.ty);
                var op = OpBuilder.init("llvm.select", self.loc).builder()
                    .add_operands(&.{ c, t, e })
                    .add_results(&.{ty})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .Call => blk: {
                const callee_name = ins.payload.Call.callee;
                const finfo = self.func_syms.get(callee_name) orelse try self.ensureDeclFromCall(ins, arena);

                // Collect operands
                var args = try self.gpa.alloc(mlir.Value, ins.payload.Call.args.len);
                defer self.gpa.free(args);
                for (ins.payload.Call.args, 0..) |vid, i| args[i] = self.value_map.get(vid).?;

                const ret_ty = try self.llvmTypeOf(arena, ins.ty);

                var attrs = ArrayList(mlir.NamedAttribute).init(self.gpa);
                defer attrs.deinit();

                // callee
                try attrs.append(self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.ctx, mlir.StringRef.from(callee_name))));

                // ALWAYS: segment sizes for operands (N args, 0 bundles)
                const seg = mlir.Attribute.denseI32ArrayGet(self.ctx, &[_]i32{ @intCast(args.len), 0 });
                try attrs.append(self.named("operandSegmentSizes", seg));

                // ALWAYS: op_bundle_sizes must exist; empty when you have no bundles
                const empty_bundles = mlir.Attribute.denseI32ArrayGet(self.ctx, &[_]i32{});
                try attrs.append(self.named("op_bundle_sizes", empty_bundles));

                // Only for variadic callees: tell LLVM the *actual* call signature at this site
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

    fn emitCmp(self: *TirLlvmGen, ins: *const tir.Instr, arena: *types.TypeArena) !mlir.Value {
        var lhs = self.value_map.get(switch (ins.tag) {
            .CmpEq => ins.payload.CmpEq.lhs,
            .CmpNe => ins.payload.CmpNe.lhs,
            .CmpLt => ins.payload.CmpLt.lhs,
            .CmpLe => ins.payload.CmpLe.lhs,
            .CmpGt => ins.payload.CmpGt.lhs,
            .CmpGe => ins.payload.CmpGe.lhs,
            else => unreachable,
        }).?;
        const rhs = self.value_map.get(switch (ins.tag) {
            .CmpEq => ins.payload.CmpEq.rhs,
            .CmpNe => ins.payload.CmpNe.rhs,
            .CmpLt => ins.payload.CmpLt.rhs,
            .CmpLe => ins.payload.CmpLe.rhs,
            .CmpGt => ins.payload.CmpGt.rhs,
            .CmpGe => ins.payload.CmpGe.rhs,
            else => unreachable,
        }).?;

        const lty = lhs.getType();
        const is_float = lty.isAFloat();

        if (is_float) {
            const pred = switch (ins.tag) {
                .CmpEq => "oeq",
                .CmpNe => "one",
                .CmpLt => "olt",
                .CmpLe => "ole",
                .CmpGt => "ogt",
                .CmpGe => "oge",
                else => unreachable,
            };
            var op = OpBuilder.init("llvm.fcmp", self.loc).builder()
                .add_operands(&.{ lhs, rhs })
                .add_results(&.{self.i1_ty})
                .add_attributes(&.{self.named("predicate", self.strAttr(pred))})
                .build();
            self.append(op);
            return op.getResult(0);
        } else {
            // ints: sign matters for order comparisons
            const unsigned = !self.isSignedInt(arena, ins.ty); // if you track per-operand type use that
            const pred = switch (ins.tag) {
                .CmpEq => "eq",
                .CmpNe => "ne",
                .CmpLt => if (unsigned) "ult" else "slt",
                .CmpLe => if (unsigned) "ule" else "sle",
                .CmpGt => if (unsigned) "ugt" else "sgt",
                .CmpGe => if (unsigned) "uge" else "sge",
                else => unreachable,
            };
            var op = OpBuilder.init("llvm.icmp", self.loc).builder()
                .add_operands(&.{ lhs, rhs })
                .add_results(&.{self.i1_ty})
                .add_attributes(&.{self.named("predicate", self.strAttr(pred))})
                .build();
            self.append(op);
            return op.getResult(0);
        }
    }

    fn emitInstrCall(self: *TirLlvmGen, ins: *const tir.Instr, arena: *types.TypeArena) !mlir.Value {
        const callee_name = ins.payload.Call.callee;
        const finfo = self.func_syms.get(callee_name) orelse try self.ensureDeclFromCall(ins, arena);

        var args = try self.gpa.alloc(mlir.Value, ins.payload.Call.args.len);
        defer self.gpa.free(args);
        for (ins.payload.Call.args, 0..) |vid, i| args[i] = self.value_map.get(vid).?;

        const ret_ty = try self.llvmTypeOf(arena, ins.ty);
        var attrs = ArrayList(mlir.NamedAttribute).init(self.gpa);
        defer attrs.deinit();

        try attrs.append(self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.ctx, mlir.StringRef.from(callee_name))));

        if (finfo.is_variadic) {
            var arg_tys = try self.gpa.alloc(mlir.Type, args.len);
            defer self.gpa.free(arg_tys);
            for (args, 0..) |*a, i| arg_tys[i] = a.getType();
            const var_fty = mlir.LLVM.getLLVMFunctionType(ret_ty, arg_tys, true);
            try attrs.append(self.named("var_callee_type", mlir.Attribute.typeAttrGet(var_fty)));
            const seg = mlir.Attribute.denseI32ArrayGet(self.ctx, &[_]i32{ @intCast(args.len), 0 });
            try attrs.append(self.named("operandSegmentSizes", seg));
            try attrs.append(self.named("op_bundle_sizes", mlir.Attribute.parseGet(self.ctx, mlir.StringRef.from("array<i32>"))));
        }

        const call = OpBuilder.init("llvm.call", self.loc).builder()
            .add_operands(args)
            .add_results(if (self.void_ty.equal(ret_ty)) &.{} else &.{ret_ty})
            .add_attributes(attrs.items)
            .build();
        self.append(call);
        return if (call.getNumResults() == 0) mlir.Value.empty() else call.getResult(0);
    }

    fn emitTerminator(self: *TirLlvmGen, term: *const tir.Terminator) !void {
        switch (term.*) {
            .Return => |rv_opt| {
                const op = if (rv_opt) |vid| blk: {
                    const v = self.value_map.get(vid).?;
                    break :blk OpBuilder.init("llvm.return", self.loc).builder()
                        .add_operands(&.{v})
                        .build();
                } else OpBuilder.init("llvm.return", self.loc).builder().build();
                self.append(op);
            },

            .Br => |edge| {
                var dest = self.block_map.get(edge.dest).?;
                const dest_n = dest.getNumArguments();
                std.debug.assert(dest_n == edge.args.len); // or return a typed error

                // Small stack buffer to dodge heap allocs on common cases
                var small: [4]mlir.Value = undefined;
                var argv: []mlir.Value = if (edge.args.len <= small.len) small[0..edge.args.len] else try self.gpa.alloc(mlir.Value, edge.args.len);
                defer if (argv.ptr != &small) self.gpa.free(argv);

                // Collect & (optionally) fix-up types
                for (edge.args, 0..) |avid, i| {
                    var v = self.value_map.get(avid).?;
                    var want_arg = dest.getArgument(i);
                    const want = want_arg.getType();
                    if (!v.getType().equal(want)) {
                        // If both are pointers, bitcast; otherwise, signal mismatch.
                        if (self.isLlvmPtr(v.getType()) and self.isLlvmPtr(want)) {
                            var bc = OpBuilder.init("llvm.bitcast", self.loc).builder()
                                .add_operands(&.{v})
                                .add_results(&.{want})
                                .build();
                            self.append(bc);
                            v = bc.getResult(0);
                        } else {
                            // You can make this a proper error if you prefer.
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

            .CondBr => |cb| {
                const cond = self.value_map.get(cb.cond).?;
                const tdest = self.block_map.get(cb.then_edge.dest).?;
                const edest = self.block_map.get(cb.else_edge.dest).?;

                // flatten operands: [cond, thenArgs..., elseArgs...]
                const n_then = cb.then_edge.args.len;
                const n_else = cb.else_edge.args.len;
                const total = 1 + n_then + n_else;

                var ops = try self.gpa.alloc(mlir.Value, total);
                defer self.gpa.free(ops);
                ops[0] = cond;

                var k: usize = 1;
                for (cb.then_edge.args) |vid| {
                    ops[k] = self.value_map.get(vid).?;
                    k += 1;
                }
                for (cb.else_edge.args) |vid| {
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

            .SwitchInt => |sw| {
                // Lower to a chain of icmp+cond_br blocks
                var scrut = self.value_map.get(sw.scrut).?;
                const default_dest = self.block_map.get(sw.default_dest).?;

                // Prepare default args now
                const ndef = sw.default_args.len;
                const def_ops = if (ndef == 0) &[_]mlir.Value{} else blk: {
                    const buf = try self.gpa.alloc(mlir.Value, ndef);
                    defer self.gpa.free(buf);
                    for (sw.default_args, 0..) |vid, i| buf[i] = self.value_map.get(vid).?;
                    break :blk buf;
                };

                // If no cases, just branch to default
                if (sw.cases.len == 0) {
                    const br = OpBuilder.init("llvm.br", self.loc).builder()
                        .add_operands(def_ops)
                        .add_successors(&.{default_dest})
                        .build();
                    self.append(br);
                    return;
                }

                // We'll create N-1 "next test" blocks
                var next_block: ?mlir.Block = null;

                for (sw.cases, 0..) |c, idx| {
                    // For the first case, emit in the current block;
                    // for subsequent cases, emit in a fresh block and fallthrough from previous.
                    if (idx != 0) {
                        const nb = mlir.Block.create(&.{}, &.{});
                        self.cur_region.?.appendOwnedBlock(nb);
                        // link previous false edge to this new block
                        const prev = next_block.?;
                        _ = prev;
                        self.cur_block = nb;
                        next_block = nb;
                    } else {
                        // mark the first "next block" (for chaining) as current block
                        next_block = self.cur_block.?;
                    }

                    // compare scrut == case_value
                    const c_ty = scrut.getType();
                    const case_val = self.constInt(c_ty, @bitCast(c.value));

                    var icmp = OpBuilder.init("llvm.icmp", self.loc).builder()
                        .add_operands(&.{ scrut, case_val })
                        .add_results(&.{self.i1_ty})
                        .add_attributes(&.{self.named("predicate", self.strAttr("eq"))})
                        .build();
                    self.append(icmp);

                    // true edge args
                    const nt = c.args.len;
                    const t_ops = if (nt == 0) &[_]mlir.Value{} else blk: {
                        const buf = try self.gpa.alloc(mlir.Value, nt);
                        defer self.gpa.free(buf);
                        for (c.args, 0..) |vid, i| buf[i] = self.value_map.get(vid).?;
                        break :blk buf;
                    };

                    // false successor: either next test block (new) or default
                    const false_is_last = (idx + 1 == sw.cases.len);
                    const false_dest = if (false_is_last) default_dest else blk: {
                        const nb = mlir.Block.create(&.{}, &.{});
                        self.cur_region.?.appendOwnedBlock(nb);
                        break :blk nb;
                    };

                    // Build operands: [cond, then..., else...]
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
                    const tdest = self.block_map.get(c.dest).?;
                    const condbr = OpBuilder.init("llvm.cond_br", self.loc).builder()
                        .add_operands(ops)
                        .add_successors(&.{ tdest, false_dest })
                        .add_attributes(&.{self.named("operandSegmentSizes", seg)})
                        .build();
                    self.append(condbr);

                    if (!false_is_last) {
                        // continue emitting in false_dest
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

    fn emitGep(self: *TirLlvmGen, base: mlir.Value, elem_ty: mlir.Type, idxs: []const tir.Instr.GepIndex) !mlir.Value {
        const dyn_min = std.math.minInt(i32);

        // gather dynamic operands and raw constant indices
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
    fn append(self: *TirLlvmGen, op: mlir.Operation) void {
        self.cur_block.?.appendOwnedOperation(op);
    }
    fn named(self: *const TirLlvmGen, name: []const u8, attr: mlir.Attribute) mlir.NamedAttribute {
        return .{
            .inner = .{
                .name = mlir.c.mlirIdentifierGet(self.ctx.handle, mlir.StringRef.from(name).inner),
                .attribute = attr.handle,
            },
        };
    }
    fn strAttr(self: *const TirLlvmGen, s: []const u8) mlir.Attribute {
        return mlir.Attribute.stringAttrGet(self.ctx, mlir.StringRef.from(s));
    }
    fn intAttr(self: *const TirLlvmGen, ty: mlir.Type, val: i64) mlir.Attribute {
        _ = self;
        return mlir.Attribute.integerAttrGet(ty, val);
    }

    fn isLlvmPtr(self: *const TirLlvmGen, ty: mlir.Type) bool {
        return ty.equal(self.llvm_ptr_ty);
    }

    fn llvmConstI64(self: *TirLlvmGen, x: i64) mlir.Value {
        const val = mlir.Attribute.integerAttrGet(self.i64_ty, x);
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{self.i64_ty})
            .add_attributes(&.{self.named("value", val)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn undefOf(self: *TirLlvmGen, ty: mlir.Type) mlir.Value {
        var op = OpBuilder.init("llvm.mlir.undef", self.loc).builder()
            .add_results(&.{ty})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn insertAt(self: *TirLlvmGen, agg: mlir.Value, val: mlir.Value, pos: []const i64) mlir.Value {
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

    fn extractAt(self: *TirLlvmGen, agg: mlir.Value, res_ty: mlir.Type, pos: []const i64) mlir.Value {
        const pos_attr = mlir.Attribute.denseI64ArrayGet(self.ctx, pos);
        var op = OpBuilder.init("llvm.extractvalue", self.loc).builder()
            .add_operands(&.{agg})
            .add_results(&.{res_ty})
            .add_attributes(&.{self.named("position", pos_attr)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn constInt(self: *TirLlvmGen, ty: mlir.Type, v: i64) mlir.Value {
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{ty})
            .add_attributes(&.{self.named("value", mlir.Attribute.integerAttrGet(ty, v))})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn constFloat(self: *TirLlvmGen, ty: mlir.Type, v: f64) mlir.Value {
        const attr = mlir.Attribute.floatAttrDoubleGet(self.ctx, ty, v);
        var op = OpBuilder.init("llvm.mlir.constant", self.loc).builder()
            .add_results(&.{ty})
            .add_attributes(&.{self.named("value", attr)})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn constBool(self: *TirLlvmGen, v: bool) mlir.Value {
        return self.constInt(self.i1_ty, if (v) 1 else 0);
    }

    // NOTE: best-effort until we wire exact unsigned types from `types`
    fn isUnsigned(self: *TirLlvmGen, arena: *types.TypeArena, ty: types.TypeId) bool {
        _ = self;
        return switch (arena.get(ty)) {
            .Usize => true,
            .U32, .U64 => true, // if you have these tags; harmless if not present
            else => false,
        };
    }

    fn isFloatType(self: *TirLlvmGen, t: mlir.Type) bool {
        _ = self;
        return t.isAFloat();
    }

    fn isIntType(self: *TirLlvmGen, t: mlir.Type) bool {
        _ = self;
        return t.isAInteger();
    }

    fn intOrFloatWidth(t: mlir.Type) !u32 {
        if (t.isAInteger()) return t.getIntegerBitwidth();
        if (t.isAFloat()) return t.getFloatBitwidth();
        return error.NotIntOrFloat;
    }

    fn binBit(self: *TirLlvmGen, name: []const u8, p: tir.Instr.Bin2, ins: *const tir.Instr, arena: *types.TypeArena) !mlir.Value {
        const lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;
        const ty = try self.llvmTypeOf(arena, ins.ty);
        var op = OpBuilder.init(name, self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{ty})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn binArith(self: *TirLlvmGen, intName: []const u8, floatName: []const u8, p: tir.Instr.Bin2, ins: *const tir.Instr, arena: *types.TypeArena) !mlir.Value {
        var lhs = self.value_map.get(p.lhs).?;
        const rhs = self.value_map.get(p.rhs).?;
        const ty = try self.llvmTypeOf(arena, ins.ty);
        const name = if (self.isFloatType(lhs.getType())) floatName else intName;
        var op = OpBuilder.init(name, self.loc).builder()
            .add_operands(&.{ lhs, rhs })
            .add_results(&.{ty})
            .build();
        self.append(op);
        return op.getResult(0);
    }

    fn blockArgType(self: *const TirLlvmGen, func_op: *mlir.Operation, idx: usize) mlir.Type {
        _ = idx;
        // Pull from function_type attribute
        const fnty_attr = func_op.getInherentAttributeByName(mlir.StringRef.from("function_type"));
        const fnty = mlir.Attribute.typeAttrGetValue(fnty_attr);
        // llvm.func types are LLVM function types; query param type from it is non-trivial via C-API,
        // but for creating entry block we only need the original types we computed earlier.
        // We recorded n_formals and we know they’re opaque pointers/ints; using ptr type for safety:
        // However, we pass exact types from header creation path via our cached computation,
        // so fallback to opaque ptr here (shouldn’t be hit for hello-world).
        _ = fnty;
        return self.llvm_ptr_ty;
    }

    fn ensureDeclFromCall(self: *TirLlvmGen, ins: *const tir.Instr, arena: *types.TypeArena) !FuncInfo {
        // Create a declaration purely from the callsite (used if callee wasn’t in the TIR function list)
        var args = try self.gpa.alloc(mlir.Value, ins.payload.Call.args.len);
        defer self.gpa.free(args);
        var arg_tys = try self.gpa.alloc(mlir.Type, ins.payload.Call.args.len);
        defer self.gpa.free(arg_tys);
        for (ins.payload.Call.args, 0..) |vid, i| {
            var v = self.value_map.get(vid).?;
            args[i] = v;
            arg_tys[i] = v.getType();
        }
        const ret_ty = try self.llvmTypeOf(arena, ins.ty);
        const fn_ty = mlir.LLVM.getLLVMFunctionType(ret_ty, arg_tys, true);
        const name = ins.payload.Call.callee;
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
        const info: FuncInfo = .{ .op = func_op, .is_variadic = true, .n_formals = arg_tys.len };
        _ = try self.func_syms.put(name, info);
        return info;
    }

    fn constStringPtr(self: *TirLlvmGen, text: []const u8) !mlir.Operation {
        // Pool `llvm.mlir.global` with nul terminator, then addr_of + gep 0,0 -> !llvm.ptr
        if (self.str_pool.get(text)) |*g| {
            return self.addrOfFirstChar(@constCast(g));
        }
        const esc = try self.escapeForMlirString(text);
        defer self.gpa.free(esc);
        const name = try std.fmt.allocPrint(self.gpa, "str_{d}", .{self.str_pool.count()});
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

    fn addrOfFirstChar(self: *TirLlvmGen, global_op: *mlir.Operation) !mlir.Operation {
        // llvm.mlir.addressof @name : !llvm.ptr
        const name_attr = global_op.getInherentAttributeByName(mlir.StringRef.from("sym_name"));
        const gsym = mlir.Attribute.flatSymbolRefAttrGet(self.ctx, mlir.Attribute.stringAttrGetValue(name_attr));
        var addr = OpBuilder.init("llvm.mlir.addressof", self.loc).builder()
            .add_results(&.{self.llvm_ptr_ty})
            .add_attributes(&.{self.named("global_name", gsym)})
            .build();
        self.append(addr);
        // gep 0,0 with elem_type = !llvm.array<N x i8>
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

    fn escapeForMlirString(self: *TirLlvmGen, s: []const u8) ![]u8 {
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

    fn typeIsAny(self: *TirLlvmGen, arena: *types.TypeArena, ty: types.TypeId) bool {
        _ = self;
        return switch (arena.get(ty)) {
            .Any => true,
            else => false,
        };
    }

    fn intWidth(self: *TirLlvmGen, arena: *types.TypeArena, ty: types.TypeId) u32 {
        _ = self;
        return switch (arena.get(ty)) {
            .I8, .U8 => 8,
            .I16, .U16 => 16,
            .I32, .U32 => 32,
            .I64, .U64 => 64,
            .Usize => 64, // TODO: target bits
            else => 0,
        };
    }

    fn isSignedInt(self: *TirLlvmGen, arena: *types.TypeArena, ty: types.TypeId) bool {
        _ = self;
        return switch (arena.get(ty)) {
            .I8, .I16, .I32, .I64 => true,
            else => false,
        };
    }

    fn llvmTypeOf(self: *TirLlvmGen, arena: *types.TypeArena, ty: types.TypeId) !mlir.Type {
        return switch (arena.get(ty)) {
            .Void => self.void_ty,
            .Bool => self.i1_ty,

            .I8, .U8 => mlir.Type.getSignlessIntegerType(self.ctx, 8),
            .I16, .U16 => mlir.Type.getSignlessIntegerType(self.ctx, 16),
            .I32, .U32 => mlir.Type.getSignlessIntegerType(self.ctx, 32),
            .I64, .U64 => mlir.Type.getSignlessIntegerType(self.ctx, 64),

            .F32 => self.f32_ty,
            .F64 => self.f64_ty,
            .Usize => self.i64_ty,

            // current choice: string as ptr-to-u8 (fits your Hello World)
            .String => self.llvm_ptr_ty,

            .Any => self.llvm_ptr_ty, // safe placeholder for now

            .Ptr => self.llvm_ptr_ty, // opaque pointers on master

            // Slice => struct { ptr, usize }
            .Slice => |s| blk: {
                const elem_ty = try self.llvmTypeOf(arena, s.elem);
                _ = elem_ty;
                const fields = [_]mlir.Type{ self.llvm_ptr_ty, self.i64_ty };
                // (elem_ty isn’t encoded in the slice layout; if you want it, carry as opaque ptr)
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.ctx, &fields, false);
            },

            .Array => |a| blk: {
                const e = try self.llvmTypeOf(arena, a.elem);
                break :blk mlir.LLVM.getLLVMArrayType(e, @intCast(a.len));
            },

            // Optional<T> => { i1, T }
            .Optional => |o| blk: {
                const inner = try self.llvmTypeOf(arena, o.elem);
                const fields = [_]mlir.Type{ self.i1_ty, inner };
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.ctx, &fields, false);
            },

            // Tuple => literal struct
            .Tuple => |t| blk: {
                const n = t.elems.len;
                var buf = try self.gpa.alloc(mlir.Type, n);
                defer self.gpa.free(buf);
                for (t.elems, 0..) |eid, i| buf[i] = try self.llvmTypeOf(arena, eid);
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.ctx, buf, false);
            },

            // Function types aren’t first-class for now -> ptr
            .Function => self.llvm_ptr_ty,

            // Struct => literal struct (field order)
            .Struct => |st| blk: {
                const n = st.fields.len;
                var buf = try self.gpa.alloc(mlir.Type, n);
                defer self.gpa.free(buf);
                for (st.fields, 0..) |f, i| buf[i] = try self.llvmTypeOf(arena, f.ty);
                break :blk mlir.LLVM.getLLVMStructTypeLiteral(self.ctx, buf, false);
            },
        };
    }
};
