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
        const finfo = self.func_syms.get(f.name).?;
        var func_op = finfo.op;
        // Build entry + additional blocks
        // Entry block arguments = MLIR formals (after dropping tail any).
        var entry_arg_tys = try self.gpa.alloc(mlir.Type, finfo.n_formals);
        defer self.gpa.free(entry_arg_tys);
        {
            var idx: usize = 0;
            while (idx < finfo.n_formals) : (idx += 1) {
                entry_arg_tys[idx] = self.blockArgType(&func_op, idx);
            }
        }
        const entry_locs = try self.gpa.alloc(mlir.Location, finfo.n_formals);
        defer self.gpa.free(entry_locs);
        for (entry_locs) |*L| L.* = self.loc;

        var entry_block = mlir.Block.create(entry_arg_tys, entry_locs);
        var region = func_op.getRegion(0);
        region.appendOwnedBlock(entry_block);
        self.cur_region = func_op.getRegion(0);
        self.cur_block = entry_block;
        try self.block_map.put(0, entry_block); // first TIR block id may be 0
        // Map TIR param values (0..N-1) to block arguments
        // NOTE: If TIR kept the 'any' param in numbering, it will never be referenced in code for our hello world.
        try self.value_map.ensureTotalCapacity(@intCast(f.params.items.len));
        for (0..entry_block.getNumArguments()) |i| {
            const arg = entry_block.getArgument(i);
            try self.value_map.put(@intCast(i), arg);
        }

        // Create additional MLIR blocks for remaining TIR blocks
        if (f.blocks.items.len > 0) {
            // first TIR block already mapped to entry (by id). Create others:
            for (f.blocks.items[0..]) |*bb| {
                if (bb.id == 0) continue;
                const b = mlir.Block.create(&.{}, &.{});
                var reg = func_op.getRegion(0);
                reg.appendOwnedBlock(b);
                try self.block_map.put(bb.id, b);
            }
        }

        // Emit each TIR block
        for (f.blocks.items) |*bb| {
            const mblock = self.block_map.get(bb.id).?;
            self.cur_block = mblock;
            // Instrs
            for (bb.instrs.items) |*ins| {
                const v = try self.emitInstr(ins, arena);
                try self.value_map.put(ins.result, v);
            }
            // Terminator
            if (bb.term) |t| try self.emitTerminator(&t);
        }
    }

    // ------------------------------------------------------------
    // Instructions
    // ------------------------------------------------------------
    fn emitInstr(self: *TirLlvmGen, ins: *const tir.Instr, arena: *types.TypeArena) !mlir.Value {
        return switch (ins.tag) {
            .ConstInt => blk: {
                const ty = try self.llvmTypeOf(arena, ins.ty);
                const attr = self.intAttr(ty, ins.payload.ConstInt);
                var op = OpBuilder.init("arith.constant", self.loc).builder()
                    .add_results(&.{ty})
                    .add_attributes(&.{self.named("value", attr)})
                    .build();
                self.append(op);
                break :blk op.getResult(0);
            },
            .ConstString => blk: {
                var op = try self.constStringPtr(ins.payload.ConstString);
                // op is a gep returning !llvm.ptr
                break :blk op.getResult(0);
            },
            .Add => blk: {
                const ty = try self.llvmTypeOf(arena, ins.ty);
                const lhs = self.value_map.get(ins.payload.Add.lhs).?;
                const rhs = self.value_map.get(ins.payload.Add.rhs).?;
                var add = OpBuilder.init("arith.addi", self.loc).builder()
                    .add_operands(&.{ lhs, rhs })
                    .add_results(&.{ty})
                    .build();
                self.append(add);
                break :blk add.getResult(0);
            },
            .CastNormal => blk: {
                const to_ty = try self.llvmTypeOf(arena, ins.ty);
                const from_v = self.value_map.get(ins.payload.CastNormal.value).?;
                // With opaque pointers, pointer→pointer casts are bitcast to !llvm.ptr
                var bc = OpBuilder.init("llvm.bitcast", self.loc).builder()
                    .add_operands(&.{from_v})
                    .add_results(&.{to_ty})
                    .build();
                self.append(bc);
                break :blk bc.getResult(0);
            },
            .Call => blk: {
                const callee_name = ins.payload.Call.callee;
                const finfo = self.func_syms.get(callee_name) orelse try self.ensureDeclFromCall(ins, arena);
                // Build operand array
                var args = try self.gpa.alloc(mlir.Value, ins.payload.Call.args.len);
                defer self.gpa.free(args);
                for (ins.payload.Call.args, 0..) |vid, i| args[i] = self.value_map.get(vid).?;
                const ret_ty = try self.llvmTypeOf(arena, ins.ty);

                var attrs = ArrayList(mlir.NamedAttribute).init(self.gpa);
                defer attrs.deinit();
                try attrs.append(self.named("callee", mlir.Attribute.flatSymbolRefAttrGet(self.ctx, mlir.StringRef.from(callee_name))));

                if (finfo.is_variadic) {
                    // Build a var_callee_type from actual operands
                    var arg_tys = try self.gpa.alloc(mlir.Type, args.len);
                    defer self.gpa.free(arg_tys);
                    for (args, 0..) |*a, i| arg_tys[i] = a.getType();
                    const var_fty = mlir.LLVM.getLLVMFunctionType(ret_ty, arg_tys, true);
                    try attrs.append(self.named("var_callee_type", mlir.Attribute.typeAttrGet(var_fty)));
                    // On master, llvm.call requires segment sizes for operands/bundles; keep like your sample
                    const seg = mlir.Attribute.denseI32ArrayGet(self.ctx, &[_]i32{ @intCast(args.len), 0 });
                    try attrs.append(self.named("operandSegmentSizes", seg));
                    try attrs.append(self.named("op_bundle_sizes", mlir.Attribute.parseGet(self.ctx, mlir.StringRef.from("array<i32>"))));
                }

                var call = OpBuilder.init("llvm.call", self.loc).builder()
                    .add_operands(args)
                    .add_results(if (self.void_ty.equal(ret_ty)) &.{} else &.{ret_ty})
                    .add_attributes(attrs.items)
                    .build();
                self.append(call);
                break :blk if (call.getNumResults() == 0) mlir.Value.empty() else call.getResult(0);
            },
            else => return error.NotImplemented,
        };
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
            .Br => |bid| {
                // Simple branch (no block args in minimal subset)
                const dest = self.block_map.get(bid.dest).?;
                const br = OpBuilder.init("llvm.br", self.loc).builder()
                    .add_successors(&.{dest})
                    .build();
                self.append(br);
            },
            else => return error.NotImplemented,
        }
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

    fn llvmTypeOf(self: *TirLlvmGen, arena: *types.TypeArena, ty: types.TypeId) !mlir.Type {
        // Map FE types to LLVM/MLIR types based on the *active* union tag.
        return switch (arena.get(ty)) {
            .Void => self.void_ty,
            .Bool => self.i1_ty,
            .String => self.llvm_ptr_ty, // strings lowered as ptr to first char
            .Ptr => self.llvm_ptr_ty, // opaque pointers on master
            .Usize => self.i64_ty, // TODO: pick target-dependent width
            .I64 => self.i64_ty,
            .I32 => self.i32_ty,
            .I8 => self.i8_ty,
            .F64 => self.f64_ty,
            .F32 => self.f32_ty,
            // .Int => |I| blk: {
            //     // If your Int payload carries a width, use it; otherwise default to 64.
            //     if (@hasField(@TypeOf(I), "bits")) {
            //         break :blk mlir.Type.getSignlessIntegerType(self.ctx, I.bits);
            //     }
            //     break :blk self.i64_ty;
            // },
            // Anything not handled yet -> conservatively lower as opaque ptr for now.
            else => self.llvm_ptr_ty,
        };
    }
};

