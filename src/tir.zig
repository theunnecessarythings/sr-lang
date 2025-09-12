const std = @import("std");
const List = std.array_list.Managed;
const types = @import("types.zig");

// ============================================================================
// Typed IR (TIR)
// - SSA with block parameters (MLIR-friendly)
// - typed ValueId on every op result and block parameter
// - structured terminators carry edge args to feed block params
// ============================================================================

pub const ValueId = u32;
pub const BlockId = u32;
pub const FuncId = u32;

// A typed, named SSA value used for function parameters and block params.
pub const NamedValue = struct {
    id: ValueId,
    name: ?[]const u8 = null,
    ty: types.TypeId,
};

// Globals (future: initializer)
pub const Global = struct {
    name: []const u8,
    ty: types.TypeId,
};

// -----------------------------------------------------------------------------
// Module
// -----------------------------------------------------------------------------
pub const Module = struct {
    allocator: std.mem.Allocator,
    type_arena: *types.TypeArena,
    functions: List(Function),
    globals: List(Global),

    pub fn init(allocator: std.mem.Allocator, type_arena: *types.TypeArena) Module {
        return .{
            .allocator = allocator,
            .type_arena = type_arena,
            .functions = List(Function).init(allocator),
            .globals = List(Global).init(allocator),
        };
    }

    pub fn deinit(self: *Module) void {
        for (self.functions.items) |*f| f.deinit(self.allocator);
        self.functions.deinit();
        self.globals.deinit();
    }
};

// -----------------------------------------------------------------------------
// Function & Block (with block parameters)
// -----------------------------------------------------------------------------
pub const Function = struct {
    name: []const u8,
    // Function parameters are SSA values (conceptually entry block args).
    params: List(NamedValue),
    result: types.TypeId,
    blocks: List(Block),

    pub fn init(allocator: std.mem.Allocator, name: []const u8, result: types.TypeId) Function {
        return .{
            .name = name,
            .params = List(NamedValue).init(allocator),
            .result = result,
            .blocks = List(Block).init(allocator),
        };
    }

    pub fn deinit(self: *Function, allocator: std.mem.Allocator) void {
        self.params.deinit();
        for (self.blocks.items) |*b| b.deinit(allocator);
        self.blocks.deinit();
    }
};

pub const BlockParam = NamedValue;

pub const Block = struct {
    id: BlockId,
    params: List(BlockParam), // SSA block parameters
    instrs: List(Instr), // non-terminator instructions
    term: ?Terminator = null, // must be set before codegen

    pub fn init(allocator: std.mem.Allocator, id: BlockId) Block {
        return .{
            .id = id,
            .params = List(BlockParam).init(allocator),
            .instrs = List(Instr).init(allocator),
            .term = null,
        };
    }

    pub fn deinit(self: *Block, allocator: std.mem.Allocator) void {
        for (self.instrs.items) |*ins| ins.deinit(allocator);
        self.instrs.deinit();

        if (self.term) |*t| t.deinit(allocator);

        self.params.deinit();
    }
};

// -----------------------------------------------------------------------------
// Instructions
// Each instruction defines exactly one SSA value of type `ty` (including "void").
// -----------------------------------------------------------------------------
pub const InstrTag = enum(u8) {
    // Consts
    ConstInt,
    ConstFloat,
    ConstBool,
    ConstString,
    ConstNull, // typed null (optional/pointer)
    ConstUndef, // typed undef/poison

    // Arithmetic/Bitwise (integer or float depending on type)
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Shl,
    Shr, // Shr is logical or arithmetic depending on type info
    BitAnd,
    BitOr,
    BitXor,

    // Logical (bool)
    LogicalAnd,
    LogicalOr,
    LogicalNot, // unary (right)

    // Comparisons (result must be bool)
    CmpEq,
    CmpNe,
    CmpLt,
    CmpLe,
    CmpGt,
    CmpGe,

    // Casts
    CastNormal,
    CastBit,
    CastSaturate,
    CastWrap,
    CastChecked,

    // Memory
    Alloca, // stack allocation of result type (or explicit elem type)
    Load,
    Store, // "void" typed op (effect)
    Gep, // compute address via indices (like LLVM GEP)

    // Aggregates
    TupleMake,
    ArrayMake,
    StructMake,
    ExtractElem, // tuple/array
    InsertElem, // tuple/array
    ExtractField, // struct
    InsertField, // struct

    // Pointers/Indexing
    Index, // base[index] (for arrays/slices)
    AddressOf, // &x (rare post-typing; often lowered earlier)

    // Control/Data
    Select, // ternary: cond ? a : b

    // Calls
    Call,
};

pub const Instr = struct {
    tag: InstrTag,
    result: ValueId,
    ty: types.TypeId,
    payload: Payload,

    pub fn deinit(self: *Instr, allocator: std.mem.Allocator) void {
        switch (self.tag) {
            .ConstString => allocator.free(self.payload.ConstString),
            .Call => allocator.free(self.payload.Call.args),
            .TupleMake => allocator.free(self.payload.TupleMake.elems),
            .ArrayMake => allocator.free(self.payload.ArrayMake.elems),
            .StructMake => allocator.free(self.payload.StructMake.fields),
            .InsertElem => {}, // no owned slices
            .ExtractElem => {},
            .InsertField => {},
            .ExtractField => {},
            .Gep => allocator.free(self.payload.Gep.indices),
            .Store => {}, // nothing to free
            else => {},
        }
    }

    pub const GepIndex = union(enum) {
        // Either a constant index or a dynamic ValueId (typed int)
        Const: i64,
        Value: ValueId,
    };

    pub const StructFieldInit = struct {
        // index is authoritative for codegen; name is optional for printing
        index: u32,
        name: ?[]const u8 = null,
        value: ValueId,
    };

    pub const Payload = union(InstrTag) {
        // -------------------- Consts --------------------
        ConstInt: i64,
        ConstFloat: f64,
        ConstBool: bool,
        ConstString: []const u8,
        ConstNull: void,
        ConstUndef: void,

        // -------------------- Arith/Bit --------------------
        Add: Bin2,
        Sub: Bin2,
        Mul: Bin2,
        Div: Bin2,
        Mod: Bin2,
        Shl: Bin2,
        Shr: Bin2,
        BitAnd: Bin2,
        BitOr: Bin2,
        BitXor: Bin2,

        // -------------------- Logic --------------------
        LogicalAnd: Bin2,
        LogicalOr: Bin2,
        LogicalNot: Un1,

        // -------------------- Compares --------------------
        CmpEq: Bin2,
        CmpNe: Bin2,
        CmpLt: Bin2,
        CmpLe: Bin2,
        CmpGt: Bin2,
        CmpGe: Bin2,

        // -------------------- Casts --------------------
        CastNormal: Un1,
        CastBit: Un1,
        CastSaturate: Un1,
        CastWrap: Un1,
        CastChecked: Un1,

        // -------------------- Memory --------------------
        // Alloca returns a pointer type (ty is the resulting pointer type).
        // Optional `count` multiplies allocation size (for arrays).
        Alloca: struct { count: ?ValueId = null, @"align": u32 = 0 },
        Load: struct { ptr: ValueId, @"align": u32 = 0 },
        // Store has "void" result type; "value" is written to "ptr".
        Store: struct { ptr: ValueId, value: ValueId, @"align": u32 = 0 },

        // GEP: result is pointer; base is pointer, indices walk into aggregates
        Gep: struct { base: ValueId, indices: []const GepIndex },

        // -------------------- Aggregates --------------------
        TupleMake: struct { elems: []const ValueId },
        ArrayMake: struct { elems: []const ValueId },
        StructMake: struct { fields: []const StructFieldInit },

        ExtractElem: struct { agg: ValueId, index: u32 },
        InsertElem: struct { agg: ValueId, index: u32, value: ValueId },
        ExtractField: struct { agg: ValueId, index: u32, name: ?[]const u8 = null },
        InsertField: struct { agg: ValueId, index: u32, value: ValueId, name: ?[]const u8 = null },

        // -------------------- Indexing/Pointers --------------------
        Index: struct { base: ValueId, index: ValueId },
        AddressOf: struct { value: ValueId },

        // -------------------- Control/Data --------------------
        Select: struct { cond: ValueId, then_value: ValueId, else_value: ValueId },

        // -------------------- Calls --------------------
        Call: struct { callee: []const u8, args: []const ValueId },
    };

    pub const Bin2 = struct { lhs: ValueId, rhs: ValueId };
    pub const Un1 = struct { value: ValueId };
};

// -----------------------------------------------------------------------------
// Terminators
// -----------------------------------------------------------------------------
pub const Terminator = union(enum) {
    Return: ?ValueId,
    Br: BlockEdge,
    CondBr: struct {
        cond: ValueId,
        then_edge: BlockEdge,
        else_edge: BlockEdge,
    },
    SwitchInt: SwitchInt, // integer (or enum lowered to int) switch
    Unreachable: void,

    pub fn deinit(self: *Terminator, allocator: std.mem.Allocator) void {
        switch (self.*) {
            .Return => {},
            .Br => |*e| e.deinit(allocator),
            .CondBr => |*cb| {
                cb.then_edge.deinit(allocator);
                cb.else_edge.deinit(allocator);
            },
            .SwitchInt => |*sw| sw.deinit(allocator),
            .Unreachable => {},
        }
    }
};

// Edge to a block with SSA arguments (feeding the destination block params)
pub const BlockEdge = struct {
    dest: BlockId,
    args: []const ValueId = &.{},

    pub fn deinit(self: *BlockEdge, allocator: std.mem.Allocator) void {
        allocator.free(self.args);
    }
};

pub const SwitchInt = struct {
    scrut: ValueId,
    cases: []Case, // owned
    default_dest: BlockId,
    default_args: []const ValueId, // owned

    pub const Case = struct {
        value: u64,
        dest: BlockId,
        args: []const ValueId, // owned
    };

    pub fn deinit(self: *SwitchInt, allocator: std.mem.Allocator) void {
        for (self.cases) |*c| allocator.free(c.args);
        allocator.free(self.cases);
        allocator.free(self.default_args);
    }
};

// -----------------------------------------------------------------------------
// Builder
// -----------------------------------------------------------------------------
pub const Builder = struct {
    allocator: std.mem.Allocator,
    mod: *Module,
    next_block: BlockId = 0,
    next_value: ValueId = 0,

    pub fn init(allocator: std.mem.Allocator, mod: *Module) Builder {
        return .{ .allocator = allocator, .mod = mod };
    }

    fn freshValue(self: *Builder) ValueId {
        const id = self.next_value;
        self.next_value += 1;
        return id;
    }

    fn freshBlock(self: *Builder) BlockId {
        const id = self.next_block;
        self.next_block += 1;
        return id;
    }

    // ----- Module / Function / Block construction -----
    pub fn addFunction(self: *Builder, name: []const u8, result: types.TypeId) !*Function {
        const f = Function.init(self.allocator, name, result);
        try self.mod.functions.append(f);
        return &self.mod.functions.items[self.mod.functions.items.len - 1];
    }

    pub fn addFuncParam(self: *Builder, f: *Function, name: ?[]const u8, ty: types.TypeId) !ValueId {
        const id = self.freshValue();
        try f.params.append(.{ .id = id, .name = name, .ty = ty });
        return id;
    }

    pub fn addBlock(self: *Builder, f: *Function) !*Block {
        const id = self.freshBlock();
        const b = Block.init(self.allocator, id);
        try f.blocks.append(b);
        return &f.blocks.items[f.blocks.items.len - 1];
    }

    pub fn addBlockParam(self: *Builder, b: *Block, name: ?[]const u8, ty: types.TypeId) !ValueId {
        const id = self.freshValue();
        try b.params.append(.{ .id = id, .name = name, .ty = ty });
        return id;
    }

    // ----- Helpers to push instructions -----
    fn append(self: *Builder, b: *Block, ty: types.TypeId, tag: InstrTag, payload: Instr.Payload) !ValueId {
        const id = self.freshValue();
        try b.instrs.append(.{
            .tag = tag,
            .result = id,
            .ty = ty,
            .payload = payload,
        });
        return id;
    }

    // -------------------- Constants --------------------
    pub fn constInt(self: *Builder, b: *Block, ty: types.TypeId, value: i64) !ValueId {
        return self.append(b, ty, .ConstInt, .{ .ConstInt = value });
    }
    pub fn constFloat(self: *Builder, b: *Block, ty: types.TypeId, value: f64) !ValueId {
        return self.append(b, ty, .ConstFloat, .{ .ConstFloat = value });
    }
    pub fn constBool(self: *Builder, b: *Block, ty: types.TypeId, value: bool) !ValueId {
        return self.append(b, ty, .ConstBool, .{ .ConstBool = value });
    }
    pub fn constString(self: *Builder, b: *Block, ty: types.TypeId, s: []const u8) !ValueId {
        const copy = try self.allocator.alloc(u8, s.len);
        std.mem.copyForwards(u8, copy, s);
        return self.append(b, ty, .ConstString, .{ .ConstString = copy });
    }
    pub fn constNull(self: *Builder, b: *Block, ty: types.TypeId) !ValueId {
        return self.append(b, ty, .ConstNull, .{ .ConstNull = {} });
    }
    pub fn constUndef(self: *Builder, b: *Block, ty: types.TypeId) !ValueId {
        return self.append(b, ty, .ConstUndef, .{ .ConstUndef = {} });
    }

    // -------------------- Arith/Bit/Logic --------------------
    pub fn add(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .Add, .{ .Add = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn sub(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .Sub, .{ .Sub = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn mul(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .Mul, .{ .Mul = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn div(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .Div, .{ .Div = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn modulo(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .Mod, .{ .Mod = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn shl(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .Shl, .{ .Shl = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn shr(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .Shr, .{ .Shr = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn bitAnd(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .BitAnd, .{ .BitAnd = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn bitOr(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .BitOr, .{ .BitOr = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn bitXor(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .BitXor, .{ .BitXor = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn lAnd(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .LogicalAnd, .{ .LogicalAnd = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn lOr(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, ty, .LogicalOr, .{ .LogicalOr = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn lNot(self: *Builder, b: *Block, ty: types.TypeId, v: ValueId) !ValueId {
        return self.append(b, ty, .LogicalNot, .{ .LogicalNot = .{ .value = v } });
    }

    // -------------------- Compares (bool result) --------------------
    pub fn cmpEq(self: *Builder, b: *Block, bool_ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, bool_ty, .CmpEq, .{ .CmpEq = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn cmpNe(self: *Builder, b: *Block, bool_ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, bool_ty, .CmpNe, .{ .CmpNe = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn cmpLt(self: *Builder, b: *Block, bool_ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, bool_ty, .CmpLt, .{ .CmpLt = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn cmpLe(self: *Builder, b: *Block, bool_ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, bool_ty, .CmpLe, .{ .CmpLe = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn cmpGt(self: *Builder, b: *Block, bool_ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, bool_ty, .CmpGt, .{ .CmpGt = .{ .lhs = lhs, .rhs = rhs } });
    }
    pub fn cmpGe(self: *Builder, b: *Block, bool_ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        return self.append(b, bool_ty, .CmpGe, .{ .CmpGe = .{ .lhs = lhs, .rhs = rhs } });
    }

    // -------------------- Casts --------------------
    pub fn castNormal(self: *Builder, b: *Block, to_ty: types.TypeId, from: ValueId) !ValueId {
        return self.append(b, to_ty, .CastNormal, .{ .CastNormal = .{ .value = from } });
    }
    pub fn castBit(self: *Builder, b: *Block, to_ty: types.TypeId, from: ValueId) !ValueId {
        return self.append(b, to_ty, .CastBit, .{ .CastBit = .{ .value = from } });
    }
    pub fn castSaturate(self: *Builder, b: *Block, to_ty: types.TypeId, from: ValueId) !ValueId {
        return self.append(b, to_ty, .CastSaturate, .{ .CastSaturate = .{ .value = from } });
    }
    pub fn castWrap(self: *Builder, b: *Block, to_ty: types.TypeId, from: ValueId) !ValueId {
        return self.append(b, to_ty, .CastWrap, .{ .CastWrap = .{ .value = from } });
    }
    pub fn castChecked(self: *Builder, b: *Block, to_ty: types.TypeId, from: ValueId) !ValueId {
        return self.append(b, to_ty, .CastChecked, .{ .CastChecked = .{ .value = from } });
    }

    // -------------------- Memory --------------------
    pub fn alloca(self: *Builder, b: *Block, ptr_ty: types.TypeId, count: ?ValueId, @"align": u32) !ValueId {
        return self.append(b, ptr_ty, .Alloca, .{ .Alloca = .{ .count = count, .@"align" = @"align" } });
    }
    pub fn load(self: *Builder, b: *Block, ty: types.TypeId, ptr: ValueId, @"align": u32) !ValueId {
        return self.append(b, ty, .Load, .{ .Load = .{ .ptr = ptr, .@"align" = @"align" } });
    }
    pub fn store(self: *Builder, b: *Block, void_ty: types.TypeId, ptr: ValueId, value: ValueId, @"align": u32) !ValueId {
        return self.append(b, void_ty, .Store, .{ .Store = .{ .ptr = ptr, .value = value, .@"align" = @"align" } });
    }
    pub fn gep(self: *Builder, b: *Block, result_ptr_ty: types.TypeId, base: ValueId, indices: []const Instr.GepIndex) !ValueId {
        const copied = try self.allocator.alloc(Instr.GepIndex, indices.len);
        std.mem.copyForwards(Instr.GepIndex, copied, indices);
        return self.append(b, result_ptr_ty, .Gep, .{ .Gep = .{ .base = base, .indices = copied } });
    }

    // -------------------- Aggregates --------------------
    pub fn tupleMake(self: *Builder, b: *Block, ty: types.TypeId, elems: []const ValueId) !ValueId {
        const copied = try self.allocator.alloc(ValueId, elems.len);
        std.mem.copyForwards(ValueId, copied, elems);
        return self.append(b, ty, .TupleMake, .{ .TupleMake = .{ .elems = copied } });
    }
    pub fn arrayMake(self: *Builder, b: *Block, ty: types.TypeId, elems: []const ValueId) !ValueId {
        const copied = try self.allocator.alloc(ValueId, elems.len);
        std.mem.copyForwards(ValueId, copied, elems);
        return self.append(b, ty, .ArrayMake, .{ .ArrayMake = .{ .elems = copied } });
    }
    pub fn structMake(self: *Builder, b: *Block, ty: types.TypeId, fields: []const Instr.StructFieldInit) !ValueId {
        const copied = try self.allocator.alloc(Instr.StructFieldInit, fields.len);
        std.mem.copyForwards(Instr.StructFieldInit, copied, fields);
        return self.append(b, ty, .StructMake, .{ .StructMake = .{ .fields = copied } });
    }
    pub fn extractElem(self: *Builder, b: *Block, result_ty: types.TypeId, agg: ValueId, idx: u32) !ValueId {
        return self.append(b, result_ty, .ExtractElem, .{ .ExtractElem = .{ .agg = agg, .index = idx } });
    }
    pub fn insertElem(self: *Builder, b: *Block, result_ty: types.TypeId, agg: ValueId, idx: u32, value: ValueId) !ValueId {
        return self.append(b, result_ty, .InsertElem, .{ .InsertElem = .{ .agg = agg, .index = idx, .value = value } });
    }
    pub fn extractField(self: *Builder, b: *Block, result_ty: types.TypeId, agg: ValueId, idx: u32, name: ?[]const u8) !ValueId {
        return self.append(b, result_ty, .ExtractField, .{ .ExtractField = .{ .agg = agg, .index = idx, .name = name } });
    }
    pub fn insertField(self: *Builder, b: *Block, result_ty: types.TypeId, agg: ValueId, idx: u32, value: ValueId, name: ?[]const u8) !ValueId {
        return self.append(b, result_ty, .InsertField, .{ .InsertField = .{ .agg = agg, .index = idx, .value = value, .name = name } });
    }

    // -------------------- Indexing/Pointers --------------------
    pub fn index(self: *Builder, b: *Block, result_ty: types.TypeId, base: ValueId, idx: ValueId) !ValueId {
        return self.append(b, result_ty, .Index, .{ .Index = .{ .base = base, .index = idx } });
    }
    pub fn addressOf(self: *Builder, b: *Block, result_ptr_ty: types.TypeId, value: ValueId) !ValueId {
        return self.append(b, result_ptr_ty, .AddressOf, .{ .AddressOf = .{ .value = value } });
    }

    // -------------------- Data --------------------
    pub fn select(self: *Builder, b: *Block, ty: types.TypeId, cond: ValueId, tval: ValueId, fval: ValueId) !ValueId {
        return self.append(b, ty, .Select, .{ .Select = .{ .cond = cond, .then_value = tval, .else_value = fval } });
    }

    // -------------------- Calls --------------------
    pub fn call(self: *Builder, b: *Block, result_ty: types.TypeId, callee: []const u8, args: []const ValueId) !ValueId {
        const args_copy = try self.allocator.alloc(ValueId, args.len);
        std.mem.copyForwards(ValueId, args_copy, args);
        return self.append(b, result_ty, .Call, .{ .Call = .{ .callee = callee, .args = args_copy } });
    }

    // -------------------- Terminators --------------------
    pub fn retVoid(_: *Builder, b: *Block) void {
        b.term = .{ .Return = null };
    }
    pub fn ret(_: *Builder, b: *Block, v: ValueId) void {
        b.term = .{ .Return = v };
    }

    pub fn br(self: *Builder, b: *Block, dest: BlockId, args: []const ValueId) !void {
        const copy = try self.allocator.alloc(ValueId, args.len);
        std.mem.copyForwards(ValueId, copy, args);
        b.term = .{ .Br = .{ .dest = dest, .args = copy } };
    }

    pub fn condBr(self: *Builder, b: *Block, cond: ValueId, then_dest: BlockId, then_args: []const ValueId, else_dest: BlockId, else_args: []const ValueId) !void {
        const tcopy = try self.allocator.alloc(ValueId, then_args.len);
        std.mem.copyForwards(ValueId, tcopy, then_args);
        const fcopy = try self.allocator.alloc(ValueId, else_args.len);
        std.mem.copyForwards(ValueId, fcopy, else_args);
        b.term = .{ .CondBr = .{
            .cond = cond,
            .then_edge = .{ .dest = then_dest, .args = tcopy },
            .else_edge = .{ .dest = else_dest, .args = fcopy },
        } };
    }

    pub fn switchInt(self: *Builder, b: *Block, scrut: ValueId, cases: []const SwitchInt.Case, default_dest: BlockId, default_args: []const ValueId) !void {
        // Deep-copy cases + their arg slices
        var copied_cases = try self.allocator.alloc(SwitchInt.Case, cases.len);
        for (cases, 0..) |c, i| {
            const args_copy = try self.allocator.alloc(ValueId, c.args.len);
            std.mem.copyForwards(ValueId, args_copy, c.args);
            copied_cases[i] = .{ .value = c.value, .dest = c.dest, .args = args_copy };
        }
        const def_copy = try self.allocator.alloc(ValueId, default_args.len);
        std.mem.copyForwards(ValueId, def_copy, default_args);
        b.term = .{ .SwitchInt = .{
            .scrut = scrut,
            .cases = copied_cases,
            .default_dest = default_dest,
            .default_args = def_copy,
        } };
    }

    pub fn unreachableOp(_: *Builder, b: *Block) void {
        b.term = .{ .Unreachable = {} };
    }
};

// -----------------------------------------------------------------------------
// Printer  (follows your style, extended for the new features)
// -----------------------------------------------------------------------------
pub const Printer = struct {
    w: *std.io.Writer,
    type_arena: *types.TypeArena,

    pub fn init(writer: *std.io.Writer, type_arena: *types.TypeArena) @This() {
        return .{ .w = writer, .type_arena = type_arena };
    }

    pub fn printModule(self: *@This(), m: *const Module) !void {
        try self.w.print("(tir.module\n", .{});
        // Globals
        for (m.globals.items) |g| {
            try self.w.print("  (global {s} : ", .{g.name});
            try self.type_arena.fmt(g.ty, self.w);
            try self.w.print(")\n", .{});
        }
        // Functions
        for (m.functions.items) |*f| try self.printFunction(f);
        try self.w.print(")\n", .{});
        try self.w.flush();
    }

    fn printFunction(self: *@This(), f: *const Function) !void {
        try self.w.print("  (func {s} (", .{f.name});
        for (f.params.items, 0..) |p, i| {
            if (i != 0) try self.w.print(", ", .{});
            if (p.name) |n| {
                try self.w.print("%{d}:{s}: ", .{ p.id, n });
            } else {
                try self.w.print("%{d}: ", .{p.id});
            }
            try self.type_arena.fmt(p.ty, self.w);
        }
        try self.w.print(") -> ", .{});
        try self.type_arena.fmt(f.result, self.w);
        try self.w.print("\n", .{});

        for (f.blocks.items) |*b| try self.printBlock(b);

        try self.w.print("  )\n", .{});
    }

    fn printBlock(self: *@This(), b: *const Block) !void {
        try self.w.print("    (block %{d}", .{b.id});
        if (b.params.items.len != 0) {
            try self.w.print(" (", .{});
            for (b.params.items, 0..) |p, i| {
                if (i != 0) try self.w.print(", ", .{});
                if (p.name) |n| {
                    try self.w.print("%{d}:{s}: ", .{ p.id, n });
                } else {
                    try self.w.print("%{d}: ", .{p.id});
                }
                try self.type_arena.fmt(p.ty, self.w);
            }
            try self.w.print(")", .{});
        }
        try self.w.print(",\n", .{});

        for (b.instrs.items) |*ins| try self.printInstr(ins);

        if (b.term) |t| {
            try self.printTerminator(&t);
        } else {
            try self.w.print("      (ret)\n", .{});
        }
        try self.w.print("    )\n", .{});
    }

    fn printValueList(self: *@This(), vals: []const ValueId) !void {
        for (vals) |v| try self.w.print(" %{d}", .{v});
    }

    fn printEdge(self: *@This(), e: *const BlockEdge) !void {
        try self.w.print(" %{d}", .{e.dest});
        try self.printValueList(e.args);
    }

    fn printTerminator(self: *@This(), t: *const Terminator) !void {
        switch (t.*) {
            .Return => |rv| {
                if (rv) |v|
                    try self.w.print("      (ret %{d})\n", .{v})
                else
                    try self.w.print("      (ret)\n", .{});
            },
            .Br => |e| {
                try self.w.print("      (br", .{});
                try self.printEdge(&e);
                try self.w.print(")\n", .{});
            },
            .CondBr => |cb| {
                try self.w.print("      (condbr %{d}", .{cb.cond});
                try self.printEdge(&cb.then_edge);
                try self.printEdge(&cb.else_edge);
                try self.w.print(")\n", .{});
            },
            .SwitchInt => |sw| {
                try self.w.print("      (switch %{d}\n", .{sw.scrut});
                for (sw.cases) |c| {
                    try self.w.print("        (case {d}", .{c.value});
                    try self.w.print(" %{d}", .{c.dest});
                    try self.printValueList(c.args);
                    try self.w.print(")\n", .{});
                }
                try self.w.print("        (default %{d}", .{sw.default_dest});
                try self.printValueList(sw.default_args);
                try self.w.print(")\n", .{});
                try self.w.print("      )\n", .{});
            },
            .Unreachable => {
                try self.w.print("      (unreachable)\n", .{});
            },
        }
    }

    fn printInstr(self: *@This(), i: *const Instr) !void {
        try self.w.print("      (%{d} : ", .{i.result});
        try self.type_arena.fmt(i.ty, self.w);
        try self.w.print(" ", .{});

        switch (i.tag) {
            // -------------------- Consts --------------------
            .ConstInt => try self.w.print("const_int {d}", .{i.payload.ConstInt}),
            .ConstFloat => try self.w.print("const_float {d}", .{i.payload.ConstFloat}),
            .ConstBool => try self.w.print("const_bool {}", .{i.payload.ConstBool}),
            .ConstString => try self.w.print("const \"{s}\"", .{i.payload.ConstString}),
            .ConstNull => try self.w.print("const_null", .{}),
            .ConstUndef => try self.w.print("const_undef", .{}),

            // -------------------- Arith/Bit/Logic --------------------
            .Add => try self.printBin2("add", i.payload.Add),
            .Sub => try self.printBin2("sub", i.payload.Sub),
            .Mul => try self.printBin2("mul", i.payload.Mul),
            .Div => try self.printBin2("div", i.payload.Div),
            .Mod => try self.printBin2("mod", i.payload.Mod),
            .Shl => try self.printBin2("shl", i.payload.Shl),
            .Shr => try self.printBin2("shr", i.payload.Shr),
            .BitAnd => try self.printBin2("band", i.payload.BitAnd),
            .BitOr => try self.printBin2("bor", i.payload.BitOr),
            .BitXor => try self.printBin2("bxor", i.payload.BitXor),
            .LogicalAnd => try self.printBin2("land", i.payload.LogicalAnd),
            .LogicalOr => try self.printBin2("lor", i.payload.LogicalOr),
            .LogicalNot => try self.printUn1("lnot", i.payload.LogicalNot),

            // -------------------- Compares --------------------
            .CmpEq => try self.printBin2("cmp_eq", i.payload.CmpEq),
            .CmpNe => try self.printBin2("cmp_ne", i.payload.CmpNe),
            .CmpLt => try self.printBin2("cmp_lt", i.payload.CmpLt),
            .CmpLe => try self.printBin2("cmp_le", i.payload.CmpLe),
            .CmpGt => try self.printBin2("cmp_gt", i.payload.CmpGt),
            .CmpGe => try self.printBin2("cmp_ge", i.payload.CmpGe),

            // -------------------- Casts --------------------
            .CastNormal => try self.printUn1("cast_normal", i.payload.CastNormal),
            .CastBit => try self.printUn1("cast_bit", i.payload.CastBit),
            .CastSaturate => try self.printUn1("cast_saturate", i.payload.CastSaturate),
            .CastWrap => try self.printUn1("cast_wrap", i.payload.CastWrap),
            .CastChecked => try self.printUn1("cast_checked", i.payload.CastChecked),

            // -------------------- Memory --------------------
            .Alloca => {
                const a = i.payload.Alloca;
                try self.w.print("alloca", .{});
                if (a.count) |c| try self.w.print(" count=%{d}", .{c});
                if (a.@"align" != 0) try self.w.print(" align={d}", .{a.@"align"});
            },
            .Load => {
                const ld = i.payload.Load;
                try self.w.print("load %{d}", .{ld.ptr});
                if (ld.@"align" != 0) try self.w.print(" align={d}", .{ld.@"align"});
            },
            .Store => {
                const st = i.payload.Store;
                try self.w.print("store %{d} %{d}", .{ st.ptr, st.value });
                if (st.@"align" != 0) try self.w.print(" align={d}", .{st.@"align"});
            },
            .Gep => {
                const g = i.payload.Gep;
                try self.w.print("gep %{d}", .{g.base});
                for (g.indices) |idx| switch (idx) {
                    .Const => |k| try self.w.print(" {d}", .{k}),
                    .Value => |v| try self.w.print(" %{d}", .{v}),
                };
            },

            // -------------------- Aggregates --------------------
            .TupleMake => {
                const tm = i.payload.TupleMake;
                try self.w.print("tuple.make", .{});
                try self.printValueList(tm.elems);
            },
            .ArrayMake => {
                const am = i.payload.ArrayMake;
                try self.w.print("array.make", .{});
                try self.printValueList(am.elems);
            },
            .StructMake => {
                const sm = i.payload.StructMake;
                try self.w.print("struct.make", .{});
                for (sm.fields) |f| {
                    if (f.name) |n|
                        try self.w.print(" {s}=%{d}", .{ n, f.value })
                    else
                        try self.w.print(" #{d}=%{d}", .{ f.index, f.value });
                }
            },
            .ExtractElem => {
                const ee = i.payload.ExtractElem;
                try self.w.print("extract.elem %{d} {d}", .{ ee.agg, ee.index });
            },
            .InsertElem => {
                const ie = i.payload.InsertElem;
                try self.w.print("insert.elem %{d} {d} %{d}", .{ ie.agg, ie.index, ie.value });
            },
            .ExtractField => {
                const ef = i.payload.ExtractField;
                if (ef.name) |n|
                    try self.w.print("extract.field %{d} {s}", .{ ef.agg, n })
                else
                    try self.w.print("extract.field %{d} #{d}", .{ ef.agg, ef.index });
            },
            .InsertField => {
                const inf = i.payload.InsertField;
                if (inf.name) |n|
                    try self.w.print("insert.field %{d} {s} %{d}", .{ inf.agg, n, inf.value })
                else
                    try self.w.print("insert.field %{d} #{d} %{d}", .{ inf.agg, inf.index, inf.value });
            },

            // -------------------- Indexing/Pointers --------------------
            .Index => {
                const ix = i.payload.Index;
                try self.w.print("index %{d} %{d}", .{ ix.base, ix.index });
            },
            .AddressOf => {
                const ao = i.payload.AddressOf;
                try self.w.print("addr_of %{d}", .{ao.value});
            },

            // -------------------- Data --------------------
            .Select => {
                const s = i.payload.Select;
                try self.w.print("select %{d} %{d} %{d}", .{ s.cond, s.then_value, s.else_value });
            },

            // -------------------- Calls --------------------
            .Call => {
                const c = i.payload.Call;
                try self.w.print("call {s}", .{c.callee});
                try self.printValueList(c.args);
            },
        }
        try self.w.print(")\n", .{});
    }

    fn printBin2(self: *@This(), opname: []const u8, b: Instr.Bin2) !void {
        try self.w.print("{s} %{d} %{d}", .{ opname, b.lhs, b.rhs });
    }
    fn printUn1(self: *@This(), opname: []const u8, u: Instr.Un1) !void {
        try self.w.print("{s} %{d}", .{ opname, u.value });
    }
};
