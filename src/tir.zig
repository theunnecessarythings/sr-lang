const std = @import("std");
const dod = @import("cst.zig");
const ast = @import("ast.zig");
const types = @import("types.zig");
const comp = @import("comptime.zig");
const Context = @import("compile.zig").Context;

pub const OptLocId = dod.OptLocId;

// Typed IR (TIR)
pub const ValueTag = struct {};
pub const InstrTag = struct {};
pub const TermTag = struct {};

pub const ValueId = dod.Index(ValueTag);
pub const OptValueId = dod.SentinelIndex(ValueTag);
pub const FuncId = dod.Index(FuncRows.Function);
pub const BlockId = dod.Index(FuncRows.Block);
pub const InstrId = dod.Index(InstrTag);
pub const TermId = dod.Index(TermTag);
pub const OptTermId = dod.SentinelIndex(TermTag);
pub const ParamId = dod.Index(FuncRows.Param);
pub const GlobalId = dod.Index(FuncRows.Global);
pub const EdgeId = dod.Index(Rows.Edge);
pub const CaseId = dod.Index(Rows.Case);
pub const AttributeId = dod.Index(Rows.Attribute);
pub const MlirPieceId = dod.Index(Rows.MlirPiece);

pub const RangeValue = dod.RangeOf(ValueId);
pub const RangeBlock = dod.RangeOf(BlockId);
pub const RangeInstr = dod.RangeOf(InstrId);
pub const RangeParam = dod.RangeOf(ParamId);
pub const RangeEdge = dod.RangeOf(EdgeId);
pub const RangeCase = dod.RangeOf(CaseId);
pub const RangeFunc = dod.RangeOf(FuncId);
pub const RangeGlobal = dod.RangeOf(GlobalId);
pub const RangeAttribute = dod.RangeOf(AttributeId);
pub const RangeMlirPiece = dod.RangeOf(MlirPieceId);
pub const RangeGepIndex = dod.RangeOf(GepIndexId);
pub const RangeStructFieldInit = dod.RangeOf(StructFieldInitId);
pub const RangeValList = dod.RangeOf(ValueId);

pub const Pool = dod.Pool;
pub const Table = dod.Table;
pub const StoreIndex = dod.StoreIndex;
pub const StringInterner = dod.StringInterner;
pub const StrId = dod.StrId;

// ---------------- Ops and Terms ----------------
pub const OpKind = enum(u16) {
    ConstInt,
    ConstFloat,
    ConstBool,
    ConstString,
    ConstNull,
    ConstUndef,
    Add,
    Sub,
    Mul,
    BinWrapAdd,
    BinWrapSub,
    BinWrapMul,
    BinSatAdd,
    BinSatSub,
    BinSatMul,
    BinSatShl,
    Div,
    Mod,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    LogicalAnd,
    LogicalOr,
    LogicalNot,
    CmpEq,
    CmpNe,
    CmpLt,
    CmpLe,
    CmpGt,
    CmpGe,
    CastNormal,
    CastBit,
    CastSaturate,
    CastWrap,
    CastChecked,
    Alloca,
    Load,
    Store,
    Gep,
    GlobalAddr,
    TupleMake,
    ArrayMake,
    StructMake,
    ExtractElem,
    InsertElem,
    ExtractField,
    InsertField,
    Index,
    AddressOf,
    Select,
    Call,
    IndirectCall,
    MlirBlock,
    VariantMake,
    VariantTag,
    VariantPayloadPtr,
    UnionMake,
    UnionField,
    UnionFieldPtr,
    ComplexMake,
    RangeMake,
    Broadcast,
    Await,
    DbgDeclare,
};

pub const TermKind = enum(u8) { Return, Br, CondBr, SwitchInt, Unreachable };

pub const ConstInit = union(enum) {
    none,
    int: i64,
    bool: bool,
    string: StrId,
    float: f64,
    aggregate: []const ConstInit,
};

pub const Rows = struct {
    pub const Bin2 = struct { result: ValueId, ty: types.TypeId, lhs: ValueId, rhs: ValueId, loc: OptLocId };
    pub const Un1 = struct { result: ValueId, ty: types.TypeId, value: ValueId, loc: OptLocId };

    pub const ConstInt = struct { result: ValueId, ty: types.TypeId, value: i128, loc: OptLocId };
    pub const ConstFloat = struct { result: ValueId, ty: types.TypeId, value: f64, loc: OptLocId };
    pub const ConstBool = struct { result: ValueId, ty: types.TypeId, value: bool, loc: OptLocId };
    pub const ConstString = struct { result: ValueId, ty: types.TypeId, text: StrId, loc: OptLocId };
    pub const ConstNull = struct { result: ValueId, ty: types.TypeId, loc: OptLocId };
    pub const ConstUndef = struct { result: ValueId, ty: types.TypeId, loc: OptLocId };

    pub const Alloca = struct { result: ValueId, ty: types.TypeId, count: OptValueId, @"align": u32, loc: OptLocId };
    pub const Load = struct { result: ValueId, ty: types.TypeId, ptr: ValueId, @"align": u32, loc: OptLocId };
    pub const Store = struct { result: ValueId, ty: types.TypeId, ptr: ValueId, value: ValueId, @"align": u32, loc: OptLocId };
    pub const GepIndex = union(enum) { Const: u64, Value: ValueId };
    pub const Gep = struct { result: ValueId, ty: types.TypeId, base: ValueId, indices: RangeGepIndex, loc: OptLocId };

    pub const TupleMake = struct { result: ValueId, ty: types.TypeId, elems: RangeValue, loc: OptLocId };
    pub const ArrayMake = struct { result: ValueId, ty: types.TypeId, elems: RangeValue, loc: OptLocId };
    pub const StructFieldInit = struct { index: u32, name: dod.OptStrId, value: ValueId };
    pub const Attribute = struct { name: StrId, value: OptValueId };
    pub const StructMake = struct { result: ValueId, ty: types.TypeId, fields: RangeStructFieldInit, loc: OptLocId };

    pub const ExtractElem = struct { result: ValueId, ty: types.TypeId, agg: ValueId, index: u32, loc: OptLocId };
    pub const InsertElem = struct { result: ValueId, ty: types.TypeId, agg: ValueId, index: u32, value: ValueId, loc: OptLocId };
    pub const ExtractField = struct { result: ValueId, ty: types.TypeId, agg: ValueId, index: u32, name: dod.OptStrId, loc: OptLocId };
    pub const InsertField = struct { result: ValueId, ty: types.TypeId, agg: ValueId, index: u32, value: ValueId, name: dod.OptStrId, loc: OptLocId };

    pub const Index = struct { result: ValueId, ty: types.TypeId, base: ValueId, index: ValueId, loc: OptLocId };
    pub const AddressOf = struct { result: ValueId, ty: types.TypeId, value: ValueId, loc: OptLocId };
    pub const GlobalAddr = struct { result: ValueId, ty: types.TypeId, name: StrId, loc: OptLocId };
    pub const Select = struct { result: ValueId, ty: types.TypeId, cond: ValueId, then_value: ValueId, else_value: ValueId, loc: OptLocId };

    pub const Call = struct { result: ValueId, ty: types.TypeId, callee: StrId, args: RangeValList, loc: OptLocId };
    pub const IndirectCall = struct { result: ValueId, ty: types.TypeId, callee: ValueId, args: RangeValList, loc: OptLocId };
    pub const MlirPiece = struct { kind: ast.MlirPieceKind, text: StrId, value: comp.ComptimeValue, ty: ?types.TypeId };
    pub const MlirBlock = struct { result: OptValueId, ty: types.TypeId, kind: ast.MlirKind, expr: ast.ExprId, text: StrId, pieces: RangeMlirPiece, args: RangeValue, loc: OptLocId };

    pub const VariantMake = struct { result: ValueId, ty: types.TypeId, tag: u32, payload: OptValueId, payload_ty: types.TypeId, loc: OptLocId };
    pub const VariantTag = struct { result: ValueId, ty: types.TypeId, value: ValueId, loc: OptLocId };
    pub const VariantPayloadPtr = struct { result: ValueId, ty: types.TypeId, value: ValueId, loc: OptLocId };
    pub const UnionMake = struct { result: ValueId, ty: types.TypeId, field_index: u32, value: ValueId, loc: OptLocId };
    pub const UnionField = struct { result: ValueId, ty: types.TypeId, base: ValueId, field_index: u32, loc: OptLocId };
    pub const UnionFieldPtr = struct { result: ValueId, ty: types.TypeId, base: ValueId, field_index: u32, loc: OptLocId };
    pub const ComplexMake = struct { result: ValueId, ty: types.TypeId, re: ValueId, im: ValueId, loc: OptLocId };
    pub const RangeMake = struct { result: ValueId, ty: types.TypeId, start: ValueId, end: ValueId, inclusive: ValueId, loc: OptLocId };
    pub const Broadcast = struct { result: ValueId, ty: types.TypeId, value: ValueId, loc: OptLocId };
    pub const Await = struct { result: ValueId, ty: types.TypeId, operand: ValueId, loc: OptLocId };
    pub const DbgDeclare = struct { result: ValueId, ty: types.TypeId, value: ValueId, name: StrId, loc: OptLocId };

    // Terminator rows
    pub const Return = struct { value: OptValueId, loc: OptLocId };
    pub const Edge = struct { dest: BlockId, args: RangeValue, loc: OptLocId };
    pub const Br = struct { edge: EdgeId, loc: OptLocId };
    pub const CondBr = struct { cond: ValueId, then_edge: EdgeId, else_edge: EdgeId, loc: OptLocId };
    pub const Case = struct { value: u64, edge: EdgeId, loc: OptLocId };
    pub const SwitchInt = struct { scrut: ValueId, cases: RangeCase, default_edge: EdgeId, loc: OptLocId };
    pub const Unreachable = struct { loc: OptLocId };
};

pub const GepIndexId = dod.Index(Rows.GepIndex);
pub const StructFieldInitId = dod.Index(Rows.StructFieldInit);

pub inline fn RowT(comptime K: OpKind) type {
    return switch (K) {
        .ConstInt => Rows.ConstInt,
        .ConstFloat => Rows.ConstFloat,
        .ConstBool => Rows.ConstBool,
        .ConstString => Rows.ConstString,
        .ConstNull => Rows.ConstNull,
        .ConstUndef => Rows.ConstUndef,
        .Add, .Sub, .Mul, .BinWrapAdd, .BinWrapSub, .BinWrapMul, .BinSatAdd, .BinSatSub, .BinSatMul, .BinSatShl, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .LogicalAnd, .LogicalOr, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe => Rows.Bin2,
        .LogicalNot, .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => Rows.Un1,
        .Alloca => Rows.Alloca,
        .Load => Rows.Load,
        .Store => Rows.Store,
        .Gep => Rows.Gep,
        .GlobalAddr => Rows.GlobalAddr,
        .TupleMake => Rows.TupleMake,
        .ArrayMake => Rows.ArrayMake,
        .StructMake => Rows.StructMake,
        .ExtractElem => Rows.ExtractElem,
        .InsertElem => Rows.InsertElem,
        .ExtractField => Rows.ExtractField,
        .InsertField => Rows.InsertField,
        .Index => Rows.Index,
        .AddressOf => Rows.AddressOf,
        .Select => Rows.Select,
        .Call => Rows.Call,
        .IndirectCall => Rows.IndirectCall,
        .MlirBlock => Rows.MlirBlock,
        .VariantMake => Rows.VariantMake,
        .VariantTag => Rows.VariantTag,
        .VariantPayloadPtr => Rows.VariantPayloadPtr,
        .UnionMake => Rows.UnionMake,
        .UnionField => Rows.UnionField,
        .UnionFieldPtr => Rows.UnionFieldPtr,
        .ComplexMake => Rows.ComplexMake,
        .RangeMake => Rows.RangeMake,
        .Broadcast => Rows.Broadcast,
        .Await => Rows.Await,
        .DbgDeclare => Rows.DbgDeclare,
    };
}
inline fn TermRowT(comptime K: TermKind) type {
    return @field(Rows, @tagName(K));
}

pub const InstrStore = struct {
    arena: *std.heap.ArenaAllocator,
    backing_gpa: std.mem.Allocator,
    allocator: std.mem.Allocator,
    index: StoreIndex(OpKind) = .{},

    ConstInt: Table(Rows.ConstInt) = .{},
    ConstFloat: Table(Rows.ConstFloat) = .{},
    ConstBool: Table(Rows.ConstBool) = .{},
    ConstString: Table(Rows.ConstString) = .{},
    ConstNull: Table(Rows.ConstNull) = .{},
    ConstUndef: Table(Rows.ConstUndef) = .{},
    Add: Table(Rows.Bin2) = .{},
    Sub: Table(Rows.Bin2) = .{},
    Mul: Table(Rows.Bin2) = .{},
    BinWrapAdd: Table(Rows.Bin2) = .{},
    BinWrapSub: Table(Rows.Bin2) = .{},
    BinWrapMul: Table(Rows.Bin2) = .{},
    BinSatAdd: Table(Rows.Bin2) = .{},
    BinSatSub: Table(Rows.Bin2) = .{},
    BinSatMul: Table(Rows.Bin2) = .{},
    BinSatShl: Table(Rows.Bin2) = .{},
    Div: Table(Rows.Bin2) = .{},
    Mod: Table(Rows.Bin2) = .{},
    Shl: Table(Rows.Bin2) = .{},
    Shr: Table(Rows.Bin2) = .{},
    BitAnd: Table(Rows.Bin2) = .{},
    BitOr: Table(Rows.Bin2) = .{},
    BitXor: Table(Rows.Bin2) = .{},
    LogicalAnd: Table(Rows.Bin2) = .{},
    LogicalOr: Table(Rows.Bin2) = .{},
    LogicalNot: Table(Rows.Un1) = .{},
    CmpEq: Table(Rows.Bin2) = .{},
    CmpNe: Table(Rows.Bin2) = .{},
    CmpLt: Table(Rows.Bin2) = .{},
    CmpLe: Table(Rows.Bin2) = .{},
    CmpGt: Table(Rows.Bin2) = .{},
    CmpGe: Table(Rows.Bin2) = .{},
    CastNormal: Table(Rows.Un1) = .{},
    CastBit: Table(Rows.Un1) = .{},
    CastSaturate: Table(Rows.Un1) = .{},
    CastWrap: Table(Rows.Un1) = .{},
    CastChecked: Table(Rows.Un1) = .{},
    Alloca: Table(Rows.Alloca) = .{},
    Load: Table(Rows.Load) = .{},
    Store: Table(Rows.Store) = .{},
    Gep: Table(Rows.Gep) = .{},
    GlobalAddr: Table(Rows.GlobalAddr) = .{},
    TupleMake: Table(Rows.TupleMake) = .{},
    ArrayMake: Table(Rows.ArrayMake) = .{},
    StructMake: Table(Rows.StructMake) = .{},
    ExtractElem: Table(Rows.ExtractElem) = .{},
    InsertElem: Table(Rows.InsertElem) = .{},
    ExtractField: Table(Rows.ExtractField) = .{},
    InsertField: Table(Rows.InsertField) = .{},
    Index: Table(Rows.Index) = .{},
    AddressOf: Table(Rows.AddressOf) = .{},
    Select: Table(Rows.Select) = .{},
    Call: Table(Rows.Call) = .{},
    IndirectCall: Table(Rows.IndirectCall) = .{},
    MlirBlock: Table(Rows.MlirBlock) = .{},
    MlirPiece: Table(Rows.MlirPiece) = .{},
    VariantMake: Table(Rows.VariantMake) = .{},
    VariantTag: Table(Rows.VariantTag) = .{},
    VariantPayloadPtr: Table(Rows.VariantPayloadPtr) = .{},
    UnionMake: Table(Rows.UnionMake) = .{},
    UnionField: Table(Rows.UnionField) = .{},
    UnionFieldPtr: Table(Rows.UnionFieldPtr) = .{},
    ComplexMake: Table(Rows.ComplexMake) = .{},
    RangeMake: Table(Rows.RangeMake) = .{},
    Broadcast: Table(Rows.Broadcast) = .{},
    Await: Table(Rows.Await) = .{},
    DbgDeclare: Table(Rows.DbgDeclare) = .{},

    GepIndex: Table(Rows.GepIndex) = .{},
    StructFieldInit: Table(Rows.StructFieldInit) = .{},
    Attribute: Table(Rows.Attribute) = .{},

    instr_pool: Pool(InstrId) = .{},
    value_pool: Pool(ValueId) = .{},
    gep_pool: Pool(GepIndexId) = .{},
    sfi_pool: Pool(StructFieldInitId) = .{},
    attribute_pool: Pool(AttributeId) = .{},
    val_list_pool: Pool(ValueId) = .{},
    mlir_piece_pool: Pool(MlirPieceId) = .{},
    strs: *StringInterner,

    pub fn init(gpa: std.mem.Allocator, interner: *StringInterner) InstrStore {
        const arena = gpa.create(std.heap.ArenaAllocator) catch @panic("OOM");
        arena.* = std.heap.ArenaAllocator.init(gpa);
        return .{ .arena = arena, .backing_gpa = gpa, .allocator = arena.allocator(), .strs = interner };
    }
    pub fn deinit(self: *@This()) void {
        self.arena.deinit();
        self.backing_gpa.destroy(self.arena);
    }

    pub fn add(self: *@This(), comptime K: OpKind, row: RowT(K)) InstrId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        return self.index.newId(self.allocator, K, tbl.add(self.allocator, row).toRaw(), InstrId);
    }
    pub fn get(self: *@This(), comptime K: OpKind, id: InstrId) RowT(K) {
        return @field(self, @tagName(K)).get(.{ .index = self.index.rows.items[id.toRaw()] });
    }
};

pub const TermStore = struct {
    arena: *std.heap.ArenaAllocator,
    backing_gpa: std.mem.Allocator,
    allocator: std.mem.Allocator,
    index: StoreIndex(TermKind) = .{},
    Return: Table(Rows.Return) = .{},
    Br: Table(Rows.Br) = .{},
    CondBr: Table(Rows.CondBr) = .{},
    SwitchInt: Table(Rows.SwitchInt) = .{},
    Unreachable: Table(Rows.Unreachable) = .{},
    Edge: Table(Rows.Edge) = .{},
    Case: Table(Rows.Case) = .{},
    term_pool: Pool(TermId) = .{},
    edge_pool: Pool(EdgeId) = .{},
    case_pool: Pool(CaseId) = .{},

    pub fn init(gpa: std.mem.Allocator) TermStore {
        const arena = gpa.create(std.heap.ArenaAllocator) catch @panic("OOM");
        arena.* = std.heap.ArenaAllocator.init(gpa);
        return .{ .arena = arena, .backing_gpa = gpa, .allocator = arena.allocator() };
    }
    pub fn deinit(self: *@This()) void {
        self.arena.deinit();
        self.backing_gpa.destroy(self.arena);
    }

    pub fn add(self: *@This(), comptime K: TermKind, row: TermRowT(K)) TermId {
        const tbl: *Table(TermRowT(K)) = &@field(self, @tagName(K));
        return self.index.newId(self.allocator, K, tbl.add(self.allocator, row).toRaw(), TermId);
    }
    pub fn get(self: *@This(), comptime K: TermKind, id: TermId) TermRowT(K) {
        return @field(self, @tagName(K)).get(.{ .index = self.index.rows.items[id.toRaw()] });
    }
};

pub const FuncRows = struct {
    pub const Param = struct { value: ValueId, name: dod.OptStrId, ty: types.TypeId };
    pub const Block = struct { params: RangeParam, instrs: RangeInstr, term: TermId };
    pub const Function = struct { name: StrId, params: RangeParam, result: types.TypeId, blocks: RangeBlock, is_variadic: bool, is_extern: bool, attrs: RangeAttribute, is_triton_fn: bool, is_async: bool, raw_asm: dod.OptStrId };
    pub const Global = struct { name: StrId, ty: types.TypeId, init: ConstInit };
};

pub const FuncStore = struct {
    arena: *std.heap.ArenaAllocator,
    backing_gpa: std.mem.Allocator,
    allocator: std.mem.Allocator,
    Param: Table(FuncRows.Param) = .{},
    Block: Table(FuncRows.Block) = .{},
    Function: Table(FuncRows.Function) = .{},
    Global: Table(FuncRows.Global) = .{},
    func_pool: Pool(FuncId) = .{},
    block_pool: Pool(BlockId) = .{},
    param_pool: Pool(ParamId) = .{},
    global_pool: Pool(GlobalId) = .{},

    pub fn init(gpa: std.mem.Allocator) FuncStore {
        const arena = gpa.create(std.heap.ArenaAllocator) catch @panic("OOM");
        arena.* = std.heap.ArenaAllocator.init(gpa);
        return .{ .arena = arena, .backing_gpa = gpa, .allocator = arena.allocator() };
    }
    pub fn deinit(self: *@This()) void {
        self.arena.deinit();
        self.backing_gpa.destroy(self.arena);
    }
};

pub const TIR = struct {
    arena: *std.heap.ArenaAllocator,
    backing_gpa: std.mem.Allocator,
    allocator: std.mem.Allocator,
    type_store: *types.TypeStore,
    instrs: InstrStore,
    terms: TermStore,
    funcs: FuncStore,
    value_defs: std.ArrayListUnmanaged(InstrId) = .{},
    loc_store: ?*const dod.LocStore = null,

    pub fn init(gpa: std.mem.Allocator, store: *types.TypeStore) TIR {
        const arena = gpa.create(std.heap.ArenaAllocator) catch @panic("OOM");
        arena.* = std.heap.ArenaAllocator.init(gpa);
        const alloc = arena.allocator();
        return .{
            .arena = arena,
            .backing_gpa = gpa,
            .allocator = alloc,
            .type_store = store,
            .instrs = .init(alloc, store.strs),
            .terms = .init(alloc),
            .funcs = .init(alloc),
        };
    }
    pub fn deinit(self: *@This()) void {
        self.instrs.deinit();
        self.terms.deinit();
        self.funcs.deinit();
        self.arena.deinit();
        self.backing_gpa.destroy(self.arena);
    }
    pub fn kind(self: *TIR, id: anytype) if (@TypeOf(id) == TermId) TermKind else OpKind {
        if (@TypeOf(id) == InstrId) return self.instrs.index.kinds.items[id.toRaw()];
        return self.terms.index.kinds.items[id.toRaw()];
    }
};

pub const Builder = struct {
    allocator: std.mem.Allocator,
    t: *TIR,
    next_value: u32 = 0,

    pub fn init(gpa: std.mem.Allocator, t: *TIR) Builder {
        return .{ .allocator = gpa, .t = t };
    }
    pub fn freshValue(self: *Builder) ValueId {
        const id = ValueId.fromRaw(self.next_value);
        self.next_value += 1;
        return id;
    }

    pub const FunctionFrame = struct {
        builder: *Builder,
        id: FuncId,
        param_vals: std.ArrayListUnmanaged(ValueId) = .{},
        param_ids: std.ArrayListUnmanaged(ParamId) = .{},
        blocks: std.ArrayListUnmanaged(BlockId) = .{},
        pub fn deinit(self: *FunctionFrame, gpa: std.mem.Allocator) void {
            self.param_vals.deinit(gpa);
            self.param_ids.deinit(gpa);
            self.blocks.deinit(gpa);
        }
    };
    pub const BlockFrame = struct {
        builder: *Builder,
        id: BlockId,
        instrs: std.ArrayListUnmanaged(InstrId) = .{},
        params: std.ArrayListUnmanaged(ParamId) = .{},
        term: OptTermId = .none(),
        pub fn deinit(self: *BlockFrame, gpa: std.mem.Allocator) void {
            self.instrs.deinit(gpa);
            self.params.deinit(gpa);
        }
    };
    pub const SwitchDest = struct { dest: BlockId, args: []const ValueId };

    pub fn beginFunction(self: *Builder, context: *Context, name: StrId, result: types.TypeId, is_variadic: bool, is_extern: bool, attrs: RangeAttribute, is_triton_fn: bool, is_async: bool, raw_asm: dod.OptStrId) !FunctionFrame {
        const idx = self.t.funcs.Function.add(self.allocator, .{ .name = name, .params = .empty(), .result = result, .blocks = .empty(), .is_variadic = is_variadic, .is_extern = is_extern, .attrs = attrs, .is_triton_fn = is_triton_fn, .is_async = is_async, .raw_asm = raw_asm });
        try context.global_func_map.put(name, .{ idx, &self.t.funcs });
        return .{ .builder = self, .id = idx };
    }

    pub fn addParam(self: *Builder, f: *FunctionFrame, name: ?StrId, ty: types.TypeId) !ValueId {
        const vid = self.freshValue();
        const pid = self.t.funcs.Param.add(self.allocator, .{ .value = vid, .name = if (name) |n| .some(n) else .none(), .ty = ty });
        try f.param_ids.append(self.allocator, pid);
        try f.param_vals.append(self.allocator, vid);
        return vid;
    }

    pub fn beginBlock(self: *Builder, f: *FunctionFrame) !BlockFrame {
        const idx = self.t.funcs.Block.add(self.allocator, .{ .params = .empty(), .instrs = .empty(), .term = TermId.fromRaw(0) });
        try f.blocks.append(self.allocator, idx);
        return .{ .builder = self, .id = idx };
    }

    pub fn endBlock(self: *Builder, _: *FunctionFrame, blk: BlockFrame) !void {
        var row = self.t.funcs.Block.get(blk.id);
        row.instrs = self.t.instrs.instr_pool.pushMany(self.allocator, blk.instrs.items);
        row.params = self.t.funcs.param_pool.pushMany(self.allocator, blk.params.items);
        row.term = blk.term.unwrap();
        self.t.funcs.Block.list.set(blk.id.toRaw(), row);
    }

    pub fn endFunction(self: *Builder, f: FunctionFrame) !void {
        var row = self.t.funcs.Function.get(f.id);
        row.params = self.t.funcs.param_pool.pushMany(self.allocator, f.param_ids.items);
        row.blocks = self.t.funcs.block_pool.pushMany(self.allocator, f.blocks.items);
        self.t.funcs.Function.list.set(f.id.toRaw(), row);
        _ = self.t.funcs.func_pool.push(self.allocator, f.id);
    }

    // --- Instruction Helpers ---
    fn addInstr(self: *Builder, blk: *BlockFrame, comptime k: OpKind, row: RowT(k)) ValueId {
        const vid = row.result;
        const iid = self.t.instrs.add(k, row);
        const cap = vid.toRaw() + 1;
        if (self.t.value_defs.capacity < cap) self.t.value_defs.ensureTotalCapacity(self.allocator, cap) catch @panic("OOM");
        if (self.t.value_defs.items.len < cap) self.t.value_defs.appendNTimes(self.allocator, InstrId.fromRaw(std.math.maxInt(u32)), cap - self.t.value_defs.items.len) catch @panic("OOM");
        self.t.value_defs.items[vid.toRaw()] = iid;
        blk.instrs.append(self.allocator, iid) catch @panic("OOM");
        return vid;
    }

    pub fn tirValue(self: *Builder, comptime kind: OpKind, blk: *BlockFrame, ty: types.TypeId, loc: OptLocId, value: anytype) ValueId {
        const vid = self.freshValue();
        var v: RowT(kind) = undefined;
        v.result = vid;
        v.ty = ty;
        v.loc = loc;
        inline for (@typeInfo(@TypeOf(value)).@"struct".fields) |f| @field(v, f.name) = @field(value, f.name);
        return self.addInstr(blk, kind, v);
    }

    pub fn bin(self: *Builder, blk: *BlockFrame, comptime k: OpKind, ty: types.TypeId, l: ValueId, r: ValueId, loc: OptLocId) ValueId {
        return self.addInstr(blk, k, .{ .result = self.freshValue(), .ty = ty, .lhs = l, .rhs = r, .loc = loc });
    }
    pub fn un1(self: *Builder, blk: *BlockFrame, comptime k: OpKind, ty: types.TypeId, v: ValueId, loc: OptLocId) ValueId {
        return self.addInstr(blk, k, .{ .result = self.freshValue(), .ty = ty, .value = v, .loc = loc });
    }

    pub fn call(self: *Builder, blk: *BlockFrame, ty: types.TypeId, callee: StrId, args: []const ValueId, loc: OptLocId) ValueId {
        const r = self.t.instrs.val_list_pool.pushMany(self.allocator, args);
        return self.addInstr(blk, .Call, .{ .result = self.freshValue(), .ty = ty, .callee = callee, .args = r, .loc = loc });
    }
    pub fn indirectCall(self: *Builder, blk: *BlockFrame, ty: types.TypeId, callee: ValueId, args: []const ValueId, loc: OptLocId) ValueId {
        const r = self.t.instrs.val_list_pool.pushMany(self.allocator, args);
        return self.addInstr(blk, .IndirectCall, .{ .result = self.freshValue(), .ty = ty, .callee = callee, .args = r, .loc = loc });
    }

    pub fn addGlobal(self: *Builder, name: StrId, ty: types.TypeId) GlobalId {
        return self.addGlobalWithInit(name, ty, .none);
    }
    pub fn addGlobalWithInit(self: *Builder, name: StrId, ty: types.TypeId, initial: ConstInit) GlobalId {
        const idx = self.t.funcs.Global.add(self.allocator, .{ .name = name, .ty = ty, .init = initial });
        _ = self.t.funcs.global_pool.push(self.allocator, idx);
        return idx;
    }
    pub fn edge(self: *Builder, dest: BlockId, args: []const ValueId, loc: OptLocId) EdgeId {
        const r = self.t.instrs.value_pool.pushMany(self.allocator, args);
        return self.t.terms.Edge.add(self.allocator, .{ .dest = dest, .args = r, .loc = loc });
    }
    pub fn br(self: *Builder, blk: *BlockFrame, dest: BlockId, args: []const ValueId, loc: OptLocId) !void {
        blk.term = .some(self.t.terms.add(.Br, .{ .edge = self.edge(dest, args, loc), .loc = loc }));
    }
    pub fn condBr(self: *Builder, blk: *BlockFrame, cond: ValueId, t_dest: BlockId, t_args: []const ValueId, e_dest: BlockId, e_args: []const ValueId, loc: OptLocId) !void {
        blk.term = .some(self.t.terms.add(.CondBr, .{ .cond = cond, .then_edge = self.edge(t_dest, t_args, loc), .else_edge = self.edge(e_dest, e_args, loc), .loc = loc }));
    }
    pub fn setReturn(self: *Builder, blk: *BlockFrame, value: OptValueId, loc: OptLocId) !void {
        blk.term = .some(self.t.terms.add(.Return, .{ .value = value, .loc = loc }));
    }
    pub fn switchInt(self: *Builder, blk: *BlockFrame, scrut: ValueId, vals: []const u64, dests: []const SwitchDest, def_dest: BlockId, def_args: []const ValueId, loc: OptLocId) !void {
        var c_ids = self.allocator.alloc(CaseId, vals.len) catch @panic("OOM");
        for (vals, 0..) |v, i| c_ids[i] = self.t.terms.Case.add(self.allocator, .{ .value = v, .edge = self.edge(dests[i].dest, dests[i].args, loc), .loc = loc });
        blk.term = .some(self.t.terms.add(.SwitchInt, .{ .scrut = scrut, .cases = self.t.terms.case_pool.pushMany(self.allocator, c_ids), .default_edge = self.edge(def_dest, def_args, loc), .loc = loc }));
    }
    pub fn setUnreachable(self: *Builder, blk: *BlockFrame, loc: OptLocId) !void {
        blk.term = .some(self.t.terms.add(.Unreachable, .{ .loc = loc }));
    }

    pub fn intern(self: *Builder, s: []const u8) StrId {
        return self.t.instrs.strs.intern(s);
    }
    pub fn addBlockParam(self: *Builder, blk: *BlockFrame, name: ?[]const u8, ty: types.TypeId) !ValueId {
        const vid = self.freshValue();
        const pid = self.t.funcs.Param.add(self.allocator, .{ .value = vid, .name = if (name) |n| .some(self.intern(n)) else .none(), .ty = ty });
        try blk.params.append(self.allocator, pid);
        return vid;
    }
    pub fn indexOp(self: *Builder, blk: *BlockFrame, ty: types.TypeId, base: ValueId, idx: ValueId, loc: OptLocId) ValueId {
        return self.addInstr(blk, .Index, .{ .result = self.freshValue(), .ty = ty, .base = base, .index = idx, .loc = loc });
    }
    pub fn gepConst(self: *Builder, v: u64) GepIndexId {
        return self.t.instrs.GepIndex.add(self.allocator, .{ .Const = v });
    }
    pub fn gepValue(self: *Builder, val: ValueId) GepIndexId {
        return self.t.instrs.GepIndex.add(self.allocator, .{ .Value = val });
    }
    pub fn gep(self: *Builder, blk: *BlockFrame, ty: types.TypeId, base: ValueId, idxs: []const GepIndexId, loc: OptLocId) ValueId {
        return self.addInstr(blk, .Gep, .{ .result = self.freshValue(), .ty = ty, .base = base, .indices = self.t.instrs.gep_pool.pushMany(self.allocator, idxs), .loc = loc });
    }
    pub fn structMake(self: *Builder, blk: *BlockFrame, ty: types.TypeId, fields: []const Rows.StructFieldInit, loc: OptLocId) ValueId {
        var ids = self.allocator.alloc(StructFieldInitId, fields.len) catch @panic("OOM");
        for (fields, 0..) |f, i| ids[i] = self.t.instrs.StructFieldInit.add(self.allocator, f);
        return self.addInstr(blk, .StructMake, .{ .result = self.freshValue(), .ty = ty, .fields = self.t.instrs.sfi_pool.pushMany(self.allocator, ids), .loc = loc });
    }
    pub fn tupleMake(self: *Builder, blk: *BlockFrame, ty: types.TypeId, elems: []const ValueId, loc: OptLocId) ValueId {
        return self.addInstr(blk, .TupleMake, .{ .result = self.freshValue(), .ty = ty, .elems = self.t.instrs.value_pool.pushMany(self.allocator, elems), .loc = loc });
    }
    pub fn arrayMake(self: *Builder, blk: *BlockFrame, ty: types.TypeId, elems: []const ValueId, loc: OptLocId) ValueId {
        return self.addInstr(blk, .ArrayMake, .{ .result = self.freshValue(), .ty = ty, .elems = self.t.instrs.value_pool.pushMany(self.allocator, elems), .loc = loc });
    }
    pub fn addMlirBlock(self: *Builder, blk: *BlockFrame, res: ValueId, ty: types.TypeId, kind: ast.MlirKind, expr: ast.ExprId, text: StrId, pieces: []const MlirPieceId, args: []const ValueId, loc: OptLocId) InstrId {
        const row: Rows.MlirBlock = .{ .result = .some(res), .ty = ty, .kind = kind, .expr = expr, .text = text, .pieces = self.t.instrs.mlir_piece_pool.pushMany(self.allocator, pieces), .args = self.t.instrs.value_pool.pushMany(self.allocator, args), .loc = loc };
        const id = self.t.instrs.add(.MlirBlock, row);
        blk.instrs.append(self.allocator, id) catch @panic("OOM");
        return id;
    }
    // Helpers for specific consts not covered by generic builders
    pub fn constNull(self: *Builder, blk: *BlockFrame, ty: types.TypeId, loc: OptLocId) ValueId {
        return self.addInstr(blk, .ConstNull, .{ .result = self.freshValue(), .ty = ty, .loc = loc });
    }
    pub fn rangeMake(self: *Builder, blk: *BlockFrame, ty: types.TypeId, start: ValueId, end: ValueId, inclusive: ValueId, loc: OptLocId) ValueId {
        return self.addInstr(blk, .RangeMake, .{ .result = self.freshValue(), .ty = ty, .start = start, .end = end, .inclusive = inclusive, .loc = loc });
    }
    pub fn binBool(self: *Builder, blk: *BlockFrame, comptime k: OpKind, l: ValueId, r: ValueId, loc: OptLocId) ValueId {
        return self.addInstr(blk, k, .{ .result = self.freshValue(), .ty = self.t.type_store.tBool(), .lhs = l, .rhs = r, .loc = loc });
    }
    pub fn setReturnVal(self: *Builder, blk: *BlockFrame, v: ValueId, loc: OptLocId) !void {
        return self.setReturn(blk, .some(v), loc);
    }
    pub fn setReturnVoid(self: *Builder, blk: *BlockFrame, loc: OptLocId) !void {
        return self.setReturn(blk, .none(), loc);
    }
    pub fn insertElem(self: *Builder, blk: *BlockFrame, ty: types.TypeId, agg: ValueId, idx: u32, val: ValueId, loc: OptLocId) ValueId {
        return self.addInstr(blk, .InsertElem, .{ .result = self.freshValue(), .ty = ty, .agg = agg, .index = idx, .value = val, .loc = loc });
    }
    pub fn extractElem(self: *Builder, blk: *BlockFrame, ty: types.TypeId, agg: ValueId, idx: u32, loc: OptLocId) ValueId {
        return self.addInstr(blk, .ExtractElem, .{ .result = self.freshValue(), .ty = ty, .agg = agg, .index = idx, .loc = loc });
    }
    pub fn extractField(self: *Builder, blk: *BlockFrame, ty: types.TypeId, agg: ValueId, idx: u32, loc: OptLocId) ValueId {
        return self.addInstr(blk, .ExtractField, .{ .result = self.freshValue(), .ty = ty, .agg = agg, .index = idx, .name = .none(), .loc = loc });
    }
    pub fn extractFieldNamed(self: *Builder, blk: *BlockFrame, ty: types.TypeId, agg: ValueId, name: StrId, loc: OptLocId) ValueId {
        return self.addInstr(blk, .ExtractField, .{ .result = self.freshValue(), .ty = ty, .agg = agg, .index = 0, .name = .some(name), .loc = loc });
    }
};

pub const TirPrinter = struct {
    writer: *std.io.Writer,
    indent: usize = 0,
    tir: *TIR,

    pub fn init(writer: anytype, tir: *TIR) TirPrinter {
        return .{ .writer = writer, .tir = tir };
    }

    inline fn s(self: *const TirPrinter, id: StrId) []const u8 {
        return self.tir.instrs.strs.get(id);
    }
    fn ws(self: *TirPrinter) !void {
        var i: usize = 0;
        while (i < self.indent) : (i += 1) try self.writer.writeByte(' ');
    }
    fn open(self: *TirPrinter, comptime fmt: []const u8, args: anytype) !void {
        try self.ws();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
        self.indent += 2;
    }
    fn close(self: *TirPrinter) !void {
        self.indent -= 2;
        try self.ws();
        try self.writer.writeAll(")\n");
    }

    pub fn print(self: *TirPrinter) !void {
        try self.open("(tir", .{});
        if (self.tir.funcs.global_pool.inner.data.items.len > 0) {
            try self.open("(globals", .{});
            for (self.tir.funcs.global_pool.inner.data.items) |gid_raw| {
                const gid = GlobalId.fromRaw(gid_raw);
                const g = self.tir.funcs.Global.get(gid);
                try self.ws();
                try self.writer.print("g{}: (global name=\"{s}\" type={})", .{ gid.toRaw(), self.s(g.name), g.ty });
                try self.writer.writeAll("\n");
            }
            try self.close();
        }
        for (self.tir.funcs.func_pool.inner.data.items) |fid_raw| {
            try self.printFunc(FuncId.fromRaw(fid_raw));
        }
        try self.close();
        try self.writer.flush();
    }

    fn printFunc(self: *TirPrinter, fid: FuncId) !void {
        const f = self.tir.funcs.Function.get(fid);
        try self.open("(function {s} result={}", .{ self.s(f.name), f.result });
        const params = self.tir.funcs.param_pool.slice(f.params);
        if (params.len > 0) {
            try self.open("(params", .{});
            for (params) |pid| {
                const p = self.tir.funcs.Param.get(pid);
                try self.ws();
                try self.writer.print("v{}: {} /* {s} */\n", .{ p.value.toRaw(), p.ty, if (p.name.isNone()) "" else self.s(p.name.unwrap()) });
            }
            try self.close();
        }
        for (self.tir.funcs.block_pool.slice(f.blocks)) |bid| try self.printBlock(bid);
        try self.close();
    }

    fn printBlock(self: *TirPrinter, bid: BlockId) !void {
        const b = self.tir.funcs.Block.get(bid);
        try self.open("(block block_{}", .{bid.toRaw()});
        const params = self.tir.funcs.param_pool.slice(b.params);
        if (params.len > 0) {
            try self.open("(params", .{});
            for (params) |pid| {
                const p = self.tir.funcs.Param.get(pid);
                try self.ws();
                try self.writer.print("v{}: {}\n", .{ p.value.toRaw(), p.ty });
            }
            try self.close();
        }
        for (self.tir.instrs.instr_pool.slice(b.instrs)) |iid| try self.printInstr(iid);
        try self.open("(terminator", .{});
        const tid = b.term;
        switch (self.tir.terms.index.kinds.items[tid.toRaw()]) {
            .Return => {
                const r = self.tir.terms.get(.Return, tid);
                try self.ws();
                try self.writer.print("(return {s})\n", .{if (r.value.isNone()) "void" else ""});
            },
            .Br => {
                const r = self.tir.terms.get(.Br, tid);
                try self.ws();
                try self.writer.print("(br block_{})\n", .{self.tir.terms.Edge.get(r.edge).dest.toRaw()});
            },
            else => try self.ws(),
        }
        try self.close();
        try self.close();
    }

    fn printInstr(self: *TirPrinter, iid: InstrId) !void {
        @setEvalBranchQuota(10000);
        const k = self.tir.instrs.index.kinds.items[iid.toRaw()];
        switch (k) {
            inline else => |tag| {
                const r = self.tir.instrs.get(tag, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.writer.print("i{}", .{iid.toRaw()});
                if (@hasField(@TypeOf(r), "result")) {
                    if (@TypeOf(r.result) == ValueId) try self.writer.print(" v{} = {s}", .{ r.result.toRaw(), @tagName(tag) }) else if (!r.result.isNone()) try self.writer.print(" v{} = {s}", .{ r.result.unwrap().toRaw(), @tagName(tag) });
                } else {
                    try self.writer.print(" {s}", .{@tagName(tag)});
                }
                inline for (@typeInfo(@TypeOf(r)).@"struct".fields) |f| {
                    if (comptime std.mem.eql(u8, f.name, "result") or std.mem.eql(u8, f.name, "loc")) continue;
                    try self.writer.print(" {s}=", .{f.name});
                    if (f.type == ValueId) {
                        try self.writer.print("v{}", .{@field(r, f.name).toRaw()});
                    } else if (f.type == OptValueId) {
                        if (@field(r, f.name).isNone()) try self.writer.writeAll("null") else try self.writer.print("v{}", .{@field(r, f.name).unwrap().toRaw()});
                    } else if (f.type == StrId) {
                        try self.writer.print("\"{s}\"", .{self.s(@field(r, f.name))});
                    } else {
                        try self.writer.writeAll("...");
                    }
                }
                try self.writer.writeAll(")\n");
            },
        }
    }
};
