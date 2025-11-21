const std = @import("std");
const dod = @import("cst.zig");
const ast = @import("ast.zig");
const types = @import("types.zig");
const comp = @import("comptime.zig");

pub const OptLocId = dod.OptLocId;

// Typed IR (TIR)
// Columnar stores with typed indices and contiguous pools.

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

pub const Pool = dod.Pool;
pub const Table = dod.Table;
pub const StoreIndex = dod.StoreIndex;
pub const StringInterner = dod.StringInterner;
pub const StrId = dod.StrId;

// ---------------- Ops and Terms ----------------
pub const OpKind = enum(u16) {
    // Constants
    ConstInt,
    ConstFloat,
    ConstBool,
    ConstString,
    ConstNull,
    ConstUndef,
    // Arithmetic/Bitwise/Logic
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
    // Comparisons (bool result)
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
    Alloca,
    Load,
    Store,
    Gep,
    GlobalAddr,
    // Aggregates
    TupleMake,
    ArrayMake,
    StructMake,
    ExtractElem,
    InsertElem,
    ExtractField,
    InsertField,
    // Indexing/Pointers
    Index,
    AddressOf,
    // Control/Data
    Select,
    // Calls
    Call,
    IndirectCall,
    MlirBlock,
    // Variants
    VariantMake,
    VariantTag,
    VariantPayloadPtr,
    UnionMake,
    UnionField,
    UnionFieldPtr,
    // Complex numbers
    ComplexMake,
    RangeMake,
    Broadcast,
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
    // All rows that produce a value carry (result, ty)
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
    pub const Gep = struct {
        result: ValueId,
        ty: types.TypeId,
        base: ValueId, // pointer
        indices: RangeGepIndex,
        loc: OptLocId,
    };

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

    pub const Call = struct { result: ValueId, ty: types.TypeId, callee: StrId, args: RangeValue, loc: OptLocId };
    pub const IndirectCall = struct { result: ValueId, ty: types.TypeId, callee: ValueId, args: RangeValue, loc: OptLocId };
    pub const MlirPiece = struct { kind: ast.MlirPieceKind, text: StrId, value: comp.ComptimeValue };
    pub const MlirBlock = struct {
        result: OptValueId,
        ty: types.TypeId,
        kind: ast.MlirKind,
        expr: ast.ExprId,
        text: StrId,
        pieces: RangeMlirPiece,
        args: RangeValue,
        loc: OptLocId,
    };
    pub const VariantMake = struct { result: ValueId, ty: types.TypeId, tag: u32, payload: OptValueId, payload_ty: types.TypeId, loc: OptLocId };
    pub const VariantTag = struct { result: ValueId, ty: types.TypeId, value: ValueId, loc: OptLocId };
    pub const VariantPayloadPtr = struct { result: ValueId, ty: types.TypeId, value: ValueId, loc: OptLocId };
    pub const UnionMake = struct { result: ValueId, ty: types.TypeId, field_index: u32, value: ValueId, loc: OptLocId };
    pub const UnionField = struct { result: ValueId, ty: types.TypeId, base: ValueId, field_index: u32, loc: OptLocId };
    pub const UnionFieldPtr = struct { result: ValueId, ty: types.TypeId, base: ValueId, field_index: u32, loc: OptLocId };
    pub const ComplexMake = struct { result: ValueId, ty: types.TypeId, re: ValueId, im: ValueId, loc: OptLocId };
    pub const RangeMake = struct { result: ValueId, ty: types.TypeId, start: ValueId, end: ValueId, inclusive: ValueId, loc: OptLocId };
    pub const Broadcast = struct { result: ValueId, ty: types.TypeId, value: ValueId, loc: OptLocId };

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

pub const RangeGepIndex = dod.RangeOf(GepIndexId);
pub const RangeStructFieldInit = dod.RangeOf(StructFieldInitId);

pub inline fn RowT(comptime K: OpKind) type {
    return switch (K) {
        .ConstInt => Rows.ConstInt,
        .ConstFloat => Rows.ConstFloat,
        .ConstBool => Rows.ConstBool,
        .ConstString => Rows.ConstString,
        .ConstNull => Rows.ConstNull,
        .ConstUndef => Rows.ConstUndef,

        .Add, .Sub, .Mul, .BinWrapAdd, .BinWrapSub, .BinWrapMul, .BinSatAdd, .BinSatSub, .BinSatMul, .BinSatShl, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .LogicalAnd, .LogicalOr, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe => Rows.Bin2,

        .LogicalNot => Rows.Un1,

        .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => Rows.Un1,

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
    };
}
inline fn TermRowT(comptime K: TermKind) type {
    return @field(Rows, @tagName(K));
}

// ---------------- Stores ----------------
pub const InstrStore = struct {
    gpa: std.mem.Allocator,
    index: StoreIndex(OpKind) = .{},

    // op tables
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

    // aux tables
    GepIndex: Table(Rows.GepIndex) = .{},
    StructFieldInit: Table(Rows.StructFieldInit) = .{},
    Attribute: Table(Rows.Attribute) = .{},

    // pools
    instr_pool: Pool(InstrId) = .{},
    value_pool: Pool(ValueId) = .{},
    gep_pool: Pool(GepIndexId) = .{},
    sfi_pool: Pool(StructFieldInitId) = .{},
    attribute_pool: Pool(AttributeId) = .{},
    val_list_pool: Pool(ValueId) = .{},
    mlir_piece_pool: Pool(MlirPieceId) = .{},

    strs: *StringInterner,

    pub fn init(gpa: std.mem.Allocator, interner: *StringInterner) InstrStore {
        return .{ .gpa = gpa, .strs = interner };
    }
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;
        self.index.deinit(gpa);
        inline for (@typeInfo(OpKind).@"enum".fields) |f| {
            @field(self, f.name).deinit(gpa);
        }
        self.GepIndex.deinit(gpa);
        self.StructFieldInit.deinit(gpa);
        self.Attribute.deinit(gpa);
        if (self.MlirPiece.list.len != 0) {
            const values = self.MlirPiece.col("value");
            for (values) |*val| val.destroy(gpa);
        }
        self.MlirPiece.deinit(gpa);
        self.instr_pool.deinit(gpa);
        self.value_pool.deinit(gpa);
        self.gep_pool.deinit(gpa);
        self.sfi_pool.deinit(gpa);
        self.attribute_pool.deinit(gpa);
        self.val_list_pool.deinit(gpa);
        self.mlir_piece_pool.deinit(gpa);
    }

    pub fn add(self: *@This(), comptime K: OpKind, row: RowT(K)) InstrId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), InstrId);
    }

    pub fn get(self: *@This(), comptime K: OpKind, id: InstrId) RowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
    }

    pub fn addMlirPieceRow(self: *@This(), row: Rows.MlirPiece) MlirPieceId {
        return self.MlirPiece.add(self.gpa, row);
    }
};

pub const TermStore = struct {
    gpa: std.mem.Allocator,
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
        return .{ .gpa = gpa };
    }
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;
        self.index.deinit(gpa);
        inline for (@typeInfo(TermKind).@"enum".fields) |f| @field(self, f.name).deinit(gpa);
        self.Edge.deinit(gpa);
        self.Case.deinit(gpa);
        self.term_pool.deinit(gpa);
        self.edge_pool.deinit(gpa);
        self.case_pool.deinit(gpa);
    }

    pub fn add(self: *@This(), comptime K: TermKind, row: TermRowT(K)) TermId {
        const tbl: *Table(TermRowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), TermId);
    }
    pub fn get(self: *@This(), comptime K: TermKind, id: TermId) TermRowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *Table(TermRowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
    }
};

pub const FuncRows = struct {
    pub const Param = struct { value: ValueId, name: dod.OptStrId, ty: types.TypeId };
    pub const Block = struct { params: RangeParam, instrs: RangeInstr, term: TermId };
    pub const Function = struct {
        name: StrId,
        params: RangeParam,
        result: types.TypeId,
        blocks: RangeBlock,
        is_variadic: bool,
        attrs: RangeAttribute,
    };
    pub const Global = struct { name: StrId, ty: types.TypeId, init: ConstInit };
};

pub const FuncStore = struct {
    gpa: std.mem.Allocator,

    Param: Table(FuncRows.Param) = .{},
    Block: Table(FuncRows.Block) = .{},
    Function: Table(FuncRows.Function) = .{},
    Global: Table(FuncRows.Global) = .{},

    func_pool: Pool(FuncId) = .{},
    block_pool: Pool(BlockId) = .{},
    param_pool: Pool(ParamId) = .{},
    global_pool: Pool(GlobalId) = .{},

    pub fn init(gpa: std.mem.Allocator) FuncStore {
        return .{ .gpa = gpa };
    }
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;
        self.Param.deinit(gpa);
        self.Block.deinit(gpa);
        self.Function.deinit(gpa);
        self.Global.deinit(gpa);
        self.func_pool.deinit(gpa);
        self.block_pool.deinit(gpa);
        self.param_pool.deinit(gpa);
        self.global_pool.deinit(gpa);
    }
};

pub const TIR = struct {
    gpa: std.mem.Allocator,
    type_store: *types.TypeStore,
    instrs: InstrStore,
    terms: TermStore,
    funcs: FuncStore,
    loc_store: ?*const dod.LocStore = null,

    pub fn init(gpa: std.mem.Allocator, store: *types.TypeStore) TIR {
        return .{
            .gpa = gpa,
            .type_store = store,
            .instrs = InstrStore.init(gpa, store.strs),
            .terms = TermStore.init(gpa),
            .funcs = FuncStore.init(gpa),
            .loc_store = null,
        };
    }
    pub fn deinit(self: *@This()) void {
        self.instrs.deinit();
        self.terms.deinit();
        self.funcs.deinit();
    }
};

// ============================
// Builder facade over TIR
// ============================

pub const Builder = struct {
    gpa: std.mem.Allocator,
    t: *TIR,
    next_value: u32 = 0,

    pub fn init(gpa: std.mem.Allocator, t: *TIR) Builder {
        return .{ .gpa = gpa, .t = t };
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

    pub fn beginFunction(
        self: *Builder,
        name: StrId,
        result: types.TypeId,
        is_variadic: bool,
        attrs: RangeAttribute,
    ) !FunctionFrame {
        const idx = self.t.funcs.Function.add(self.gpa, .{
            .name = name,
            .params = RangeParam.empty(),
            .result = result,
            .blocks = RangeBlock.empty(),
            .is_variadic = is_variadic,
            .attrs = attrs,
        });
        return .{ .builder = self, .id = idx };
    }

    pub fn addParam(self: *Builder, f: *FunctionFrame, name: ?StrId, ty: types.TypeId) !ValueId {
        const vid = self.freshValue();
        const pid_u32 = self.t.funcs.Param.add(self.gpa, .{ .value = vid, .name = if (name) |n| .some(n) else .none(), .ty = ty });
        try f.param_ids.append(self.gpa, pid_u32);
        try f.param_vals.append(self.gpa, vid);
        return vid;
    }

    pub fn beginBlock(self: *Builder, f: *FunctionFrame) !BlockFrame {
        const idx = self.t.funcs.Block.add(self.gpa, .{ .params = .empty(), .instrs = .empty(), .term = TermId.fromRaw(0) });
        try f.blocks.append(self.gpa, idx);
        return .{ .builder = self, .id = idx };
    }

    pub fn endBlock(self: *Builder, f: *FunctionFrame, blk: BlockFrame) !void {
        const instr_range = self.t.instrs.instr_pool.pushMany(self.gpa, blk.instrs.items);
        const param_range = self.t.funcs.param_pool.pushMany(self.gpa, blk.params.items);
        var row = self.t.funcs.Block.get(blk.id);
        row.instrs = instr_range;
        row.params = param_range;
        row.term = blk.term.unwrap();
        self.t.funcs.Block.list.set(blk.id.toRaw(), row);

        _ = f;
    }

    pub fn endFunction(self: *Builder, f: FunctionFrame) !void {
        const prange = self.t.funcs.param_pool.pushMany(self.gpa, f.param_ids.items);
        const brange = self.t.funcs.block_pool.pushMany(self.gpa, f.blocks.items);
        var row = self.t.funcs.Function.get(f.id);
        row.params = prange;
        row.blocks = brange;
        self.t.funcs.Function.list.set(f.id.toRaw(), row);

        _ = self.t.funcs.func_pool.push(self.gpa, f.id);
    }

    // ---- instruction helpers ----
    pub fn tirValue(
        self: *Builder,
        comptime kind: OpKind,
        blk: *BlockFrame,
        ty: types.TypeId,
        loc: OptLocId,
        value: anytype,
    ) ValueId {
        const vid = self.freshValue();
        var v: RowT(kind) = undefined;
        v.result = vid;
        v.ty = ty;
        inline for (@typeInfo(@TypeOf(value)).@"struct".fields) |f| {
            @field(v, f.name) = @field(value, f.name);
        }
        v.loc = loc;
        const instr_id = self.t.instrs.add(kind, v);
        blk.instrs.append(self.gpa, instr_id) catch @panic("OOM");
        return vid;
    }
    pub fn bin(
        self: *Builder,
        blk: *BlockFrame,
        comptime k: OpKind,
        ty: types.TypeId,
        l: ValueId,
        r: ValueId,
        loc: OptLocId,
    ) ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(k, Rows.Bin2{ .result = vid, .ty = ty, .lhs = l, .rhs = r, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn binBool(
        self: *Builder,
        blk: *BlockFrame,
        comptime k: OpKind,
        l: ValueId,
        r: ValueId,
        loc: OptLocId,
    ) ValueId {
        const bty = self.t.type_store.tBool();
        const vid = self.freshValue();
        const iid = self.t.instrs.add(k, Rows.Bin2{ .result = vid, .ty = bty, .lhs = l, .rhs = r, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn call(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        callee: StrId,
        args: []const ValueId,
        loc: OptLocId,
    ) ValueId {
        const r = self.t.instrs.val_list_pool.pushMany(self.gpa, args);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.Call, Rows.Call{ .result = vid, .ty = ty, .callee = callee, .args = r, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn indirectCall(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        callee: ValueId,
        args: []const ValueId,
        loc: OptLocId,
    ) ValueId {
        const r = self.t.instrs.val_list_pool.pushMany(self.gpa, args);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.IndirectCall, Rows.IndirectCall{ .result = vid, .ty = ty, .callee = callee, .args = r, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn indexOp(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        base: ValueId,
        idx: ValueId,
        loc: OptLocId,
    ) ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.Index, Rows.Index{ .result = vid, .ty = ty, .base = base, .index = idx, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn rangeMake(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        start: ValueId,
        end: ValueId,
        inclusive: ValueId,
        loc: OptLocId,
    ) ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(
            .RangeMake,
            Rows.RangeMake{ .result = vid, .ty = ty, .start = start, .end = end, .inclusive = inclusive, .loc = loc },
        );
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn intern(self: *Builder, s: []const u8) StrId {
        return self.t.instrs.strs.intern(s);
    }
    pub fn un1(
        self: *Builder,
        blk: *BlockFrame,
        comptime k: OpKind,
        ty: types.TypeId,
        v: ValueId,
        loc: OptLocId,
    ) ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(k, Rows.Un1{ .result = vid, .ty = ty, .value = v, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn constNull(self: *Builder, blk: *BlockFrame, ty: types.TypeId, loc: OptLocId) ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ConstNull, Rows.ConstNull{ .result = vid, .ty = ty, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn tupleMake(self: *Builder, blk: *BlockFrame, ty: types.TypeId, elems: []const ValueId, loc: OptLocId) ValueId {
        const r = self.t.instrs.value_pool.pushMany(self.gpa, elems);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.TupleMake, Rows.TupleMake{ .result = vid, .ty = ty, .elems = r, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn arrayMake(self: *Builder, blk: *BlockFrame, ty: types.TypeId, elems: []const ValueId, loc: OptLocId) ValueId {
        const r = self.t.instrs.value_pool.pushMany(self.gpa, elems);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ArrayMake, Rows.ArrayMake{ .result = vid, .ty = ty, .elems = r, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn structMake(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        fields: []const Rows.StructFieldInit,
        loc: OptLocId,
    ) ValueId {
        var ids = self.gpa.alloc(StructFieldInitId, fields.len) catch @panic("OOM");
        defer self.gpa.free(ids);
        var i: usize = 0;
        while (i < fields.len) : (i += 1) {
            ids[i] = self.t.instrs.StructFieldInit.add(self.gpa, fields[i]);
        }
        const r = self.t.instrs.sfi_pool.pushMany(self.gpa, ids);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.StructMake, Rows.StructMake{ .result = vid, .ty = ty, .fields = r, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn extractElem(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        agg: ValueId,
        index: u32,
        loc: OptLocId,
    ) ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.ExtractElem, Rows.ExtractElem{ .result = vid, .ty = ty, .agg = agg, .index = index, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn insertElem(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        agg: ValueId,
        index: u32,
        value: ValueId,
        loc: OptLocId,
    ) ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(
            .InsertElem,
            Rows.InsertElem{ .result = vid, .ty = ty, .agg = agg, .index = index, .value = value, .loc = loc },
        );
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn extractField(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        agg: ValueId,
        index: u32,
        loc: OptLocId,
    ) ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(
            .ExtractField,
            Rows.ExtractField{ .result = vid, .ty = ty, .agg = agg, .index = index, .name = .none(), .loc = loc },
        );
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn extractFieldNamed(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        agg: ValueId,
        name: StrId,
        loc: OptLocId,
    ) ValueId {
        const vid = self.freshValue();
        const iid = self.t.instrs.add(
            .ExtractField,
            Rows.ExtractField{
                .result = vid,
                .ty = ty,
                .agg = agg,
                .index = 0, // ignored when name is provided
                .name = .some(name),
                .loc = loc,
            },
        );
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
    pub fn addBlockParam(self: *Builder, blk: *BlockFrame, name: ?[]const u8, ty: types.TypeId) !ValueId {
        const vid = self.freshValue();
        const sid: ast.OptStrId = if (name) |n| .some(self.intern(n)) else .none();
        const pid = self.t.funcs.Param.add(self.gpa, .{ .value = vid, .name = sid, .ty = ty });
        try blk.params.append(self.gpa, pid);
        return vid;
    }
    pub fn addGlobal(self: *Builder, name: StrId, ty: types.TypeId) GlobalId {
        return self.addGlobalWithInit(name, ty, .none);
    }

    pub fn addGlobalWithInit(self: *Builder, name: StrId, ty: types.TypeId, initial: ConstInit) GlobalId {
        const idx = self.t.funcs.Global.add(self.gpa, .{ .name = name, .ty = ty, .init = initial });
        _ = self.t.funcs.global_pool.push(self.gpa, idx);
        return idx;
    }
    pub fn edge(self: *Builder, dest: BlockId, args: []const ValueId, loc: OptLocId) EdgeId {
        const r = self.t.instrs.value_pool.pushMany(self.gpa, args);
        return self.t.terms.Edge.add(self.gpa, .{ .dest = dest, .args = r, .loc = loc });
    }
    pub fn br(self: *Builder, blk: *BlockFrame, dest: BlockId, args: []const ValueId, loc: OptLocId) !void {
        const e = self.edge(dest, args, loc);
        const tid = self.t.terms.add(.Br, .{ .edge = e, .loc = loc });
        blk.term = .some(tid);
    }
    pub fn condBr(
        self: *Builder,
        blk: *BlockFrame,
        cond: ValueId,
        then_dest: BlockId,
        then_args: []const ValueId,
        else_dest: BlockId,
        else_args: []const ValueId,
        loc: OptLocId,
    ) !void {
        const te = self.edge(then_dest, then_args, loc);
        const ee = self.edge(else_dest, else_args, loc);
        const tid = self.t.terms.add(.CondBr, .{ .cond = cond, .then_edge = te, .else_edge = ee, .loc = loc });
        blk.term = OptTermId.some(tid);
    }
    pub fn setReturn(self: *Builder, blk: *BlockFrame, value: OptValueId, loc: OptLocId) !void {
        const tid = self.t.terms.add(.Return, .{ .value = value, .loc = loc });
        blk.term = OptTermId.some(tid);
    }
    pub fn setReturnVal(self: *Builder, blk: *BlockFrame, v: ValueId, loc: OptLocId) !void {
        return self.setReturn(blk, OptValueId.some(v), loc);
    }
    pub fn setReturnVoid(self: *Builder, blk: *BlockFrame, loc: OptLocId) !void {
        return self.setReturn(blk, OptValueId.none(), loc);
    }
    pub fn setUnreachable(self: *Builder, blk: *BlockFrame, loc: OptLocId) !void {
        const tid = self.t.terms.add(.Unreachable, .{ .loc = loc });
        blk.term = OptTermId.some(tid);
    }

    pub fn switchInt(
        self: *Builder,
        blk: *BlockFrame,
        scrut: ValueId,
        case_vals: []const u64,
        case_dests: []const SwitchDest,
        default_dest: BlockId,
        default_args: []const ValueId,
        loc: OptLocId,
    ) !void {
        std.debug.assert(case_vals.len == case_dests.len);
        var case_ids = self.gpa.alloc(CaseId, case_vals.len) catch @panic("OOM");
        defer self.gpa.free(case_ids);
        var i: usize = 0;
        while (i < case_vals.len) : (i += 1) {
            const e = self.edge(case_dests[i].dest, case_dests[i].args, loc);
            case_ids[i] = self.t.terms.Case.add(self.gpa, .{ .value = case_vals[i], .edge = e, .loc = loc });
        }
        const crange = self.t.terms.case_pool.pushMany(self.gpa, case_ids);
        const def_e = self.edge(default_dest, default_args, loc);
        const tid = self.t.terms.add(.SwitchInt, .{ .scrut = scrut, .cases = crange, .default_edge = def_e, .loc = loc });
        blk.term = .some(tid);
    }

    pub fn addCall(
        self: *Builder,
        blk: *BlockFrame,
        result: ValueId,
        ty: types.TypeId,
        callee: StrId,
        args: []const ValueId,
        loc: OptLocId,
    ) InstrId {
        const r = self.t.instrs.val_list_pool.pushMany(self.gpa, args);
        const row: Rows.Call = .{ .result = result, .ty = ty, .callee = callee, .args = r, .loc = loc };
        const id = self.t.instrs.add(.Call, row);
        blk.instrs.append(self.gpa, id) catch @panic("OOM");
        return id;
    }

    pub fn addMlirBlock(
        self: *Builder,
        blk: *BlockFrame,
        result: ValueId,
        ty: types.TypeId,
        kind: ast.MlirKind,
        expr: ast.ExprId,
        text: StrId,
        pieces: []const MlirPieceId,
        args: []const ValueId,
        loc: OptLocId,
    ) InstrId {
        const args_range = self.t.instrs.value_pool.pushMany(self.gpa, args);
        const pieces_range = self.t.instrs.mlir_piece_pool.pushMany(self.gpa, pieces);
        const row: Rows.MlirBlock = .{
            .result = .some(result),
            .ty = ty,
            .kind = kind,
            .expr = expr,
            .text = text,
            .pieces = pieces_range,
            .args = args_range,
            .loc = loc,
        };
        const id = self.t.instrs.add(.MlirBlock, row);
        blk.instrs.append(self.gpa, id) catch @panic("OOM");
        return id;
    }

    // GEP helpers
    pub fn gepConst(self: *Builder, v: u64) GepIndexId {
        return self.t.instrs.GepIndex.add(self.gpa, .{ .Const = v });
    }
    pub fn gepValue(self: *Builder, val: ValueId) GepIndexId {
        return self.t.instrs.GepIndex.add(self.gpa, .{ .Value = val });
    }
    pub fn gep(
        self: *Builder,
        blk: *BlockFrame,
        ty: types.TypeId,
        base: ValueId,
        idxs: []const GepIndexId,
        loc: OptLocId,
    ) ValueId {
        const r = self.t.instrs.gep_pool.pushMany(self.gpa, idxs);
        const vid = self.freshValue();
        const iid = self.t.instrs.add(.Gep, Rows.Gep{ .result = vid, .ty = ty, .base = base, .indices = r, .loc = loc });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        return vid;
    }
};

pub const TirPrinter = struct {
    // Writes readable SSA with distinct namespaces:
    //   fN = function, bN = block, iN = instr, vN = value, gN = global
    // Example line:
    //   (i12 v19 = Add lhs=v4 rhs=v7 : i32)

    writer: *std.io.Writer,
    indent: usize = 0,
    tir: *TIR,

    pub fn init(writer: anytype, tir: *TIR) TirPrinter {
        return .{ .writer = writer, .tir = tir };
    }

    const TypeFmt = struct {
        store: *types.TypeStore,
        ty: types.TypeId,
        pub fn format(self: @This(), w: anytype) !void {
            try self.store.fmt(self.ty, w);
        }
    };
    inline fn tf(self: *const TirPrinter, ty: types.TypeId) TypeFmt {
        return .{ .store = self.tir.type_store, .ty = ty };
    }

    inline fn s(self: *const TirPrinter, id: StrId) []const u8 {
        return self.tir.instrs.strs.get(id);
    }

    fn ws(self: *TirPrinter) !void {
        var i: usize = 0;
        while (i < self.indent) : (i += 1) try self.writer.writeByte(' ');
    }
    fn open(self: *TirPrinter, comptime head: []const u8, args: anytype) !void {
        try self.ws();
        try self.writer.print(head, args);
        try self.writer.writeAll("\n");
        self.indent += 2;
    }
    fn close(self: *TirPrinter) !void {
        self.indent = if (self.indent >= 2) self.indent - 2 else 0;
        try self.ws();
        try self.writer.writeAll(")\n");
    }
    fn leaf(self: *TirPrinter, comptime fmt: []const u8, args: anytype) !void {
        try self.ws();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
    }

    inline fn pv(self: *TirPrinter, v: ValueId) !void {
        try self.writer.print("v{}", .{v.toRaw()});
    }
    inline fn pi(self: *TirPrinter, i: InstrId) !void {
        try self.writer.print("i{}", .{i.toRaw()});
    }
    inline fn pb(self: *TirPrinter, b: BlockId) !void {
        try self.writer.print("block_{}", .{b.toRaw()});
    }
    inline fn pg(self: *TirPrinter, g: GlobalId) !void {
        try self.writer.print("g{}", .{g.toRaw()});
    }

    fn printValueList(self: *TirPrinter, vals: []const ValueId) !void {
        try self.writer.writeAll("[");
        var first = true;
        for (vals) |v| {
            if (!first) try self.writer.writeAll(", ");
            first = false;
            try self.pv(v);
        }
        try self.writer.writeAll("]");
    }

    fn printEdge(self: *TirPrinter, e: Rows.Edge) !void {
        try self.writer.writeAll("dest=");
        try self.pb(e.dest);
        const args = self.tir.instrs.value_pool.slice(e.args);
        if (args.len > 0) {
            try self.writer.writeAll(" args=");
            try self.printValueList(args);
        }
    }

    pub fn print(self: *TirPrinter) !void {
        try self.open("(tir", .{});

        // Globals
        const globals = self.tir.funcs.global_pool.data.items;
        if (globals.len > 0) {
            try self.open("(globals", .{});
            for (globals) |gid| {
                const g = self.tir.funcs.Global.get(gid);
                try self.ws();
                try self.pg(gid);
                switch (g.init) {
                    .none => try self.writer.print(": (global name=\"{s}\" type={f})\n", .{ self.s(g.name), self.tf(g.ty) }),
                    .int => |val| try self.writer.print(": (global name=\"{s}\" type={f} init=int({}))\n", .{ self.s(g.name), self.tf(g.ty), val }),
                    .bool => |val| try self.writer.print(": (global name=\"{s}\" type={f} init=bool({}))\n", .{ self.s(g.name), self.tf(g.ty), val }),
                    .string => |sid| try self.writer.print(": (global name=\"{s}\" type={f} init=string(\"{s}\"))\n", .{ self.s(g.name), self.tf(g.ty), self.s(sid) }),
                    .float => |val| try self.writer.print(": (global name=\"{s}\" type={f} init=float({}))\n", .{ self.s(g.name), self.tf(g.ty), val }),
                    .aggregate => |fields| {
                        try self.writer.print(": (global name=\"{s}\" type={f} init=[", .{ self.s(g.name), self.tf(g.ty) });
                        for (fields, 0..) |field, i| {
                            if (i > 0) try self.writer.writeAll(", ");
                            try self.writer.print("{}", .{field});
                        }
                        try self.writer.writeAll("])\n");
                    },
                }
            }
            try self.close();
        }

        // Functions
        const funcs = self.tir.funcs.func_pool.data.items;
        for (funcs) |fid| try self.printFunc(fid);

        try self.close();
        try self.writer.flush();
    }

    fn printFunc(self: *TirPrinter, fid: FuncId) !void {
        const f = self.tir.funcs.Function.get(fid);
        try self.open("(function ", .{});
        try self.ws();
        try self.writer.print("{s} ", .{self.s(f.name)});
        try self.writer.print("result={f}", .{self.tf(f.result)});
        if (f.is_variadic) try self.writer.writeAll(" variadic");
        try self.writer.writeAll("\n");

        // Params (function)
        const params = self.tir.funcs.param_pool.slice(f.params);
        if (params.len > 0) {
            try self.open("(params", .{});
            for (params) |pid| {
                const p = self.tir.funcs.Param.get(pid);
                try self.ws();
                try self.pv(p.value);
                try self.writer.print(": {f}", .{self.tf(p.ty)});
                if (!p.name.isNone()) try self.writer.print(" /* {s} */", .{self.s(p.name.unwrap())});
                try self.writer.writeAll("\n");
            }
            try self.close();
        }

        // Blocks
        const blocks = self.tir.funcs.block_pool.slice(f.blocks);
        for (blocks) |bid| try self.printBlock(bid);

        try self.close(); // function
    }

    fn printBlock(self: *TirPrinter, bid: BlockId) !void {
        const b = self.tir.funcs.Block.get(bid);
        try self.open("(block ", .{});
        try self.ws();
        try self.pb(bid);
        try self.writer.writeAll("\n");

        // Block params
        const params = self.tir.funcs.param_pool.slice(b.params);
        if (params.len > 0) {
            try self.open("(params", .{});
            for (params) |pid| {
                const p = self.tir.funcs.Param.get(pid);
                try self.ws();
                try self.pv(p.value);
                try self.writer.print(": {f}", .{self.tf(p.ty)});
                if (!p.name.isNone()) try self.writer.print(" /* {s} */", .{self.s(p.name.unwrap())});
                try self.writer.writeAll("\n");
            }
            try self.close();
        }

        // Instrs
        const instrs = self.tir.instrs.instr_pool.slice(b.instrs);
        for (instrs) |iid| try self.printInstr(iid);

        // Terminator
        try self.open("(terminator", .{});
        const tid = b.term;
        const tk = self.tir.terms.index.kinds.items[tid.toRaw()];
        switch (tk) {
            .Return => {
                const row = self.tir.terms.get(.Return, tid);
                if (row.value.isNone()) {
                    try self.leaf("(return)", .{});
                } else {
                    try self.ws();
                    try self.writer.writeAll("(return value=");
                    try self.pv(row.value.unwrap());
                    try self.writer.writeAll(")\n");
                }
            },
            .Br => {
                const row = self.tir.terms.get(.Br, tid);
                const e = self.tir.terms.Edge.get(row.edge);
                try self.ws();
                try self.writer.writeAll("(br ");
                try self.printEdge(e);
                try self.writer.writeAll(")\n");
            },
            .CondBr => {
                const row = self.tir.terms.get(.CondBr, tid);
                const te = self.tir.terms.Edge.get(row.then_edge);
                const ee = self.tir.terms.Edge.get(row.else_edge);
                try self.ws();
                try self.writer.writeAll("(cond_br cond=");
                try self.pv(row.cond);
                try self.writer.writeAll(" then=");
                try self.pb(te.dest);
                const targs = self.tir.terms.Edge.get(row.then_edge).args;
                const eargs = self.tir.terms.Edge.get(row.else_edge).args;
                const ta = self.tir.instrs.value_pool.slice(targs);
                const ea = self.tir.instrs.value_pool.slice(eargs);
                if (ta.len > 0) {
                    try self.writer.writeAll(" args=");
                    try self.printValueList(ta);
                }
                try self.writer.writeAll(" else=");
                try self.pb(ee.dest);
                if (ea.len > 0) {
                    try self.writer.writeAll(" args=");
                    try self.printValueList(ea);
                }
                try self.writer.writeAll(")\n");
            },
            .SwitchInt => {
                const row = self.tir.terms.get(.SwitchInt, tid);
                const cases = self.tir.terms.case_pool.slice(row.cases);
                const def_edge = self.tir.terms.Edge.get(row.default_edge);
                try self.open("(switch_int scrut=", .{});
                try self.pv(row.scrut);
                try self.writer.writeAll("\n");
                for (cases) |cid| {
                    const c = self.tir.terms.Case.get(cid);
                    const e = self.tir.terms.Edge.get(c.edge);
                    try self.ws();
                    try self.writer.print("(case value={} ", .{c.value});
                    try self.printEdge(e);
                    try self.writer.writeAll(")\n");
                }
                try self.ws();
                try self.writer.writeAll("(default ");
                try self.printEdge(def_edge);
                try self.writer.writeAll(")\n");
                try self.close();
            },
            .Unreachable => {
                _ = self.tir.terms.get(.Unreachable, tid);
                try self.leaf("(unreachable)", .{});
            },
        }
        try self.close(); // terminator
        try self.close(); // block
    }

    pub fn printInstr(self: *TirPrinter, iid: InstrId) !void {
        const k = self.tir.instrs.index.kinds.items[iid.toRaw()];
        switch (k) {
            .ConstInt => {
                const r = self.tir.instrs.get(.ConstInt, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = ConstInt value={} : {f})\n", .{ r.value, self.tf(r.ty) });
            },
            .ConstFloat => {
                const r = self.tir.instrs.get(.ConstFloat, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = ConstFloat value={} : {f})\n", .{ r.value, self.tf(r.ty) });
            },
            .ConstBool => {
                const r = self.tir.instrs.get(.ConstBool, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = ConstBool value={} : {f})\n", .{ r.value, self.tf(r.ty) });
            },
            .ConstString => {
                const r = self.tir.instrs.get(.ConstString, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = ConstString \"{s}\" : {f})\n", .{ self.s(r.text), self.tf(r.ty) });
            },
            .ConstNull => {
                const r = self.tir.instrs.get(.ConstNull, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = ConstNull : {f})\n", .{self.tf(r.ty)});
            },
            .ConstUndef => {
                const r = self.tir.instrs.get(.ConstUndef, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = ConstUndef : {f})\n", .{self.tf(r.ty)});
            },

            inline .Add, .Sub, .Mul, .BinWrapAdd, .BinWrapSub, .BinWrapMul, .BinSatAdd, .BinSatSub, .BinSatMul, .BinSatShl, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .LogicalAnd, .LogicalOr, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe => |opk| {
                const r = self.tir.instrs.get(opk, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = {s} lhs=", .{@tagName(k)});
                try self.pv(r.lhs);
                try self.writer.writeAll(" rhs=");
                try self.pv(r.rhs);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .LogicalNot => {
                const r = self.tir.instrs.get(.LogicalNot, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = LogicalNot value=");
                try self.pv(r.value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            inline .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => |opk| {
                const r = self.tir.instrs.get(opk, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = {s} value=", .{@tagName(k)});
                try self.pv(r.value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .Alloca => {
                const r = self.tir.instrs.get(.Alloca, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = Alloca align={} ", .{r.@"align"});
                if (r.count.isNone()) {
                    try self.writer.writeAll("count=null");
                } else {
                    try self.writer.writeAll("count=");
                    try self.pv(r.count.unwrap());
                }
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },
            .Load => {
                const r = self.tir.instrs.get(.Load, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = Load ptr=");
                try self.pv(r.ptr);
                try self.writer.print(" align={} : {f})\n", .{ r.@"align", self.tf(r.ty) });
            },
            .Store => {
                const r = self.tir.instrs.get(.Store, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" Store ptr=");
                try self.pv(r.ptr);
                try self.writer.writeAll(" value=");
                try self.pv(r.value);
                try self.writer.print(" align={})\n", .{r.@"align"});
            },
            .Gep => {
                const r = self.tir.instrs.get(.Gep, iid);
                const idxs = self.tir.instrs.gep_pool.slice(r.indices);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = Gep base=");
                try self.pv(r.base);
                try self.writer.writeAll(" indices=[");
                var first = true;
                for (idxs) |gid| {
                    if (!first) try self.writer.writeAll(", ");
                    first = false;
                    const g = self.tir.instrs.GepIndex.get(gid);
                    switch (g) {
                        .Const => try self.writer.print("{}", .{g.Const}),
                        .Value => {
                            try self.pv(g.Value);
                        },
                    }
                }
                try self.writer.print("] : {f})\n", .{self.tf(r.ty)});
            },
            .GlobalAddr => {
                const r = self.tir.instrs.get(.GlobalAddr, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = GlobalAddr \"{s}\" : {f})\n", .{ self.s(r.name), self.tf(r.ty) });
            },

            .TupleMake => {
                const r = self.tir.instrs.get(.TupleMake, iid);
                const elems = self.tir.instrs.value_pool.slice(r.elems);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = TupleMake elems=", .{});
                try self.printValueList(elems);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },
            .ArrayMake => {
                const r = self.tir.instrs.get(.ArrayMake, iid);
                const elems = self.tir.instrs.value_pool.slice(r.elems);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = ArrayMake elems=", .{});
                try self.printValueList(elems);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },
            .StructMake => {
                const r = self.tir.instrs.get(.StructMake, iid);
                const fields = self.tir.instrs.sfi_pool.slice(r.fields);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = StructMake fields=[", .{});
                var first = true;
                for (fields) |sfid| {
                    if (!first) try self.writer.writeAll(", ");
                    first = false;
                    const sf = self.tir.instrs.StructFieldInit.get(sfid);
                    try self.writer.print("(index={} name=", .{sf.index});
                    if (sf.name.isNone()) try self.writer.writeAll("null") else try self.writer.print("\"{s}\"", .{self.s(sf.name.unwrap())});
                    try self.writer.writeAll(" value=");
                    try self.pv(sf.value);
                    try self.writer.writeAll(")");
                }
                try self.writer.print("] : {f})\n", .{self.tf(r.ty)});
            },

            .ExtractElem => {
                const r = self.tir.instrs.get(.ExtractElem, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = ExtractElem agg=", .{});
                try self.pv(r.agg);
                try self.writer.print(" index={} : {f})\n", .{ r.index, self.tf(r.ty) });
            },
            .InsertElem => {
                const r = self.tir.instrs.get(.InsertElem, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = InsertElem agg=", .{});
                try self.pv(r.agg);
                try self.writer.print(" index={} value=", .{r.index});
                try self.pv(r.value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },
            .ExtractField => {
                const r = self.tir.instrs.get(.ExtractField, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = ExtractField agg=", .{});
                try self.pv(r.agg);
                if (r.name.isNone()) {
                    try self.writer.print(" index={} ", .{r.index});
                } else {
                    try self.writer.print(" name=\"{s}\" ", .{self.s(r.name.unwrap())});
                }
                try self.writer.print(": {f})\n", .{self.tf(r.ty)});
            },
            .InsertField => {
                const r = self.tir.instrs.get(.InsertField, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = InsertField agg=", .{});
                try self.pv(r.agg);
                if (r.name.isNone()) {
                    try self.writer.print(" index={} ", .{r.index});
                } else {
                    try self.writer.print(" name=\"{s}\" ", .{self.s(r.name.unwrap())});
                }
                try self.writer.writeAll("value=");
                try self.pv(r.value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .Index => {
                const r = self.tir.instrs.get(.Index, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = Index base=");
                try self.pv(r.base);
                try self.writer.writeAll(" index=");
                try self.pv(r.index);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },
            .AddressOf => {
                const r = self.tir.instrs.get(.AddressOf, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = AddressOf value=");
                try self.pv(r.value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .Select => {
                const r = self.tir.instrs.get(.Select, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = Select cond=");
                try self.pv(r.cond);
                try self.writer.writeAll(" then=");
                try self.pv(r.then_value);
                try self.writer.writeAll(" else=");
                try self.pv(r.else_value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .Call => {
                const r = self.tir.instrs.get(.Call, iid);
                const args = self.tir.instrs.val_list_pool.slice(r.args);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = Call \"{s}\" args=", .{self.s(r.callee)});
                try self.printValueList(args);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .IndirectCall => {
                const r = self.tir.instrs.get(.IndirectCall, iid);
                const args = self.tir.instrs.val_list_pool.slice(r.args);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = IndirectCall callee=", .{});
                try self.pv(r.callee);
                try self.writer.writeAll(" args=");
                try self.printValueList(args);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .VariantMake => {
                const r = self.tir.instrs.get(.VariantMake, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = VariantMake tag={} payload=", .{r.tag});
                if (r.payload.isNone()) try self.writer.writeAll("null") else try self.pv(r.payload.unwrap());
                try self.writer.print(" : {f} (payload_ty={f}))\n", .{ self.tf(r.ty), self.tf(r.payload_ty) });
            },
            .VariantTag => {
                const r = self.tir.instrs.get(.VariantTag, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = VariantTag value=");
                try self.pv(r.value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },
            .VariantPayloadPtr => {
                const r = self.tir.instrs.get(.VariantPayloadPtr, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = VariantPayloadPtr value=");
                try self.pv(r.value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .UnionMake => {
                const r = self.tir.instrs.get(.UnionMake, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.print(" = UnionMake field_index={} value=", .{r.field_index});
                try self.pv(r.value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },
            .UnionField => {
                const r = self.tir.instrs.get(.UnionField, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = UnionField base=");
                try self.pv(r.base);
                try self.writer.print(" field_index={} : {f})\n", .{ r.field_index, self.tf(r.ty) });
            },
            .UnionFieldPtr => {
                const r = self.tir.instrs.get(.UnionFieldPtr, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = UnionFieldPtr base=");
                try self.pv(r.base);
                try self.writer.print(" field_index={} : {f})\n", .{ r.field_index, self.tf(r.ty) });
            },

            .ComplexMake => {
                const r = self.tir.instrs.get(.ComplexMake, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = ComplexMake re=");
                try self.pv(r.re);
                try self.writer.writeAll(" im=");
                try self.pv(r.im);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .RangeMake => {
                const r = self.tir.instrs.get(.RangeMake, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = RangeMake start=");
                try self.pv(r.start);
                try self.writer.writeAll(" end=");
                try self.pv(r.end);
                try self.writer.writeAll(" inclusive=");
                try self.pv(r.inclusive);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .Broadcast => {
                const r = self.tir.instrs.get(.Broadcast, iid);
                try self.ws();
                try self.writer.writeByte('(');
                try self.pi(iid);
                try self.writer.writeAll(" ");
                try self.pv(r.result);
                try self.writer.writeAll(" = Broadcast value=");
                try self.pv(r.value);
                try self.writer.print(" : {f})\n", .{self.tf(r.ty)});
            },

            .MlirBlock => {
                const r = self.tir.instrs.get(.MlirBlock, iid);
                try self.open("(MlirBlock ", .{});
                try self.ws();
                try self.pi(iid);
                try self.writer.print(" kind={s} text=\"{s}\" : {f}\n", .{
                    @tagName(r.kind), self.s(r.text), self.tf(r.ty),
                });
                if (!r.result.isNone()) {
                    try self.ws();
                    try self.writer.writeAll("result=");
                    try self.pv(r.result.unwrap());
                    try self.writer.writeAll("\n");
                } else {
                    try self.leaf("result=null", .{});
                }
                const pieces = self.tir.instrs.mlir_piece_pool.slice(r.pieces);
                try self.ws();
                try self.writer.writeAll("pieces=[");
                for (pieces, 0..) |pid, i| {
                    if (i > 0) try self.writer.writeAll(", ");
                    const piece = self.tir.instrs.MlirPiece.get(pid);
                    switch (piece.kind) {
                        .literal => try self.writer.print("literal:\"{s}\"", .{self.s(piece.text)}),
                        .splice => try self.writer.print("splice:{s}", .{self.s(piece.text)}),
                    }
                }
                try self.writer.writeAll("]\n");
                try self.ws();
                try self.writer.writeAll("args=");
                const args = self.tir.instrs.value_pool.slice(r.args);
                try self.printValueList(args);
                try self.writer.writeAll("\n");
                try self.close();
            },
        }
    }
};
