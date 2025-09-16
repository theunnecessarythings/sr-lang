const std = @import("std");
const dod = @import("cst_v2.zig");
const types = @import("types.zig");

// Typed IR (TIR) — DOD v2
// Columnar stores with typed indices and contiguous pools.

pub const ValueTag = struct {};
pub const FuncTag = struct {};
pub const BlockTag = struct {};
pub const InstrTag = struct {};
pub const TermTag = struct {};
pub const ParamTag = struct {};
pub const GlobalTag = struct {};
pub const EdgeTag = struct {};
pub const CaseTag = struct {};

pub const ValueId = dod.Index(ValueTag);
pub const OptValueId = dod.SentinelIndex(ValueTag);
pub const FuncId = dod.Index(FuncTag);
pub const BlockId = dod.Index(BlockTag);
pub const InstrId = dod.Index(InstrTag);
pub const TermId = dod.Index(TermTag);
pub const ParamId = dod.Index(ParamTag);
pub const GlobalId = dod.Index(GlobalTag);
pub const EdgeId = dod.Index(EdgeTag);
pub const CaseId = dod.Index(CaseTag);

pub const RangeValue = dod.RangeOf(ValueId);
pub const RangeBlock = dod.RangeOf(BlockId);
pub const RangeInstr = dod.RangeOf(InstrId);
pub const RangeParam = dod.RangeOf(ParamId);
pub const RangeEdge = dod.RangeOf(EdgeId);
pub const RangeCase = dod.RangeOf(CaseId);
pub const RangeFunc = dod.RangeOf(FuncId);
pub const RangeGlobal = dod.RangeOf(GlobalId);

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
    Add, Sub, Mul, Div, Mod, Shl, Shr, BitAnd, BitOr, BitXor,
    LogicalAnd, LogicalOr, LogicalNot,
    // Comparisons (bool result)
    CmpEq, CmpNe, CmpLt, CmpLe, CmpGt, CmpGe,
    // Casts
    CastNormal, CastBit, CastSaturate, CastWrap, CastChecked,
    // Memory
    Alloca, Load, Store, Gep,
    // Aggregates
    TupleMake, ArrayMake, StructMake,
    ExtractElem, InsertElem, ExtractField, InsertField,
    // Indexing/Pointers
    Index, AddressOf,
    // Control/Data
    Select,
    // Calls
    Call,
};

pub const TermKind = enum(u8) { Return, Br, CondBr, SwitchInt, Unreachable };

pub const Rows = struct {
    // All rows that produce a value carry (result, ty)
    pub const Bin2 = struct { result: ValueId, ty: types.TypeId, lhs: ValueId, rhs: ValueId };
    pub const Un1 = struct { result: ValueId, ty: types.TypeId, value: ValueId };

    pub const ConstInt = struct { result: ValueId, ty: types.TypeId, value: i64 };
    pub const ConstFloat = struct { result: ValueId, ty: types.TypeId, value: f64 };
    pub const ConstBool = struct { result: ValueId, ty: types.TypeId, value: bool };
    pub const ConstString = struct { result: ValueId, ty: types.TypeId, text: StrId };
    pub const ConstNull = struct { result: ValueId, ty: types.TypeId };
    pub const ConstUndef = struct { result: ValueId, ty: types.TypeId };

    pub const Alloca = struct { result: ValueId, ty: types.TypeId, count: OptValueId, @"align": u32 };
    pub const Load = struct { result: ValueId, ty: types.TypeId, ptr: ValueId, @"align": u32 };
    pub const Store = struct { result: ValueId, ty: types.TypeId, ptr: ValueId, value: ValueId, @"align": u32 };
    pub const GepIndex = union(enum) { Const: i64, Value: ValueId };
    pub const Gep = struct { result: ValueId, ty: types.TypeId, base: ValueId, // pointer
        indices: RangeGepIndex };

    pub const TupleMake = struct { result: ValueId, ty: types.TypeId, elems: RangeValue };
    pub const ArrayMake = struct { result: ValueId, ty: types.TypeId, elems: RangeValue };
    pub const StructFieldInit = struct { index: u32, name: dod.OptStrId, value: ValueId };
    pub const StructMake = struct { result: ValueId, ty: types.TypeId, fields: RangeStructFieldInit };

    pub const ExtractElem = struct { result: ValueId, ty: types.TypeId, agg: ValueId, index: u32 };
    pub const InsertElem = struct { result: ValueId, ty: types.TypeId, agg: ValueId, index: u32, value: ValueId };
    pub const ExtractField = struct { result: ValueId, ty: types.TypeId, agg: ValueId, index: u32, name: dod.OptStrId };
    pub const InsertField = struct { result: ValueId, ty: types.TypeId, agg: ValueId, index: u32, value: ValueId, name: dod.OptStrId };

    pub const Index = struct { result: ValueId, ty: types.TypeId, base: ValueId, index: ValueId };
    pub const AddressOf = struct { result: ValueId, ty: types.TypeId, value: ValueId };

    pub const Select = struct { result: ValueId, ty: types.TypeId, cond: ValueId, then_value: ValueId, else_value: ValueId };

    pub const Call = struct { result: ValueId, ty: types.TypeId, callee: StrId, args: RangeValue };

    // Terminator rows
    pub const Return = struct { value: OptValueId };
    pub const Edge = struct { dest: BlockId, args: RangeValue };
    pub const Br = struct { edge: EdgeId };
    pub const CondBr = struct { cond: ValueId, then_edge: EdgeId, else_edge: EdgeId };
    pub const Case = struct { value: u64, edge: EdgeId };
    pub const SwitchInt = struct { scrut: ValueId, cases: RangeCase, default_edge: EdgeId };
    pub const Unreachable = struct {};
};

pub const GepIndexTag = struct {};
pub const StructFieldInitTag = struct {};

pub const GepIndexId = dod.Index(GepIndexTag);
pub const StructFieldInitId = dod.Index(StructFieldInitTag);

pub const RangeGepIndex = dod.RangeOf(GepIndexId);
pub const RangeStructFieldInit = dod.RangeOf(StructFieldInitId);

inline fn RowT(comptime K: OpKind) type {
    return @field(Rows, @tagName(K));
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

    // aux tables
    GepIndex: Table(Rows.GepIndex) = .{},
    StructFieldInit: Table(Rows.StructFieldInit) = .{},

    // pools
    instr_pool: Pool(InstrId) = .{},
    value_pool: Pool(ValueId) = .{},
    gep_pool: Pool(GepIndexId) = .{},
    sfi_pool: Pool(StructFieldInitId) = .{},
    val_list_pool: Pool(ValueId) = .{},

    strs: StringInterner,

    pub fn init(gpa: std.mem.Allocator) InstrStore {
        return .{ .gpa = gpa, .strs = StringInterner.init(gpa) };
    }
    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;
        self.index.deinit(gpa);
        inline for (@typeInfo(OpKind).@"enum".fields) |f| {
            @field(self, f.name).deinit(gpa);
        }
        self.GepIndex.deinit(gpa);
        self.StructFieldInit.deinit(gpa);
        self.instr_pool.deinit(gpa);
        self.value_pool.deinit(gpa);
        self.gep_pool.deinit(gpa);
        self.sfi_pool.deinit(gpa);
        self.val_list_pool.deinit(gpa);
        self.strs.deinit();
    }

    pub fn add(self: *@This(), comptime K: OpKind, row: RowT(K)) InstrId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx, InstrId);
    }

    pub fn get(self: *const @This(), comptime K: OpKind, id: InstrId) RowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *const Table(RowT(K)) = &@field(self, @tagName(K));
        return tbl.get(row_idx);
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
        return self.index.newId(self.gpa, K, idx, TermId);
    }
    pub fn get(self: *const @This(), comptime K: TermKind, id: TermId) TermRowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *const Table(TermRowT(K)) = &@field(self, @tagName(K));
        return tbl.get(row_idx);
    }
};

pub const FuncRows = struct {
    pub const Param = struct { value: ValueId, name: dod.OptStrId, ty: types.TypeId };
    pub const Block = struct { params: RangeParam, instrs: RangeInstr, term: TermId };
    pub const Function = struct { name: StrId, params: RangeParam, result: types.TypeId, blocks: RangeBlock };
    pub const Global = struct { name: StrId, ty: types.TypeId };
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
    type_arena: *types.TypeArena,
    instrs: InstrStore,
    terms: TermStore,
    funcs: FuncStore,

    pub fn init(gpa: std.mem.Allocator, arena: *types.TypeArena) TIR {
        return .{ .gpa = gpa, .type_arena = arena, .instrs = InstrStore.init(gpa), .terms = TermStore.init(gpa), .funcs = FuncStore.init(gpa) };
    }
    pub fn deinit(self: *@This()) void {
        self.instrs.deinit();
        self.terms.deinit();
        self.funcs.deinit();
    }
};
