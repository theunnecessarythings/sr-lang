const std = @import("std");
const dod = @import("cst.zig");
const ast = @import("ast.zig");
const types = @import("types.zig");

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
    Add,
    Sub,
    Mul,
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
    MlirBlock,
    // Variants
    VariantMake,
    VariantTag,
    VariantPayloadPtr,
    // Complex numbers
    ComplexMake,
    RangeMake,
};

pub const TermKind = enum(u8) { Return, Br, CondBr, SwitchInt, Unreachable };

pub const Rows = struct {
    // All rows that produce a value carry (result, ty)
    pub const Bin2 = struct { result: ValueId, ty: types.TypeId, lhs: ValueId, rhs: ValueId };
    pub const Un1 = struct { result: ValueId, ty: types.TypeId, value: ValueId };

    pub const ConstInt = struct { result: ValueId, ty: types.TypeId, value: u64 };
    pub const ConstFloat = struct { result: ValueId, ty: types.TypeId, value: f64 };
    pub const ConstBool = struct { result: ValueId, ty: types.TypeId, value: bool };
    pub const ConstString = struct { result: ValueId, ty: types.TypeId, text: StrId };
    pub const ConstNull = struct { result: ValueId, ty: types.TypeId };
    pub const ConstUndef = struct { result: ValueId, ty: types.TypeId };

    pub const Alloca = struct { result: ValueId, ty: types.TypeId, count: OptValueId, @"align": u32 };
    pub const Load = struct { result: ValueId, ty: types.TypeId, ptr: ValueId, @"align": u32 };
    pub const Store = struct { result: ValueId, ty: types.TypeId, ptr: ValueId, value: ValueId, @"align": u32 };
    pub const GepIndex = union(enum) { Const: u64, Value: ValueId };
    pub const Gep = struct {
        result: ValueId,
        ty: types.TypeId,
        base: ValueId, // pointer
        indices: RangeGepIndex,
    };

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
    pub const GlobalAddr = struct { result: ValueId, ty: types.TypeId, name: StrId };

    pub const Select = struct { result: ValueId, ty: types.TypeId, cond: ValueId, then_value: ValueId, else_value: ValueId };

    pub const Call = struct { result: ValueId, ty: types.TypeId, callee: StrId, args: RangeValue };
    pub const MlirBlock = struct { result: OptValueId, ty: types.TypeId, kind: ast.MlirKind, text: StrId };
    pub const VariantMake = struct { result: ValueId, ty: types.TypeId, tag: u32, payload: OptValueId, payload_ty: types.TypeId };
    pub const VariantTag = struct { result: ValueId, ty: types.TypeId, value: ValueId };
    pub const VariantPayloadPtr = struct { result: ValueId, ty: types.TypeId, value: ValueId };
    pub const ComplexMake = struct { result: ValueId, ty: types.TypeId, re: ValueId, im: ValueId };
    pub const RangeMake = struct { result: ValueId, ty: types.TypeId, start: ValueId, end: ValueId, inclusive: ValueId };

    // Terminator rows
    pub const Return = struct { value: OptValueId };
    pub const Edge = struct { dest: BlockId, args: RangeValue };
    pub const Br = struct { edge: EdgeId };
    pub const CondBr = struct { cond: ValueId, then_edge: EdgeId, else_edge: EdgeId };
    pub const Case = struct { value: u64, edge: EdgeId };
    pub const SwitchInt = struct { scrut: ValueId, cases: RangeCase, default_edge: EdgeId };
    pub const Unreachable = struct {};
};

pub const GepIndexId = dod.Index(Rows.GepIndex);
pub const StructFieldInitId = dod.Index(Rows.StructFieldInit);

pub const RangeGepIndex = dod.RangeOf(GepIndexId);
pub const RangeStructFieldInit = dod.RangeOf(StructFieldInitId);

inline fn RowT(comptime K: OpKind) type {
    return switch (K) {
        .ConstInt => Rows.ConstInt,
        .ConstFloat => Rows.ConstFloat,
        .ConstBool => Rows.ConstBool,
        .ConstString => Rows.ConstString,
        .ConstNull => Rows.ConstNull,
        .ConstUndef => Rows.ConstUndef,

        .Add, .Sub, .Mul, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .LogicalAnd, .LogicalOr, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe => Rows.Bin2,

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
        .MlirBlock => Rows.MlirBlock,
        .VariantMake => Rows.VariantMake,
        .VariantTag => Rows.VariantTag,
        .VariantPayloadPtr => Rows.VariantPayloadPtr,
        .ComplexMake => Rows.ComplexMake,
        .RangeMake => Rows.RangeMake,
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
    MlirBlock: Table(Rows.MlirBlock) = .{},
    VariantMake: Table(Rows.VariantMake) = .{},
    VariantTag: Table(Rows.VariantTag) = .{},
    VariantPayloadPtr: Table(Rows.VariantPayloadPtr) = .{},
    ComplexMake: Table(Rows.ComplexMake) = .{},
    RangeMake: Table(Rows.RangeMake) = .{},

    // aux tables
    GepIndex: Table(Rows.GepIndex) = .{},
    StructFieldInit: Table(Rows.StructFieldInit) = .{},

    // pools
    instr_pool: Pool(InstrId) = .{},
    value_pool: Pool(ValueId) = .{},
    gep_pool: Pool(GepIndexId) = .{},
    sfi_pool: Pool(StructFieldInitId) = .{},
    val_list_pool: Pool(ValueId) = .{},

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
        self.instr_pool.deinit(gpa);
        self.value_pool.deinit(gpa);
        self.gep_pool.deinit(gpa);
        self.sfi_pool.deinit(gpa);
        self.val_list_pool.deinit(gpa);
    }

    pub fn add(self: *@This(), comptime K: OpKind, row: RowT(K)) InstrId {
        const tbl: *Table(RowT(K)) = &@field(self, @tagName(K));
        const idx = tbl.add(self.gpa, row);
        return self.index.newId(self.gpa, K, idx.toRaw(), InstrId);
    }

    pub fn get(self: *const @This(), comptime K: OpKind, id: InstrId) RowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *const Table(RowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
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
    pub fn get(self: *const @This(), comptime K: TermKind, id: TermId) TermRowT(K) {
        std.debug.assert(self.index.kinds.items[id.toRaw()] == K);
        const row_idx = self.index.rows.items[id.toRaw()];
        const tbl: *const Table(TermRowT(K)) = &@field(self, @tagName(K));
        return tbl.get(.{ .index = row_idx });
    }
};

pub const FuncRows = struct {
    pub const Param = struct { value: ValueId, name: dod.OptStrId, ty: types.TypeId };
    pub const Block = struct { params: RangeParam, instrs: RangeInstr, term: TermId };
    pub const Function = struct { name: StrId, params: RangeParam, result: types.TypeId, blocks: RangeBlock, is_variadic: bool };
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
    type_store: *types.TypeStore,
    instrs: InstrStore,
    terms: TermStore,
    funcs: FuncStore,

    pub fn init(gpa: std.mem.Allocator, store: *types.TypeStore) TIR {
        return .{ .gpa = gpa, .type_store = store, .instrs = InstrStore.init(gpa, store.strs), .terms = TermStore.init(gpa), .funcs = FuncStore.init(gpa) };
    }
    pub fn deinit(self: *@This()) void {
        self.instrs.deinit();
        self.terms.deinit();
        self.funcs.deinit();
    }
};

pub const TirPrinter = struct {
    writer: *std.io.Writer,
    indent: usize = 0,

    tir: *const TIR,
    pub fn init(writer: anytype, tir: *const TIR) TirPrinter {
        return .{ .writer = writer, .tir = tir };
    }

    const TypeFmt = struct {
        store: *const types.TypeStore,
        ty: types.TypeId,

        pub fn format(self: @This(), w: anytype) !void {
            try self.store.fmt(self.ty, w);
        }
    };

    inline fn tf(self: *const TirPrinter, ty: types.TypeId) TypeFmt {
        return .{ .store = self.tir.type_store, .ty = ty };
    }

    fn ws(self: *TirPrinter) anyerror!void {
        var i: usize = 0;
        while (i < self.indent) : (i += 1) try self.writer.writeByte(' ');
    }

    fn open(self: *TirPrinter, comptime head: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(head, args);
        try self.writer.writeAll("\n");
        self.indent += 2;
    }

    fn close(self: *TirPrinter) anyerror!void {
        self.indent = if (self.indent >= 2) self.indent - 2 else 0;
        try self.ws();
        try self.writer.writeAll(")\n");
    }

    fn leaf(self: *TirPrinter, comptime fmt: []const u8, args: anytype) anyerror!void {
        try self.ws();
        try self.writer.print(fmt, args);
        try self.writer.writeAll("\n");
    }

    inline fn s(self: *const TirPrinter, id: StrId) []const u8 {
        return self.tir.instrs.strs.get(id);
    }

    pub fn print(self: *TirPrinter) anyerror!void {
        try self.open("(tir", .{});
        // Globals
        const globals = self.tir.funcs.global_pool.data.items;
        if (globals.len > 0) {
            try self.open("(globals", .{});
            for (globals) |gid| {
                const g = self.tir.funcs.Global.get(gid);
                try self.leaf("(global name=\"{s}\" type={f})", .{ self.s(g.name), self.tf(g.ty) });
            }
            try self.close();
        }
        // Functions
        const funcs = self.tir.funcs.func_pool.data.items;
        for (funcs) |fid| try self.printFunc(fid);
        try self.close();
        try self.writer.flush();
    }

    fn printFunc(self: *TirPrinter, id: FuncId) anyerror!void {
        const func = self.tir.funcs.Function.get(id);
        try self.open("(function name=\"{s}\" result={f})", .{ self.s(func.name), self.tf(func.result) });
        // Params
        const params = self.tir.funcs.param_pool.slice(func.params);
        if (params.len > 0) {
            try self.open("(params", .{});
            for (params) |pid| {
                const p = self.tir.funcs.Param.get(pid);
                try self.leaf("(param name={s} type={f})", .{ if (p.name.isNone()) "null" else self.s(p.name.unwrap()), self.tf(p.ty) });
            }
            try self.close();
        }
        // Blocks
        const blocks = self.tir.funcs.block_pool.slice(func.blocks);
        for (blocks) |bid| try self.printBlock(bid);
        try self.close();
    }

    fn printBlock(self: *TirPrinter, id: BlockId) anyerror!void {
        const block = self.tir.funcs.Block.get(id);
        try self.open("(block", .{});
        // Params
        const params = self.tir.funcs.param_pool.slice(block.params);
        if (params.len > 0) {
            try self.open("(params", .{});
            for (params) |pid| {
                const p = self.tir.funcs.Param.get(pid);
                try self.leaf("(param name={s} type={f})", .{ if (p.name.isNone()) "null" else self.s(p.name.unwrap()), self.tf(p.ty) });
            }
            try self.close();
        }
        // Instrs
        const instrs = self.tir.instrs.instr_pool.slice(block.instrs);
        for (instrs) |iid| try self.printInstr(iid);
        // Term
        try self.open("(terminator", .{});
        const term_id = block.term;
        const term_kind = self.tir.terms.index.kinds.items[term_id.toRaw()];
        switch (term_kind) {
            .Return => {
                const row = self.tir.terms.get(.Return, term_id);
                if (!row.value.isNone()) {
                    try self.leaf("(return value={})", .{row.value.unwrap().toRaw()});
                } else {
                    try self.leaf("(return)", .{});
                }
            },
            .Br => {
                const row = self.tir.terms.get(.Br, term_id);
                const edge = self.tir.terms.Edge.get(row.edge);
                try self.leaf("(br dest=block_{})", .{edge.dest});
            },
            .CondBr => {
                const row = self.tir.terms.get(.CondBr, term_id);
                const then_edge = self.tir.terms.Edge.get(row.then_edge);
                const else_edge = self.tir.terms.Edge.get(row.else_edge);
                try self.leaf("(cond_br cond={} then=block_{} else=block_{})", .{ row.cond.toRaw(), then_edge.dest.toRaw(), else_edge.dest.toRaw() });
            },
            .SwitchInt => {
                const row = self.tir.terms.get(.SwitchInt, term_id);
                const cases = self.tir.terms.case_pool.slice(row.cases);
                const default_edge = self.tir.terms.Edge.get(row.default_edge);
                try self.open("(switch_int scrut={} default=block_{})", .{ row.scrut.toRaw(), default_edge.dest.toRaw() });
                for (cases) |cid| {
                    const c = self.tir.terms.Case.get(cid);
                    const edge = self.tir.terms.Edge.get(c.edge);
                    try self.leaf("(case value={} dest=block_{})", .{ c.value, edge.dest.toRaw() });
                }
                try self.close();
            },
            .Unreachable => {
                _ = self.tir.terms.get(.Unreachable, term_id);
                try self.leaf("(unreachable)", .{});
            },
        }
        try self.close(); // terminator
        try self.close(); // block
    }

    pub fn printInstr(self: *TirPrinter, id: InstrId) anyerror!void {
        const kind = self.tir.instrs.index.kinds.items[id.toRaw()];
        switch (kind) {
            .ConstInt => {
                const row = self.tir.instrs.get(.ConstInt, id);
                try self.leaf("(instr id={} op=ConstInt value={} type={f})", .{ id.toRaw(), row.value, self.tf(row.ty) });
            },
            .ConstFloat => {
                const row = self.tir.instrs.get(.ConstFloat, id);
                try self.leaf("(instr id={} op=ConstFloat value={} type={f})", .{ id.toRaw(), row.value, self.tf(row.ty) });
            },
            .ConstBool => {
                const row = self.tir.instrs.get(.ConstBool, id);
                try self.leaf("(instr id={} op=ConstBool value={} type={f})", .{ id.toRaw(), row.value, self.tf(row.ty) });
            },
            .ConstString => {
                const row = self.tir.instrs.get(.ConstString, id);
                try self.leaf("(instr id={} op=ConstString value=\"{s}\" type={f})", .{ id.toRaw(), self.s(row.text), self.tf(row.ty) });
            },
            .ConstNull => {
                const row = self.tir.instrs.get(.ConstNull, id);
                try self.leaf("(instr id={} op=ConstNull type={f})", .{ id.toRaw(), self.tf(row.ty) });
            },
            .ConstUndef => {
                const row = self.tir.instrs.get(.ConstUndef, id);
                try self.leaf("(instr id={} op=ConstUndef type={f})", .{ id.toRaw(), self.tf(row.ty) });
            },
            inline .Add, .Sub, .Mul, .Div, .Mod, .Shl, .Shr, .BitAnd, .BitOr, .BitXor, .LogicalAnd, .LogicalOr, .CmpEq, .CmpNe, .CmpLt, .CmpLe, .CmpGt, .CmpGe => |x| {
                const row = self.tir.instrs.get(x, id);
                try self.leaf("(instr id={} op={s} lhs={} rhs={} result={} type={f})", .{ id.toRaw(), @tagName(kind), row.lhs.toRaw(), row.rhs.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .LogicalNot => {
                const row = self.tir.instrs.get(.LogicalNot, id);
                try self.leaf("(instr id={} op=LogicalNot value={} result={} type={f})", .{ id.toRaw(), row.value.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            inline .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => |x| {
                const row = self.tir.instrs.get(x, id);
                try self.leaf("(instr id={} op={s} value={} result={} type={f})", .{ id.toRaw(), @tagName(kind), row.value.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .Alloca => {
                const row = self.tir.instrs.get(.Alloca, id);
                if (!row.count.isNone()) {
                    try self.leaf("(instr id={} op=Alloca count={} align={} result={} type={f})", .{ id.toRaw(), row.count.unwrap().toRaw(), row.@"align", row.result.toRaw(), self.tf(row.ty) });
                } else {
                    try self.leaf("(instr id={} op=Alloca count=null align={} result={} type={f})", .{ id.toRaw(), row.@"align", row.result.toRaw(), self.tf(row.ty) });
                }
            },
            .Load => {
                const row = self.tir.instrs.get(.Load, id);
                try self.leaf("(instr id={} op=Load ptr={} align={} result={} type={f})", .{ id.toRaw(), row.ptr.toRaw(), row.@"align", row.result.toRaw(), self.tf(row.ty) });
            },
            .Store => {
                const row = self.tir.instrs.get(.Store, id);
                try self.leaf("(instr id={} op=Store ptr={} value={} align={})", .{ id.toRaw(), row.ptr.toRaw(), row.value.toRaw(), row.@"align" });
            },
            .Gep => {
                const row = self.tir.instrs.get(.Gep, id);
                const indices = self.tir.instrs.gep_pool.slice(row.indices);
                try self.open("(instr id={} op=Gep base={} result={} type={f} indices=[", .{ id.toRaw(), row.base.toRaw(), row.result.toRaw(), self.tf(row.ty) });
                for (indices) |gid| {
                    const g = self.tir.instrs.GepIndex.get(gid);
                    switch (g) {
                        .Const => try self.leaf("  (const {})", .{g.Const}),
                        .Value => try self.leaf("  (value {})", .{g.Value.toRaw()}),
                    }
                }
                try self.leaf("])", .{});
                try self.close();
            },
            .GlobalAddr => {
                const row = self.tir.instrs.get(.GlobalAddr, id);
                try self.leaf("(instr id={} op=GlobalAddr name=\"{s}\" result={} type={f})", .{ id.toRaw(), self.s(row.name), row.result.toRaw(), self.tf(row.ty) });
            },
            .TupleMake => {
                const row = self.tir.instrs.get(.TupleMake, id);
                const elems = self.tir.instrs.value_pool.slice(row.elems);
                try self.open("(instr id={} op=TupleMake result={} type={f} elems=[", .{ id.toRaw(), row.result.toRaw(), self.tf(row.ty) });
                for (elems) |vid| try self.leaf("  {}", .{vid.toRaw()});
                try self.leaf("])", .{});
                try self.close();
            },
            .ArrayMake => {
                const row = self.tir.instrs.get(.ArrayMake, id);
                const elems = self.tir.instrs.value_pool.slice(row.elems);
                try self.open("(instr id={} op=ArrayMake result={} type={f} elems=[", .{ id.toRaw(), row.result.toRaw(), self.tf(row.ty) });
                for (elems) |vid| try self.leaf("  {}", .{vid.toRaw()});
                try self.leaf("])", .{});
                try self.close();
            },
            .RangeMake => {
                const row = self.tir.instrs.get(.RangeMake, id);
                try self.leaf("(instr id={} op=RangeMake start={} end={} inclusive={} result={} type={f})", .{ id.toRaw(), row.start.toRaw(), row.end.toRaw(), row.inclusive.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .StructMake => {
                const row = self.tir.instrs.get(.StructMake, id);
                const fields = self.tir.instrs.sfi_pool.slice(row.fields);
                try self.open("(instr id={} op=StructMake result={} type={f} fields=[", .{ id.toRaw(), row.result.toRaw(), self.tf(row.ty) });
                for (fields) |sfid| {
                    const sf = self.tir.instrs.StructFieldInit.get(sfid);
                    try self.leaf("  (field index={} name={s} value={})", .{ sf.index, if (sf.name.isNone()) "null" else self.s(sf.name.unwrap()), sf.value.toRaw() });
                }
                try self.leaf("])", .{});
                try self.close();
            },
            .ExtractElem => {
                const row = self.tir.instrs.get(.ExtractElem, id);
                try self.leaf("(instr id={} op=ExtractElem agg={} index={} result={} type={f})", .{
                    id.toRaw(),
                    row.agg.toRaw(),
                    row.index,
                    row.result.toRaw(),
                    self.tf(row.ty),
                });
            },
            .InsertElem => {
                const row = self.tir.instrs.get(.InsertElem, id);
                try self.leaf("(instr id={} op=InsertElem agg={} index={} value={} result={} type={f})", .{ id.toRaw(), row.agg.toRaw(), row.index, row.value.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .ExtractField => {
                const row = self.tir.instrs.get(.ExtractField, id);
                try self.leaf("(instr id={} op=ExtractField agg={} index={} name={s} result={} type={f})", .{
                    id.toRaw(),
                    row.agg.toRaw(),
                    row.index,
                    if (row.name.isNone()) "null" else self.s(row.name.unwrap()),
                    row.result.toRaw(),
                    self.tf(row.ty),
                });
            },
            .InsertField => {
                const row = self.tir.instrs.get(.InsertField, id);
                try self.leaf("(instr id={} op=InsertField agg={} index={} value={} name={s} result={} type={f})", .{
                    id.toRaw(),
                    row.agg.toRaw(),
                    row.index,
                    row.value.toRaw(),
                    if (row.name.isNone()) "null" else self.s(row.name.unwrap()),
                    row.result.toRaw(),
                    self.tf(row.ty),
                });
            },
            .Index => {
                const row = self.tir.instrs.get(.Index, id);
                try self.leaf("(instr id={} op=Index base={} index={} result={} type={f})", .{ id.toRaw(), row.base.toRaw(), row.index.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .AddressOf => {
                const row = self.tir.instrs.get(.AddressOf, id);
                try self.leaf("(instr id={} op=AddressOf value={} result={} type={f})", .{ id.toRaw(), row.value.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .Select => {
                const row = self.tir.instrs.get(.Select, id);
                try self.leaf("(instr id={} op=Select cond={} then={} else={} result={} type={f})", .{ id.toRaw(), row.cond.toRaw(), row.then_value.toRaw(), row.else_value.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .Call => {
                const row = self.tir.instrs.get(.Call, id);
                const args = self.tir.instrs.val_list_pool.slice(row.args);
                try self.open("(instr id={} op=Call callee=\"{s}\" result={} type={f} args=[", .{ id.toRaw(), self.s(row.callee), row.result.toRaw(), self.tf(row.ty) });
                for (args) |vid| try self.leaf("  {}", .{vid.toRaw()});
                try self.leaf("])", .{});
                try self.close();
            },
            .VariantMake => {
                const row = self.tir.instrs.get(.VariantMake, id);
                try self.leaf("(instr id={} op=VariantMake tag={} payload={} result={} type={f} payload_ty={f})", .{
                    id.toRaw(),
                    row.tag,
                    if (row.payload.isNone()) 0 else row.payload.unwrap().toRaw(),
                    row.result.toRaw(),
                    self.tf(row.ty),
                    self.tf(row.payload_ty),
                });
            },
            .VariantTag => {
                const row = self.tir.instrs.get(.VariantTag, id);
                try self.leaf("(instr id={} op=VariantTag value={} result={} type={f})", .{ id.toRaw(), row.value.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .VariantPayloadPtr => {
                const row = self.tir.instrs.get(.VariantPayloadPtr, id);
                try self.leaf("(instr id={} op=VariantPayloadPtr value={} result={} type={f})", .{ id.toRaw(), row.value.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .ComplexMake => {
                const row = self.tir.instrs.get(.ComplexMake, id);
                try self.leaf("(instr id={} op=ComplexMake re={} im={} result={} type={f})", .{ id.toRaw(), row.re.toRaw(), row.im.toRaw(), row.result.toRaw(), self.tf(row.ty) });
            },
            .MlirBlock => {
                const row = self.tir.instrs.get(.MlirBlock, id);
                try self.open("(instr id={} op=MlirBlock kind={s} text=\"{s}\" type={f})", .{
                    id.toRaw(),
                    @tagName(row.kind),
                    self.s(row.text),
                    self.tf(row.ty),
                });
                if (!row.result.isNone()) {
                    try self.leaf("  (result {})", .{row.result.unwrap().toRaw()});
                } else {
                    try self.leaf("  (result null)", .{});
                }
                try self.close();
            },
        }
    }
};
