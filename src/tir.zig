const std = @import("std");
const List = std.array_list.Managed;
const types = @import("types.zig");

// Typed IR for codegen (post-checker/inference):
// - SSA-ish blocks with typed values
// - Simplified instruction set for initial codegen

pub const ValueId = u32;
pub const BlockId = u32;
pub const FuncId = u32;

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

pub const Global = struct {
    name: []const u8,
    ty: types.TypeId,
    // future: initial value
};

pub const Function = struct {
    name: []const u8,
    params: List(Param),
    result: types.TypeId,
    blocks: List(Block),

    pub fn init(allocator: std.mem.Allocator, name: []const u8, result: types.TypeId) Function {
        return .{
            .name = name,
            .params = List(Param).init(allocator),
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

pub const Param = struct { name: []const u8, ty: types.TypeId };

pub const Block = struct {
    id: BlockId,
    instrs: List(Instr),
    term: ?Terminator = null,

    pub fn init(allocator: std.mem.Allocator, id: BlockId) Block {
        return .{ .id = id, .instrs = List(Instr).init(allocator), .term = null };
    }

    pub fn deinit(self: *Block, allocator: std.mem.Allocator) void { _ = allocator; self.instrs.deinit(); }
};

pub const InstrTag = enum(u8) {
    ConstInt,
    ConstString,
    Add,
    Call,
};

pub const Instr = struct {
    tag: InstrTag,
    // each instr defines one value
    result: ValueId,
    ty: types.TypeId,
    payload: Payload,

    pub const Payload = union(InstrTag) {
        ConstInt: i64,
        ConstString: []const u8,
        Add: struct { lhs: ValueId, rhs: ValueId },
        Call: struct { callee: []const u8, args: []const ValueId },
    };
};

pub const Terminator = union(enum) {
    Return: ?ValueId,
    Br: BlockId,
};

pub const Builder = struct {
    allocator: std.mem.Allocator,
    mod: *Module,
    next_block: BlockId = 0,
    next_value: ValueId = 0,

    pub fn init(allocator: std.mem.Allocator, mod: *Module) Builder {
        return .{ .allocator = allocator, .mod = mod };
    }

    pub fn addFunction(self: *Builder, name: []const u8, result: types.TypeId, params: []const Param) !*Function {
        var f = Function.init(self.allocator, name, result);
        for (params) |p| try f.params.append(p);
        try self.mod.functions.append(f);
        return &self.mod.functions.items[self.mod.functions.items.len - 1];
    }

    pub fn addBlock(self: *Builder, f: *Function) !*Block {
        const id = self.next_block;
        self.next_block += 1;
        const b = Block.init(self.allocator, id);
        try f.blocks.append(b);
        return &f.blocks.items[f.blocks.items.len - 1];
    }

    fn freshValue(self: *Builder) ValueId { const id = self.next_value; self.next_value += 1; return id; }

    pub fn constInt(self: *Builder, b: *Block, ty: types.TypeId, value: i64) !ValueId {
        const id = self.freshValue();
        try b.instrs.append(.{ .tag = .ConstInt, .result = id, .ty = ty, .payload = .{ .ConstInt = value } });
        return id;
    }

    pub fn constString(self: *Builder, b: *Block, ty: types.TypeId, s: []const u8) !ValueId {
        const id = self.freshValue();
        try b.instrs.append(.{ .tag = .ConstString, .result = id, .ty = ty, .payload = .{ .ConstString = s } });
        return id;
    }

    pub fn add(self: *Builder, b: *Block, ty: types.TypeId, lhs: ValueId, rhs: ValueId) !ValueId {
        const id = self.freshValue();
        try b.instrs.append(.{ .tag = .Add, .result = id, .ty = ty, .payload = .{ .Add = .{ .lhs = lhs, .rhs = rhs } } });
        return id;
    }

    pub fn call(self: *Builder, b: *Block, ty: types.TypeId, callee: []const u8, args: []const ValueId) !ValueId {
        const id = self.freshValue();
        const copied = try self.allocator.alloc(ValueId, args.len);
        std.mem.copyForwards(ValueId, copied, args);
        try b.instrs.append(.{ .tag = .Call, .result = id, .ty = ty, .payload = .{ .Call = .{ .callee = callee, .args = copied } } });
        return id;
    }

    pub fn retVoid(_: *Builder, b: *Block) void { b.term = .{ .Return = null }; }
    pub fn ret(_: *Builder, b: *Block, v: ValueId) void { b.term = .{ .Return = v }; }
};

pub fn Printer(comptime WriterType: type) type { return struct {
    w: WriterType,
    type_arena: *types.TypeArena,

    pub fn init(writer: WriterType, type_arena: *types.TypeArena) @This() {
        return .{ .w = writer, .type_arena = type_arena };
    }

    pub fn printModule(self: *@This(), m: *const Module) anyerror!void {
        try self.w.print("(tir.module\n", .{});
        for (m.functions.items) |*f| try self.printFunction(f);
        try self.w.print(")\n", .{});
    }

    fn printFunction(self: *@This(), f: *const Function) anyerror!void {
        try self.w.print("  (func {s} (", .{f.name});
        for (f.params.items, 0..) |p, i| {
            if (i != 0) try self.w.print(", ", .{});
            try self.type_arena.fmt(p.ty, self.w);
        }
        try self.w.print(") -> ", .{});
        try self.type_arena.fmt(f.result, self.w);
        try self.w.print("\n", .{});
        for (f.blocks.items) |*b| try self.printBlock(b);
        try self.w.print("  )\n", .{});
    }

    fn printBlock(self: *@This(), b: *const Block) anyerror!void {
        try self.w.print("    (block %{d},\n", .{b.id});
        for (b.instrs.items) |*ins| try self.printInstr(ins);
        if (b.term) |t| {
            switch (t) {
                .Return => |rv| if (rv) |v| try self.w.print("      (ret %{d})\n", .{v}) else try self.w.print("      (ret)\n", .{}),
                .Br => |bb| try self.w.print("      (br %{d} )\n", .{bb}),
            }
        } else {
            try self.w.print("      (ret)\n", .{});
        }
        try self.w.print("    )\n", .{});
    }

    fn printInstr(self: *@This(), i: *const Instr) anyerror!void {
        try self.w.print("      (%{d} : ", .{i.result});
        try self.type_arena.fmt(i.ty, self.w);
        try self.w.print(" ", .{});
        switch (i.tag) {
            .ConstInt => try self.w.print("const {d}", .{i.payload.ConstInt}),
            .ConstString => try self.w.print("const \"{s}\"", .{i.payload.ConstString}),
            .Add => {
                const a = i.payload.Add;
                try self.w.print("add %{d} %{d}", .{ a.lhs, a.rhs });
            },
            .Call => {
                const c = i.payload.Call;
                try self.w.print("call {s}", .{c.callee});
                for (c.args) |v| try self.w.print(" %{d}", .{v});
            },
        }
        try self.w.print(")\n", .{});
    }
}; }

test "tir: build minimal function" {
    var gpa = std.heap.page_allocator;
    var arena = types.TypeArena.init(gpa);
    defer arena.deinit();
    const t_i32 = try arena.mk(.{ .I32 = {} });
    const void_t = try arena.mk(.{ .Void = {} });

    var m = Module.init(gpa, &arena);
    defer m.deinit();
    var b = Builder.init(gpa, &m);
    const f = try b.addFunction("main", void_t, &[_]Param{});
    const entry = try b.addBlock(f);
    _ = try b.constInt(entry, t_i32, 42);
    b.retVoid(entry);

    var out = std.array_list.Managed(u8).init(gpa);
    defer out.deinit();
    const writer = out.writer();
    const P = Printer(@TypeOf(writer));
    var p = P.init(writer, &arena);
    try p.printModule(&m);
    const s = try out.toOwnedSlice();
    defer gpa.free(s);
    try std.testing.expect(std.mem.indexOf(u8, s, "(tir.module") != null);
}
