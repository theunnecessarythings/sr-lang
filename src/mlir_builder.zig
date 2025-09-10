const std = @import("std");
const List = std.array_list.Managed;

// A lightweight, generic MLIR textual IR builder.
//
// Goals:
// - Build arbitrary operations (generic form) with results, operands, attributes
// - Support regions and blocks with block arguments
// - Emit valid generic MLIR assembly (quoted op names, attr-dict, types)
// - Keep semantics minimal: types/attrs are treated as textual payloads
//
// Notes:
// - We intentionally target MLIR generic assembly to avoid dialect-specific printers.
//   Example op form: %0 = "arith.constant"() {value = 42 : i32} : () -> i32
// - Regions are printed in the generic syntax as a list of region bodies: ( { ... } ) ( { ... } )
// - Blocks are labeled (^bbN) and may have block arguments

pub const MlirBuilder = struct {
    allocator: std.mem.Allocator,

    module_ops: List(Op),

    next_block_id: usize = 0,
    next_value_id: usize = 0,

    pub fn init(allocator: std.mem.Allocator) MlirBuilder {
        return .{
            .allocator = allocator,
            .module_ops = List(Op).init(allocator),
        };
    }

    pub fn deinit(self: *MlirBuilder) void {
        for (self.module_ops.items) |*op| op.deinit(self.allocator);
        self.module_ops.deinit();
    }

    // Types/Attributes/Values are textual; we do not attempt to model MLIR's type system.

    pub const Type = struct { text: []const u8 };

    pub const Value = struct {
        name: []const u8, // e.g., "%0" or user-provided "%x"
        ty: Type,
    };

    pub const AttrValue = union(enum) {
        // Minimal attribute value set; generic printing covers common cases.
        Int: i64,
        Float: f64,
        Bool: bool,
        String: []const u8, // printed as "..."
        Type: Type, // printed as type literal after colon is caller's job if needed
        Array: List(AttrValue),
        Dict: List(Attr),
        Raw: []const u8, // inserted verbatim (e.g., dense<[...]> : tensor<...>)
    };

    pub const Attr = struct {
        name: []const u8,
        value: AttrValue,
    };

    pub const BlockArg = struct {
        name: []const u8, // with leading '%'
        ty: Type,
    };

    pub const Block = struct {
        label: []const u8, // '^bbN'
        args: List(BlockArg),
        ops: List(Op),

        fn init(allocator: std.mem.Allocator, label: []const u8) Block {
            return .{
                .label = label,
                .args = List(BlockArg).init(allocator),
                .ops = List(Op).init(allocator),
            };
        }

        fn deinit(self: *Block, allocator: std.mem.Allocator) void {
            self.args.deinit();
            for (self.ops.items) |*op| op.deinit(allocator);
            self.ops.deinit();
        }
    };

    pub const Region = struct {
        blocks: List(Block),

        fn init(allocator: std.mem.Allocator) Region {
            return .{ .blocks = List(Block).init(allocator) };
        }

        fn deinit(self: *Region, allocator: std.mem.Allocator) void {
            for (self.blocks.items) |*b| b.deinit(allocator);
            self.blocks.deinit();
        }
    };

    pub const Op = struct {
        // Generic op: "dialect.op"
        name: []const u8, // without quotes; printer will add quotes
        results: List(Value),
        operands: List(Value),
        attrs: List(Attr),
        regions: List(Region),

        fn init(allocator: std.mem.Allocator, name: []const u8) Op {
            return .{
                .name = name,
                .results = List(Value).init(allocator),
                .operands = List(Value).init(allocator),
                .attrs = List(Attr).init(allocator),
                .regions = List(Region).init(allocator),
            };
        }

        fn deinit(self: *Op, allocator: std.mem.Allocator) void {
            for (self.attrs.items) |*a| attrDeinit(allocator, &a.value);
            self.attrs.deinit();
            self.results.deinit();
            self.operands.deinit();
            for (self.regions.items) |*r| r.deinit(allocator);
            self.regions.deinit();
        }
    };

    // Factory helpers
    pub fn makeType(_: *MlirBuilder, text: []const u8) Type {
        return .{ .text = text };
    }

    pub fn makeAnonValue(self: *MlirBuilder, ty: Type) Value {
        const name = self.fmtSymbol("%", self.nextValue());
        return .{ .name = name, .ty = ty };
    }

    pub fn makeNamedValue(_: *MlirBuilder, name: []const u8, ty: Type) Value {
        return .{ .name = name, .ty = ty };
    }

    pub fn newOp(self: *MlirBuilder, name: []const u8) *Op {
        const op = Op.init(self.allocator, name);
        self.module_ops.append(op) catch unreachable;
        return &self.module_ops.items[self.module_ops.items.len - 1];
    }

    pub fn addResult(self: *MlirBuilder, op: *Op, ty: Type) *Value {
        const v = self.makeAnonValue(ty);
        op.results.append(v) catch unreachable;
        return &op.results.items[op.results.items.len - 1];
    }

    pub fn addOperand(_: *MlirBuilder, op: *Op, v: Value) void {
        op.operands.append(v) catch unreachable;
    }

    pub fn addAttr(_: *MlirBuilder, op: *Op, name: []const u8, value: AttrValue) void {
        op.attrs.append(.{ .name = name, .value = value }) catch unreachable;
    }

    pub fn addRegion(self: *MlirBuilder, op: *Op) *Region {
        const region = Region.init(self.allocator);
        op.regions.append(region) catch unreachable;
        return &op.regions.items[op.regions.items.len - 1];
    }

    pub fn addBlock(self: *MlirBuilder, region: *Region) *Block {
        const label = self.fmtSymbol("^bb", self.nextBlock());
        const block = Block.init(self.allocator, label);
        region.blocks.append(block) catch unreachable;
        return &region.blocks.items[region.blocks.items.len - 1];
    }

    pub fn addBlockArg(_: *MlirBuilder, block: *Block, name: []const u8, ty: Type) void {
        block.args.append(.{ .name = name, .ty = ty }) catch unreachable;
    }

    pub fn addNestedOp(self: *MlirBuilder, block: *Block, name: []const u8) *Op {
        const op = Op.init(self.allocator, name);
        block.ops.append(op) catch unreachable;
        return &block.ops.items[block.ops.items.len - 1];
    }

    // Emission
    pub fn emitModule(self: *MlirBuilder, writer: anytype) !void {
        const P = Printer(@TypeOf(writer));
        var p = P{ .w = writer, .indent = 0 };
        try p.writeStr("module {\n");
        p.indent += 2;
        for (self.module_ops.items) |*op| try p.printOp(op);
        p.indent -= 2;
        try p.writeStr("}\n");
    }

    fn Printer(comptime WriterType: type) type {
        return struct {
            w: WriterType,
            indent: usize,

        fn ws(self: *@This()) anyerror!void {
            var i: usize = 0;
            while (i < self.indent) : (i += 1) try self.w.print(" ", .{});
        }

        fn writeStr(self: *@This(), s: []const u8) anyerror!void {
            try self.w.print("{s}", .{s});
        }

        fn printQuoted(self: *@This(), s: []const u8) anyerror!void {
            try self.w.print("\"{s}\"", .{s});
        }

        fn printType(self: *@This(), ty: Type) anyerror!void {
            try self.w.print("{s}", .{ty.text});
        }

        fn printValue(self: *@This(), v: Value) anyerror!void {
            try self.w.print("{s}", .{v.name});
        }

        fn printAttrValue(self: *@This(), v: *const AttrValue) anyerror!void {
            switch (v.*) {
                .Int => |x| try self.w.print("{d}", .{x}),
                .Float => |x| try self.w.print("{d}", .{x}),
                .Bool => |b| try self.w.print("{}", .{b}),
                .String => |s| try self.w.print("\"{s}\"", .{s}),
                .Type => |t| try self.printType(t),
                .Array => |arr| {
                    try self.writeStr("[");
                    var first = true;
                    for (arr.items) |*elem| {
                        if (!first) try self.writeStr(", ") else first = false;
                        try self.printAttrValue(elem);
                    }
                    try self.writeStr("]");
                },
                .Dict => |dict| {
                    try self.writeStr("{");
                    var first = true;
                    for (dict.items) |a| {
                        if (!first) try self.writeStr(", ") else first = false;
                        try self.w.print("{s} = ", .{a.name});
                        try self.printAttrValue(&a.value);
                    }
                    try self.writeStr("}");
                },
                .Raw => |s| try self.writeStr(s),
            }
        }

        fn printAttrDict(self: *@This(), attrs: []const Attr) anyerror!void {
            if (attrs.len == 0) return;
            try self.writeStr(" {");
            var first = true;
            for (attrs) |a| {
                if (!first) try self.writeStr(", ") else first = false;
                try self.w.print("{s} = ", .{a.name});
                try self.printAttrValue(&a.value);
            }
            try self.writeStr("}");
        }

        fn printBlock(self: *@This(), b: *const Block) anyerror!void {
            try self.ws();
            try self.w.print("{s}", .{b.label});
            if (b.args.items.len > 0) {
                try self.writeStr("(");
                var first = true;
                for (b.args.items) |a| {
                    if (!first) try self.writeStr(", ") else first = false;
                    try self.w.print("{s}: ", .{a.name});
                    try self.printType(a.ty);
                }
                try self.writeStr(")");
            }
            try self.writeStr(":\n");
            self.indent += 2;
            for (b.ops.items) |*op| try self.printOp(op);
            self.indent -= 2;
        }

        fn printRegion(self: *@This(), r: *const Region) anyerror!void {
            // Generic region body: ( { <blocks> } )
            try self.writeStr(" ( {\n");
            self.indent += 2;
            for (r.blocks.items) |*b| try self.printBlock(b);
            self.indent -= 2;
            try self.ws();
            try self.writeStr("} )");
        }

        fn printOp(self: *@This(), op: *const Op) anyerror!void {
            try self.ws();
            if (op.results.items.len > 0) {
                var first_res = true;
                for (op.results.items) |res| {
                    if (!first_res) try self.writeStr(", ") else first_res = false;
                    try self.printValue(res);
                }
                try self.writeStr(" = ");
            }
            try self.printQuoted(op.name);
            try self.writeStr("(");
            var first = true;
            for (op.operands.items) |operand| {
                if (!first) try self.writeStr(", ") else first = false;
                try self.printValue(operand);
            }
            try self.writeStr(")");
            try self.printAttrDict(op.attrs.items);

            // Types section
            try self.writeStr(" : (");
            first = true;
            for (op.operands.items) |operand| {
                if (!first) try self.writeStr(", ") else first = false;
                try self.printType(operand.ty);
            }
            try self.writeStr(") -> (");
            first = true;
            for (op.results.items) |res| {
                if (!first) try self.writeStr(", ") else first = false;
                try self.printType(res.ty);
            }
            try self.writeStr(")");

            // Regions, if any
            for (op.regions.items) |*region| {
                try self.printRegion(region);
            }

            try self.writeStr("\n");
        }
        };
    }

    fn attrDeinit(allocator: std.mem.Allocator, v: *AttrValue) void {
        switch (v.*) {
            .Array => |*arr| {
                for (arr.items) |*elem| attrDeinit(allocator, elem);
                arr.deinit();
            },
            .Dict => |*dict| {
                for (dict.items) |*a| attrDeinit(allocator, &a.value);
                dict.deinit();
            },
            else => {},
        }
    }

    fn nextBlock(self: *MlirBuilder) usize {
        const id = self.next_block_id;
        self.next_block_id += 1;
        return id;
    }

    fn nextValue(self: *MlirBuilder) usize {
        const id = self.next_value_id;
        self.next_value_id += 1;
        return id;
    }

    fn fmtSymbol(self: *MlirBuilder, prefix: []const u8, id: usize) []const u8 {
        var buf = List(u8).init(self.allocator);
        buf.writer().print("{s}{d}", .{ prefix, id }) catch unreachable;
        return buf.toOwnedSlice() catch unreachable;
    }
};

// -----------------
// Basic smoke tests
// -----------------

test "mlir builder: empty module" {
    var gpa = std.heap.page_allocator;
    var b = MlirBuilder.init(gpa);
    defer b.deinit();

    var out = List(u8).init(gpa);
    defer out.deinit();
    try b.emitModule(out.writer());
    const s = try out.toOwnedSlice();
    defer gpa.free(s);
    try std.testing.expect(std.mem.startsWith(u8, s, "module {\n"));
}

test "mlir builder: func with constant and return" {
    var gpa = std.heap.page_allocator;
    var b = MlirBuilder.init(gpa);
    defer b.deinit();

    // Build: "func.func" @main() -> i32 { %0 = "arith.constant"() {value = 42 : i32} : () -> i32  "func.return"(%0) : (i32) -> () }
    const func_op = b.newOp("func.func");
    b.addAttr(func_op, "sym_name", .{ .String = "main" });
    b.addAttr(func_op, "function_type", .{ .Raw = "( ) -> i32" }); // generic attr payload

    const r = b.addRegion(func_op);
    const entry = b.addBlock(r);

    const i32t = b.makeType("i32");
    const cst = b.addNestedOp(entry, "arith.constant");
    const cst_res = b.addResult(cst, i32t);
    b.addAttr(cst, "value", .{ .Raw = "42 : i32" });

    const ret = b.addNestedOp(entry, "func.return");
    b.addOperand(ret, cst_res.*);

    var out = List(u8).init(gpa);
    defer out.deinit();
    try b.emitModule(out.writer());
    const s = try out.toOwnedSlice();
    defer gpa.free(s);
    try std.testing.expect(std.mem.indexOf(u8, s, "\"func.func\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, s, "\"arith.constant\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, s, "\"func.return\"") != null);
}
