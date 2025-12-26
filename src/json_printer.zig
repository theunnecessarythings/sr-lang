const std = @import("std");
const ast = @import("ast.zig");

pub const JsonPrinter = struct {
    stream: std.json.Stringify,
    exprs: *ast.ExprStore,
    stmts: *ast.StmtStore,
    pats: *ast.PatternStore,

    pub fn init(writer: anytype, exprs: *ast.ExprStore, stmts: *ast.StmtStore, pats: *ast.PatternStore) JsonPrinter {
        return .{ .stream = .{ .writer = writer, .options = .{ .whitespace = .indent_2 } }, .exprs = exprs, .stmts = stmts, .pats = pats };
    }

    // --- Helpers ---
    inline fn s(self: *const JsonPrinter, id: ast.StrId) []const u8 {
        return self.exprs.strs.get(id);
    }
    inline fn key(self: *JsonPrinter, k: []const u8) !void {
        try self.stream.objectField(k);
    }
    inline fn val(self: *JsonPrinter, k: []const u8, v: anytype) !void {
        try self.key(k);
        const T = @TypeOf(v);
        const ti = @typeInfo(T);
        if (ti == .pointer and ti.pointer.size == .slice) {
            if (ti.pointer.child == u8) {
                try self.stream.print("{s}", .{v});
            } else {
                try self.stream.print("{any}", .{v});
            }
        } else {
            try self.stream.print("{}", .{v});
        }
    }
    inline fn str(self: *JsonPrinter, k: []const u8, id: ast.StrId) !void {
        try self.key(k);
        try self.stream.write(self.s(id));
    }
    inline fn nullVal(self: *JsonPrinter, k: []const u8) !void {
        try self.key(k);
        try self.stream.write("null");
    }
    inline fn start(self: *JsonPrinter, k: []const u8) !void {
        try self.stream.beginObject();
        try self.val("kind", k);
    }
    inline fn end(self: *JsonPrinter) !void {
        try self.stream.endObject();
    }

    fn loc(self: *JsonPrinter, id: ast.LocId) !void {
        const l = self.exprs.locs.get(id);
        try self.key("loc");
        try self.stream.beginObject();
        try self.val("start", l.start);
        try self.val("end", l.end);
        try self.end();
    }
    fn optLoc(self: *JsonPrinter, id: ast.OptLocId) !void {
        if (id.isNone()) try self.nullVal("loc") else try self.loc(id.unwrap());
    }

    fn list(self: *JsonPrinter, k: []const u8, items: anytype, comptime f: anytype) !void {
        try self.key(k);
        try self.stream.beginArray();
        for (items) |i| try f(self, i);
        try self.stream.endArray();
    }

    // --- Comptime Reflected Printer ---
    fn printStruct(self: *JsonPrinter, value: anytype) anyerror!void {
        inline for (@typeInfo(@TypeOf(value)).@"struct".fields) |f| {
            const v = @field(value, f.name);
            const T = f.type;
            if (comptime std.mem.eql(u8, f.name, "kind")) continue; // Skip discriminant
            if (comptime std.mem.eql(u8, f.name, "loc")) {
                try self.loc(v);
                continue;
            }

            if (T == ast.ExprId) {
                try self.key(f.name);
                try self.printExpr(v);
            } else if (T == ast.StmtId) {
                try self.key(f.name);
                try self.printStmt(v);
            } else if (T == ast.DeclId) {
                try self.key(f.name);
                try self.printDecl(v);
            } else if (T == ast.PatternId) {
                try self.key(f.name);
                try self.printPattern(v);
            } else if (T == ast.StrId) {
                try self.str(f.name, v);
            }

            // Ranges
            else if (T == ast.RangeExpr) {
                try self.list(f.name, self.exprs.expr_pool.slice(v), printExpr);
            } else if (T == ast.RangeStmt) {
                try self.list(f.name, self.stmts.stmt_pool.slice(v), printStmt);
            } else if (T == ast.RangeDecl) {
                try self.list(f.name, self.exprs.decl_pool.slice(v), printDecl);
            } else if (T == ast.RangePat) {
                try self.list(f.name, self.pats.pat_pool.slice(v), printPattern);
            } else if (T == ast.RangeParam) {
                try self.list(f.name, self.exprs.param_pool.slice(v), printParam);
            } else if (T == ast.RangeField) {
                try self.list(f.name, self.exprs.sfield_pool.slice(v), printStructField);
            } else if (T == ast.RangeVariantField) {
                try self.list(f.name, self.exprs.vfield_pool.slice(v), printVariantField);
            } else if (T == ast.RangeEnumField) {
                try self.list(f.name, self.exprs.efield_pool.slice(v), printEnumField);
            } else if (T == ast.RangePathSeg) {
                try self.list(f.name, self.pats.seg_pool.slice(v), printPathSeg);
            } else if (T == ast.RangeMatchArm) {
                try self.list(f.name, self.exprs.arm_pool.slice(v), printMatchArm);
            } else if (T == ast.RangeAttr) {
                try self.list(f.name, self.exprs.attr_pool.slice(v), printAttr);
            } else if (T == ast.RangeStructFieldValue) {
                try self.list(f.name, self.exprs.sfv_pool.slice(v), printStructLitField);
            } else if (T == ast.RangePatField) {
                try self.list(f.name, self.pats.field_pool.slice(v), printPatField);
            }

            // Optionals
            else if (T == ast.OptExprId) {
                if (v.isNone()) try self.nullVal(f.name) else {
                    try self.key(f.name);
                    try self.printExpr(v.unwrap());
                }
            } else if (T == ast.OptPatternId) {
                if (v.isNone()) try self.nullVal(f.name) else {
                    try self.key(f.name);
                    try self.printPattern(v.unwrap());
                }
            } else if (T == ast.OptStrId) {
                if (v.isNone()) try self.nullVal(f.name) else try self.str(f.name, v.unwrap());
            } else if (T == ast.OptLocId) {
                try self.optLoc(v);
            } else if (T == ast.OptRangeAttr) {
                if (v.isNone()) try self.nullVal(f.name) else try self.list(f.name, self.exprs.attr_pool.slice(v.asRange()), printAttr);
            } else if (T == ast.OptRangeMethodPathSeg) {
                if (v.isNone()) try self.nullVal(f.name) else try self.list(f.name, self.exprs.method_path_pool.slice(v.asRange()), printMethodPathSeg);
            }

            // Primitives & Special
            else if (@typeInfo(T) == .@"enum") {
                try self.val(f.name, @tagName(v));
            } else if (T == ast.RangeMlirPiece) {
                try self.key(f.name);
                try self.stream.beginArray();
                for (self.exprs.mlir_piece_pool.slice(v)) |pid| {
                    const p = self.exprs.MlirPiece.get(pid);
                    try self.stream.beginObject();
                    try self.val("kind", @tagName(p.kind));
                    try self.str("text", p.text);
                    try self.end();
                }
                try self.stream.endArray();
            } else {
                try self.val(f.name, v);
            }
        }
    }

    // --- Main Entry Points ---
    pub fn printUnit(self: *JsonPrinter, unit: *const ast.Unit) !void {
        try self.start("Unit");
        try self.printStruct(unit.*);
        try self.end();
    }
    fn printDecl(self: *JsonPrinter, id: ast.DeclId) !void {
        try self.start("Decl");
        try self.printStruct(self.exprs.Decl.get(id));
        try self.end();
    }
    fn printStmt(self: *JsonPrinter, id: ast.StmtId) !void {
        const k = self.stmts.kind(id);
        try self.start(@tagName(k));
        switch (k) {
            inline else => |tag| try self.printStruct(self.stmts.get(tag, id)),
        }
        try self.end();
    }
    fn printPattern(self: *JsonPrinter, id: ast.PatternId) !void {
        const k = self.pats.kind(id);
        try self.start(@tagName(k));
        switch (k) {
            inline else => |tag| try self.printStruct(self.pats.get(tag, id)),
        }
        try self.end();
    }

    pub fn printExpr(self: *JsonPrinter, id: ast.ExprId) !void {
        const k = self.exprs.kind(id);
        try self.start(@tagName(k));
        switch (k) {
            .Literal => { // Manual handling for Union data
                const n = self.exprs.get(.Literal, id);
                try self.loc(n.loc);
                try self.val("literal_kind", @tagName(n.kind));
                try self.key("value");
                switch (n.data) {
                    .none => try self.stream.write("null"),
                    .bool => |b| try self.stream.print("{}", .{b}),
                    .char => |c| try self.stream.print("{}", .{c}),
                    .string => |st| try self.stream.write(self.s(st)),
                    .int => |i| try self.stream.print("{}", .{i.value}),
                    .float => |f| try self.stream.print("{}", .{f.value}),
                    .imaginary => |m| try self.stream.print("{}", .{m.value}),
                }
            },
            .MapLit => { // Manual handling for KeyValue pool
                const n = self.exprs.get(.MapLit, id);
                try self.loc(n.loc);
                try self.key("entries");
                try self.stream.beginArray();
                for (self.exprs.kv_pool.slice(n.entries)) |kv_id| {
                    const kv = self.exprs.KeyValue.get(kv_id);
                    try self.stream.beginObject();
                    try self.loc(kv.loc);
                    try self.key("key");
                    try self.printExpr(kv.key);
                    try self.key("value");
                    try self.printExpr(kv.value);
                    try self.end();
                }
                try self.stream.endArray();
            },
            inline else => |tag| try self.printStruct(self.exprs.get(tag, id)),
        }
        try self.end();
    }

    // --- Sub-Node Helpers ---
    fn printAttr(self: *JsonPrinter, id: ast.AttributeId) !void {
        try self.stream.beginObject();
        try self.printStruct(self.exprs.Attribute.get(id));
        try self.end();
    }
    fn printParam(self: *JsonPrinter, id: ast.ParamId) !void {
        try self.stream.beginObject();
        try self.printStruct(self.exprs.Param.get(id));
        try self.end();
    }
    fn printStructField(self: *JsonPrinter, id: ast.StructFieldId) !void {
        try self.stream.beginObject();
        try self.printStruct(self.exprs.StructField.get(id));
        try self.end();
    }
    fn printEnumField(self: *JsonPrinter, id: ast.EnumFieldId) !void {
        try self.stream.beginObject();
        try self.printStruct(self.exprs.EnumField.get(id));
        try self.end();
    }
    fn printMatchArm(self: *JsonPrinter, id: ast.MatchArmId) !void {
        try self.stream.beginObject();
        try self.printStruct(self.exprs.MatchArm.get(id));
        try self.end();
    }
    fn printPathSeg(self: *JsonPrinter, id: ast.PathSegId) !void {
        try self.stream.beginObject();
        try self.printStruct(self.pats.PathSeg.get(id));
        try self.end();
    }
    fn printMethodPathSeg(self: *JsonPrinter, id: ast.MethodPathSegId) !void {
        try self.stream.beginObject();
        try self.printStruct(self.exprs.MethodPathSeg.get(id));
        try self.end();
    }
    fn printPatField(self: *JsonPrinter, id: ast.PatFieldId) !void {
        try self.stream.beginObject();
        try self.printStruct(self.pats.StructField.get(id));
        try self.end();
    }
    fn printStructLitField(self: *JsonPrinter, id: ast.StructFieldValueId) !void {
        try self.stream.beginObject();
        try self.printStruct(self.exprs.StructFieldValue.get(id));
        try self.end();
    }

    fn printVariantField(self: *JsonPrinter, id: ast.VariantFieldId) !void {
        const f = self.exprs.VariantField.get(id);
        try self.stream.beginObject();
        try self.loc(f.loc);
        try self.str("name", f.name);
        try self.list("attrs", self.exprs.attr_pool.slice(f.attrs.asRange()), printAttr);
        try self.val("payload_kind", @tagName(f.payload_kind));
        switch (f.payload_kind) {
            .none => {},
            .tuple => try self.list("payload_elems", self.exprs.expr_pool.slice(f.payload_elems.asRange()), printExpr),
            .@"struct" => try self.list("payload_fields", self.exprs.sfield_pool.slice(f.payload_fields.asRange()), printStructField),
        }
        if (f.value.isNone()) try self.nullVal("value") else {
            try self.key("value");
            try self.printExpr(f.value.unwrap());
        }
        try self.end();
    }
};
