const std = @import("std");
const ast = @import("ast.zig");

const JsonStream = std.json.Stream;

/// Helper that walks AST stores and renders them as JSON.
pub const JsonPrinter = struct {
    /// JSON stream writer used for emitting nodes.
    stream: std.json.Stringify,
    /// Expression store supplying nodes and metadata.
    exprs: *ast.ExprStore,
    /// Statement store referenced while printing expressions.
    stmts: *ast.StmtStore,
    /// Pattern store for match-related metadata.
    pats: *ast.PatternStore,

    /// Build a JSON printer that targets `writer` and walks the provided AST stores.
    pub fn init(writer: anytype, exprs: *ast.ExprStore, stmts: *ast.StmtStore, pats: *ast.PatternStore) JsonPrinter {
        return .{
            .stream = .{ .writer = writer, .options = .{ .whitespace = .indent_2 } },
            .exprs = exprs,
            .stmts = stmts,
            .pats = pats,
        };
    }

    /// Resolve string identifier `id` from the shared interner.
    inline fn s(self: *const JsonPrinter, id: ast.StrId) []const u8 {
        return self.exprs.strs.get(id);
    }

    /// Serialize `value` into JSON using the configured writer.
    inline fn writeValue(self: *JsonPrinter, value: anytype) anyerror!void {
        try self.stream.print("{}", .{value});
    }

    /// Emit the `null` literal.
    inline fn writeNull(self: *JsonPrinter) anyerror!void {
        try self.stream.write("null");
    }

    /// Print the span information for `loc_id`.
    fn printLoc(self: *JsonPrinter, loc_id: ast.LocId) !void {
        const loc = self.exprs.locs.get(loc_id);
        try self.stream.objectField("loc");
        try self.stream.beginObject();
        try self.stream.objectField("start");
        try self.writeValue(loc.start);
        try self.stream.objectField("end");
        try self.writeValue(loc.end);
        try self.stream.endObject();
    }

    /// Print optional location metadata when present.
    fn printOptLoc(self: *JsonPrinter, loc_id: ast.OptLocId) !void {
        if (loc_id.isNone()) {
            try self.stream.objectField("loc");
            try self.writeNull();
        } else {
            try self.printLoc(loc_id.unwrap());
        }
    }

    /// Dump the entire AST unit as JSON.
    pub fn printUnit(self: *JsonPrinter, unit: *const ast.Unit) anyerror!void {
        try self.stream.beginObject();
        try self.stream.objectField("kind");
        try self.stream.write("Unit");

        if (!unit.package_name.isNone()) {
            try self.stream.objectField("package_name");
            try self.stream.write(self.s(unit.package_name.unwrap()));
        } else {
            try self.stream.objectField("package_name");
            try self.writeNull();
        }
        try self.printOptLoc(unit.package_loc);

        try self.stream.objectField("decls");
        try self.printDeclRange(unit.decls);

        try self.stream.endObject();
    }

    /// Emit JSON array entries for every declaration in `r`.
    fn printDeclRange(self: *JsonPrinter, r: ast.RangeDecl) anyerror!void {
        try self.stream.beginArray();
        const decl_ids = self.exprs.decl_pool.slice(r);
        for (decl_ids) |did| {
            try self.printDecl(did);
        }
        try self.stream.endArray();
    }

    /// Serialize declaration `id` and its children.
    fn printDecl(self: *JsonPrinter, id: ast.DeclId) anyerror!void {
        const row = self.exprs.Decl.get(id);
        try self.stream.beginObject();
        try self.stream.objectField("kind");
        try self.stream.write("Decl");
        try self.printLoc(row.loc);
        try self.stream.objectField("is_const");
        try self.writeValue(row.flags.is_const);

        try self.stream.objectField("pattern");
        if (!row.pattern.isNone()) {
            try self.printPattern(row.pattern.unwrap());
        } else {
            try self.writeNull();
        }

        try self.stream.objectField("method_path");
        if (!row.method_path.isNone()) {
            try self.stream.beginArray();
            const seg_ids = self.exprs.method_path_pool.slice(row.method_path.asRange());
            for (seg_ids) |sid| {
                const seg = self.exprs.MethodPathSeg.get(sid);
                try self.stream.beginObject();
                try self.stream.objectField("name");
                try self.stream.write(self.s(seg.name));
                try self.stream.objectField("loc");
                try self.stream.beginObject();
                const loc = self.exprs.locs.get(seg.loc);
                try self.stream.objectField("start");
                try self.writeValue(loc.start);
                try self.stream.objectField("end");
                try self.writeValue(loc.end);
                try self.stream.endObject();
                try self.stream.endObject();
            }
            try self.stream.endArray();
        } else {
            try self.writeNull();
        }

        try self.stream.objectField("type");
        if (!row.ty.isNone()) {
            try self.printExpr(row.ty.unwrap());
        } else {
            try self.writeNull();
        }

        try self.stream.objectField("value");
        try self.printExpr(row.value);

        try self.stream.endObject();
    }

    /// Serialize statement `id` into JSON form.
    fn printStmt(self: *JsonPrinter, id: ast.StmtId) anyerror!void {
        const kind = self.stmts.kind(id);
        try self.stream.beginObject();
        try self.stream.objectField("kind");
        try self.stream.write(@tagName(kind));

        switch (kind) {
            .Expr => {
                const row = self.stmts.get(.Expr, id);
                try self.stream.objectField("expr");
                try self.printExpr(row.expr);
            },
            .Decl => {
                const row = self.stmts.get(.Decl, id);
                try self.stream.objectField("decl");
                try self.printDecl(row.decl);
            },
            .Assign => {
                const row = self.stmts.get(.Assign, id);
                try self.printLoc(row.loc);
                try self.stream.objectField("left");
                try self.printExpr(row.left);
                try self.stream.objectField("right");
                try self.printExpr(row.right);
            },
            .Insert => {
                const row = self.stmts.get(.Insert, id);
                try self.printLoc(row.loc);
                try self.stream.objectField("expr");
                try self.printExpr(row.expr);
            },
            .Return => {
                const row = self.stmts.get(.Return, id);
                try self.printLoc(row.loc);
                try self.stream.objectField("value");
                if (!row.value.isNone())
                    try self.printExpr(row.value.unwrap())
                else
                    try self.writeNull();
            },
            .Break => {
                const row = self.stmts.get(.Break, id);
                try self.printLoc(row.loc);
                try self.stream.objectField("label");
                if (!row.label.isNone())
                    try self.stream.write(self.s(row.label.unwrap()))
                else
                    try self.writeNull();
                try self.stream.objectField("value");
                if (!row.value.isNone())
                    try self.printExpr(row.value.unwrap())
                else
                    try self.writeNull();
            },
            .Continue => {
                const row = self.stmts.get(.Continue, id);
                try self.printLoc(row.loc);
            },
            .Unreachable => {
                const row = self.stmts.get(.Unreachable, id);
                try self.printLoc(row.loc);
            },
            .Defer => {
                const row = self.stmts.get(.Defer, id);
                try self.printLoc(row.loc);
                try self.stream.objectField("expr");
                try self.printExpr(row.expr);
            },
            .ErrDefer => {
                const row = self.stmts.get(.ErrDefer, id);
                try self.printLoc(row.loc);
                try self.stream.objectField("expr");
                try self.printExpr(row.expr);
            },
        }
        try self.stream.endObject();
    }

    /// Serialize expression `id`, recursing into nested nodes.
    pub fn printExpr(self: *JsonPrinter, id: ast.ExprId) anyerror!void {
        const kind = self.exprs.kind(id);
        try self.stream.beginObject();
        try self.stream.objectField("kind");
        try self.stream.write(@tagName(kind));

        switch (kind) {
            .Literal => {
                const node = self.exprs.get(.Literal, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("literal_kind");
                try self.stream.write(@tagName(node.kind));
                try self.stream.objectField("value");
                switch (node.data) {
                    .none => try self.stream.write("null"),
                    .bool => |b| try self.writeValue(b),
                    .char => |c| try self.writeValue(c),
                    .string => |sid| try self.stream.write(self.s(sid)),
                    .int => |info| try self.writeValue(info.value),
                    .float => |info| try self.writeValue(info.value),
                    .imaginary => |info| try self.writeValue(info.value),
                }
            },
            .Ident => {
                const node = self.exprs.get(.Ident, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("name");
                try self.stream.write(self.s(node.name));
            },
            .Unary => {
                const node = self.exprs.get(.Unary, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("op");
                try self.stream.write(@tagName(node.op));
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .Binary => {
                const node = self.exprs.get(.Binary, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("op");
                try self.stream.write(@tagName(node.op));
                try self.stream.objectField("wrap");
                try self.writeValue(node.wrap);
                try self.stream.objectField("saturate");
                try self.writeValue(node.saturate);
                try self.stream.objectField("left");
                try self.printExpr(node.left);
                try self.stream.objectField("right");
                try self.printExpr(node.right);
            },
            .Range => {
                const node = self.exprs.get(.Range, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("inclusive_right");
                try self.writeValue(node.inclusive_right);
                try self.stream.objectField("start");
                if (!node.start.isNone())
                    try self.printExpr(node.start.unwrap())
                else
                    try self.writeNull();
                try self.stream.objectField("end");
                if (!node.end.isNone())
                    try self.printExpr(node.end.unwrap())
                else
                    try self.writeNull();
            },
            .Deref => {
                const node = self.exprs.get(.Deref, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .ArrayLit => {
                const node = self.exprs.get(.ArrayLit, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elems");
                try self.printExprRange(node.elems);
            },
            .TupleLit => {
                const node = self.exprs.get(.TupleLit, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elems");
                try self.printExprRange(node.elems);
            },
            .MapLit => {
                const node = self.exprs.get(.MapLit, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("entries");
                try self.stream.beginArray();
                const entries = self.exprs.kv_pool.slice(node.entries);
                for (entries) |kv_id| {
                    const kv = self.exprs.KeyValue.get(kv_id);
                    try self.stream.beginObject();
                    try self.printLoc(kv.loc);
                    try self.stream.objectField("key");
                    try self.printExpr(kv.key);
                    try self.stream.objectField("value");
                    try self.printExpr(kv.value);
                    try self.stream.endObject();
                }
                try self.stream.endArray();
            },
            .Call => {
                const node = self.exprs.get(.Call, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("callee");
                try self.printExpr(node.callee);
                try self.stream.objectField("args");
                try self.printExprRange(node.args);
            },
            .IndexAccess => {
                const node = self.exprs.get(.IndexAccess, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("collection");
                try self.printExpr(node.collection);
                try self.stream.objectField("index");
                try self.printExpr(node.index);
            },
            .FieldAccess => {
                const node = self.exprs.get(.FieldAccess, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("parent");
                try self.printExpr(node.parent);
                try self.stream.objectField("field");
                try self.stream.write(self.s(node.field));
                try self.stream.objectField("is_tuple");
                try self.writeValue(node.is_tuple);
            },
            .StructLit => {
                const node = self.exprs.get(.StructLit, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("type");
                if (!node.ty.isNone())
                    try self.printExpr(node.ty.unwrap())
                else
                    try self.writeNull();
                try self.stream.objectField("fields");
                try self.stream.beginArray();
                const fields = self.exprs.sfv_pool.slice(node.fields);
                for (fields) |fid| {
                    const field = self.exprs.StructFieldValue.get(fid);
                    try self.stream.beginObject();
                    try self.printLoc(field.loc);
                    try self.stream.objectField("name");
                    if (!field.name.isNone())
                        try self.stream.write(self.s(field.name.unwrap()))
                    else
                        try self.writeNull();
                    try self.stream.objectField("value");
                    try self.printExpr(field.value);
                    try self.stream.endObject();
                }
                try self.stream.endArray();
            },
            .FunctionLit => {
                const node = self.exprs.get(.FunctionLit, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("is_proc");
                try self.writeValue(node.flags.is_proc);
                try self.stream.objectField("is_async");
                try self.writeValue(node.flags.is_async);
                try self.stream.objectField("is_variadic");
                try self.writeValue(node.flags.is_variadic);
                try self.stream.objectField("is_extern");
                try self.writeValue(node.flags.is_extern);
                try self.stream.objectField("attrs");
                try self.printAttrs(node.attrs);
                try self.stream.objectField("params");
                try self.printParams(node.params);
                try self.stream.objectField("result_ty");
                if (!node.result_ty.isNone())
                    try self.printExpr(node.result_ty.unwrap())
                else
                    try self.writeNull();
                try self.stream.objectField("body");
                if (!node.body.isNone())
                    try self.printExpr(node.body.unwrap())
                else
                    try self.writeNull();
                try self.stream.objectField("raw_asm");
                if (!node.raw_asm.isNone())
                    try self.stream.write(self.s(node.raw_asm.unwrap()))
                else
                    try self.writeNull();
            },
            .Block => {
                const node = self.exprs.get(.Block, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("items");
                try self.stream.beginArray();
                const stmts = self.stmts.stmt_pool.slice(node.items);
                for (stmts) |sid| try self.printStmt(sid);
                try self.stream.endArray();
            },
            .ComptimeBlock => {
                const node = self.exprs.get(.ComptimeBlock, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("block");
                try self.printExpr(node.block);
            },
            .CodeBlock => {
                const node = self.exprs.get(.CodeBlock, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("block");
                try self.printExpr(node.block);
            },
            .AsyncBlock => {
                const node = self.exprs.get(.AsyncBlock, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("body");
                try self.printExpr(node.body);
            },
            .MlirBlock => {
                const node = self.exprs.get(.MlirBlock, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("mlir_kind");
                try self.stream.write(@tagName(node.kind));
                try self.stream.objectField("text");
                try self.stream.write(self.s(node.text));
                try self.stream.objectField("pieces");
                try self.stream.beginArray();
                const pieces = self.exprs.mlir_piece_pool.slice(node.pieces);
                for (pieces) |pid| {
                    const piece = self.exprs.MlirPiece.get(pid);
                    try self.stream.beginObject();
                    try self.stream.objectField("kind");
                    try self.stream.write(@tagName(piece.kind));
                    try self.stream.objectField("text");
                    try self.stream.write(self.s(piece.text));
                    try self.stream.endObject();
                }
                try self.stream.endArray();
                try self.stream.objectField("args");
                try self.printExprRange(node.args);
            },
            .Insert => {
                const node = self.exprs.get(.Insert, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .Return => {
                const node = self.exprs.get(.Return, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("value");
                if (!node.value.isNone())
                    try self.printExpr(node.value.unwrap())
                else
                    try self.writeNull();
            },
            .If => {
                const node = self.exprs.get(.If, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("cond");
                try self.printExpr(node.cond);
                try self.stream.objectField("then_block");
                try self.printExpr(node.then_block);
                try self.stream.objectField("else_block");
                if (!node.else_block.isNone())
                    try self.printExpr(node.else_block.unwrap())
                else
                    try self.writeNull();
            },
            .While => {
                const node = self.exprs.get(.While, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("is_pattern");
                try self.writeValue(node.is_pattern);
                try self.stream.objectField("label");
                if (!node.label.isNone())
                    try self.stream.write(self.s(node.label.unwrap()))
                else
                    try self.writeNull();
                try self.stream.objectField("pattern");
                if (!node.pattern.isNone())
                    try self.printPattern(node.pattern.unwrap())
                else
                    try self.writeNull();
                try self.stream.objectField("cond");
                if (!node.cond.isNone())
                    try self.printExpr(node.cond.unwrap())
                else
                    try self.writeNull();
                try self.stream.objectField("body");
                try self.printExpr(node.body);
            },
            .For => {
                const node = self.exprs.get(.For, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("label");
                if (!node.label.isNone())
                    try self.stream.write(self.s(node.label.unwrap()))
                else
                    try self.writeNull();
                try self.stream.objectField("pattern");
                try self.printPattern(node.pattern);
                try self.stream.objectField("iterable");
                try self.printExpr(node.iterable);
                try self.stream.objectField("body");
                try self.printExpr(node.body);
            },
            .Match => {
                const node = self.exprs.get(.Match, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
                try self.stream.objectField("arms");
                try self.stream.beginArray();
                const arms = self.exprs.arm_pool.slice(node.arms);
                for (arms) |aid| {
                    const arm = self.exprs.MatchArm.get(aid);
                    try self.stream.beginObject();
                    try self.printLoc(arm.loc);
                    try self.stream.objectField("pattern");
                    try self.printPattern(arm.pattern);
                    try self.stream.objectField("guard");
                    if (!arm.guard.isNone())
                        try self.printExpr(arm.guard.unwrap())
                    else
                        try self.writeNull();
                    try self.stream.objectField("body");
                    try self.printExpr(arm.body);
                    try self.stream.endObject();
                }
                try self.stream.endArray();
            },
            .Break => {
                const node = self.exprs.get(.Break, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("label");
                if (!node.label.isNone())
                    try self.stream.write(self.s(node.label.unwrap()))
                else
                    try self.writeNull();
                try self.stream.objectField("value");
                if (!node.value.isNone())
                    try self.printExpr(node.value.unwrap())
                else
                    try self.writeNull();
            },
            .Continue => {
                const node = self.exprs.get(.Continue, id);
                try self.printLoc(node.loc);
            },
            .Unreachable => {
                const node = self.exprs.get(.Unreachable, id);
                try self.printLoc(node.loc);
            },
            .NullLit => {
                const node = self.exprs.get(.NullLit, id);
                try self.printLoc(node.loc);
            },
            .UndefLit => {
                const node = self.exprs.get(.UndefLit, id);
                try self.printLoc(node.loc);
            },
            .TypeType => {
                const node = self.exprs.get(.TypeType, id);
                try self.printLoc(node.loc);
            },
            .AnyType => {
                const node = self.exprs.get(.AnyType, id);
                try self.printLoc(node.loc);
            },
            .NoreturnType => {
                const node = self.exprs.get(.NoreturnType, id);
                try self.printLoc(node.loc);
            },
            .Defer => {
                const node = self.exprs.get(.Defer, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .ErrDefer => {
                const node = self.exprs.get(.ErrDefer, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .ErrUnwrap => {
                const node = self.exprs.get(.ErrUnwrap, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .OptionalUnwrap => {
                const node = self.exprs.get(.OptionalUnwrap, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .Await => {
                const node = self.exprs.get(.Await, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .Closure => {
                const node = self.exprs.get(.Closure, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("params");
                try self.printParams(node.params);
                try self.stream.objectField("result_ty");
                if (!node.result_ty.isNone())
                    try self.printExpr(node.result_ty.unwrap())
                else
                    try self.writeNull();
                try self.stream.objectField("body");
                try self.printExpr(node.body);
            },
            .Cast => {
                const node = self.exprs.get(.Cast, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("cast_kind");
                try self.stream.write(@tagName(node.kind));
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
                try self.stream.objectField("type");
                try self.printExpr(node.ty);
            },
            .Catch => {
                const node = self.exprs.get(.Catch, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
                try self.stream.objectField("binding_name");
                if (!node.binding_name.isNone())
                    try self.stream.write(self.s(node.binding_name.unwrap()))
                else
                    try self.writeNull();
                try self.printOptLoc(node.binding_loc);
                try self.stream.objectField("handler");
                try self.printExpr(node.handler);
            },
            .Import => {
                const node = self.exprs.get(.Import, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("path");
                try self.stream.write(self.s(node.path));
            },
            .TypeOf => {
                const node = self.exprs.get(.TypeOf, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .TupleType => {
                const node = self.exprs.get(.TupleType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elems");
                try self.printExprRange(node.elems);
            },
            .ArrayType => {
                const node = self.exprs.get(.ArrayType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elem");
                try self.printExpr(node.elem);
                try self.stream.objectField("size");
                try self.printExpr(node.size);
            },
            .DynArrayType => {
                const node = self.exprs.get(.DynArrayType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elem");
                try self.printExpr(node.elem);
            },
            .MapType => {
                const node = self.exprs.get(.MapType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("key");
                try self.printExpr(node.key);
                try self.stream.objectField("value");
                try self.printExpr(node.value);
            },
            .SliceType => {
                const node = self.exprs.get(.SliceType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("is_const");
                try self.writeValue(node.is_const);
                try self.stream.objectField("elem");
                try self.printExpr(node.elem);
            },
            .OptionalType => {
                const node = self.exprs.get(.OptionalType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elem");
                try self.printExpr(node.elem);
            },
            .ErrorSetType => {
                const node = self.exprs.get(.ErrorSetType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("err");
                try self.printExpr(node.err);
                try self.stream.objectField("value");
                try self.printExpr(node.value);
            },
            .StructType => {
                const node = self.exprs.get(.StructType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("is_extern");
                try self.writeValue(node.is_extern);
                try self.stream.objectField("attrs");
                try self.printAttrs(node.attrs);
                try self.stream.objectField("fields");
                try self.printStructFieldRange(node.fields);
            },
            .EnumType => {
                const node = self.exprs.get(.EnumType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("is_extern");
                try self.writeValue(node.is_extern);
                try self.stream.objectField("attrs");
                try self.printAttrs(node.attrs);
                try self.stream.objectField("discriminant");
                if (!node.discriminant.isNone())
                    try self.printExpr(node.discriminant.unwrap())
                else
                    try self.writeNull();
                try self.stream.objectField("fields");
                try self.stream.beginArray();
                const fields = self.exprs.efield_pool.slice(node.fields);
                for (fields) |eid| {
                    const field = self.exprs.EnumField.get(eid);
                    try self.stream.beginObject();
                    try self.printLoc(field.loc);
                    try self.stream.objectField("name");
                    try self.stream.write(self.s(field.name));
                    try self.stream.objectField("attrs");
                    try self.printAttrs(field.attrs);
                    try self.stream.objectField("value");
                    if (!field.value.isNone())
                        try self.printExpr(field.value.unwrap())
                    else
                        try self.writeNull();
                    try self.stream.endObject();
                }
                try self.stream.endArray();
            },
            .VariantType, .ErrorType => {
                const node = self.exprs.get(.VariantType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("fields");
                try self.printVariantFieldRange(node.fields);
            },
            .UnionType => {
                const node = self.exprs.get(.UnionType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("is_extern");
                try self.writeValue(node.is_extern);
                try self.stream.objectField("attrs");
                try self.printAttrs(node.attrs);
                try self.stream.objectField("fields");
                try self.printStructFieldRange(node.fields);
            },
            .PointerType => {
                const node = self.exprs.get(.PointerType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("is_const");
                try self.writeValue(node.is_const);
                try self.stream.objectField("elem");
                try self.printExpr(node.elem);
            },
            .SimdType => {
                const node = self.exprs.get(.SimdType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elem");
                try self.printExpr(node.elem);
                try self.stream.objectField("lanes");
                try self.printExpr(node.lanes);
            },
            .ComplexType => {
                const node = self.exprs.get(.ComplexType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elem");
                try self.printExpr(node.elem);
            },
            .TensorType => {
                const node = self.exprs.get(.TensorType, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elem");
                try self.printExpr(node.elem);
                try self.stream.objectField("shape");
                try self.printExprRange(node.shape);
            },
        }
        try self.stream.endObject();
    }

    /// Print an array of expressions described by `r`.
    fn printExprRange(self: *JsonPrinter, r: ast.RangeExpr) anyerror!void {
        try self.stream.beginArray();
        const ids = self.exprs.expr_pool.slice(r);
        for (ids) |eid| try self.printExpr(eid);
        try self.stream.endArray();
    }

    /// Serialize attribute list `opt_r` when present.
    fn printAttrs(self: *JsonPrinter, opt_r: ast.OptRangeAttr) anyerror!void {
        if (!opt_r.isNone()) {
            try self.stream.beginArray();
            const attrs = self.exprs.attr_pool.slice(opt_r.asRange());
            for (attrs) |aid| {
                const attr = self.exprs.Attribute.get(aid);
                try self.stream.beginObject();
                try self.printLoc(attr.loc);
                try self.stream.objectField("name");
                try self.stream.write(self.s(attr.name));
                try self.stream.objectField("value");
                if (!attr.value.isNone())
                    try self.printExpr(attr.value.unwrap())
                else
                    try self.writeNull();
                try self.stream.endObject();
            }
            try self.stream.endArray();
        } else {
            try self.writeNull();
        }
    }

    /// Serialize a sequence of parameters `r`.
    fn printParams(self: *JsonPrinter, r: ast.RangeParam) anyerror!void {
        try self.stream.beginArray();
        const params = self.exprs.param_pool.slice(r);
        for (params) |pid| {
            const param = self.exprs.Param.get(pid);
            try self.stream.beginObject();
            try self.printLoc(param.loc);
            try self.stream.objectField("attrs");
            try self.printAttrs(param.attrs);
            try self.stream.objectField("pattern");
            if (!param.pat.isNone())
                try self.printPattern(param.pat.unwrap())
            else
                try self.writeNull();
            try self.stream.objectField("type");
            if (!param.ty.isNone())
                try self.printExpr(param.ty.unwrap())
            else
                try self.writeNull();
            try self.stream.objectField("value");
            if (!param.value.isNone())
                try self.printExpr(param.value.unwrap())
            else
                try self.writeNull();
            try self.stream.endObject();
        }
        try self.stream.endArray();
    }

    /// Serialize struct field metadata `id`.
    fn printStructField(self: *JsonPrinter, id: ast.StructFieldId) anyerror!void {
        const field = self.exprs.StructField.get(id);
        try self.stream.beginObject();
        try self.printLoc(field.loc);
        try self.stream.objectField("name");
        try self.stream.write(self.s(field.name));
        try self.stream.objectField("attrs");
        try self.printAttrs(field.attrs);
        try self.stream.objectField("type");
        try self.printExpr(field.ty);
        try self.stream.objectField("value");
        if (!field.value.isNone())
            try self.printExpr(field.value.unwrap())
        else
            try self.writeNull();
        try self.stream.endObject();
    }

    /// Serialize every struct field ID in `r`.
    fn printStructFieldRange(self: *JsonPrinter, r: ast.RangeField) anyerror!void {
        try self.stream.beginArray();
        const fields = self.exprs.sfield_pool.slice(r);
        for (fields) |fid| try self.printStructField(fid);
        try self.stream.endArray();
    }

    /// Serialize variant field metadata `id`.
    fn printVariantField(self: *JsonPrinter, id: ast.VariantFieldId) anyerror!void {
        const field = self.exprs.VariantField.get(id);
        try self.stream.beginObject();
        try self.printLoc(field.loc);
        try self.stream.objectField("name");
        try self.stream.write(self.s(field.name));
        try self.stream.objectField("attrs");
        try self.printAttrs(field.attrs);
        try self.stream.objectField("payload_kind");
        try self.stream.write(@tagName(field.payload_kind));
        switch (field.payload_kind) {
            .none => {},
            .tuple => {
                try self.stream.objectField("payload_elems");
                try self.printExprRange(field.payload_elems.asRange());
            },
            .@"struct" => {
                try self.stream.objectField("payload_fields");
                try self.printStructFieldRange(field.payload_fields.asRange());
            },
        }
        try self.stream.objectField("value");
        if (!field.value.isNone())
            try self.printExpr(field.value.unwrap())
        else
            try self.writeNull();
        try self.stream.endObject();
    }

    /// Serialize a range of variant fields described by `r`.
    fn printVariantFieldRange(self: *JsonPrinter, r: ast.RangeVariantField) anyerror!void {
        try self.stream.beginArray();
        const fields = self.exprs.vfield_pool.slice(r);
        for (fields) |vid| try self.printVariantField(vid);
        try self.stream.endArray();
    }

    /// Emit metadata for pattern `id` and all of its nested nodes.
    pub fn printPattern(self: *JsonPrinter, id: ast.PatternId) anyerror!void {
        const kind = self.pats.kind(id);
        try self.stream.beginObject();
        try self.stream.objectField("kind");
        try self.stream.write(@tagName(kind));

        switch (kind) {
            .Wildcard => {
                const node = self.pats.get(.Wildcard, id);
                try self.printLoc(node.loc);
            },
            .Literal => {
                const node = self.pats.get(.Literal, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("expr");
                try self.printExpr(node.expr);
            },
            .Path => {
                const node = self.pats.get(.Path, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("segments");
                try self.printPathSegRange(node.segments);
            },
            .Binding => {
                const node = self.pats.get(.Binding, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("name");
                try self.stream.write(self.s(node.name));
                try self.stream.objectField("by_ref");
                try self.writeValue(node.by_ref);
                try self.stream.objectField("is_mut");
                try self.writeValue(node.is_mut);
            },
            .Tuple => {
                const node = self.pats.get(.Tuple, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("elems");
                try self.printPatternRange(node.elems);
            },
            .Slice => {
                const node = self.pats.get(.Slice, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("has_rest");
                try self.writeValue(node.has_rest);
                try self.stream.objectField("rest_index");
                try self.writeValue(node.rest_index);
                try self.stream.objectField("elems");
                try self.printPatternRange(node.elems);
                try self.stream.objectField("rest_binding");
                if (!node.rest_binding.isNone())
                    try self.printPattern(node.rest_binding.unwrap())
                else
                    try self.writeNull();
            },
            .Struct => {
                const node = self.pats.get(.Struct, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("has_rest");
                try self.writeValue(node.has_rest);
                try self.stream.objectField("path");
                try self.printPathSegRange(node.path);
                try self.stream.objectField("fields");
                try self.printPatFieldRange(node.fields);
            },
            .VariantTuple => {
                const node = self.pats.get(.VariantTuple, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("path");
                try self.printPathSegRange(node.path);
                try self.stream.objectField("elems");
                try self.printPatternRange(node.elems);
            },
            .VariantStruct => {
                const node = self.pats.get(.VariantStruct, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("has_rest");
                try self.writeValue(node.has_rest);
                try self.stream.objectField("path");
                try self.printPathSegRange(node.path);
                try self.stream.objectField("fields");
                try self.printPatFieldRange(node.fields);
            },
            .Range => {
                const node = self.pats.get(.Range, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("inclusive_right");
                try self.writeValue(node.inclusive_right);
                try self.stream.objectField("start");
                if (!node.start.isNone())
                    try self.printExpr(node.start.unwrap())
                else
                    try self.writeNull();
                try self.stream.objectField("end");
                if (!node.end.isNone())
                    try self.printExpr(node.end.unwrap())
                else
                    try self.writeNull();
            },
            .Or => {
                const node = self.pats.get(.Or, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("alts");
                try self.printPatternRange(node.alts);
            },
            .At => {
                const node = self.pats.get(.At, id);
                try self.printLoc(node.loc);
                try self.stream.objectField("binder");
                try self.stream.write(self.s(node.binder));
                try self.stream.objectField("pattern");
                try self.printPattern(node.pattern);
            },
        }
        try self.stream.endObject();
    }

    /// Serialize the sequence of patterns inside `r`.
    fn printPatternRange(self: *JsonPrinter, r: ast.RangePat) anyerror!void {
        try self.stream.beginArray();
        const pids = self.pats.pat_pool.slice(r);
        for (pids) |pid| try self.printPattern(pid);
        try self.stream.endArray();
    }

    /// Serialize the path segments recorded in `r`.
    fn printPathSegRange(self: *JsonPrinter, r: ast.RangePathSeg) anyerror!void {
        try self.stream.beginArray();
        const segs = self.pats.seg_pool.slice(r);
        for (segs) |sid| {
            const seg = self.pats.PathSeg.get(sid);
            try self.stream.beginObject();
            try self.printLoc(seg.loc);
            try self.stream.objectField("name");
            try self.stream.write(self.s(seg.name));
            try self.stream.objectField("by_ref");
            try self.writeValue(seg.by_ref);
            try self.stream.objectField("is_mut");
            try self.writeValue(seg.is_mut);
            try self.stream.endObject();
        }
        try self.stream.endArray();
    }

    /// Serialize each pattern field entry listed in `r`.
    fn printPatFieldRange(self: *JsonPrinter, r: ast.RangePatField) anyerror!void {
        try self.stream.beginArray();
        const fields = self.pats.field_pool.slice(r);
        for (fields) |fid| {
            const field = self.pats.StructField.get(fid);
            try self.stream.beginObject();
            try self.printLoc(field.loc);
            try self.stream.objectField("name");
            try self.stream.write(self.s(field.name));
            try self.stream.objectField("pattern");
            try self.printPattern(field.pattern);
            try self.stream.endObject();
        }
        try self.stream.endArray();
    }
};
