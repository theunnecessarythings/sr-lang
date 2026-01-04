const std = @import("std");
const ast = @import("ast.zig");
const comptime_mod = @import("comptime.zig");
const mlir = @import("mlir_bindings.zig");
const types = @import("types.zig");

const Value = comptime_mod.ValueId;
const ValueRows = comptime_mod.ValueRows;
const Sequence = ValueRows.Sequence;
const StructField = ValueRows.StructField;
const StructValue = ValueRows.Struct;
const MapEntry = ValueRows.MapEntry;
const FunctionValue = ValueRows.Function;

const MethodKey = struct { owner: ast.StrId, method: ast.StrId };

pub const Binding = struct { name: ast.StrId, value: Value, store: *comptime_mod.ValueStore };

pub const Interpreter = struct {
    allocator: std.mem.Allocator,
    ast: *ast.Ast,
    symtab: ?*@import("symbols.zig").SymbolStore,
    compilation_unit: ?*@import("package.zig").CompilationUnit,
    bindings: std.ArrayListUnmanaged(Binding) = .{},
    method_table: std.AutoHashMap(MethodKey, ast.ExprId),
    get_module_symtab: ?*const fn (*anyopaque, u32) ?*@import("symbols.zig").SymbolStore = null,
    checker_context: *anyopaque = undefined,

    pub const Error = error{
        UnsupportedExpr,
        InvalidStatement,
        InvalidBinaryOperand,
        DivisionByZero,
        InvalidType,
        BindingNotFound,
        AllocationFailed,
        InvalidCall,
        MissingArgument,
        TooManyArguments,
        InvalidFieldAccess,
        InvalidIndexAccess,
    };

    pub fn init(
        allocator: std.mem.Allocator,
        ast_unit: *ast.Ast,
        symtab: ?*@import("symbols.zig").SymbolStore,
        comp_unit: ?*@import("package.zig").CompilationUnit,
        get_sym: ?*const fn (*anyopaque, u32) ?*@import("symbols.zig").SymbolStore,
        ctx: *anyopaque,
    ) !Interpreter {
        var interp = Interpreter{
            .allocator = allocator,
            .ast = ast_unit,
            .symtab = symtab,
            .compilation_unit = comp_unit,
            .get_module_symtab = get_sym,
            .checker_context = ctx,
            .method_table = std.AutoHashMap(MethodKey, ast.ExprId).init(allocator),
        };
        try interp.registerMethods();
        return interp;
    }

    pub fn deinit(self: *Interpreter) void {
        self.bindings.deinit(self.allocator);
        self.method_table.deinit();
    }

    pub fn store(self: *Interpreter) *comptime_mod.ValueStore {
        return &self.ast.type_info.val_store;
    }

    pub fn evalExpr(self: *Interpreter, expr: ast.ExprId) anyerror!Value {
        const k = self.ast.kind(expr);
        // Fast-path common expressions
        if (k == .Ident) return self.evalIdent(expr);
        if (k == .Literal) return self.evalLiteral(self.ast.exprs.get(.Literal, expr));

        switch (k) {
            .NullLit, .UndefLit, .Await => return self.store().add(.Void, .{}),
            .Import => return self.evalImport(expr),
            .Block => return self.evalBlock(self.ast.exprs.get(.Block, expr)),
            .ComptimeBlock => return self.evalBlock(self.ast.exprs.get(.Block, self.ast.exprs.get(.ComptimeBlock, expr).block)),
            .Binary => return self.evalBinary(self.ast.exprs.get(.Binary, expr)),
            .Unary => return self.evalUnary(self.ast.exprs.get(.Unary, expr)),
            .If => return self.evalIf(self.ast.exprs.get(.If, expr)),
            .FunctionLit => return self.store().add(.Function, .{ .expr = expr, .ast = self.ast }),
            .ArrayLit => return self.evalSequence(self.ast.exprs.get(.ArrayLit, expr).elems),
            .TupleLit => {
                const idx = expr.toRaw();
                const tys = self.ast.type_info.expr_types.items;
                if (idx < tys.len) if (tys[idx]) |t| {
                    if (self.ast.type_info.store.getKind(t) == .TypeType) {
                        return self.store().add(.Type, .{ .ty = self.ast.type_info.store.get(.TypeType, t).of });
                    }
                };
                return self.evalSequence(self.ast.exprs.get(.TupleLit, expr).elems);
            },
            .MapLit => return self.evalMapLit(self.ast.exprs.get(.MapLit, expr)),
            .Call => return self.evalCall(self.ast.exprs.get(.Call, expr)),
            .FieldAccess => return self.evalFieldAccess(self.ast.exprs.get(.FieldAccess, expr)),
            .IndexAccess => return self.evalIndexAccess(self.ast.exprs.get(.IndexAccess, expr)),
            .StructLit => return self.evalStructLit(self.ast.exprs.get(.StructLit, expr)),
            .Range => return self.evalRange(self.ast.exprs.get(.Range, expr)),
            .Match => return self.evalMatch(self.ast.exprs.get(.Match, expr)),
            .For => return self.evalFor(self.ast.exprs.get(.For, expr)),
            .While => return self.evalWhile(self.ast.exprs.get(.While, expr)),
            .Return => return self.evalReturn(self.ast.exprs.get(.Return, expr)),
            .Cast => return self.evalCast(self.ast.exprs.get(.Cast, expr)),
            .Deref => return self.evalDeref(self.ast.exprs.get(.Deref, expr)),
            .Catch => return self.evalWrappable(self.ast.exprs.get(.Catch, expr).expr),
            .OptionalUnwrap => return self.evalWrappable(self.ast.exprs.get(.OptionalUnwrap, expr).expr),
            .ErrUnwrap => return self.evalWrappable(self.ast.exprs.get(.ErrUnwrap, expr).expr),
            .Defer => {
                _ = try self.evalExpr(self.ast.exprs.get(.Defer, expr).expr);
                return self.store().add(.Void, .{});
            },
            .TypeOf => return self.evalTypeOf(self.ast.exprs.get(.TypeOf, expr)),
            .MlirBlock => return self.evalMlirBlock(expr),
            .CodeBlock => return try self.evalCodeBlock(expr),
            // Type Expressions
            .EnumType => return self.evalEnumType(self.ast.exprs.get(.EnumType, expr)),
            .StructType => return self.evalStructType(self.ast.exprs.get(.StructType, expr)),
            .UnionType => return self.evalUnionType(self.ast.exprs.get(.UnionType, expr)),
            .VariantType => return self.evalVariantType(self.ast.exprs.get(.VariantType, expr)),
            .ArrayType, .DynArrayType, .SliceType, .MapType, .OptionalType, .ErrorSetType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType, .ErrorType => return self.evalTypeExpr(k, expr),
            else => return Error.UnsupportedExpr,
        }
    }

    fn evalCodeBlock(self: *Interpreter, expr: ast.ExprId) !Value {
        const block_id = self.ast.exprs.get(.CodeBlock, expr).block;
        var name_set = std.AutoArrayHashMapUnmanaged(ast.StrId, void){};
        defer name_set.deinit(self.allocator);
        try self.collectSpliceNamesInExpr(block_id, &name_set);

        var captures = std.ArrayList(ValueRows.CodeBinding){};
        defer captures.deinit(self.allocator);

        var it = name_set.iterator();
        while (it.next()) |entry| {
            if (self.findBinding(entry.key_ptr.*)) |b| {
                const cloned = if (b.store == self.store())
                    try self.cloneValue(b.value)
                else
                    try self.store().cloneValue(b.store, b.value);
                try captures.append(self.allocator, .{ .name = b.name, .value = cloned });
            }
        }

        const caps_range = self.store().addCodeBindings(captures.items);
        return self.store().add(.Code, .{ .block = block_id, .ast = self.ast, .captures = caps_range });
    }

    fn collectSpliceNamesInExpr(self: *Interpreter, expr: ast.ExprId, names: *std.AutoArrayHashMapUnmanaged(ast.StrId, void)) !void {
        const kind = self.ast.kind(expr);
        if (kind == .Splice) {
            const row = self.ast.exprs.get(.Splice, expr);
            try names.put(self.allocator, row.name, {});
            return;
        }
        if (kind == .CodeBlock) return;
        switch (kind) {
            inline else => |k| {
                const row = self.ast.exprs.get(k, expr);
                inline for (@typeInfo(@TypeOf(row)).@"struct".fields) |f| {
                    if (comptime std.mem.eql(u8, f.name, "loc")) continue;
                    if (f.type == ast.ExprId) {
                        try self.collectSpliceNamesInExpr(@field(row, f.name), names);
                    } else if (f.type == ast.OptExprId) {
                        const opt = @field(row, f.name);
                        if (!opt.isNone()) try self.collectSpliceNamesInExpr(opt.unwrap(), names);
                    } else if (f.type == ast.RangeExpr) {
                        for (self.ast.exprs.expr_pool.slice(@field(row, f.name))) |child| {
                            try self.collectSpliceNamesInExpr(child, names);
                        }
                    } else if (f.type == ast.RangeStmt) {
                        for (self.ast.stmts.stmt_pool.slice(@field(row, f.name))) |sid| {
                            try self.collectSpliceNamesInStmt(sid, names);
                        }
                    } else if (f.type == ast.RangeMatchArm) {
                        for (self.ast.exprs.arm_pool.slice(@field(row, f.name))) |arm_id| {
                            const arm = self.ast.exprs.MatchArm.get(arm_id);
                            if (!arm.guard.isNone()) try self.collectSpliceNamesInExpr(arm.guard.unwrap(), names);
                            try self.collectSpliceNamesInExpr(arm.body, names);
                        }
                    }
                }
            },
        }
    }

    fn collectSpliceNamesInStmt(self: *Interpreter, sid: ast.StmtId, names: *std.AutoArrayHashMapUnmanaged(ast.StrId, void)) anyerror!void {
        switch (self.ast.kind(sid)) {
            .Expr => try self.collectSpliceNamesInExpr(self.ast.stmts.get(.Expr, sid).expr, names),
            .Decl => {
                const decl = self.ast.exprs.Decl.get(self.ast.stmts.get(.Decl, sid).decl);
                if (!decl.ty.isNone()) try self.collectSpliceNamesInExpr(decl.ty.unwrap(), names);
                try self.collectSpliceNamesInExpr(decl.value, names);
            },
            .Assign => {
                const row = self.ast.stmts.get(.Assign, sid);
                if (row.left == .expr) try self.collectSpliceNamesInExpr(row.left.expr, names);
                try self.collectSpliceNamesInExpr(row.right, names);
            },
            .Insert => try self.collectSpliceNamesInExpr(self.ast.stmts.get(.Insert, sid).expr, names),
            .Return => {
                const row = self.ast.stmts.get(.Return, sid);
                if (!row.value.isNone()) try self.collectSpliceNamesInExpr(row.value.unwrap(), names);
            },
            .Break => {
                const row = self.ast.stmts.get(.Break, sid);
                if (!row.value.isNone()) try self.collectSpliceNamesInExpr(row.value.unwrap(), names);
            },
            .Defer => try self.collectSpliceNamesInExpr(self.ast.stmts.get(.Defer, sid).expr, names),
            .ErrDefer => try self.collectSpliceNamesInExpr(self.ast.stmts.get(.ErrDefer, sid).expr, names),
            else => {},
        }
    }

    fn evalTypeExpr(self: *Interpreter, kind: ast.ExprKind, expr: ast.ExprId) !Value {
        const ts = self.ast.type_info.store;
        const ty = switch (kind) {
            .ArrayType => ts.mkArray(try self.typeIdFromTypeExpr(self.ast.exprs.get(.ArrayType, expr).elem), @intCast((try self.expectInt(try self.evalExpr(self.ast.exprs.get(.ArrayType, expr).size))))),
            .DynArrayType => ts.mkDynArray(try self.typeIdFromTypeExpr(self.ast.exprs.get(.DynArrayType, expr).elem)),
            .SliceType => blk: {
                const r = self.ast.exprs.get(.SliceType, expr);
                break :blk ts.mkSlice(try self.typeIdFromTypeExpr(r.elem), r.is_const);
            },
            .MapType => blk: {
                const r = self.ast.exprs.get(.MapType, expr);
                break :blk ts.mkMap(try self.typeIdFromTypeExpr(r.key), try self.typeIdFromTypeExpr(r.value));
            },
            .OptionalType => ts.mkOptional(try self.typeIdFromTypeExpr(self.ast.exprs.get(.OptionalType, expr).elem)),
            .ErrorSetType => blk: {
                const r = self.ast.exprs.get(.ErrorSetType, expr);
                break :blk ts.mkErrorSet(try self.typeIdFromTypeExpr(r.value), try self.typeIdFromTypeExpr(r.err));
            },
            .PointerType => blk: {
                const r = self.ast.exprs.get(.PointerType, expr);
                const val = try self.evalExpr(r.elem);
                if (self.store().kind(val) != .Type) return Error.InvalidType;
                break :blk ts.mkPtr(self.store().get(.Type, val).ty, r.is_const);
            },
            .SimdType => blk: {
                const r = self.ast.exprs.get(.SimdType, expr);
                const l = try self.expectInt(try self.evalExpr(r.lanes));
                break :blk ts.mkSimd(try self.typeIdFromTypeExpr(r.elem), @intCast(l));
            },
            .ComplexType => blk: {
                const r = self.ast.exprs.get(.ComplexType, expr);
                break :blk ts.mkComplex(try self.typeIdFromTypeExpr(r.elem));
            },
            .TypeType => ts.tType(),
            .AnyType => ts.tAny(),
            .NoreturnType => ts.tNoreturn(),
            .ErrorType => return self.evalErrorType(self.ast.exprs.get(.ErrorType, expr)),
            .TensorType => return self.evalTensorType(self.ast.exprs.get(.TensorType, expr)),
            else => unreachable,
        };
        return self.store().add(.Type, .{ .ty = ty });
    }

    fn evalWrappable(self: *Interpreter, expr: ast.ExprId) !Value {
        const val = try self.evalExpr(expr);
        return self.cloneValue(val);
    }

    fn evalMlirBlock(self: *Interpreter, expr: ast.ExprId) !Value {
        const block = self.ast.exprs.get(.MlirBlock, expr);
        var buf = std.ArrayListUnmanaged(u8){};
        defer buf.deinit(self.allocator);
        const w = buf.writer(self.allocator);
        const s = self.store();

        for (self.ast.exprs.mlir_piece_pool.slice(block.pieces)) |pid| {
            const piece = self.ast.exprs.MlirPiece.get(pid);
            switch (piece.kind) {
                .literal => try buf.appendSlice(self.allocator, self.ast.exprs.strs.get(piece.text)),
                .splice => {
                    const v = try self.lookup(piece.text) orelse return Error.BindingNotFound;
                    switch (s.kind(v)) {
                        .Type => try self.ast.type_info.store.fmt(s.get(.Type, v).ty, w),
                        .Int => try w.print("{}", .{s.get(.Int, v).value}),
                        .Float => try w.print("{}", .{s.get(.Float, v).value}),
                        .Bool => try w.print("{}", .{s.get(.Bool, v).value}),
                        .String => try w.print("{s}", .{s.get(.String, v).value}),
                        else => return Error.InvalidType,
                    }
                },
            }
        }
        const str_val = self.ast.type_info.store.strs.intern(buf.items);
        const ts = self.ast.type_info.store;

        const ty = switch (block.kind) {
            .Type => ts.mkMlirType(str_val),
            .Attribute => ts.mkMlirAttribute(str_val),
            .Module => ts.tMlirModule(),
            .Operation => ts.mkMlirAttribute(str_val),
        };
        return s.add(.Type, .{ .ty = ty });
    }

    pub fn bind(self: *Interpreter, name: ast.StrId, value: Value) !void {
        try self.setBinding(name, value);
    }

    pub fn lookup(self: *Interpreter, name: ast.StrId) !?Value {
        if (self.findBinding(name)) |b| {
            self.ensureValueInStore(name, b.value, b.store);
            if (b.store == self.store()) return try self.cloneValue(b.value);
            return try self.store().cloneValue(b.store, b.value);
        }
        return null;
    }

    fn evalBlock(self: *Interpreter, block: ast.Rows.Block) !Value {
        var last: Value = self.store().add(.Void, .{});
        for (self.ast.stmts.stmt_pool.slice(block.items)) |sid| {
            if (try self.evalStatement(sid, &last)) |ret| {
                return ret;
            }
        }
        return last;
    }

    fn evalStatement(self: *Interpreter, stmt_id: ast.StmtId, last: *Value) !?Value {
        switch (self.ast.kind(stmt_id)) {
            .Expr => {
                last.* = try self.evalExpr(self.ast.stmts.get(.Expr, stmt_id).expr);
            },
            .Decl => {
                const r = self.ast.stmts.get(.Decl, stmt_id);
                const d = self.ast.exprs.Decl.get(r.decl);
                if (d.pattern.isNone()) return Error.InvalidStatement;
                const pid = d.pattern.unwrap();
                if (self.ast.kind(pid) == .Binding) {
                    const name = self.ast.pats.get(.Binding, pid).name;
                    if (!d.ty.isNone() and self.ast.kind(d.ty.unwrap()) == .TypeType) {
                        const ty = try self.typeIdFromTypeExpr(d.value);
                        try self.setBinding(name, self.store().add(.Type, .{ .ty = ty }));
                    } else {
                        try self.setBinding(name, try self.evalExpr(d.value));
                    }
                } else return Error.InvalidStatement;
            },
            .Assign => {
                const r = self.ast.stmts.get(.Assign, stmt_id);
                switch (r.left) {
                    .expr => |e| {
                        if (self.ast.kind(e) != .Ident) return Error.InvalidStatement;
                        try self.setBinding(self.ast.exprs.get(.Ident, e).name, try self.evalExpr(r.right));
                    },
                    .pattern => |p| {
                        if (self.ast.kind(p) != .Binding) return Error.InvalidStatement;
                        try self.setBinding(self.ast.pats.get(.Binding, p).name, try self.evalExpr(r.right));
                    },
                }
            },
            .Return => {
                const r = self.ast.stmts.get(.Return, stmt_id);
                return if (!r.value.isNone()) try self.evalExpr(r.value.unwrap()) else self.store().add(.Void, .{});
            },
            .Insert => {
                const r = self.ast.stmts.get(.Insert, stmt_id);
                _ = try self.evalExpr(r.expr);
            },
            else => return Error.InvalidStatement,
        }
        return null;
    }

    fn evalCast(self: *Interpreter, row: ast.Rows.Cast) !Value {
        const val = try self.evalExpr(row.expr);
        const t = self.typeIdFromTypeExpr(row.ty) catch return val;
        const k = self.ast.type_info.store.getKind(t);
        const s = self.store();
        return switch (s.kind(val)) {
            .Float => {
                const f = s.get(.Float, val).value;
                if (isIntType(k)) return s.add(.Int, .{ .value = @intFromFloat(f) });
                return val;
            },
            .Int => {
                const i = s.get(.Int, val).value;
                if (k == .F32 or k == .F64) return s.add(.Float, .{ .value = @floatFromInt(i) });
                return val;
            },
            else => val,
        };
    }
    inline fn isIntType(k: types.TypeKind) bool {
        return switch (k) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
            else => false,
        };
    }

    fn evalTypeOf(self: *Interpreter, row: ast.Rows.TypeOf) !Value {
        const idx = row.expr.toRaw();
        const tys = self.ast.type_info.expr_types.items;
        if (idx < tys.len) if (tys[idx]) |t| return self.store().add(.Type, .{ .ty = t });
        return Error.InvalidType;
    }
    fn evalDeref(self: *Interpreter, row: ast.Rows.Deref) !Value {
        const ptr = try self.evalExpr(row.expr);
        const s = self.store();
        return if (s.kind(ptr) == .Pointer) self.cloneValue(s.get(.Pointer, ptr).pointee) else Error.InvalidType;
    }

    fn evalTensorType(self: *Interpreter, row: ast.Rows.TensorType) !Value {
        const elem = try self.typeIdFromTypeExpr(row.elem);
        var dims = std.ArrayList(usize){};
        defer dims.deinit(self.allocator);
        const s = self.store();
        for (self.ast.exprs.expr_pool.slice(row.shape)) |eid| {
            var tgt = eid;
            var spread = false;
            if (self.ast.kind(eid) == .Range) {
                const rng = self.ast.exprs.get(.Range, eid);
                if (rng.start.isNone() and !rng.end.isNone()) {
                    spread = true;
                    tgt = rng.end.unwrap();
                }
            }
            const v = try self.evalExpr(tgt);
            switch (s.kind(v)) {
                .Int => {
                    const i = s.get(.Int, v).value;
                    if (spread) return Error.InvalidType else try dims.append(self.allocator, @intCast(i));
                },
                .Sequence => {
                    const seq = s.get(.Sequence, v);
                    const items = s.val_pool.slice(seq.elems);
                    for (items) |iv| try dims.append(self.allocator, @intCast(try self.expectInt(iv)));
                },
                else => return Error.InvalidType,
            }
        }
        const d = try self.ast.type_info.store.gpa.alloc(usize, dims.items.len);
        @memcpy(d, dims.items);
        return s.add(.Type, .{ .ty = self.ast.type_info.store.mkTensor(elem, d) });
    }

    fn evalStructType(self: *Interpreter, row: ast.Rows.StructType) !Value {
        const ts = self.ast.type_info.store;
        const sfs = self.ast.exprs.sfield_pool.slice(row.fields);
        const buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
        errdefer ts.gpa.free(buf);
        for (sfs, 0..) |id, i| {
            const f = self.ast.exprs.StructField.get(id);
            buf[i] = .{ .name = f.name, .ty = try self.typeIdFromTypeExpr(f.ty) };
        }
        return self.store().add(.Type, .{ .ty = ts.mkStruct(buf, 0) });
    }

    fn evalVariantType(self: *Interpreter, row: ast.Rows.VariantType) !Value {
        const ts = self.ast.type_info.store;
        const vfs = self.ast.exprs.vfield_pool.slice(row.fields);
        const buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
        errdefer ts.gpa.free(buf);
        for (vfs, 0..) |id, i| {
            const vf = self.ast.exprs.VariantField.get(id);
            buf[i] = .{ .name = vf.name, .ty = try self.evalVariantPayload(vf) };
        }
        return self.store().add(.Type, .{ .ty = ts.mkVariant(buf) });
    }

    fn evalErrorType(self: *Interpreter, row: ast.Rows.ErrorType) !Value {
        const ts = self.ast.type_info.store;
        const vfs = self.ast.exprs.vfield_pool.slice(row.fields);
        const buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
        errdefer ts.gpa.free(buf);
        for (vfs, 0..) |id, i| {
            const vf = self.ast.exprs.VariantField.get(id);
            buf[i] = .{ .name = vf.name, .ty = try self.evalVariantPayload(vf) };
        }
        return self.store().add(.Type, .{ .ty = ts.mkError(buf) });
    }

    fn evalVariantPayload(self: *Interpreter, f: ast.Rows.VariantField) !types.TypeId {
        const ts = self.ast.type_info.store;
        return switch (f.payload_kind) {
            .none => ts.tVoid(),
            .tuple => blk: {
                if (f.payload_elems.isNone()) break :blk ts.tVoid();
                const elems = self.ast.exprs.expr_pool.slice(f.payload_elems.asRange());
                const buf = try ts.gpa.alloc(types.TypeId, elems.len);
                errdefer ts.gpa.free(buf);
                for (elems, 0..) |e, i| buf[i] = try self.typeIdFromTypeExpr(e);
                break :blk ts.mkTuple(buf);
            },
            .@"struct" => blk: {
                if (f.payload_fields.isNone()) break :blk ts.tVoid();
                const flds = self.ast.exprs.sfield_pool.slice(f.payload_fields.asRange());
                const buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, flds.len);
                errdefer ts.gpa.free(buf);
                for (flds, 0..) |id, i| {
                    const sf = self.ast.exprs.StructField.get(id);
                    buf[i] = .{ .name = sf.name, .ty = try self.typeIdFromTypeExpr(sf.ty) };
                }
                break :blk ts.mkStruct(buf, 0);
            },
        };
    }

    fn evalImport(self: *Interpreter, expr: ast.ExprId) !Value {
        const idx = expr.toRaw();
        const tys = self.ast.type_info.expr_types.items;
        if (idx < tys.len) if (tys[idx]) |t| return self.store().add(.Type, .{ .ty = t });
        return Error.InvalidType;
    }

    fn evalUnionType(self: *Interpreter, row: ast.Rows.UnionType) !Value {
        const ts = self.ast.type_info.store;
        const sfs = self.ast.exprs.sfield_pool.slice(row.fields);
        const buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
        errdefer ts.gpa.free(buf);
        for (sfs, 0..) |id, i| {
            const f = self.ast.exprs.StructField.get(id);
            buf[i] = .{ .name = f.name, .ty = try self.typeIdFromTypeExpr(f.ty) };
        }
        return self.store().add(.Type, .{ .ty = ts.mkUnion(buf) });
    }

    fn evalEnumType(self: *Interpreter, row: ast.Rows.EnumType) !Value {
        const ts = self.ast.type_info.store;
        const tag = if (!row.discriminant.isNone()) try self.typeIdFromTypeExpr(row.discriminant.unwrap()) else ts.tI32();
        const efs = self.ast.exprs.efield_pool.slice(row.fields);
        const buf = try ts.gpa.alloc(types.TypeStore.EnumMemberArg, efs.len);
        errdefer ts.gpa.free(buf);
        var nkt: i128 = 0;
        for (efs, 0..) |id, i| {
            const f = self.ast.exprs.EnumField.get(id);
            if (!f.value.isNone()) nkt = try self.expectInt(try self.evalExpr(f.value.unwrap()));
            buf[i] = .{ .name = f.name, .value = @intCast(nkt) };
            nkt += 1;
        }
        return self.store().add(.Type, .{ .ty = ts.mkEnum(buf, tag) });
    }

    fn typeIdFromTypeExpr(self: *Interpreter, expr: ast.ExprId) !types.TypeId {
        const ts = self.ast.type_info.store;
        if (self.ast.kind(expr) == .Ident) {
            const name = self.ast.exprs.get(.Ident, expr).name;
            if (try self.lookup(name)) |val| {
                const s = self.store();
                return if (s.kind(val) == .Type) s.get(.Type, val).ty else Error.InvalidType;
            }
        }
        const idx = expr.toRaw();
        if (idx < self.ast.type_info.expr_types.items.len) {
            if (self.ast.type_info.expr_types.items[idx]) |t| {
                if (ts.getKind(t) == .TypeType) return ts.get(.TypeType, t).of;
            }
        }
        const val = try self.evalExpr(expr);
        // defer val.destroy // REMOVED
        const s = self.store();
        return if (s.kind(val) == .Type) s.get(.Type, val).ty else Error.InvalidType;
    }

    fn evalCall(self: *Interpreter, row: ast.Rows.Call) !Value {
        if (self.ast.kind(row.callee) == .Ident) {
            const name = self.ast.exprs.get(.Ident, row.callee).name;
            const name_str = self.ast.exprs.strs.get(name);
            if (std.mem.eql(u8, name_str, "typeinfo")) {
                const args = self.ast.exprs.expr_pool.slice(row.args);
                if (args.len != 1) return Error.InvalidCall;
                const ty = try self.typeIdFromTypeExpr(args[0]);
                return self.evalTypeInfo(ty);
            }
            if (std.mem.eql(u8, name_str, "codeinfo")) {
                const args = self.ast.exprs.expr_pool.slice(row.args);
                if (args.len != 1) return Error.InvalidCall;
                const arg_val = try self.evalExpr(args[0]);
                if (self.store().kind(arg_val) != .Code) return Error.InvalidType;
                return self.evalCodeInfo(self.store().get(.Code, arg_val));
            }
            if (std.mem.eql(u8, name_str, "codeFromInfo")) {
                const args = self.ast.exprs.expr_pool.slice(row.args);
                if (args.len != 1) return Error.InvalidCall;
                const arg_val = try self.evalExpr(args[0]);
                return self.evalCodeFromInfo(arg_val);
            }
        }
        var callee: Value = undefined;
        var rcv: ?Value = null;
        if (self.ast.kind(row.callee) == .FieldAccess) {
            const fr = self.ast.exprs.get(.FieldAccess, row.callee);
            const parent = try self.evalExpr(fr.parent);
            const owner = self.resolveOwner(parent, ast.OptExprId.some(fr.parent));
            if (owner != null and self.method_table.get(.{ .owner = owner.?, .method = fr.field }) != null) {
                callee = self.store().add(.Function, .{ .expr = self.method_table.get(.{ .owner = owner.?, .method = fr.field }).?, .ast = self.ast });
                rcv = parent;
            } else {
                callee = try self.evalFieldAccessWithParent(fr, parent);
            }
        } else callee = try self.evalExpr(row.callee);
        var args = try self.evalCallArgs(row.args);
        defer {
            args.deinit(self.allocator);
        }
        if (rcv) |r| {
            try args.insert(self.allocator, 0, r);
            rcv = null;
        }
        return if (self.store().kind(callee) == .Function) self.callFunction(self.store().get(.Function, callee), &args) else Error.InvalidCall;
    }

    fn evalCodeFromInfo(self: *Interpreter, value: Value) !Value {
        const Builder = struct {
            interp: *Interpreter,

            fn parseDest(b: @This(), val: Value, comptime T: type) anyerror!T {
                if (T == ast.ExprId) return b.buildExpr(val);
                if (T == ast.StmtId) return b.buildStmt(val);
                if (T == ast.OptExprId) {
                    if (b.interp.store().kind(val) == .Void) return .none();
                    return .some(try b.buildExpr(val));
                }
                if (T == ast.StrId) {
                    const s = try b.interp.expectString(val);
                    return b.interp.ast.exprs.strs.intern(s);
                }
                if (T == bool) {
                    const s = b.interp.store();
                    if (s.kind(val) != .Bool) return error.InvalidType;
                    return s.get(.Bool, val).value;
                }
                if (@typeInfo(T) == .@"enum") {
                    const s = try b.interp.expectString(val);
                    inline for (@typeInfo(T).@"enum".fields) |f| {
                        const sym = Interpreter.getOpSymbol(T, @enumFromInt(f.value));
                        if (std.mem.eql(u8, s, sym)) return @enumFromInt(f.value);
                    }
                    return error.InvalidEnum;
                }
                return error.UnsupportedType;
            }

            fn buildAggregate(b: @This(), val: Value, comptime T: type) !T {
                var result: T = undefined;
                inline for (std.meta.fields(T)) |f| {
                    if (comptime std.mem.eql(u8, f.name, "loc")) {
                        result.loc = ast.LocId.fromRaw(0);
                        continue;
                    }
                    if (b.interp.getStructField(val, f.name)) |field_val| {
                        @field(result, f.name) = try b.parseDest(field_val, f.type);
                    } else |err| {
                        if (f.type == bool) {
                            @field(result, f.name) = false;
                        } else {
                            return err;
                        }
                    }
                }
                return result;
            }

            fn buildExpr(b: @This(), v: Value) !ast.ExprId {
                @setEvalBranchQuota(10000);
                const s = b.interp.store();
                if (s.kind(v) != .Variant) return error.InvalidType;
                const vv = s.get(.Variant, v);
                const tag = b.interp.ast.exprs.strs.get(vv.tag);
                const payload = if (vv.payload.isNone()) s.add(.Void, .{}) else vv.payload.unwrap();

                if (std.mem.eql(u8, tag, "Literal")) {
                    const val_f = try b.interp.getStructField(payload, "value");
                    var data: ast.LiteralValue = undefined;
                    const kind: ast.LiteralKind = switch (s.kind(val_f)) {
                        .Int => k: {
                            data = .{ .int = .{ .text = b.interp.ast.exprs.strs.intern(""), .value = @intCast(s.get(.Int, val_f).value), .base = 10, .valid = true } };
                            break :k .int;
                        },
                        .String => k: {
                            data = .{ .string = b.interp.ast.exprs.strs.intern(s.get(.String, val_f).value) };
                            break :k .string;
                        },
                        .Bool => k: {
                            data = .{ .bool = s.get(.Bool, val_f).value };
                            break :k .bool;
                        },
                        .Float => k: {
                            data = .{ .float = .{ .text = b.interp.ast.exprs.strs.intern(""), .value = s.get(.Float, val_f).value, .valid = true } };
                            break :k .float;
                        },
                        else => return error.InvalidType,
                    };
                    return b.interp.ast.exprs.add(.Literal, .{ .kind = kind, .data = data, .loc = ast.LocId.fromRaw(0) });
                }

                if (std.mem.eql(u8, tag, "Call")) {
                    const callee = try b.buildExpr(try b.interp.getStructField(payload, "callee"));
                    const args_v = try b.interp.getStructField(payload, "args");
                    if (s.kind(args_v) != .Sequence) return error.InvalidType;

                    const seq = s.get(.Sequence, args_v);
                    const items = s.val_pool.slice(seq.elems);
                    var args = try std.ArrayList(ast.ExprId).initCapacity(b.interp.allocator, items.len);
                    for (items) |arg| args.appendAssumeCapacity(try b.buildExpr(arg));

                    return b.interp.ast.exprs.add(.Call, .{ .callee = callee, .args = b.interp.ast.exprs.expr_pool.pushMany(b.interp.allocator, args.items), .loc = ast.LocId.fromRaw(0) });
                }

                if (std.mem.eql(u8, tag, "Block")) {
                    const stmts_v = try b.interp.getStructField(payload, "stmts");
                    if (s.kind(stmts_v) != .Sequence) return error.InvalidType;

                    const seq = s.get(.Sequence, stmts_v);
                    const items = s.val_pool.slice(seq.elems);
                    var stmts = std.ArrayList(ast.StmtId){};
                    defer stmts.deinit(b.interp.allocator);
                    for (items) |sv| try stmts.append(b.interp.allocator, try b.buildStmt(sv));

                    return b.interp.ast.exprs.add(.Block, .{ .items = b.interp.ast.stmts.stmt_pool.pushMany(b.interp.allocator, stmts.items), .loc = ast.LocId.fromRaw(0) });
                }

                inline for (std.meta.fields(ast.ExprKind)) |f| {
                    if (comptime Interpreter.isSpecialExpr(f.name)) continue;
                    if (std.mem.eql(u8, tag, f.name)) {
                        const Row = ast.RowT(@field(ast.ExprKind, f.name));
                        const row_data = try b.buildAggregate(payload, Row);
                        return b.interp.ast.exprs.add(@field(ast.ExprKind, f.name), row_data);
                    }
                }

                if (std.mem.eql(u8, tag, "StructLit")) {
                    const fields_v = try b.interp.getStructField(payload, "fields");
                    const ty_v = try b.interp.getStructField(payload, "ty");

                    var ty = ast.OptExprId.none();
                    if (s.kind(ty_v) != .Void) ty = ast.OptExprId.some(try b.buildExpr(ty_v));

                    if (s.kind(fields_v) != .Sequence) return error.InvalidType;
                    const items = s.val_pool.slice(s.get(.Sequence, fields_v).elems);
                    var fields = try std.ArrayList(ast.StructFieldValueId).initCapacity(b.interp.allocator, items.len);

                    for (items) |fv| {
                        if (s.kind(fv) != .Variant) return error.InvalidType;
                        const fvv = s.get(.Variant, fv);
                        const f_tag = b.interp.ast.exprs.strs.get(fvv.tag);
                        const f_val = if (fvv.payload.isNone()) s.add(.Void, .{}) else fvv.payload.unwrap();

                        var name = ast.OptStrId.none();
                        var val_expr: ast.ExprId = undefined;

                        if (std.mem.eql(u8, f_tag, "Field")) {
                            const name_v = try b.interp.getStructField(f_val, "name");
                            const val_v = try b.interp.getStructField(f_val, "value");
                            const ns = try b.interp.expectString(name_v);
                            if (ns.len > 0) name = ast.OptStrId.some(b.interp.ast.exprs.strs.intern(ns));
                            val_expr = try b.buildExpr(val_v);
                        } else if (std.mem.eql(u8, f_tag, "Spread")) {
                            const spread_val = try b.buildExpr(f_val);
                            val_expr = b.interp.ast.exprs.add(.Range, .{ .start = ast.OptExprId.none(), .end = ast.OptExprId.some(spread_val), .inclusive_right = false, .loc = ast.LocId.fromRaw(0) });
                        } else return error.InvalidType;

                        fields.appendAssumeCapacity(b.interp.ast.exprs.StructFieldValue.add(b.interp.allocator, .{ .name = name, .value = val_expr, .loc = ast.LocId.fromRaw(0) }));
                    }
                    return b.interp.ast.exprs.add(.StructLit, .{ .fields = b.interp.ast.exprs.sfv_pool.pushMany(b.interp.allocator, fields.items), .ty = ty, .loc = ast.LocId.fromRaw(0) });
                }

                if (std.mem.eql(u8, tag, "ArrayLit")) {
                    const elems_v = try b.interp.getStructField(payload, "elems");
                    if (s.kind(elems_v) != .Sequence) return error.InvalidType;
                    const items = s.val_pool.slice(s.get(.Sequence, elems_v).elems);
                    var elems = try std.ArrayList(ast.ExprId).initCapacity(b.interp.allocator, items.len);
                    for (items) |ev| elems.appendAssumeCapacity(try b.buildExpr(ev));
                    return b.interp.ast.exprs.add(.ArrayLit, .{ .elems = b.interp.ast.exprs.expr_pool.pushMany(b.interp.allocator, elems.items), .loc = ast.LocId.fromRaw(0) });
                }

                return error.UnsupportedExpr;
            }

            fn buildStmt(b: @This(), v: Value) anyerror!ast.StmtId {
                const s = b.interp.store();
                if (s.kind(v) != .Variant) return error.InvalidType;
                const vv = s.get(.Variant, v);
                const tag = b.interp.ast.exprs.strs.get(vv.tag);
                const payload = if (vv.payload.isNone()) s.add(.Void, .{}) else vv.payload.unwrap();

                if (std.mem.eql(u8, tag, "Decl")) {
                    const name = try b.interp.expectString(try b.interp.getStructField(payload, "name"));
                    const val = try b.buildExpr(try b.interp.getStructField(payload, "value"));
                    const ty_v = try b.interp.getStructField(payload, "ty");
                    const is_c_val = try b.interp.getStructField(payload, "is_const");
                    const is_c = if (s.kind(is_c_val) == .Bool) s.get(.Bool, is_c_val).value else true;

                    const pat_id = b.interp.ast.pats.add(.Binding, .{ .name = b.interp.ast.exprs.strs.intern(name), .by_ref = false, .is_mut = !is_c, .loc = ast.LocId.fromRaw(0) });

                    const ty_expr: ast.OptExprId = if (s.kind(ty_v) != .Void) .some(try b.buildExpr(ty_v)) else .none();
                    const did = b.interp.ast.exprs.Decl.add(b.interp.allocator, .{ .pattern = .some(pat_id), .value = val, .ty = ty_expr, .method_path = .none(), .flags = .{ .is_const = is_c }, .loc = ast.LocId.fromRaw(0) });
                    return b.interp.ast.stmts.add(.Decl, .{ .decl = did });
                }

                if (std.mem.eql(u8, tag, "Assign")) {
                    const left_v = try b.interp.getStructField(payload, "left");
                    const right_v = try b.interp.getStructField(payload, "right");
                    const right = try b.buildExpr(right_v);

                    if (s.kind(left_v) != .Variant) return error.InvalidType;
                    const lvv = s.get(.Variant, left_v);
                    const l_tag = b.interp.ast.exprs.strs.get(lvv.tag);
                    const l_payload = if (lvv.payload.isNone()) s.add(.Void, .{}) else lvv.payload.unwrap();

                    var lhs: ast.StmtRows.AssignLhs = undefined;
                    if (std.mem.eql(u8, l_tag, "expr")) {
                        lhs = .{ .expr = try b.buildExpr(l_payload) };
                    } else if (std.mem.eql(u8, l_tag, "pattern")) {
                        return error.UnsupportedPattern;
                    } else return error.InvalidType;

                    return b.interp.ast.stmts.add(.Assign, .{ .left = lhs, .right = right, .loc = ast.LocId.fromRaw(0) });
                }

                inline for (std.meta.fields(ast.StmtKind)) |f| {
                    if (comptime std.mem.eql(u8, f.name, "Expr")) continue;
                    if (comptime std.mem.eql(u8, f.name, "Decl")) continue;
                    if (comptime std.mem.eql(u8, f.name, "Assign")) continue;

                    if (std.mem.eql(u8, tag, f.name)) {
                        const K = @field(ast.StmtKind, f.name);
                        const Row = ast.StmtRowT(K);
                        const row_data = try b.buildAggregate(payload, Row);
                        return b.interp.ast.stmts.add(K, row_data);
                    }
                }

                if (b.buildExpr(v)) |eid| {
                    return b.interp.ast.stmts.add(.Expr, .{ .expr = eid });
                } else |err| {
                    if (err == error.UnsupportedExpr) return error.UnsupportedStmt;
                    return err;
                }
            }
        };

        var builder = Builder{ .interp = self };
        const root_expr = try builder.buildExpr(value);

        var final_block = root_expr;
        if (self.ast.kind(root_expr) != .Block) {
            const sid = self.ast.stmts.add(.Expr, .{ .expr = root_expr });
            const range = self.ast.stmts.stmt_pool.pushMany(self.allocator, &.{sid});
            final_block = self.ast.exprs.add(.Block, .{ .items = range, .loc = ast.LocId.fromRaw(0) });
        }

        const s = self.store();
        const empty_caps = s.code_binding_pool.pushMany(s.gpa, &.{});
        return s.add(.Code, .{ .block = final_block, .ast = self.ast, .captures = empty_caps });
    }

    // Helpers

    fn isSpecialExpr(name: []const u8) bool {
        const specials = [_][]const u8{ "Literal", "Call", "StructLit", "ArrayLit", "Block", "FunctionLit", "CodeBlock" };
        for (specials) |s| if (std.mem.eql(u8, s, name)) return true;
        return false;
    }

    // Centralize symbol mapping
    fn getOpSymbol(comptime T: type, val: T) []const u8 {
        if (T == ast.BinaryOp) {
            return switch (val) {
                .add => "+",
                .sub => "-",
                .mul => "*",
                .div => "/",
                .mod => "%",
                .eq => "==",
                .neq => "!=",
                .lt => "<",
                .lte => "<=",
                .gt => ">",
                .gte => ">=",
                .logical_and => "&&",
                .logical_or => "||",
                else => @tagName(val), // fallback to enum name if no symbol
            };
        }
        if (T == ast.UnaryOp) {
            return switch (val) {
                .pos => "+",
                .neg => "-",
                .logical_not => "!",
                .address_of => "&",
            };
        }
        return @tagName(val);
    }
    pub fn cloneCodeToAst(self: *Interpreter, code: comptime_mod.CodeValue, target_ast: *ast.Ast) !comptime_mod.CodeValue {
        const src_store = self.store();
        const val = try self.evalCodeInfo(code);

        const prev_ast = self.ast;
        const prev_alloc = self.allocator;
        self.ast = target_ast;
        self.allocator = target_ast.gpa;
        defer {
            self.ast = prev_ast;
            self.allocator = prev_alloc;
        }

        const res = try self.evalCodeFromInfo(val);
        var out = self.store().get(.Code, res);

        const dst_store = self.store();
        const src_caps = src_store.code_binding_pool.slice(code.captures);
        if (src_caps.len > 0) {
            var new_captures = std.ArrayList(comptime_mod.ValueRows.CodeBinding){};
            defer new_captures.deinit(self.allocator);
            for (src_caps) |cid| {
                const b = src_store.CodeBinding.get(cid);
                const name_str = target_ast.exprs.strs.get(b.name);
                const new_name = target_ast.exprs.strs.intern(name_str);
                const cloned_val = try dst_store.cloneValue(src_store, b.value);
                try new_captures.append(self.allocator, .{ .name = new_name, .value = cloned_val });
            }
            out.captures = dst_store.addCodeBindings(new_captures.items);
        }

        return out;
    }

    fn evalCodeInfo(self: *Interpreter, code_val: comptime_mod.CodeValue) !Value {
        const ts = self.ast.type_info.store;
        const strs = ts.strs;
        const expr = code_val.block;
        const kind = code_val.ast.kind(expr);
        var payload: ?Value = null;
        var tag: []const u8 = "None";

        const intern = struct {
            fn call(s: *types.StringInterner, v: []const u8) ast.StrId {
                return s.intern(v);
            }
        }.call;

        const recurse = struct {
            pub fn call(interp: *Interpreter, parent: comptime_mod.CodeValue, e: ast.ExprId) anyerror!Value {
                return interp.evalCodeInfo(.{ .block = e, .ast = parent.ast, .captures = parent.captures });
            }
            pub fn call_opt(interp: *Interpreter, parent: comptime_mod.CodeValue, e: ast.OptExprId) !Value {
                if (e.isNone()) return interp.store().add(.Void, .{});
                return call(interp, parent, e.unwrap());
            }
        };

        const s = self.store();

        switch (kind) {
            .Literal => {
                tag = "Literal";
                const lit = code_val.ast.exprs.get(.Literal, expr);
                var val: Value = undefined;
                switch (lit.data) {
                    .int => |i| val = s.add(.Int, .{ .value = @intCast(i.value) }),
                    .string => |str| val = s.add(.String, .{ .value = try s.arena.allocator().dupe(u8, code_val.ast.exprs.strs.get(str)) }),
                    .bool => |b| val = s.add(.Bool, .{ .value = b }),
                    .float => |f| val = s.add(.Float, .{ .value = f.value }),
                    else => val = s.add(.Void, .{}),
                }
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "value"), .value = val },
                });
            },
            .Ident => {
                tag = "Ident";
                const id = code_val.ast.exprs.get(.Ident, expr);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "name"), .value = try self.makeString(code_val.ast.exprs.strs.get(id.name)) },
                });
            },
            .Binary => {
                tag = "Binary";
                const bin = code_val.ast.exprs.get(.Binary, expr);
                const op_str = switch (bin.op) {
                    .add => "+",
                    .sub => "-",
                    .mul => "*",
                    .div => "/",
                    .mod => "%",
                    .shl => "<<",
                    .shr => ">>",
                    .bit_and => "&",
                    .bit_or => "|",
                    .bit_xor => "^",
                    .eq => "==",
                    .neq => "!=",
                    .lt => "<",
                    .lte => "<=",
                    .gt => ">",
                    .gte => ">=",
                    .logical_and => "&&",
                    .logical_or => "||",
                    .@"orelse" => "orelse",
                    .contains => "in",
                };
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "op"), .value = try self.makeString(op_str) },
                    .{ .name = intern(strs, "left"), .value = try recurse.call(self, code_val, bin.left) },
                    .{ .name = intern(strs, "right"), .value = try recurse.call(self, code_val, bin.right) },
                });
            },
            .Unary => {
                tag = "Unary";
                const un = code_val.ast.exprs.get(.Unary, expr);
                const op_str = switch (un.op) {
                    .pos => "+",
                    .neg => "-",
                    .logical_not => "!",
                    .address_of => "&",
                };
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "op"), .value = try self.makeString(op_str) },
                    .{ .name = intern(strs, "expr"), .value = try recurse.call(self, code_val, un.expr) },
                });
            },
            .Call => {
                tag = "Call";
                const row = code_val.ast.exprs.get(.Call, expr);
                const args = code_val.ast.exprs.expr_pool.slice(row.args);
                var arg_vals = try std.ArrayListUnmanaged(Value).initCapacity(self.allocator, args.len);
                defer arg_vals.deinit(self.allocator);
                for (args) |arg| arg_vals.appendAssumeCapacity(try recurse.call(self, code_val, arg));

                const seq = s.val_pool.pushMany(s.gpa, arg_vals.items);
                const args_val = s.add(.Sequence, .{ .elems = seq });

                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "callee"), .value = try recurse.call(self, code_val, row.callee) },
                    .{ .name = intern(strs, "args"), .value = args_val },
                });
            },
            .IndexAccess => {
                tag = "IndexAccess";
                const row = code_val.ast.exprs.get(.IndexAccess, expr);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "collection"), .value = try recurse.call(self, code_val, row.collection) },
                    .{ .name = intern(strs, "index"), .value = try recurse.call(self, code_val, row.index) },
                });
            },
            .FieldAccess => {
                tag = "FieldAccess";
                const row = code_val.ast.exprs.get(.FieldAccess, expr);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "parent"), .value = try recurse.call(self, code_val, row.parent) },
                    .{ .name = intern(strs, "field"), .value = try self.makeString(code_val.ast.exprs.strs.get(row.field)) },
                });
            },
            .If => {
                tag = "If";
                const row = code_val.ast.exprs.get(.If, expr);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "cond"), .value = try recurse.call(self, code_val, row.cond) },
                    .{ .name = intern(strs, "then_block"), .value = try recurse.call(self, code_val, row.then_block) },
                    .{ .name = intern(strs, "else_block"), .value = try recurse.call_opt(self, code_val, row.else_block) },
                });
            },

            .Splice => {
                tag = "Splice";
                const row = code_val.ast.exprs.get(.Splice, expr);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "name"), .value = try self.makeString(code_val.ast.exprs.strs.get(row.name)) },
                });
            },
            .Insert => {
                tag = "Insert";
                const row = code_val.ast.exprs.get(.Insert, expr);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "expr"), .value = try recurse.call(self, code_val, row.expr) },
                });
            },
            .StructLit => {
                tag = "StructLit";
                const row = code_val.ast.exprs.get(.StructLit, expr);

                const fields = code_val.ast.exprs.sfv_pool.slice(row.fields);
                var field_vals = try std.ArrayListUnmanaged(Value).initCapacity(self.allocator, fields.len);
                defer field_vals.deinit(self.allocator);

                for (fields) |fid| {
                    const f = code_val.ast.exprs.StructFieldValue.get(fid);
                    const name = if (f.name.isNone()) "" else code_val.ast.exprs.strs.get(f.name.unwrap());
                    const f_payload = try self.typeInfoStruct(&.{
                        .{ .name = intern(strs, "name"), .value = try self.makeString(name) },
                        .{ .name = intern(strs, "value"), .value = try recurse.call(self, code_val, f.value) },
                    });
                    field_vals.appendAssumeCapacity(s.add(.Variant, .{ .tag = intern(strs, "Field"), .payload = .some(f_payload) }));
                }

                const seq = s.val_pool.pushMany(s.gpa, field_vals.items);
                const fields_val = s.add(.Sequence, .{ .elems = seq });

                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "fields"), .value = fields_val },
                    .{ .name = intern(strs, "ty"), .value = try recurse.call_opt(self, code_val, row.ty) },
                });
            },
            .ArrayLit => {
                tag = "ArrayLit";
                const row = code_val.ast.exprs.get(.ArrayLit, expr);
                const elems = code_val.ast.exprs.expr_pool.slice(row.elems);
                var elem_vals = try std.ArrayListUnmanaged(Value).initCapacity(self.allocator, elems.len);
                defer elem_vals.deinit(self.allocator);
                for (elems) |e| elem_vals.appendAssumeCapacity(try recurse.call(self, code_val, e));

                const seq = s.val_pool.pushMany(s.gpa, elem_vals.items);
                const elems_val = s.add(.Sequence, .{ .elems = seq });

                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "elems"), .value = elems_val },
                });
            },
            .CodeBlock => {
                const cb = code_val.ast.exprs.get(.CodeBlock, expr);
                return self.evalCodeInfo(.{ .block = cb.block, .ast = code_val.ast, .captures = code_val.captures });
            },
            .Block => {
                tag = "Block";
                const blk = code_val.ast.exprs.get(.Block, expr);
                const stmts = code_val.ast.stmts.stmt_pool.slice(blk.items);
                var stmt_vals = try std.ArrayListUnmanaged(Value).initCapacity(self.allocator, stmts.len);
                defer stmt_vals.deinit(self.allocator);

                for (stmts) |sid| {
                    const sk = code_val.ast.kind(sid);
                    if (sk == .Expr) {
                        const s_expr = code_val.ast.stmts.get(.Expr, sid).expr;
                        stmt_vals.appendAssumeCapacity(try recurse.call(self, code_val, s_expr));
                    } else if (sk == .Decl) {
                        const did = code_val.ast.stmts.get(.Decl, sid).decl;
                        const decl = code_val.ast.exprs.Decl.get(did);
                        var name: []const u8 = "";
                        if (!decl.pattern.isNone()) {
                            const pid = decl.pattern.unwrap();
                            if (code_val.ast.kind(pid) == .Binding) {
                                const b = code_val.ast.pats.get(.Binding, pid);
                                name = code_val.ast.exprs.strs.get(b.name);
                            }
                        }
                        const decl_payload = try self.typeInfoStruct(&.{
                            .{ .name = intern(strs, "name"), .value = try self.makeString(name) },
                            .{ .name = intern(strs, "value"), .value = try recurse.call(self, code_val, decl.value) },
                            .{ .name = intern(strs, "ty"), .value = try recurse.call_opt(self, code_val, decl.ty) },
                            .{ .name = intern(strs, "is_const"), .value = s.add(.Bool, .{ .value = decl.flags.is_const }) },
                        });
                        const decl_val = s.add(.Variant, .{ .tag = intern(strs, "Decl"), .payload = .some(decl_payload) });
                        stmt_vals.appendAssumeCapacity(decl_val);
                    } else if (sk == .Insert) {
                        const r = code_val.ast.stmts.get(.Insert, sid);
                        const insert_payload = try self.typeInfoStruct(&.{
                            .{ .name = intern(strs, "expr"), .value = try recurse.call(self, code_val, r.expr) },
                        });
                        stmt_vals.appendAssumeCapacity(s.add(.Variant, .{ .tag = intern(strs, "Insert"), .payload = .some(insert_payload) }));
                    } else if (sk == .Return) {
                        const r = code_val.ast.stmts.get(.Return, sid);
                        const ret_payload = try self.typeInfoStruct(&.{
                            .{ .name = intern(strs, "value"), .value = try recurse.call_opt(self, code_val, r.value) },
                        });
                        stmt_vals.appendAssumeCapacity(s.add(.Variant, .{ .tag = intern(strs, "Return"), .payload = .some(ret_payload) }));
                    } else {
                        stmt_vals.appendAssumeCapacity(s.add(.Void, .{}));
                    }
                }
                const seq = s.val_pool.pushMany(s.gpa, stmt_vals.items);
                const seq_val = s.add(.Sequence, .{ .elems = seq });
                payload = try self.typeInfoStruct(&.{
                    .{ .name = intern(strs, "stmts"), .value = seq_val },
                });
            },
            else => {},
        }
        return s.add(.Variant, .{ .tag = strs.intern(tag), .payload = if (payload) |p| .some(p) else .none() });
    }

    fn evalCallArgs(self: *Interpreter, range: ast.RangeExpr) !std.ArrayListUnmanaged(Value) {
        const exprs = self.ast.exprs.expr_pool.slice(range);
        var list = try std.ArrayListUnmanaged(Value).initCapacity(self.allocator, exprs.len);
        errdefer {
            list.deinit(self.allocator);
        }
        for (exprs) |e| {
            if (self.ast.kind(e) == .Range) {
                const r = self.ast.exprs.get(.Range, e);
                if (r.start.isNone()) {
                    if (r.end.isNone()) continue;
                    const spread_val = try self.evalExpr(r.end.unwrap());
                    const s = self.store();
                    if (s.kind(spread_val) == .Sequence) {
                        const items = s.val_pool.slice(s.get(.Sequence, spread_val).elems);
                        for (items) |item| list.appendAssumeCapacity(try self.cloneValue(item));
                    } else {
                        list.appendAssumeCapacity(spread_val);
                    }
                    continue;
                }
            }
            list.appendAssumeCapacity(try self.evalExpr(e));
        }
        return list;
    }

    fn evalTypeInfo(self: *Interpreter, ty: types.TypeId) !Value {
        const ts = self.ast.type_info.store;
        const kind = ts.getKind(ty);
        const keys = ts.typeInfoKeys();
        const s = self.store();

        var payload: ?Value = null;

        switch (kind) {
            .Ptr => {
                const row = ts.get(.Ptr, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = s.add(.Int, .{ .value = row.elem.toRaw() }) },
                    .{ .name = keys.is_const, .value = s.add(.Bool, .{ .value = row.is_const }) },
                });
            },
            .Slice => {
                const row = ts.get(.Slice, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = s.add(.Int, .{ .value = row.elem.toRaw() }) },
                    .{ .name = keys.is_const, .value = s.add(.Bool, .{ .value = row.is_const }) },
                });
            },
            .Array => {
                const row = ts.get(.Array, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = s.add(.Int, .{ .value = row.elem.toRaw() }) },
                    .{ .name = keys.len, .value = s.add(.Int, .{ .value = @intCast(row.len) }) },
                });
            },
            .DynArray => {
                const row = ts.get(.DynArray, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = s.add(.Int, .{ .value = row.elem.toRaw() }) },
                });
            },
            .Map => {
                const row = ts.get(.Map, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.key, .value = s.add(.Int, .{ .value = row.key.toRaw() }) },
                    .{ .name = keys.value, .value = s.add(.Int, .{ .value = row.value.toRaw() }) },
                });
            },
            .Optional => {
                const row = ts.get(.Optional, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = s.add(.Int, .{ .value = row.elem.toRaw() }) },
                });
            },
            .Future => {
                const row = ts.get(.Future, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = s.add(.Int, .{ .value = row.elem.toRaw() }) },
                });
            },
            .Complex => {
                const row = ts.get(.Complex, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = s.add(.Int, .{ .value = row.elem.toRaw() }) },
                });
            },
            .Simd => {
                const row = ts.get(.Simd, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = s.add(.Int, .{ .value = row.elem.toRaw() }) },
                    .{ .name = keys.lanes, .value = s.add(.Int, .{ .value = @intCast(row.lanes) }) },
                });
            },
            .Tensor => {
                const row = ts.get(.Tensor, ty);
                const rank: usize = @intCast(row.rank);
                const dims_val = try self.makeUsizeSequence(row.dims[0..rank]);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = s.add(.Int, .{ .value = row.elem.toRaw() }) },
                    .{ .name = keys.rank, .value = s.add(.Int, .{ .value = @intCast(row.rank) }) },
                    .{ .name = keys.dims, .value = dims_val },
                });
            },
            .Tuple => {
                const row = ts.get(.Tuple, ty);
                const elems = ts.type_pool.slice(row.elems);
                const elems_val = try self.makeTypeIdSequence(elems);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.elems, .value = elems_val },
                });
            },
            .Function => {
                const row = ts.get(.Function, ty);
                const params = ts.type_pool.slice(row.params);
                const params_val = try self.makeTypeIdSequence(params);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.params, .value = params_val },
                    .{ .name = keys.result, .value = s.add(.Int, .{ .value = row.result.toRaw() }) },
                    .{ .name = keys.is_variadic, .value = s.add(.Bool, .{ .value = row.is_variadic }) },
                    .{ .name = keys.is_pure, .value = s.add(.Bool, .{ .value = row.is_pure }) },
                    .{ .name = keys.is_extern, .value = s.add(.Bool, .{ .value = row.is_extern }) },
                });
            },
            .Struct => {
                const row = ts.get(.Struct, ty);
                const fields = ts.field_pool.slice(row.fields);
                const fields_val = try self.makeFieldInfoSequence(fields, keys);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.fields, .value = fields_val },
                    .{ .name = keys.provenance, .value = s.add(.Int, .{ .value = @intCast(row.provenance) }) },
                });
            },
            .Union => {
                const row = ts.get(.Union, ty);
                const fields = ts.field_pool.slice(row.fields);
                const fields_val = try self.makeFieldInfoSequence(fields, keys);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.fields, .value = fields_val },
                });
            },
            .Enum => {
                const row = ts.get(.Enum, ty);
                const members = ts.enum_member_pool.slice(row.members);
                const members_val = try self.makeEnumMemberSequence(members, keys);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.members, .value = members_val },
                    .{ .name = keys.tag, .value = s.add(.Int, .{ .value = row.tag_type.toRaw() }) },
                });
            },
            .Variant => {
                const row = ts.get(.Variant, ty);
                const fields = ts.field_pool.slice(row.variants);
                const fields_val = try self.makeFieldInfoSequence(fields, keys);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.cases, .value = fields_val },
                });
            },
            .Error => {
                const row = ts.get(.Error, ty);
                const fields = ts.field_pool.slice(row.variants);
                const fields_val = try self.makeFieldInfoSequence(fields, keys);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.cases, .value = fields_val },
                });
            },
            .ErrorSet => {
                const row = ts.get(.ErrorSet, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.value, .value = s.add(.Int, .{ .value = row.value_ty.toRaw() }) },
                    .{ .name = keys.err, .value = s.add(.Int, .{ .value = row.error_ty.toRaw() }) },
                });
            },
            .TypeType => {
                const row = ts.get(.TypeType, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.of, .value = s.add(.Int, .{ .value = row.of.toRaw() }) },
                });
            },
            .MlirType => {
                const row = ts.get(.MlirType, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.src, .value = try self.makeString(ts.strs.get(row.src)) },
                });
            },
            .MlirAttribute => {
                const row = ts.get(.MlirAttribute, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.src, .value = try self.makeString(ts.strs.get(row.src)) },
                });
            },
            .Ast => {
                const row = ts.get(.Ast, ty);
                payload = try self.typeInfoStruct(&.{
                    .{ .name = keys.pkg, .value = try self.makeString(self.ast.exprs.strs.get(row.pkg_name)) },
                    .{ .name = keys.filepath, .value = try self.makeString(self.ast.exprs.strs.get(row.filepath)) },
                });
            },
            else => {},
        }

        const payload_id = if (payload) |p| comptime_mod.OptValueId.some(p) else comptime_mod.OptValueId.none();
        return s.add(.Variant, .{ .tag = ts.strs.intern(@tagName(kind)), .payload = payload_id });
    }

    fn makeTypeIdSequence(self: *Interpreter, ids: []const types.TypeId) !Value {
        var list = std.ArrayListUnmanaged(Value){};
        defer list.deinit(self.allocator);
        try list.ensureTotalCapacity(self.allocator, ids.len);
        for (ids) |id| list.appendAssumeCapacity(self.store().add(.Int, .{ .value = id.toRaw() }));
        const elems = self.store().val_pool.pushMany(self.store().gpa, list.items);
        return self.store().add(.Sequence, .{ .elems = elems });
    }

    fn makeUsizeSequence(self: *Interpreter, dims: []const usize) !Value {
        var list = std.ArrayListUnmanaged(Value){};
        defer list.deinit(self.allocator);
        try list.ensureTotalCapacity(self.allocator, dims.len);
        for (dims) |dim| list.appendAssumeCapacity(self.store().add(.Int, .{ .value = @intCast(dim) }));
        const elems = self.store().val_pool.pushMany(self.store().gpa, list.items);
        return self.store().add(.Sequence, .{ .elems = elems });
    }

    fn makeFieldInfoSequence(self: *Interpreter, fields: []const types.FieldId, keys: types.TypeStore.TypeInfoKeys) !Value {
        var list = std.ArrayListUnmanaged(Value){};
        defer list.deinit(self.allocator);
        try list.ensureTotalCapacity(self.allocator, fields.len);
        for (fields) |fid| {
            const f = self.ast.type_info.store.Field.get(fid);
            const field_val = try self.typeInfoStruct(&.{
                .{ .name = keys.name, .value = try self.makeString(self.ast.type_info.store.strs.get(f.name)) },
                .{ .name = keys.ty, .value = self.store().add(.Int, .{ .value = f.ty.toRaw() }) },
            });
            list.appendAssumeCapacity(field_val);
        }
        const elems = self.store().val_pool.pushMany(self.store().gpa, list.items);
        return self.store().add(.Sequence, .{ .elems = elems });
    }

    fn makeEnumMemberSequence(self: *Interpreter, members: []const types.EnumMemberId, keys: types.TypeStore.TypeInfoKeys) !Value {
        var list = std.ArrayListUnmanaged(Value){};
        defer list.deinit(self.allocator);
        try list.ensureTotalCapacity(self.allocator, members.len);
        for (members) |mid| {
            const m = self.ast.type_info.store.EnumMember.get(mid);
            const member_val = try self.typeInfoStruct(&.{
                .{ .name = keys.name, .value = try self.makeString(self.ast.type_info.store.strs.get(m.name)) },
                .{ .name = keys.value, .value = self.store().add(.Int, .{ .value = m.value }) },
            });
            list.appendAssumeCapacity(member_val);
        }
        const elems = self.store().val_pool.pushMany(self.store().gpa, list.items);
        return self.store().add(.Sequence, .{ .elems = elems });
    }

    fn typeInfoStruct(self: *Interpreter, fields: []const struct { name: types.StrId, value: Value }) !Value {
        var list = try std.ArrayListUnmanaged(ValueRows.StructField).initCapacity(self.allocator, fields.len);
        defer list.deinit(self.allocator);
        for (fields) |field| {
            try list.append(self.allocator, .{
                .name = field.name,
                .value = field.value,
            });
        }
        const fields_range = self.store().addStructFields(list.items);
        return self.store().add(.Struct, .{ .fields = fields_range, .owner = .none() });
    }

    fn makeString(self: *Interpreter, text: []const u8) !Value {
        return self.store().add(.String, .{ .value = try self.store().arena.allocator().dupe(u8, text) });
    }

    fn getStructField(self: *Interpreter, val: Value, name: []const u8) !Value {
        const s = self.store();
        if (s.kind(val) != .Struct) return Error.InvalidType;
        const sv = s.get(.Struct, val);
        const fields = s.struct_field_pool.slice(sv.fields);
        for (fields) |fid| {
            const f = s.StructField.get(fid);
            if (std.mem.eql(u8, self.ast.exprs.strs.get(f.name), name)) return f.value;
        }
        return Error.BindingNotFound;
    }

    fn expectString(self: *Interpreter, val: Value) ![]const u8 {
        const s = self.store();
        if (s.kind(val) != .String) return Error.InvalidType;
        return s.get(.String, val).value;
    }

    fn callFunction(self: *Interpreter, func: FunctionValue, args: *std.ArrayListUnmanaged(Value)) !Value {
        const row = func.ast.exprs.get(.FunctionLit, func.expr);
        const params = func.ast.exprs.param_pool.slice(row.params);
        if (!row.flags.is_variadic and args.items.len > params.len) return Error.TooManyArguments;
        const saved_ast = self.ast;
        const caller_store = self.store();
        const callee_store = &func.ast.type_info.val_store;
        const cross_ast = func.ast != saved_ast;
        if (cross_ast) {
            for (args.items) |*arg| arg.* = try callee_store.cloneValue(caller_store, arg.*);
            self.ast = func.ast;
        }
        defer {
            if (cross_ast) self.ast = saved_ast;
        }
        var matches = std.ArrayListUnmanaged(Binding){};
        defer {
            matches.deinit(self.allocator);
        }

        for (params, 0..) |pid, i| {
            const p = func.ast.exprs.Param.get(pid);
            var val: Value = undefined;
            if (row.flags.is_variadic and i == params.len - 1) {
                val = try self.collectVariadicArgs(args, i);
            } else if (i < args.items.len) {
                val = args.items[i];
                args.items[i] = self.store().add(.Void, .{});
            } else if (!p.value.isNone()) {
                val = try self.evalExpr(p.value.unwrap());
            } else return Error.MissingArgument;

            if (!p.pat.isNone()) {
                if (!try self.matchPattern(func.ast, val, p.pat.unwrap(), &matches)) {
                    return Error.InvalidCall;
                }
            }
        }
        var scope = try self.pushBindings(&matches);
        defer scope.deinit();
        matches.clearRetainingCapacity();
        var result = if (!row.body.isNone()) try self.evalExpr(row.body.unwrap()) else self.store().add(.Void, .{});
        if (cross_ast) result = try caller_store.cloneValue(callee_store, result);
        return result;
    }

    fn collectVariadicArgs(self: *Interpreter, args: *std.ArrayListUnmanaged(Value), start: usize) !Value {
        if (start >= args.items.len) {
            const empty = self.store().val_pool.pushMany(self.store().gpa, &.{});
            return self.store().add(.Sequence, .{ .elems = empty });
        }
        var list = try std.ArrayListUnmanaged(Value).initCapacity(self.allocator, args.items.len - start);
        defer list.deinit(self.allocator);
        for (start..args.items.len) |i| {
            list.appendAssumeCapacity(args.items[i]);
            args.items[i] = self.store().add(.Void, .{});
        }
        const elems = self.store().val_pool.pushMany(self.store().gpa, list.items);
        return self.store().add(.Sequence, .{ .elems = elems });
    }

    fn evalSequence(self: *Interpreter, range: ast.RangeExpr) !Value {
        var vals = try self.evalCallArgs(range);
        defer vals.deinit(self.allocator);
        const elems = self.store().val_pool.pushMany(self.store().gpa, vals.items);
        return self.store().add(.Sequence, .{ .elems = elems });
    }

    fn evalStructLit(self: *Interpreter, row: ast.Rows.StructLit) !Value {
        const fids = self.ast.exprs.sfv_pool.slice(row.fields);
        var spread_val: ?Value = null;
        for (fids) |id| {
            if (ast.structFieldSpreadExpr(self.ast, id)) |payload| {
                const v = try self.evalExpr(payload);
                if (self.store().kind(v) != .Struct) return Error.InvalidStatement;
                spread_val = v;
                break;
            }
        }

        const owner = self.resolveOwner(spread_val, row.ty);
        var list = try std.ArrayListUnmanaged(ValueRows.StructField).initCapacity(self.allocator, fids.len);
        defer list.deinit(self.allocator);

        if (spread_val) |sval| {
            const sv = self.store().get(.Struct, sval);
            const fields = self.store().struct_field_pool.slice(sv.fields);
            for (fields) |fid| {
                const f = self.store().StructField.get(fid);
                try list.append(self.allocator, .{ .name = f.name, .value = try self.cloneValue(f.value) });
            }
        }
        for (fids) |id| {
            const f = self.ast.exprs.StructFieldValue.get(id);
            if (f.name.isNone()) continue;
            const name = f.name.unwrap();
            const v = try self.evalExpr(f.value);
            var replaced = false;
            for (list.items) |*field| {
                if (field.name.eq(name)) {
                    field.value = v;
                    replaced = true;
                    break;
                }
            }
            if (!replaced) {
                try list.append(self.allocator, .{ .name = name, .value = v });
            }
        }
        const fields_range = self.store().addStructFields(list.items);
        const owner_id = if (owner) |o| ast.OptStrId.some(o) else ast.OptStrId.none();
        return self.store().add(.Struct, .{ .fields = fields_range, .owner = owner_id });
    }

    fn evalMapLit(self: *Interpreter, row: ast.Rows.MapLit) !Value {
        const entries = self.ast.exprs.kv_pool.slice(row.entries);
        var list = try std.ArrayListUnmanaged(ValueRows.MapEntry).initCapacity(self.allocator, entries.len);
        defer list.deinit(self.allocator);

        for (entries) |id| {
            const kv = self.ast.exprs.KeyValue.get(id);
            try list.append(self.allocator, .{ .key = try self.evalExpr(kv.key), .value = try self.evalExpr(kv.value) });
        }
        const entries_range = self.store().addMapEntries(list.items);
        return self.store().add(.Map, .{ .entries = entries_range });
    }

    fn resolveOwner(self: *Interpreter, parent: ?Value, ty_expr: ast.OptExprId) ?ast.StrId {
        if (parent) |p| {
            if (self.store().kind(p) == .Struct) {
                const owner = self.store().get(.Struct, p).owner;
                if (!owner.isNone()) return owner.unwrap();
            }
        }
        if (!ty_expr.isNone()) {
            const e = ty_expr.unwrap();
            return switch (self.ast.kind(e)) {
                .Ident => self.ast.exprs.get(.Ident, e).name,
                .FieldAccess => self.ast.exprs.get(.FieldAccess, e).field,
                else => null,
            };
        }
        return null;
    }

    fn evalRange(self: *Interpreter, row: ast.Rows.Range) !Value {
        if (row.start.isNone() or row.end.isNone()) return Error.InvalidStatement;
        const start = try self.evalExpr(row.start.unwrap());
        const end = try self.evalExpr(row.end.unwrap());
        const s = self.store();
        return s.add(.Range, .{ .start = try self.expectInt(start), .end = try self.expectInt(end), .inclusive = row.inclusive_right });
    }

    fn evalFieldAccess(self: *Interpreter, row: ast.Rows.FieldAccess) !Value {
        const parent = try self.evalExpr(row.parent);
        return self.evalFieldAccessWithParent(row, parent);
    }

    fn evalFieldAccessWithParent(self: *Interpreter, row: ast.Rows.FieldAccess, parent: Value) !Value {
        const s = self.store();
        if (row.is_tuple) {
            const idx = std.fmt.parseInt(usize, self.ast.exprs.strs.get(row.field), 10) catch return Error.InvalidFieldAccess;
            return switch (s.kind(parent)) {
                .Sequence => {
                    const seq = s.get(.Sequence, parent);
                    const items = s.val_pool.slice(seq.elems);
                    if (idx < items.len) return self.cloneValue(items[idx]) else return Error.InvalidFieldAccess;
                },
                else => Error.InvalidFieldAccess,
            };
        }
        if (std.mem.eql(u8, self.ast.exprs.strs.get(row.field), "len")) {
            return switch (s.kind(parent)) {
                .Sequence => s.add(.Int, .{ .value = @intCast(s.val_pool.slice(s.get(.Sequence, parent).elems).len) }),
                .String => s.add(.Int, .{ .value = @intCast(s.get(.String, parent).value.len) }),
                else => Error.InvalidFieldAccess,
            };
        }
        if (std.mem.eql(u8, self.ast.exprs.strs.get(row.field), "ptr")) {
            return switch (s.kind(parent)) {
                .String => s.add(.Pointer, .{ .pointee = parent }),
                else => Error.InvalidFieldAccess,
            };
        }
        return switch (s.kind(parent)) {
            .Pointer => {
                const t = try self.cloneValue(s.get(.Pointer, parent).pointee);
                return self.evalFieldAccessWithParent(row, t);
            },
            .Struct => {
                const sv = s.get(.Struct, parent);
                if (self.findStructField(sv, row.field)) |f| return self.cloneValue(f.value) else return Error.InvalidFieldAccess;
            },
            .Type => self.evalStaticMember(s.get(.Type, parent).ty, row.field),
            else => Error.InvalidFieldAccess,
        };
    }

    fn evalStaticMember(self: *Interpreter, tid: types.TypeId, field: ast.StrId) !Value {
        const ts = self.ast.type_info.store;
        const id = if (ts.getKind(tid) == .TypeType) ts.get(.TypeType, tid).of else tid;
        switch (ts.getKind(id)) {
            .Enum => for (ts.enum_member_pool.slice(ts.get(.Enum, id).members)) |mid| {
                const m = ts.EnumMember.get(mid);
                if (m.name.eq(field)) return self.store().add(.Int, .{ .value = m.value });
            },
            .Struct => for (ts.field_pool.slice(ts.get(.Struct, id).fields)) |fid| {
                const f = ts.Field.get(fid);
                if (f.name.eq(field)) return self.store().add(.Type, .{ .ty = ts.mkTypeType(f.ty) });
            },
            .Ast => return self.resolveImportMember(ts.get(.Ast, id), field),
            else => {},
        }
        return Error.InvalidFieldAccess;
    }

    fn resolveImportMember(self: *Interpreter, at: types.Rows.Ast, field: ast.StrId) !Value {
        const unit = self.compilation_unit orelse return Error.InvalidFieldAccess;
        const pkg = unit.packages.getPtr(self.ast.exprs.strs.get(at.pkg_name)) orelse return Error.InvalidFieldAccess;
        const pu = pkg.sources.getPtr(self.ast.exprs.strs.get(at.filepath)) orelse return Error.InvalidFieldAccess;
        const other_ast = pu.ast orelse return Error.InvalidFieldAccess;
        const target_sid = other_ast.exprs.strs.intern(self.ast.exprs.strs.get(field));

        var did: ?ast.DeclId = null;
        if (self.get_module_symtab) |g| if (g(self.checker_context, pu.file_id)) |st| if (st.stack.items.len > 0)
            if (st.lookup(st.stack.items[0].id, target_sid)) |sid| if (!st.syms.get(sid).origin_decl.isNone()) {
                did = st.syms.get(sid).origin_decl.unwrap();
            };

        if (did == null) for (other_ast.exprs.decl_pool.slice(other_ast.unit.decls)) |d| {
            const r = other_ast.exprs.Decl.get(d);
            if (!r.pattern.isNone()) if (other_ast.kind(r.pattern.unwrap()) == .Binding)
                if (other_ast.pats.get(.Binding, r.pattern.unwrap()).name.eq(target_sid)) {
                    did = d;
                    break;
                };
        };

        if (did) |d| {
            const decl = other_ast.exprs.Decl.get(d);
            if (other_ast.type_info.getComptimeValue(decl.value)) |v| return self.store().cloneValue(&other_ast.type_info.val_store, v.*);
            if (other_ast.kind(decl.value) == .FunctionLit) return self.store().add(.Function, .{ .expr = decl.value, .ast = other_ast });
        }
        return Error.InvalidFieldAccess;
    }

    fn evalIndexAccess(self: *Interpreter, row: ast.Rows.IndexAccess) !Value {
        const coll = try self.evalExpr(row.collection);
        const idx = try self.evalExpr(row.index);
        const s = self.store();
        return switch (s.kind(coll)) {
            .Sequence => try self.sliceCollection(Sequence, s.get(.Sequence, coll), idx),
            .String => try self.sliceCollection(ValueRows.String, s.get(.String, coll), idx),
            .Map => {
                const m = s.get(.Map, coll);
                const entries = s.map_entry_pool.slice(m.entries);
                for (entries) |e_id| {
                    const e = s.MapEntry.get(e_id);
                    if (self.valuesEqual(idx, e.key)) return self.cloneValue(e.value);
                }
                return Error.InvalidIndexAccess;
            },
            else => Error.InvalidIndexAccess,
        };
    }

    fn sliceCollection(self: *Interpreter, comptime T: type, list: T, idx: Value) !Value {
        const s = self.store();
        const len = if (T == ValueRows.String) list.value.len else s.val_pool.slice(list.elems).len;
        switch (s.kind(idx)) {
            .Int => {
                const i = s.get(.Int, idx).value;
                if (i >= len) return Error.InvalidIndexAccess;
                const index: usize = @intCast(i);
                if (T == ValueRows.String) return s.add(.Int, .{ .value = @intCast(list.value[index]) });
                return self.cloneValue(s.val_pool.slice(list.elems)[index]);
            },
            .Range => {
                const r = s.get(.Range, idx);
                const start: usize = if (r.start < 0) 0 else @intCast(r.start);
                const end: usize = if (r.end < 0) 0 else @intCast(r.end);
                const actual_end = if (r.inclusive) end + 1 else end;
                const final_end = @min(actual_end, len);
                const final_start = @min(start, final_end);

                if (T == ValueRows.String) {
                    return s.add(.String, .{ .value = try s.arena.allocator().dupe(u8, list.value[final_start..final_end]) });
                } else {
                    const count = final_end - final_start;
                    var new_list = try std.ArrayList(Value).initCapacity(self.allocator, count);
                    defer new_list.deinit(self.allocator);
                    const items = s.val_pool.slice(list.elems);
                    for (items[final_start..final_end]) |v| {
                        new_list.appendAssumeCapacity(try self.cloneValue(v));
                    }
                    return s.add(.Sequence, .{ .elems = s.val_pool.pushMany(s.gpa, new_list.items) });
                }
            },
            else => return Error.InvalidIndexAccess,
        }
    }

    fn evalMatch(self: *Interpreter, row: ast.Rows.Match) !Value {
        const scrut = try self.evalExpr(row.expr);
        var matches = std.ArrayListUnmanaged(Binding){};
        defer matches.deinit(self.allocator);

        for (self.ast.exprs.arm_pool.slice(row.arms)) |id| {
            matches.clearRetainingCapacity();
            const arm = self.ast.exprs.MatchArm.get(id);
            if (!try self.matchPattern(self.ast, scrut, arm.pattern, &matches)) continue;
            if (!arm.guard.isNone()) {
                const g = try self.evalExpr(arm.guard.unwrap());
                if (!try self.valueToBool(g)) continue;
            }
            var scope = try self.pushBindings(&matches);
            defer scope.deinit();
            matches.clearRetainingCapacity();
            return self.evalExpr(arm.body);
        }
        return self.store().add(.Void, .{});
    }

    fn evalFor(self: *Interpreter, row: ast.Rows.For) !Value {
        const iter = try self.evalExpr(row.iterable);
        const s = self.store();
        switch (s.kind(iter)) {
            .Range => {
                const r = s.get(.Range, iter);
                var c = r.start;
                while (if (r.inclusive) c <= r.end else c < r.end) : (c += 1) _ = try self.runLoop(row.pattern, row.body, s.add(.Int, .{ .value = c }));
            },
            .Sequence => {
                const seq = s.get(.Sequence, iter);
                const items = s.val_pool.slice(seq.elems);
                for (items) |v| _ = try self.runLoop(row.pattern, row.body, v);
            },
            else => return Error.InvalidType,
        }
        return s.add(.Void, .{});
    }

    fn runLoop(self: *Interpreter, pat: ast.PatternId, body: ast.ExprId, val: Value) !bool {
        var matches = std.ArrayListUnmanaged(Binding){};
        defer matches.deinit(self.allocator);
        if (!try self.matchPattern(self.ast, val, pat, &matches)) return false;
        var scope = try self.pushBindings(&matches);
        defer scope.deinit();
        matches.clearRetainingCapacity();
        _ = try self.evalExpr(body);
        return true;
    }

    fn evalWhile(self: *Interpreter, row: ast.Rows.While) !Value {
        var matches = std.ArrayListUnmanaged(Binding){};
        defer matches.deinit(self.allocator);
        while (true) {
            matches.clearRetainingCapacity();
            if (row.cond.isNone()) {
                _ = try self.evalExpr(row.body);
                continue;
            }
            const cond = try self.evalExpr(row.cond.unwrap());
            if (row.is_pattern and !row.pattern.isNone()) {
                if (!try self.matchPattern(self.ast, cond, row.pattern.unwrap(), &matches)) {
                    break;
                }
                var scope = try self.pushBindings(&matches);
                defer scope.deinit();
                matches.clearRetainingCapacity();
                _ = try self.evalExpr(row.body);
            } else {
                const b = try self.valueToBool(cond);
                if (!b) break;
                _ = try self.evalExpr(row.body);
            }
        }
        return self.store().add(.Void, .{});
    }

    fn evalLiteral(self: *Interpreter, l: ast.Rows.Literal) !Value {
        const s = self.store();
        return switch (l.kind) {
            .int => s.add(.Int, .{ .value = @intCast(l.data.int.value) }),
            .float => s.add(.Float, .{ .value = l.data.float.value }),
            .bool => s.add(.Bool, .{ .value = l.data.bool }),
            .char => s.add(.Int, .{ .value = @intCast(l.data.char) }),
            .string => s.add(.String, .{ .value = try s.arena.allocator().dupe(u8, self.ast.exprs.strs.get(l.data.string)) }),
            .imaginary => s.add(.Float, .{ .value = l.data.imaginary.value }),
        };
    }

    fn evalIdent(self: *Interpreter, expr: ast.ExprId) !Value {
        const name = self.ast.exprs.get(.Ident, expr).name;
        if (try self.lookup(name)) |v| return v;

        const ts = self.ast.type_info.store;
        if (self.symtab) |t| if (t.lookup(t.currentId(), name)) |sid| if (!t.syms.get(sid).origin_decl.isNone()) {
            const did = t.syms.get(sid).origin_decl.unwrap();
            if (did.toRaw() < self.ast.type_info.decl_types.items.len) if (self.ast.type_info.decl_types.items[did.toRaw()]) |ty|
                if (ts.getKind(ty) == .TypeType) return self.store().add(.Type, .{ .ty = ts.get(.TypeType, ty).of });
        };
        const idx = expr.toRaw();
        if (idx < self.ast.type_info.expr_types.items.len) if (self.ast.type_info.expr_types.items[idx]) |ty|
            if (ts.getKind(ty) == .TypeType) return self.store().add(.Type, .{ .ty = ts.get(.TypeType, ty).of });

        if (self.ast.type_info.getExport(name)) |e| {
            const r = self.ast.exprs.Decl.get(e.decl_id);
            if (isTypeExpr(self.ast.kind(r.value))) return self.evalExpr(r.value);
            return self.store().add(.Type, .{ .ty = e.ty });
        }
        if (comptime_mod.builtinTypeId(ts, self.ast.exprs.strs.get(name))) |t| return self.store().add(.Type, .{ .ty = t });

        for (self.ast.exprs.decl_pool.slice(self.ast.unit.decls)) |d| {
            const r = self.ast.exprs.Decl.get(d);
            if (!r.pattern.isNone()) {
                const pat_id = r.pattern.unwrap();
                if (self.ast.kind(pat_id) == .Binding) {
                    if (self.ast.pats.get(.Binding, pat_id).name.eq(name)) {
                        if (isTypeExpr(self.ast.kind(r.value))) return self.evalExpr(r.value);
                    }
                }
            }
        }
        return Error.BindingNotFound;
    }
    fn isTypeExpr(k: ast.ExprKind) bool {
        return switch (k) {
            .Literal, .Import, .Call, .FieldAccess, .MlirBlock, .FunctionLit, .TupleType, .ArrayType, .DynArrayType, .MapType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => true,
            else => false,
        };
    }
    fn evalBinary(self: *Interpreter, row: ast.Rows.Binary) !Value {
        const l = try self.evalExpr(row.left);
        const r = try self.evalExpr(row.right);
        const s = self.store();
        return switch (row.op) {
            .add => self.mathOp(l, r, .Add),
            .sub => self.mathOp(l, r, .Sub),
            .mul => self.mathOp(l, r, .Mul),
            .div => self.mathOp(l, r, .Div),
            .mod => blk: {
                const denom = try self.expectInt(r);
                if (denom == 0) return Error.DivisionByZero;
                break :blk s.add(.Int, .{ .value = @rem(try self.expectInt(l), denom) });
            },
            .logical_and => s.add(.Bool, .{ .value = (try self.valueToBool(l)) and (try self.valueToBool(r)) }),
            .logical_or => s.add(.Bool, .{ .value = (try self.valueToBool(l)) or (try self.valueToBool(r)) }),
            .shl => s.add(.Int, .{ .value = try self.expectInt(l) << @as(u7, @intCast(try self.expectInt(r))) }),
            .shr => s.add(.Int, .{ .value = try self.expectInt(l) >> @as(u7, @intCast(try self.expectInt(r))) }),
            .bit_and => s.add(.Int, .{ .value = (try self.expectInt(l)) & (try self.expectInt(r)) }),
            .bit_or => s.add(.Int, .{ .value = (try self.expectInt(l)) | (try self.expectInt(r)) }),
            .bit_xor => s.add(.Int, .{ .value = (try self.expectInt(l)) ^ (try self.expectInt(r)) }),
            .lt => s.add(.Bool, .{ .value = try self.cmpOp(l, r, .Lt) }),
            .lte => s.add(.Bool, .{ .value = try self.cmpOp(l, r, .Lte) }),
            .gt => s.add(.Bool, .{ .value = try self.cmpOp(l, r, .Gt) }),
            .gte => s.add(.Bool, .{ .value = try self.cmpOp(l, r, .Gte) }),
            .eq => s.add(.Bool, .{ .value = self.valuesEqual(l, r) }),
            .neq => s.add(.Bool, .{ .value = !self.valuesEqual(l, r) }),
            else => Error.InvalidBinaryOperand,
        };
    }
    const Op = enum { Add, Sub, Mul, Div };
    fn mathOp(self: *Interpreter, l: Value, r: Value, op: Op) !Value {
        const s = self.store();
        switch (s.kind(l)) {
            .Int => {
                const li = s.get(.Int, l).value;
                switch (s.kind(r)) {
                    .Int => {
                        const ri = s.get(.Int, r).value;
                        if (op == .Div and ri == 0) return Error.DivisionByZero;
                        return s.add(.Int, .{ .value = switch (op) {
                            .Add => li + ri,
                            .Sub => li - ri,
                            .Mul => li * ri,
                            .Div => @divTrunc(li, ri),
                        } });
                    },
                    .Float => {
                        const rf = s.get(.Float, r).value;
                        return s.add(.Float, .{ .value = fOp(@as(f64, @floatFromInt(li)), rf, op) });
                    },
                    else => {},
                }
            },
            .Float => {
                const lf = s.get(.Float, l).value;
                switch (s.kind(r)) {
                    .Int => {
                        const ri = s.get(.Int, r).value;
                        return s.add(.Float, .{ .value = fOp(lf, @as(f64, @floatFromInt(ri)), op) });
                    },
                    .Float => {
                        const rf = s.get(.Float, r).value;
                        return s.add(.Float, .{ .value = fOp(lf, rf, op) });
                    },
                    else => {},
                }
            },
            else => {},
        }
        return Error.InvalidBinaryOperand;
    }
    fn fOp(a: f64, b: f64, op: Op) f64 {
        return switch (op) {
            .Add => a + b,
            .Sub => a - b,
            .Mul => a * b,
            .Div => a / b,
        };
    }
    const Cmp = enum { Lt, Lte, Gt, Gte };
    fn cmpOp(self: *Interpreter, l: Value, r: Value, op: Cmp) !bool {
        const s = self.store();
        switch (s.kind(l)) {
            .Int => {
                const li = s.get(.Int, l).value;
                switch (s.kind(r)) {
                    .Int => {
                        const ri = s.get(.Int, r).value;
                        return cOp(li, ri, op);
                    },
                    .Float => {
                        const rf = s.get(.Float, r).value;
                        return cOp(@as(f64, @floatFromInt(li)), rf, op);
                    },
                    else => {},
                }
            },
            .Float => {
                const lf = s.get(.Float, l).value;
                switch (s.kind(r)) {
                    .Int => {
                        const ri = s.get(.Int, r).value;
                        return cOp(lf, @as(f64, @floatFromInt(ri)), op);
                    },
                    .Float => {
                        const rf = s.get(.Float, r).value;
                        return cOp(lf, rf, op);
                    },
                    else => {},
                }
            },
            else => {},
        }
        return Error.InvalidBinaryOperand;
    }
    fn cOp(a: anytype, b: anytype, op: Cmp) bool {
        return switch (op) {
            .Lt => a < b,
            .Lte => a <= b,
            .Gt => a > b,
            .Gte => a >= b,
        };
    }

    fn evalUnary(self: *Interpreter, row: ast.Rows.Unary) !Value {
        const v = try self.evalExpr(row.expr);
        const s = self.store();
        if (row.op == .address_of) {
            return s.add(.Pointer, .{ .pointee = v });
        }
        return switch (row.op) {
            .pos => s.add(.Int, .{ .value = try self.expectInt(v) }),
            .neg => s.add(.Int, .{ .value = -(try self.expectInt(v)) }),
            .logical_not => s.add(.Bool, .{ .value = !(try self.valueToBool(v)) }),
            else => Error.InvalidBinaryOperand,
        };
    }
    fn evalIf(self: *Interpreter, row: ast.Rows.If) !Value {
        const c = try self.evalExpr(row.cond);
        if (try self.valueToBool(c)) return self.evalExpr(row.then_block);
        return if (!row.else_block.isNone()) self.evalExpr(row.else_block.unwrap()) else self.store().add(.Void, .{});
    }

    fn evalReturn(self: *Interpreter, row: ast.Rows.Return) !Value {
        return if (!row.value.isNone()) self.evalExpr(row.value.unwrap()) else self.store().add(.Void, .{});
    }

    pub fn setBinding(self: *Interpreter, name: ast.StrId, value: Value) !void {
        self.ensureValueInStore(name, value, self.store());
        if (self.ast.type_info.lookupComptimeBindingType(name)) |t| try self.ast.type_info.setComptimeBinding(name, t, value);
        if (self.findBinding(name)) |b| {
            b.value = value;
            b.store = self.store();
        } else try self.bindings.append(self.allocator, .{ .name = name, .value = value, .store = self.store() });
    }

    fn ensureValueInStore(self: *Interpreter, name: ast.StrId, value: Value, value_store: *comptime_mod.ValueStore) void {
        self.validateValue(name, value, value_store, 0);
    }

    fn validateValue(self: *Interpreter, name: ast.StrId, value: Value, value_store: *comptime_mod.ValueStore, depth: u8) void {
        if (depth > 32) return;
        const raw = value.toRaw();
        const kinds_len = value_store.index.kinds.items.len;
        if (raw >= kinds_len) {
            const name_str = self.ast.exprs.strs.get(name);
            std.debug.print("comptime> invalid binding value: name='{s}', id={}, store_len={}\n", .{ name_str, raw, kinds_len });
            @panic("comptime binding value not in interpreter store");
        }
        switch (value_store.kind(value)) {
            .Sequence => {
                const seq = value_store.get(.Sequence, value);
                const items = value_store.val_pool.slice(seq.elems);
                for (items, 0..) |item, i| {
                    const item_raw = item.toRaw();
                    if (item_raw >= kinds_len) {
                        const name_str = self.ast.exprs.strs.get(name);
                        std.debug.print(
                            "comptime> invalid sequence element: name='{s}', parent_id={}, index={}, elem_id={}, store_len={}\n",
                            .{ name_str, raw, i, item_raw, kinds_len },
                        );
                        @panic("comptime sequence element not in interpreter store");
                    }
                    self.validateValue(name, item, value_store, depth + 1);
                }
            },
            .Struct => {
                const st = value_store.get(.Struct, value);
                const fields = value_store.struct_field_pool.slice(st.fields);
                for (fields) |fid| {
                    const f = value_store.StructField.get(fid);
                    self.validateValue(name, f.value, value_store, depth + 1);
                }
            },
            .Map => {
                const m = value_store.get(.Map, value);
                const entries = value_store.map_entry_pool.slice(m.entries);
                for (entries) |eid| {
                    const e = value_store.MapEntry.get(eid);
                    self.validateValue(name, e.key, value_store, depth + 1);
                    self.validateValue(name, e.value, value_store, depth + 1);
                }
            },
            .Variant => {
                const v = value_store.get(.Variant, value);
                if (!v.payload.isNone()) self.validateValue(name, v.payload.unwrap(), value_store, depth + 1);
            },
            .Pointer => self.validateValue(name, value_store.get(.Pointer, value).pointee, value_store, depth + 1),
            .Code => {
                const c = value_store.get(.Code, value);
                const caps = value_store.code_binding_pool.slice(c.captures);
                for (caps) |cid| {
                    const cb = value_store.CodeBinding.get(cid);
                    self.validateValue(name, cb.value, value_store, depth + 1);
                }
            },
            else => {},
        }
    }

    fn registerMethods(self: *Interpreter) !void {
        for (self.ast.exprs.decl_pool.slice(self.ast.unit.decls)) |d| {
            const decl = self.ast.exprs.Decl.get(d);
            if (decl.method_path.isNone()) continue;
            const s = self.ast.exprs.method_path_pool.slice(decl.method_path.asRange());
            if (s.len > 1) try self.method_table.put(.{ .owner = self.ast.exprs.MethodPathSeg.get(s[0]).name, .method = self.ast.exprs.MethodPathSeg.get(s[s.len - 1]).name }, decl.value);
        }
    }

    pub fn findBinding(self: *Interpreter, name: ast.StrId) ?*Binding {
        for (self.bindings.items) |*b| if (b.name.eq(name)) return b;
        return null;
    }

    pub fn cloneValue(self: *Interpreter, v: Value) !Value {
        return self.store().cloneValue(self.store(), v);
    }

    fn expectInt(self: *Interpreter, v: Value) !i128 {
        const s = self.store();
        return switch (s.kind(v)) {
            .Int => s.get(.Int, v).value,
            .Bool => if (s.get(.Bool, v).value) 1 else 0,
            else => Error.InvalidBinaryOperand,
        };
    }
    fn valueToBool(self: *Interpreter, v: Value) !bool {
        const s = self.store();
        return switch (s.kind(v)) {
            .Bool => s.get(.Bool, v).value,
            .Int => s.get(.Int, v).value != 0,
            .Float => s.get(.Float, v).value != 0.0,
            else => Error.InvalidType,
        };
    }
    fn findStructField(self: *Interpreter, sv: StructValue, name: ast.StrId) ?StructField {
        const s = self.store();
        const fields = s.struct_field_pool.slice(sv.fields);
        for (fields) |fid| {
            const f = s.StructField.get(fid);
            if (f.name.eq(name)) return f;
        }
        return null;
    }

    fn valuesEqual(self: *Interpreter, l: Value, r: Value) bool {
        const s = self.store();
        const lk = s.kind(l);
        const rk = s.kind(r);
        return switch (lk) {
            .Int => blk: {
                const li = s.get(.Int, l).value;
                break :blk switch (rk) {
                    .Int => li == s.get(.Int, r).value,
                    .Float => @as(f64, @floatFromInt(li)) == s.get(.Float, r).value,
                    .Bool => li == @intFromBool(s.get(.Bool, r).value),
                    else => false,
                };
            },
            .Float => blk: {
                const lf = s.get(.Float, l).value;
                break :blk switch (rk) {
                    .Float => lf == s.get(.Float, r).value,
                    .Int => lf == @as(f64, @floatFromInt(s.get(.Int, r).value)),
                    .Bool => lf == @as(f64, @floatFromInt(@intFromBool(s.get(.Bool, r).value))),
                    else => false,
                };
            },
            .Bool => blk: {
                const lb = s.get(.Bool, l).value;
                break :blk switch (rk) {
                    .Bool => lb == s.get(.Bool, r).value,
                    .Int => @intFromBool(lb) == s.get(.Int, r).value,
                    .Float => @as(f64, @floatFromInt(@intFromBool(lb))) == s.get(.Float, r).value,
                    else => false,
                };
            },
            .String => rk == .String and std.mem.eql(u8, s.get(.String, l).value, s.get(.String, r).value),
            .Sequence => rk == .Sequence and blk: {
                const ls = s.get(.Sequence, l).elems;
                const rs = s.get(.Sequence, r).elems;
                const litems = s.val_pool.slice(ls);
                const ritems = s.val_pool.slice(rs);
                if (litems.len != ritems.len) break :blk false;
                for (litems, ritems) |a, b| if (!self.valuesEqual(a, b)) break :blk false;
                break :blk true;
            },
            .Struct => rk == .Struct and blk: {
                const ls = s.get(.Struct, l);
                const rs = s.get(.Struct, r);
                const lfields = s.struct_field_pool.slice(ls.fields);
                const rfields = s.struct_field_pool.slice(rs.fields);
                if (lfields.len != rfields.len) break :blk false;

                if (ls.owner.isNone() != rs.owner.isNone()) break :blk false;
                if (!ls.owner.isNone() and !ls.owner.unwrap().eq(rs.owner.unwrap())) break :blk false;

                for (lfields, rfields) |fid1, fid2| {
                    const f1 = s.StructField.get(fid1);
                    const f2 = s.StructField.get(fid2);
                    if (!f1.name.eq(f2.name) or !self.valuesEqual(f1.value, f2.value)) break :blk false;
                }
                break :blk true;
            },
            .Map => rk == .Map and blk: {
                const lm = s.get(.Map, l);
                const rm = s.get(.Map, r);
                const lentries = s.map_entry_pool.slice(lm.entries);
                const rentries = s.map_entry_pool.slice(rm.entries);
                if (lentries.len != rentries.len) break :blk false;
                for (lentries, rentries) |e1id, e2id| {
                    const e1 = s.MapEntry.get(e1id);
                    const e2 = s.MapEntry.get(e2id);
                    if (!self.valuesEqual(e1.key, e2.key) or !self.valuesEqual(e1.value, e2.value)) break :blk false;
                }
                break :blk true;
            },
            .Range => rk == .Range and blk: {
                const lr = s.get(.Range, l);
                const rr = s.get(.Range, r);
                break :blk lr.start == rr.start and lr.end == rr.end and lr.inclusive == rr.inclusive;
            },
            .Function => rk == .Function and s.get(.Function, l).expr.eq(s.get(.Function, r).expr),
            else => false,
        };
    }

    fn matchPattern(self: *Interpreter, past: *ast.Ast, val: Value, pid: ast.PatternId, matches: *std.ArrayListUnmanaged(Binding)) !bool {
        const s = self.store();
        switch (past.kind(pid)) {
            .Wildcard => return true,
            .Literal => {
                const lit = try self.evalExpr(past.pats.get(.Literal, pid).expr);
                return self.valuesEqual(val, lit);
            },
            .Binding => {
                const v = try self.cloneValue(val);
                try matches.append(self.allocator, .{ .name = past.pats.get(.Binding, pid).name, .value = v, .store = self.store() });
                return true;
            },
            .Tuple => {
                if (s.kind(val) != .Sequence) return false;
                const r = past.pats.get(.Tuple, pid);
                const ps = past.pats.pat_pool.slice(r.elems);
                const items = s.val_pool.slice(s.get(.Sequence, val).elems);
                if (items.len != ps.len) return false;
                for (ps, 0..) |p, i| if (!try self.matchPattern(past, items[i], p, matches)) {
                    self.rollbackBindings(matches, matches.items.len - i);
                    return false;
                };
                return true;
            },
            .Slice => {
                if (s.kind(val) != .Sequence) return false;
                const r = past.pats.get(.Slice, pid);
                const ps = past.pats.pat_pool.slice(r.elems);
                const items = s.val_pool.slice(s.get(.Sequence, val).elems);
                const fix = if (r.has_rest) @as(usize, @intCast(r.rest_index)) else ps.len;
                if (items.len < fix) return false;
                for (ps[0..fix], 0..) |p, i| if (!try self.matchPattern(past, items[i], p, matches)) {
                    self.rollbackBindings(matches, matches.items.len - i);
                    return false;
                };
                if (!r.has_rest) return items.len == ps.len;
                if (@as(usize, @intCast(r.rest_index)) > items.len) return false;
                if (!r.rest_binding.isNone()) {
                    const rv = try self.cloneValue(val);
                    const mark = matches.items.len;
                    if (!try self.matchPattern(past, rv, r.rest_binding.unwrap(), matches)) {
                        self.rollbackBindings(matches, mark);
                        return false;
                    }
                }
                return true;
            },
            .Struct => {
                if (s.kind(val) != .Struct) return false;
                const r = past.pats.get(.Struct, pid);
                const fs = past.pats.field_pool.slice(r.fields);
                const sv = s.get(.Struct, val);
                if (!r.has_rest and s.struct_field_pool.slice(sv.fields).len != fs.len) return false;
                const mark = matches.items.len;
                for (fs) |fid| {
                    const f = past.pats.StructField.get(fid);
                    const sf = self.findStructField(sv, f.name) orelse return false;
                    if (!try self.matchPattern(past, sf.value, f.pattern, matches)) {
                        self.rollbackBindings(matches, mark);
                        return false;
                    }
                }
                return true;
            },
            .At => {
                const r = past.pats.get(.At, pid);
                const mark = matches.items.len;
                if (!try self.matchPattern(past, val, r.pattern, matches)) {
                    self.rollbackBindings(matches, mark);
                    return false;
                }
                const v = try self.cloneValue(val);
                try matches.append(self.allocator, .{ .name = r.binder, .value = v, .store = self.store() });
                return true;
            },
            else => return false,
        }
    }

    fn rollbackBindings(_: *Interpreter, m: *std.ArrayListUnmanaged(Binding), to: usize) void {
        m.shrinkRetainingCapacity(to);
    }

    pub const BindingScope = struct {
        interp: *Interpreter,
        prev_len: usize,
        replaced: std.ArrayListUnmanaged(Binding),
        pub fn deinit(self: *BindingScope) void {
            if (self.interp.bindings.items.len > self.prev_len) {
                self.interp.bindings.shrinkRetainingCapacity(self.prev_len);
            }
            for (self.replaced.items) |b| if (self.interp.findBinding(b.name)) |e| {
                e.value = b.value;
                e.store = b.store;
            };
            self.replaced.deinit(self.interp.allocator);
        }
    };

    pub fn pushBindings(self: *Interpreter, matches: *std.ArrayListUnmanaged(Binding)) !BindingScope {
        var s = BindingScope{ .interp = self, .prev_len = self.bindings.items.len, .replaced = .{} };
        errdefer s.deinit();
        for (matches.items) |*b| {
            const v = b.value;
            b.value = self.store().add(.Void, .{});
            if (self.findBinding(b.name)) |e| {
                try s.replaced.append(self.allocator, .{ .name = b.name, .value = e.value, .store = e.store });
                e.value = v;
                e.store = b.store;
            } else try self.bindings.append(self.allocator, .{ .name = b.name, .value = v, .store = b.store });
        }
        return s;
    }
};
