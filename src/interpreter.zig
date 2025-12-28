const std = @import("std");
const ast = @import("ast.zig");
const comptime_mod = @import("comptime.zig");
const mlir = @import("mlir_bindings.zig");
const types = @import("types.zig");

const Value = comptime_mod.ComptimeValue;
const Sequence = comptime_mod.Sequence;
const StructField = comptime_mod.StructField;
const StructValue = comptime_mod.StructValue;
const MapEntry = comptime_mod.MapEntry;
const MapValue = comptime_mod.MapValue;
const FunctionValue = comptime_mod.FunctionValue;

const MethodKey = struct { owner: ast.StrId, method: ast.StrId };
const FunctionKey = struct { decl_id: ast.DeclId, bindings_hash: u64 };

pub const Binding = struct { name: ast.StrId, value: Value };

pub const SpecializationResult = struct {
    func: FunctionValue,
    snapshot: BindingSnapshot,
};

pub const BindingSnapshot = struct {
    bindings: std.ArrayListUnmanaged(Binding),
    hash: u64,

    pub fn lookup(self: *BindingSnapshot, name: ast.StrId) ?*Binding {
        for (self.bindings.items) |*b| if (b.name.eq(name)) return b;
        return null;
    }

    pub fn destroy(self: *BindingSnapshot, allocator: std.mem.Allocator) void {
        for (self.bindings.items) |*b| b.value.destroy(allocator);
        self.bindings.deinit(allocator);
        self.hash = 0;
    }
};

const FunctionSpecializationEntry = struct {
    key: FunctionKey,
    func_expr: ast.ExprId,
    bindings: BindingSnapshot,
    fn destroy(self: *FunctionSpecializationEntry, alloc: std.mem.Allocator) void {
        self.bindings.destroy(alloc);
    }
};

pub const Interpreter = struct {
    allocator: std.mem.Allocator,
    ast: *ast.Ast,
    symtab: ?*@import("symbols.zig").SymbolStore,
    compilation_unit: ?*@import("package.zig").CompilationUnit,
    bindings: std.ArrayListUnmanaged(Binding) = .{},
    method_table: std.AutoHashMap(MethodKey, ast.ExprId),
    specializations: std.AutoHashMap(u128, FunctionSpecializationEntry),
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
            .specializations = std.AutoHashMap(u128, FunctionSpecializationEntry).init(allocator),
        };
        try interp.registerMethods();
        return interp;
    }

    pub fn deinit(self: *Interpreter) void {
        for (self.bindings.items) |*b| b.value.destroy(self.allocator);
        self.bindings.deinit(self.allocator);
        self.method_table.deinit();
        var iter = self.specializations.iterator();
        while (iter.next()) |entry| entry.value_ptr.destroy(self.allocator);
        self.specializations.deinit();
    }

    pub fn evalExpr(self: *Interpreter, expr: ast.ExprId) anyerror!Value {
        const k = self.ast.kind(expr);
        // Fast-path common expressions
        if (k == .Ident) return self.evalIdent(expr);
        if (k == .Literal) return self.evalLiteral(self.ast.exprs.get(.Literal, expr));

        switch (k) {
            .NullLit, .UndefLit, .Await => return Value{ .Void = {} },
            .Import => return self.evalImport(expr),
            .Block => return self.evalBlock(self.ast.exprs.get(.Block, expr)),
            .ComptimeBlock => return self.evalBlock(self.ast.exprs.get(.Block, self.ast.exprs.get(.ComptimeBlock, expr).block)),
            .Binary => return self.evalBinary(self.ast.exprs.get(.Binary, expr)),
            .Unary => return self.evalUnary(self.ast.exprs.get(.Unary, expr)),
            .If => return self.evalIf(self.ast.exprs.get(.If, expr)),
            .FunctionLit => return Value{ .Function = .{ .expr = expr, .ast = self.ast } },
            .ArrayLit => return self.evalSequence(self.ast.exprs.get(.ArrayLit, expr).elems),
            .TupleLit => {
                const idx = expr.toRaw();
                const tys = self.ast.type_info.expr_types.items;
                if (idx < tys.len) if (tys[idx]) |t| {
                    if (self.ast.type_info.store.getKind(t) == .TypeType) {
                        return Value{ .Type = self.ast.type_info.store.get(.TypeType, t).of };
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
                var defer_val = try self.evalExpr(self.ast.exprs.get(.Defer, expr).expr);
                defer_val.destroy(self.allocator);
                return Value{ .Void = {} };
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

        var captures = std.ArrayList(comptime_mod.CodeBinding){};
        errdefer {
            for (captures.items) |*binding| binding.value.destroy(self.allocator);
            captures.deinit(self.allocator);
        }

        var it = name_set.iterator();
        while (it.next()) |entry| {
            if (self.findBinding(entry.key_ptr.*)) |b| {
                try captures.append(self.allocator, .{ .name = b.name, .value = try self.cloneValue(b.value) });
            }
        }

        return Value{ .Code = .{ .block = block_id, .ast = self.ast, .captures = captures } };
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
        return Value{ .Type = switch (kind) {
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
                var val = try self.evalExpr(r.elem);
                defer val.destroy(self.allocator);
                if (val != .Type) return Error.InvalidType;
                break :blk ts.mkPtr(val.Type, r.is_const);
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
            .ErrorType => return self.evalVariantType(self.ast.exprs.get(.ErrorType, expr)),
            .TensorType => return self.evalTensorType(self.ast.exprs.get(.TensorType, expr)),
            else => unreachable,
        } };
    }

    fn evalWrappable(self: *Interpreter, expr: ast.ExprId) !Value {
        var val = try self.evalExpr(expr);
        defer val.destroy(self.allocator);
        return self.cloneValue(val);
    }

    fn evalMlirBlock(self: *Interpreter, expr: ast.ExprId) !Value {
        const block = self.ast.exprs.get(.MlirBlock, expr);
        var buf = std.ArrayListUnmanaged(u8){};
        defer buf.deinit(self.allocator);
        const w = buf.writer(self.allocator);
        for (self.ast.exprs.mlir_piece_pool.slice(block.pieces)) |pid| {
            const piece = self.ast.exprs.MlirPiece.get(pid);
            switch (piece.kind) {
                .literal => try buf.appendSlice(self.allocator, self.ast.exprs.strs.get(piece.text)),
                .splice => {
                    var v = try self.lookup(piece.text) orelse return Error.BindingNotFound;
                    defer v.destroy(self.allocator);
                    switch (v) {
                        .Type => |t| try self.ast.type_info.store.fmt(t, w),
                        .Int => |i| try w.print("{}", .{i}),
                        .Float => |f| try w.print("{}", .{f}),
                        .Bool => |b| try w.print("{}", .{b}),
                        .String => |s| try w.print("{s}", .{s}),
                        else => return Error.InvalidType,
                    }
                },
            }
        }
        const s = self.ast.type_info.store.strs.intern(buf.items);
        const ts = self.ast.type_info.store;
        return Value{ .Type = switch (block.kind) {
            .Type => ts.mkMlirType(s),
            .Attribute => ts.mkMlirAttribute(s),
            .Module => ts.tMlirModule(),
            .Operation => ts.mkMlirAttribute(s),
        } };
    }

    pub fn bind(self: *Interpreter, name: ast.StrId, value: Value) !void {
        try self.setBinding(name, value);
    }

    pub fn lookup(self: *Interpreter, name: ast.StrId) !?Value {
        if (self.findBinding(name)) |b| return try self.cloneValue(b.value);
        return null;
    }

    fn evalBlock(self: *Interpreter, block: ast.Rows.Block) !Value {
        var last: Value = .{ .Void = {} };
        for (self.ast.stmts.stmt_pool.slice(block.items)) |sid| {
            if (try self.evalStatement(sid, &last)) |ret| {
                last.destroy(self.allocator);
                return ret;
            }
        }
        return last;
    }

    fn evalStatement(self: *Interpreter, stmt_id: ast.StmtId, last: *Value) !?Value {
        switch (self.ast.kind(stmt_id)) {
            .Expr => {
                last.destroy(self.allocator);
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
                        try self.setBinding(name, Value{ .Type = ty });
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
                return if (!r.value.isNone()) try self.evalExpr(r.value.unwrap()) else Value{ .Void = {} };
            },
            .Insert => {
                const r = self.ast.stmts.get(.Insert, stmt_id);
                var v = try self.evalExpr(r.expr);
                v.destroy(self.allocator);
            },
            else => return Error.InvalidStatement,
        }
        return null;
    }

    fn evalCast(self: *Interpreter, row: ast.Rows.Cast) !Value {
        const val = try self.evalExpr(row.expr);
        const t = self.typeIdFromTypeExpr(row.ty) catch return val;
        const k = self.ast.type_info.store.getKind(t);
        return switch (val) {
            .Float => |f| if (isIntType(k)) Value{ .Int = @intFromFloat(f) } else val,
            .Int => |i| if (k == .F32 or k == .F64) Value{ .Float = @floatFromInt(i) } else val,
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
        if (idx < tys.len) if (tys[idx]) |t| return Value{ .Type = t };
        return Error.InvalidType;
    }
    fn evalDeref(self: *Interpreter, row: ast.Rows.Deref) !Value {
        var ptr = try self.evalExpr(row.expr);
        defer ptr.destroy(self.allocator);
        return if (ptr == .Pointer) self.cloneValue(ptr.Pointer.*) else Error.InvalidType;
    }

    fn evalTensorType(self: *Interpreter, row: ast.Rows.TensorType) !Value {
        const elem = try self.typeIdFromTypeExpr(row.elem);
        var dims = std.ArrayList(usize){};
        defer dims.deinit(self.allocator);
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
            var v = try self.evalExpr(tgt);
            defer v.destroy(self.allocator);
            switch (v) {
                .Int => |i| if (spread) return Error.InvalidType else try dims.append(self.allocator, @intCast(i)),
                .Sequence => |s| for (s.values.items) |iv| try dims.append(self.allocator, @intCast(try self.expectInt(iv))),
                else => return Error.InvalidType,
            }
        }
        const d = try self.ast.type_info.store.gpa.alloc(usize, dims.items.len);
        @memcpy(d, dims.items);
        return Value{ .Type = self.ast.type_info.store.mkTensor(elem, d) };
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
        return Value{ .Type = ts.mkStruct(buf, 0) };
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
        return Value{ .Type = ts.mkVariant(buf) };
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
        if (idx < tys.len) if (tys[idx]) |t| return Value{ .Type = t };
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
        return Value{ .Type = ts.mkUnion(buf) };
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
        return Value{ .Type = ts.mkEnum(buf, tag) };
    }

    fn typeIdFromTypeExpr(self: *Interpreter, expr: ast.ExprId) !types.TypeId {
        const ts = self.ast.type_info.store;
        if (self.ast.kind(expr) == .Ident) {
            const name = self.ast.exprs.get(.Ident, expr).name;
            if (try self.lookup(name)) |val| {
                return if (val == .Type) val.Type else Error.InvalidType;
            }
        }
        const idx = expr.toRaw();
        if (idx < self.ast.type_info.expr_types.items.len) {
            if (self.ast.type_info.expr_types.items[idx]) |t| {
                if (ts.getKind(t) == .TypeType) return ts.get(.TypeType, t).of;
            }
        }
        var val = try self.evalExpr(expr);
        defer val.destroy(self.allocator);
        return if (val == .Type) val.Type else Error.InvalidType;
    }

    fn evalCall(self: *Interpreter, row: ast.Rows.Call) !Value {
        if (self.ast.kind(row.callee) == .Ident) {
            const name = self.ast.exprs.get(.Ident, row.callee).name;
            if (std.mem.eql(u8, self.ast.exprs.strs.get(name), "typeinfo")) {
                const args = self.ast.exprs.expr_pool.slice(row.args);
                if (args.len != 1) return Error.InvalidCall;
                const ty = try self.typeIdFromTypeExpr(args[0]);
                return self.evalTypeInfo(ty);
            }
        }
        var callee: Value = undefined;
        var rcv: ?Value = null;
        if (self.ast.kind(row.callee) == .FieldAccess) {
            const fr = self.ast.exprs.get(.FieldAccess, row.callee);
            var parent = try self.evalExpr(fr.parent);
            errdefer parent.destroy(self.allocator);
            const owner = self.resolveOwner(parent, ast.OptExprId.some(fr.parent));
            if (owner != null and self.method_table.get(.{ .owner = owner.?, .method = fr.field }) != null) {
                callee = Value{ .Function = .{ .expr = self.method_table.get(.{ .owner = owner.?, .method = fr.field }).?, .ast = self.ast } };
                rcv = parent;
            } else {
                callee = try self.evalFieldAccessWithParent(fr, &parent, true);
            }
        } else callee = try self.evalExpr(row.callee);
        defer callee.destroy(self.allocator);

        errdefer if (rcv) |*r| r.destroy(self.allocator);
        var args = try self.evalCallArgs(row.args);
        defer {
            for (args.items) |*v| v.destroy(self.allocator);
            args.deinit(self.allocator);
        }
        if (rcv) |r| {
            try args.insert(self.allocator, 0, r);
            rcv = null;
        }
        return if (callee == .Function) self.callFunction(callee.Function, &args) else Error.InvalidCall;
    }

    fn evalCallArgs(self: *Interpreter, range: ast.RangeExpr) !std.ArrayListUnmanaged(Value) {
        const exprs = self.ast.exprs.expr_pool.slice(range);
        var list = try std.ArrayListUnmanaged(Value).initCapacity(self.allocator, exprs.len);
        errdefer {
            for (list.items) |*v| v.destroy(self.allocator);
            list.deinit(self.allocator);
        }
        for (exprs) |e| list.appendAssumeCapacity(try self.evalExpr(e));
        return list;
    }

    fn evalTypeInfo(self: *Interpreter, ty: types.TypeId) !Value {
        const ts = self.ast.type_info.store;
        const kind = ts.getKind(ty);
        const keys = ts.typeInfoKeys();

        var payload: ?*Value = null;
        errdefer if (payload) |p| {
            p.destroy(self.allocator);
            self.allocator.destroy(p);
        };

        switch (kind) {
            .Ptr => {
                const row = ts.get(.Ptr, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = .{ .Int = row.elem.toRaw() } },
                    .{ .name = keys.is_const, .value = .{ .Bool = row.is_const } },
                }));
            },
            .Slice => {
                const row = ts.get(.Slice, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = .{ .Int = row.elem.toRaw() } },
                    .{ .name = keys.is_const, .value = .{ .Bool = row.is_const } },
                }));
            },
            .Array => {
                const row = ts.get(.Array, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = .{ .Int = row.elem.toRaw() } },
                    .{ .name = keys.len, .value = .{ .Int = @intCast(row.len) } },
                }));
            },
            .DynArray => {
                const row = ts.get(.DynArray, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = .{ .Int = row.elem.toRaw() } },
                }));
            },
            .Map => {
                const row = ts.get(.Map, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.key, .value = .{ .Int = row.key.toRaw() } },
                    .{ .name = keys.value, .value = .{ .Int = row.value.toRaw() } },
                }));
            },
            .Optional => {
                const row = ts.get(.Optional, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = .{ .Int = row.elem.toRaw() } },
                }));
            },
            .Future => {
                const row = ts.get(.Future, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = .{ .Int = row.elem.toRaw() } },
                }));
            },
            .Complex => {
                const row = ts.get(.Complex, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = .{ .Int = row.elem.toRaw() } },
                }));
            },
            .Simd => {
                const row = ts.get(.Simd, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = .{ .Int = row.elem.toRaw() } },
                    .{ .name = keys.lanes, .value = .{ .Int = @intCast(row.lanes) } },
                }));
            },
            .Tensor => {
                const row = ts.get(.Tensor, ty);
                const rank: usize = @intCast(row.rank);
                var dims_val = try self.makeUsizeSequence(row.dims[0..rank]);
                errdefer dims_val.destroy(self.allocator);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elem, .value = .{ .Int = row.elem.toRaw() } },
                    .{ .name = keys.rank, .value = .{ .Int = @intCast(row.rank) } },
                    .{ .name = keys.dims, .value = dims_val },
                }));
            },
            .Tuple => {
                const row = ts.get(.Tuple, ty);
                const elems = ts.type_pool.slice(row.elems);
                var elems_val = try self.makeTypeIdSequence(elems);
                errdefer elems_val.destroy(self.allocator);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.elems, .value = elems_val },
                }));
            },
            .Function => {
                const row = ts.get(.Function, ty);
                const params = ts.type_pool.slice(row.params);
                var params_val = try self.makeTypeIdSequence(params);
                errdefer params_val.destroy(self.allocator);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.params, .value = params_val },
                    .{ .name = keys.result, .value = .{ .Int = row.result.toRaw() } },
                    .{ .name = keys.is_variadic, .value = .{ .Bool = row.is_variadic } },
                    .{ .name = keys.is_pure, .value = .{ .Bool = row.is_pure } },
                    .{ .name = keys.is_extern, .value = .{ .Bool = row.is_extern } },
                }));
            },
            .Struct => {
                const row = ts.get(.Struct, ty);
                const fields = ts.field_pool.slice(row.fields);
                var fields_val = try self.makeFieldInfoSequence(fields, keys);
                errdefer fields_val.destroy(self.allocator);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.fields, .value = fields_val },
                    .{ .name = keys.provenance, .value = .{ .Int = @intCast(row.provenance) } },
                }));
            },
            .Union => {
                const row = ts.get(.Union, ty);
                const fields = ts.field_pool.slice(row.fields);
                var fields_val = try self.makeFieldInfoSequence(fields, keys);
                errdefer fields_val.destroy(self.allocator);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.fields, .value = fields_val },
                }));
            },
            .Enum => {
                const row = ts.get(.Enum, ty);
                const members = ts.enum_member_pool.slice(row.members);
                var members_val = try self.makeEnumMemberSequence(members, keys);
                errdefer members_val.destroy(self.allocator);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.members, .value = members_val },
                    .{ .name = keys.tag, .value = .{ .Int = row.tag_type.toRaw() } },
                }));
            },
            .Variant => {
                const row = ts.get(.Variant, ty);
                const fields = ts.field_pool.slice(row.variants);
                var fields_val = try self.makeFieldInfoSequence(fields, keys);
                errdefer fields_val.destroy(self.allocator);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.cases, .value = fields_val },
                }));
            },
            .Error => {
                const row = ts.get(.Error, ty);
                const fields = ts.field_pool.slice(row.variants);
                var fields_val = try self.makeFieldInfoSequence(fields, keys);
                errdefer fields_val.destroy(self.allocator);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.cases, .value = fields_val },
                }));
            },
            .ErrorSet => {
                const row = ts.get(.ErrorSet, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.value, .value = .{ .Int = row.value_ty.toRaw() } },
                    .{ .name = keys.err, .value = .{ .Int = row.error_ty.toRaw() } },
                }));
            },
            .TypeType => {
                const row = ts.get(.TypeType, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.of, .value = .{ .Int = row.of.toRaw() } },
                }));
            },
            .MlirType => {
                const row = ts.get(.MlirType, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.src, .value = try self.makeString(ts.strs.get(row.src)) },
                }));
            },
            .MlirAttribute => {
                const row = ts.get(.MlirAttribute, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.src, .value = try self.makeString(ts.strs.get(row.src)) },
                }));
            },
            .Ast => {
                const row = ts.get(.Ast, ty);
                payload = try self.boxValue(try self.typeInfoStruct(&.{
                    .{ .name = keys.pkg, .value = try self.makeString(self.ast.exprs.strs.get(row.pkg_name)) },
                    .{ .name = keys.filepath, .value = try self.makeString(self.ast.exprs.strs.get(row.filepath)) },
                }));
            },
            else => {},
        }

        return Value{ .Variant = .{ .tag = ts.strs.intern(@tagName(kind)), .payload = payload } };
    }

    fn boxValue(self: *Interpreter, value: Value) !*Value {
        const ptr = try self.allocator.create(Value);
        ptr.* = value;
        return ptr;
    }

    fn makeTypeIdSequence(self: *Interpreter, ids: []const types.TypeId) !Value {
        var list = std.ArrayListUnmanaged(Value){};
        errdefer {
            for (list.items) |*v| v.destroy(self.allocator);
            list.deinit(self.allocator);
        }
        try list.ensureTotalCapacity(self.allocator, ids.len);
        for (ids) |id| list.appendAssumeCapacity(.{ .Int = id.toRaw() });
        return Value{ .Sequence = .{ .values = list } };
    }

    fn makeUsizeSequence(self: *Interpreter, dims: []const usize) !Value {
        var list = std.ArrayListUnmanaged(Value){};
        errdefer {
            for (list.items) |*v| v.destroy(self.allocator);
            list.deinit(self.allocator);
        }
        try list.ensureTotalCapacity(self.allocator, dims.len);
        for (dims) |dim| list.appendAssumeCapacity(.{ .Int = @intCast(dim) });
        return Value{ .Sequence = .{ .values = list } };
    }

    fn makeFieldInfoSequence(self: *Interpreter, fields: []const types.FieldId, keys: types.TypeStore.TypeInfoKeys) !Value {
        var list = std.ArrayListUnmanaged(Value){};
        errdefer {
            for (list.items) |*v| v.destroy(self.allocator);
            list.deinit(self.allocator);
        }
        try list.ensureTotalCapacity(self.allocator, fields.len);
        for (fields) |fid| {
            const f = self.ast.type_info.store.Field.get(fid);
            const field_val = try self.typeInfoStruct(&.{
                .{ .name = keys.name, .value = try self.makeString(self.ast.type_info.store.strs.get(f.name)) },
                .{ .name = keys.ty, .value = .{ .Int = f.ty.toRaw() } },
            });
            list.appendAssumeCapacity(field_val);
        }
        return Value{ .Sequence = .{ .values = list } };
    }

    fn makeEnumMemberSequence(self: *Interpreter, members: []const types.EnumMemberId, keys: types.TypeStore.TypeInfoKeys) !Value {
        var list = std.ArrayListUnmanaged(Value){};
        errdefer {
            for (list.items) |*v| v.destroy(self.allocator);
            list.deinit(self.allocator);
        }
        try list.ensureTotalCapacity(self.allocator, members.len);
        for (members) |mid| {
            const m = self.ast.type_info.store.EnumMember.get(mid);
            const member_val = try self.typeInfoStruct(&.{
                .{ .name = keys.name, .value = try self.makeString(self.ast.type_info.store.strs.get(m.name)) },
                .{ .name = keys.value, .value = .{ .Int = m.value } },
            });
            list.appendAssumeCapacity(member_val);
        }
        return Value{ .Sequence = .{ .values = list } };
    }

    fn typeInfoStruct(self: *Interpreter, fields: []const struct { name: types.StrId, value: Value }) !Value {
        var list = try std.ArrayListUnmanaged(StructField).initCapacity(self.allocator, fields.len);
        errdefer {
            for (list.items) |*f| f.value.destroy(self.allocator);
            list.deinit(self.allocator);
        }
        for (fields) |field| {
            try list.append(self.allocator, .{
                .name = field.name,
                .value = field.value,
            });
        }
        return Value{ .Struct = .{ .fields = list, .owner = null } };
    }

    fn makeString(self: *Interpreter, text: []const u8) !Value {
        return Value{ .String = try self.allocator.dupe(u8, text) };
    }

    fn callFunction(self: *Interpreter, func: FunctionValue, args: *std.ArrayListUnmanaged(Value)) !Value {
        const row = func.ast.exprs.get(.FunctionLit, func.expr);
        const params = func.ast.exprs.param_pool.slice(row.params);
        if (!row.flags.is_variadic and args.items.len > params.len) return Error.TooManyArguments;
        var matches = std.ArrayListUnmanaged(Binding){};
        defer {
            for (matches.items) |*b| b.value.destroy(self.allocator);
            matches.deinit(self.allocator);
        }

        for (params, 0..) |pid, i| {
            const p = func.ast.exprs.Param.get(pid);
            var val: Value = undefined;
            if (row.flags.is_variadic and i == params.len - 1) {
                val = try self.collectVariadicArgs(args, i);
            } else if (i < args.items.len) {
                val = args.items[i];
                args.items[i] = .Void;
            } else if (!p.value.isNone()) {
                val = try self.evalExpr(p.value.unwrap());
            } else return Error.MissingArgument;

            if (!p.pat.isNone()) {
                if (!try self.matchPattern(func.ast, val, p.pat.unwrap(), &matches)) {
                    val.destroy(self.allocator);
                    return Error.InvalidCall;
                }
            }
            val.destroy(self.allocator);
        }
        var scope = try self.pushBindings(&matches);
        defer scope.deinit();
        matches.clearRetainingCapacity();
        if (!row.body.isNone()) {
            const saved = self.ast;
            self.ast = func.ast;
            defer self.ast = saved;
            return self.evalExpr(row.body.unwrap());
        }
        return Value{ .Void = {} };
    }

    fn collectVariadicArgs(self: *Interpreter, args: *std.ArrayListUnmanaged(Value), start: usize) !Value {
        if (start >= args.items.len) return Value{ .Sequence = .{ .values = .{} } };
        var list = try std.ArrayListUnmanaged(Value).initCapacity(self.allocator, args.items.len - start);
        errdefer {
            for (list.items) |*v| v.destroy(self.allocator);
            list.deinit(self.allocator);
        }
        for (start..args.items.len) |i| {
            list.appendAssumeCapacity(args.items[i]);
            args.items[i] = .Void;
        }
        return Value{ .Sequence = .{ .values = list } };
    }

    fn evalSequence(self: *Interpreter, range: ast.RangeExpr) !Value {
        return Value{ .Sequence = .{ .values = try self.evalCallArgs(range) } };
    }

    fn evalStructLit(self: *Interpreter, row: ast.Rows.StructLit) !Value {
        const fids = self.ast.exprs.sfv_pool.slice(row.fields);
        var spread_val: ?Value = null;
        for (fids) |id| {
            if (ast.structFieldSpreadExpr(self.ast, id)) |payload| {
                const v = try self.evalExpr(payload);
                if (v != .Struct) return Error.InvalidStatement;
                spread_val = v;
                break;
            }
        }

        const owner = self.resolveOwner(spread_val, row.ty);
        var list = try std.ArrayListUnmanaged(StructField).initCapacity(self.allocator, fids.len);
        errdefer {
            for (list.items) |*f| f.value.destroy(self.allocator);
            list.deinit(self.allocator);
        }
        if (spread_val) |sval| {
            var val = sval;
            for (sval.Struct.fields.items) |f| {
                list.appendAssumeCapacity(.{ .name = f.name, .value = try self.cloneValue(f.value) });
            }
            val.destroy(self.allocator);
        }
        for (fids) |id| {
            const f = self.ast.exprs.StructFieldValue.get(id);
            if (f.name.isNone()) continue;
            const name = f.name.unwrap();
            const v = try self.evalExpr(f.value);
            var replaced = false;
            for (list.items) |*field| {
                if (field.name.eq(name)) {
                    field.value.destroy(self.allocator);
                    field.value = v;
                    replaced = true;
                    break;
                }
            }
            if (!replaced) {
                list.appendAssumeCapacity(.{ .name = name, .value = v });
            }
        }
        return Value{ .Struct = .{ .fields = list, .owner = owner } };
    }

    fn evalMapLit(self: *Interpreter, row: ast.Rows.MapLit) !Value {
        const entries = self.ast.exprs.kv_pool.slice(row.entries);
        var list = try std.ArrayListUnmanaged(MapEntry).initCapacity(self.allocator, entries.len);
        errdefer {
            for (list.items) |*e| {
                e.key.destroy(self.allocator);
                e.value.destroy(self.allocator);
            }
            list.deinit(self.allocator);
        }
        for (entries) |id| {
            const kv = self.ast.exprs.KeyValue.get(id);
            list.appendAssumeCapacity(.{ .key = try self.evalExpr(kv.key), .value = try self.evalExpr(kv.value) });
        }
        return Value{ .Map = .{ .entries = list } };
    }

    fn resolveOwner(self: *Interpreter, parent: ?Value, ty_expr: ast.OptExprId) ?ast.StrId {
        if (parent) |p| if (p == .Struct) return p.Struct.owner;
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
        var start = try self.evalExpr(row.start.unwrap());
        defer start.destroy(self.allocator);
        var end = try self.evalExpr(row.end.unwrap());
        defer end.destroy(self.allocator);
        return Value{ .Range = .{ .start = try self.expectInt(start), .end = try self.expectInt(end), .inclusive = row.inclusive_right } };
    }

    fn evalFieldAccess(self: *Interpreter, row: ast.Rows.FieldAccess) !Value {
        var parent = try self.evalExpr(row.parent);
        return self.evalFieldAccessWithParent(row, &parent, true);
    }

    fn evalFieldAccessWithParent(self: *Interpreter, row: ast.Rows.FieldAccess, parent: *Value, destroy_parent: bool) !Value {
        defer if (destroy_parent) parent.destroy(self.allocator);
        if (row.is_tuple) {
            const idx = std.fmt.parseInt(usize, self.ast.exprs.strs.get(row.field), 10) catch return Error.InvalidFieldAccess;
            return switch (parent.*) {
                .Sequence => |s| if (idx < s.values.items.len) self.cloneValue(s.values.items[idx]) else Error.InvalidFieldAccess,
                else => Error.InvalidFieldAccess,
            };
        }
        if (std.mem.eql(u8, self.ast.exprs.strs.get(row.field), "len")) {
            return switch (parent.*) {
                .Sequence => |s| Value{ .Int = @intCast(s.values.items.len) },
                .String => |s| Value{ .Int = @intCast(s.len) },
                else => Error.InvalidFieldAccess,
            };
        }
        return switch (parent.*) {
            .Pointer => |p| {
                var t = try self.cloneValue(p.*);
                return self.evalFieldAccessWithParent(row, &t, true);
            },
            .Struct => |s| if (self.findStructField(s, row.field)) |f| self.cloneValue(f.value) else Error.InvalidFieldAccess,
            .Type => |t| self.evalStaticMember(t, row.field),
            else => Error.InvalidFieldAccess,
        };
    }

    fn evalStaticMember(self: *Interpreter, tid: types.TypeId, field: ast.StrId) !Value {
        const ts = self.ast.type_info.store;
        const id = if (ts.getKind(tid) == .TypeType) ts.get(.TypeType, tid).of else tid;
        switch (ts.getKind(id)) {
            .Enum => for (ts.enum_member_pool.slice(ts.get(.Enum, id).members)) |mid| {
                const m = ts.EnumMember.get(mid);
                if (m.name.eq(field)) return Value{ .Int = m.value };
            },
            .Struct => for (ts.field_pool.slice(ts.get(.Struct, id).fields)) |fid| {
                const f = ts.Field.get(fid);
                if (f.name.eq(field)) return Value{ .Type = ts.mkTypeType(f.ty) };
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
            if (other_ast.type_info.getComptimeValue(decl.value)) |v| return self.cloneValue(v.*);
            if (other_ast.kind(decl.value) == .FunctionLit) return Value{ .Function = .{ .expr = decl.value, .ast = other_ast } };
        }
        return Error.InvalidFieldAccess;
    }

    fn evalIndexAccess(self: *Interpreter, row: ast.Rows.IndexAccess) !Value {
        var coll = try self.evalExpr(row.collection);
        defer coll.destroy(self.allocator);
        var idx = try self.evalExpr(row.index);
        defer idx.destroy(self.allocator);
        return switch (coll) {
            .Sequence => |s| if ((try self.expectInt(idx)) < s.values.items.len) self.cloneValue(s.values.items[@intCast(try self.expectInt(idx))]) else Error.InvalidIndexAccess,
            .String => |s| if ((try self.expectInt(idx)) < s.len) Value{ .Int = @intCast(s[@intCast(try self.expectInt(idx))]) } else Error.InvalidIndexAccess,
            .Map => |m| for (m.entries.items) |e| {
                if (self.valuesEqual(idx, e.key)) return self.cloneValue(e.value);
            } else Error.InvalidIndexAccess,
            else => Error.InvalidIndexAccess,
        };
    }

    fn evalMatch(self: *Interpreter, row: ast.Rows.Match) !Value {
        var scrut = try self.evalExpr(row.expr);
        defer scrut.destroy(self.allocator);
        var matches = std.ArrayListUnmanaged(Binding){};
        defer {
            for (matches.items) |*b| b.value.destroy(self.allocator);
            matches.deinit(self.allocator);
        }

        for (self.ast.exprs.arm_pool.slice(row.arms)) |id| {
            for (matches.items) |*b| b.value.destroy(self.allocator);
            matches.clearRetainingCapacity();
            const arm = self.ast.exprs.MatchArm.get(id);
            if (!try self.matchPattern(self.ast, scrut, arm.pattern, &matches)) continue;
            if (!arm.guard.isNone()) {
                var g = try self.evalExpr(arm.guard.unwrap());
                defer g.destroy(self.allocator);
                if (!try self.valueToBool(g)) continue;
            }
            var scope = try self.pushBindings(&matches);
            defer scope.deinit();
            matches.clearRetainingCapacity();
            return self.evalExpr(arm.body);
        }
        return Value{ .Void = {} };
    }

    fn evalFor(self: *Interpreter, row: ast.Rows.For) !Value {
        var iter = try self.evalExpr(row.iterable);
        defer iter.destroy(self.allocator);
        switch (iter) {
            .Range => |r| {
                var c = r.start;
                while (if (r.inclusive) c <= r.end else c < r.end) : (c += 1) _ = try self.runLoop(row.pattern, row.body, .{ .Int = c });
            },
            .Sequence => |s| {
                for (s.values.items) |v| _ = try self.runLoop(row.pattern, row.body, v);
            },
            else => return Error.InvalidType,
        }
        return Value{ .Void = {} };
    }

    fn runLoop(self: *Interpreter, pat: ast.PatternId, body: ast.ExprId, val: Value) !bool {
        var matches = std.ArrayListUnmanaged(Binding){};
        defer {
            for (matches.items) |*b| b.value.destroy(self.allocator);
            matches.deinit(self.allocator);
        }
        if (!try self.matchPattern(self.ast, val, pat, &matches)) return false;
        var scope = try self.pushBindings(&matches);
        defer scope.deinit();
        matches.clearRetainingCapacity();
        var body_val = try self.evalExpr(body);
        body_val.destroy(self.allocator);
        return true;
    }

    fn evalWhile(self: *Interpreter, row: ast.Rows.While) !Value {
        var matches = std.ArrayListUnmanaged(Binding){};
        defer {
            for (matches.items) |*b| b.value.destroy(self.allocator);
            matches.deinit(self.allocator);
        }
        while (true) {
            for (matches.items) |*b| b.value.destroy(self.allocator);
            matches.clearRetainingCapacity();
            if (row.cond.isNone()) {
                var body_val = try self.evalExpr(row.body);
                body_val.destroy(self.allocator);
                continue;
            }
            var cond = try self.evalExpr(row.cond.unwrap());
            if (row.is_pattern and !row.pattern.isNone()) {
                if (!try self.matchPattern(self.ast, cond, row.pattern.unwrap(), &matches)) {
                    cond.destroy(self.allocator);
                    break;
                }
                cond.destroy(self.allocator);
                var scope = try self.pushBindings(&matches);
                defer scope.deinit();
                matches.clearRetainingCapacity();
                var body_val = try self.evalExpr(row.body);
                body_val.destroy(self.allocator);
            } else {
                const b = try self.valueToBool(cond);
                cond.destroy(self.allocator);
                if (!b) break;
                var body_val = try self.evalExpr(row.body);
                body_val.destroy(self.allocator);
            }
        }
        return Value{ .Void = {} };
    }

    fn evalLiteral(self: *Interpreter, l: ast.Rows.Literal) !Value {
        return switch (l.kind) {
            .int => Value{ .Int = @intCast(l.data.int.value) },
            .float => Value{ .Float = l.data.float.value },
            .bool => Value{ .Bool = l.data.bool },
            .char => Value{ .Int = @intCast(l.data.char) },
            .string => Value{ .String = try self.allocator.dupe(u8, self.ast.exprs.strs.get(l.data.string)) },
            .imaginary => Value{ .Float = l.data.imaginary.value },
        };
    }

    fn evalIdent(self: *Interpreter, expr: ast.ExprId) !Value {
        const name = self.ast.exprs.get(.Ident, expr).name;
        if (try self.lookup(name)) |v| return v;
        const ts = self.ast.type_info.store;
        if (self.symtab) |t| if (t.lookup(t.currentId(), name)) |sid| if (!t.syms.get(sid).origin_decl.isNone()) {
            const did = t.syms.get(sid).origin_decl.unwrap();
            if (did.toRaw() < self.ast.type_info.decl_types.items.len) if (self.ast.type_info.decl_types.items[did.toRaw()]) |ty|
                if (ts.getKind(ty) == .TypeType) return Value{ .Type = ts.get(.TypeType, ty).of };
        };
        const idx = expr.toRaw();
        if (idx < self.ast.type_info.expr_types.items.len) if (self.ast.type_info.expr_types.items[idx]) |ty|
            if (ts.getKind(ty) == .TypeType) return Value{ .Type = ts.get(.TypeType, ty).of };

        if (self.ast.type_info.getExport(name)) |e| return Value{ .Type = e.ty };
        if (comptime_mod.builtinTypeId(ts, self.ast.exprs.strs.get(name))) |t| return Value{ .Type = t };

        for (self.ast.exprs.decl_pool.slice(self.ast.unit.decls)) |d| {
            const r = self.ast.exprs.Decl.get(d);
            if (!r.pattern.isNone()) if (self.ast.kind(r.pattern.unwrap()) == .Binding)
                if (self.ast.pats.get(.Binding, r.pattern.unwrap()).name.eq(name))
                    if (isTypeExpr(self.ast.kind(r.value))) return self.evalExpr(r.value);
        }
        return Error.BindingNotFound;
    }
    fn isTypeExpr(k: ast.ExprKind) bool {
        return switch (k) {
            .Literal, .Import, .Call, .FieldAccess, .MlirBlock, .TupleType, .ArrayType, .DynArrayType, .MapType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => true,
            else => false,
        };
    }
    fn evalBinary(self: *Interpreter, row: ast.Rows.Binary) !Value {
        var l = try self.evalExpr(row.left);
        defer l.destroy(self.allocator);
        var r = try self.evalExpr(row.right);
        defer r.destroy(self.allocator);
        return switch (row.op) {
            .add => mathOp(l, r, .Add),
            .sub => mathOp(l, r, .Sub),
            .mul => mathOp(l, r, .Mul),
            .div => mathOp(l, r, .Div),
            .mod => blk: {
                const denom = try self.expectInt(r);
                if (denom == 0) return Error.DivisionByZero;
                break :blk Value{ .Int = @rem(try self.expectInt(l), denom) };
            },
            .logical_and => Value{ .Bool = (try self.valueToBool(l)) and (try self.valueToBool(r)) },
            .logical_or => Value{ .Bool = (try self.valueToBool(l)) or (try self.valueToBool(r)) },
            .shl => Value{ .Int = try self.expectInt(l) << @as(u7, @intCast(try self.expectInt(r))) },
            .shr => Value{ .Int = try self.expectInt(l) >> @as(u7, @intCast(try self.expectInt(r))) },
            .bit_and => Value{ .Int = (try self.expectInt(l)) & (try self.expectInt(r)) },
            .bit_or => Value{ .Int = (try self.expectInt(l)) | (try self.expectInt(r)) },
            .bit_xor => Value{ .Int = (try self.expectInt(l)) ^ (try self.expectInt(r)) },
            .lt => Value{ .Bool = try cmpOp(l, r, .Lt) },
            .lte => Value{ .Bool = try cmpOp(l, r, .Lte) },
            .gt => Value{ .Bool = try cmpOp(l, r, .Gt) },
            .gte => Value{ .Bool = try cmpOp(l, r, .Gte) },
            .eq => Value{ .Bool = self.valuesEqual(l, r) },
            .neq => Value{ .Bool = !self.valuesEqual(l, r) },
            else => Error.InvalidBinaryOperand,
        };
    }
    const Op = enum { Add, Sub, Mul, Div };
    fn mathOp(l: Value, r: Value, op: Op) !Value {
        switch (l) {
            .Int => |li| switch (r) {
                .Int => |ri| if (op == .Div and ri == 0) return error.DivisionByZero else return Value{ .Int = switch (op) {
                    .Add => li + ri,
                    .Sub => li - ri,
                    .Mul => li * ri,
                    .Div => @divTrunc(li, ri),
                } },
                .Float => |rf| return Value{ .Float = fOp(@as(f64, @floatFromInt(li)), rf, op) },
                else => {},
            },
            .Float => |lf| switch (r) {
                .Int => |ri| return Value{ .Float = fOp(lf, @as(f64, @floatFromInt(ri)), op) },
                .Float => |rf| return Value{ .Float = fOp(lf, rf, op) },
                else => {},
            },
            else => {},
        }
        return error.InvalidBinaryOperand;
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
    fn cmpOp(l: Value, r: Value, op: Cmp) !bool {
        switch (l) {
            .Int => |li| switch (r) {
                .Int => |ri| return cOp(li, ri, op),
                .Float => |rf| return cOp(@as(f64, @floatFromInt(li)), rf, op),
                else => {},
            },
            .Float => |lf| switch (r) {
                .Int => |ri| return cOp(lf, @as(f64, @floatFromInt(ri)), op),
                .Float => |rf| return cOp(lf, rf, op),
                else => {},
            },
            else => {},
        }
        return error.InvalidBinaryOperand;
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
        var v = try self.evalExpr(row.expr);
        if (row.op == .address_of) {
            const p = try self.allocator.create(Value);
            p.* = v;
            return Value{ .Pointer = p };
        }
        defer v.destroy(self.allocator);
        return switch (row.op) {
            .pos => Value{ .Int = try self.expectInt(v) },
            .neg => Value{ .Int = -(try self.expectInt(v)) },
            .logical_not => Value{ .Bool = !(try self.valueToBool(v)) },
            else => Error.InvalidBinaryOperand,
        };
    }
    fn evalIf(self: *Interpreter, row: ast.Rows.If) !Value {
        var c = try self.evalExpr(row.cond);
        defer c.destroy(self.allocator);
        if (try self.valueToBool(c)) return self.evalExpr(row.then_block);
        return if (!row.else_block.isNone()) self.evalExpr(row.else_block.unwrap()) else Value{ .Void = {} };
    }

    fn evalReturn(self: *Interpreter, row: ast.Rows.Return) !Value {
        return if (!row.value.isNone()) self.evalExpr(row.value.unwrap()) else Value{ .Void = {} };
    }

    pub fn setBinding(self: *Interpreter, name: ast.StrId, value: Value) !void {
        if (self.ast.type_info.lookupComptimeBindingType(name)) |t| try self.ast.type_info.setComptimeBinding(name, t, try comptime_mod.cloneComptimeValue(self.ast.type_info.gpa, value));
        if (self.findBinding(name)) |b| {
            b.value.destroy(self.allocator);
            b.value = value;
        } else try self.bindings.append(self.allocator, .{ .name = name, .value = value });
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
        return switch (v) {
            .String => |s| Value{ .String = try self.allocator.dupe(u8, s) },
            .Sequence => |s| blk: {
                var l = try std.ArrayListUnmanaged(Value).initCapacity(self.allocator, s.values.items.len);
                errdefer {
                    for (l.items) |*x| x.destroy(self.allocator);
                    l.deinit(self.allocator);
                }
                for (s.values.items) |i| l.appendAssumeCapacity(try self.cloneValue(i));
                break :blk Value{ .Sequence = .{ .values = l } };
            },
            .Struct => |s| blk: {
                var l = try std.ArrayListUnmanaged(StructField).initCapacity(self.allocator, s.fields.items.len);
                errdefer {
                    for (l.items) |*x| x.value.destroy(self.allocator);
                    l.deinit(self.allocator);
                }
                for (s.fields.items) |f| l.appendAssumeCapacity(.{ .name = f.name, .value = try self.cloneValue(f.value) });
                break :blk Value{ .Struct = .{ .fields = l, .owner = s.owner } };
            },
            .Map => |m| blk: {
                var l = try std.ArrayListUnmanaged(MapEntry).initCapacity(self.allocator, m.entries.items.len);
                errdefer {
                    for (l.items) |*x| {
                        x.key.destroy(self.allocator);
                        x.value.destroy(self.allocator);
                    }
                    l.deinit(self.allocator);
                }
                for (m.entries.items) |e| l.appendAssumeCapacity(.{ .key = try self.cloneValue(e.key), .value = try self.cloneValue(e.value) });
                break :blk Value{ .Map = .{ .entries = l } };
            },
            .Pointer => |p| {
                const n = try self.allocator.create(Value);
                n.* = try self.cloneValue(p.*);
                return Value{ .Pointer = n };
            },
            .Variant => |val| {
                const payload = if (val.payload) |p| blk: {
                    const n = try self.allocator.create(Value);
                    n.* = try self.cloneValue(p.*);
                    break :blk n;
                } else null;
                return Value{ .Variant = .{ .tag = val.tag, .payload = payload } };
            },
            .Function => Value{ .Function = v.Function },
            .MlirModule => |mod| Value{ .MlirModule = mlir.Module.fromOperation(mlir.Operation.clone(mod.getOperation())) },
            .Code => |code| blk: {
                var captures = try std.ArrayList(comptime_mod.CodeBinding).initCapacity(self.allocator, code.captures.items.len);
                errdefer {
                    for (captures.items) |*binding| binding.value.destroy(self.allocator);
                    captures.deinit(self.allocator);
                }
                for (code.captures.items) |binding| {
                    captures.appendAssumeCapacity(.{ .name = binding.name, .value = try self.cloneValue(binding.value) });
                }
                break :blk Value{ .Code = .{ .block = code.block, .ast = code.ast, .captures = captures } };
            },
            else => v,
        };
    }

    fn expectInt(self: *Interpreter, v: Value) !i128 {
        _ = self;
        return switch (v) {
            .Int => |i| i,
            .Bool => |b| if (b) 1 else 0,
            else => Error.InvalidBinaryOperand,
        };
    }
    fn valueToBool(self: *Interpreter, v: Value) !bool {
        _ = self;
        return switch (v) {
            .Bool => |b| b,
            .Int => |i| i != 0,
            .Float => |f| f != 0.0,
            else => Error.InvalidType,
        };
    }
    fn findStructField(self: *Interpreter, sv: StructValue, name: ast.StrId) ?*StructField {
        _ = self;
        for (sv.fields.items) |*f| if (f.name.eq(name)) return f;
        return null;
    }

    fn valuesEqual(self: *Interpreter, l: Value, r: Value) bool {
        return switch (l) {
            .Int => |i| switch (r) {
                .Int => |j| i == j,
                .Float => |f| @as(f64, @floatFromInt(i)) == f,
                .Bool => |b| i == @intFromBool(b),
                else => false,
            },
            .Float => |f| switch (r) {
                .Float => |g| f == g,
                .Int => |i| f == @as(f64, @floatFromInt(i)),
                .Bool => |b| f == @as(f64, @floatFromInt(@intFromBool(b))),
                else => false,
            },
            .Bool => |b| switch (r) {
                .Bool => |c| b == c,
                .Int => |i| @intFromBool(b) == i,
                .Float => |f| @as(f64, @floatFromInt(@intFromBool(b))) == f,
                else => false,
            },
            .String => |s| r == .String and std.mem.eql(u8, s, r.String),
            .Sequence => |s| r == .Sequence and s.values.items.len == r.Sequence.values.items.len and blk: {
                for (s.values.items, r.Sequence.values.items) |a, b| if (!self.valuesEqual(a, b)) break :blk false;
                break :blk true;
            },
            .Struct => |s| r == .Struct and s.fields.items.len == r.Struct.fields.items.len and (if (s.owner) |o| if (r.Struct.owner) |p| o.eq(p) else false else r.Struct.owner == null) and blk: {
                for (s.fields.items, r.Struct.fields.items) |a, b| if (!a.name.eq(b.name) or !self.valuesEqual(a.value, b.value)) break :blk false;
                break :blk true;
            },
            .Map => |m| r == .Map and m.entries.items.len == r.Map.entries.items.len and blk: {
                for (m.entries.items, r.Map.entries.items) |a, b| if (!self.valuesEqual(a.key, b.key) or !self.valuesEqual(a.value, b.value)) break :blk false;
                break :blk true;
            },
            .Range => |g| r == .Range and g.start == r.Range.start and g.end == r.Range.end and g.inclusive == r.Range.inclusive,
            .Function => |f| r == .Function and f.expr.eq(r.Function.expr),
            else => false,
        };
    }

    fn matchPattern(self: *Interpreter, past: *ast.Ast, val: Value, pid: ast.PatternId, matches: *std.ArrayListUnmanaged(Binding)) !bool {
        switch (past.kind(pid)) {
            .Wildcard => return true,
            .Literal => {
                var lit = try self.evalExpr(past.pats.get(.Literal, pid).expr);
                defer lit.destroy(self.allocator);
                return self.valuesEqual(val, lit);
            },
            .Binding => {
                var v = try self.cloneValue(val);
                errdefer v.destroy(self.allocator);
                try matches.append(self.allocator, .{ .name = past.pats.get(.Binding, pid).name, .value = v });
                return true;
            },
            .Tuple => {
                if (val != .Sequence) return false;
                const r = past.pats.get(.Tuple, pid);
                const ps = past.pats.pat_pool.slice(r.elems);
                if (val.Sequence.values.items.len != ps.len) return false;
                for (ps, 0..) |p, i| if (!try self.matchPattern(past, val.Sequence.values.items[i], p, matches)) {
                    self.rollbackBindings(matches, matches.items.len - i);
                    return false;
                };
                return true;
            },
            .Slice => {
                if (val != .Sequence) return false;
                const r = past.pats.get(.Slice, pid);
                const ps = past.pats.pat_pool.slice(r.elems);
                const items = val.Sequence.values.items;
                const fix = if (r.has_rest) @as(usize, @intCast(r.rest_index)) else ps.len;
                if (items.len < fix) return false;
                for (ps[0..fix], 0..) |p, i| if (!try self.matchPattern(past, items[i], p, matches)) {
                    self.rollbackBindings(matches, matches.items.len - i);
                    return false;
                };
                if (!r.has_rest) return items.len == ps.len;
                if (@as(usize, @intCast(r.rest_index)) > items.len) return false;
                if (!r.rest_binding.isNone()) {
                    var rv = try self.cloneValue(val);
                    defer rv.destroy(self.allocator);
                    const mark = matches.items.len;
                    if (!try self.matchPattern(past, rv, r.rest_binding.unwrap(), matches)) {
                        self.rollbackBindings(matches, mark);
                        return false;
                    }
                }
                return true;
            },
            .Struct => {
                if (val != .Struct) return false;
                const r = past.pats.get(.Struct, pid);
                const fs = past.pats.field_pool.slice(r.fields);
                if (!r.has_rest and val.Struct.fields.items.len != fs.len) return false;
                const mark = matches.items.len;
                for (fs) |fid| {
                    const f = past.pats.StructField.get(fid);
                    const sf = self.findStructField(val.Struct, f.name) orelse return false;
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
                var v = try self.cloneValue(val);
                errdefer v.destroy(self.allocator);
                try matches.append(self.allocator, .{ .name = r.binder, .value = v });
                return true;
            },
            else => return false,
        }
    }
    fn rollbackBindings(self: *Interpreter, m: *std.ArrayListUnmanaged(Binding), to: usize) void {
        for (m.items[to..]) |*b| b.value.destroy(self.allocator);
        m.shrinkRetainingCapacity(to);
    }

    pub fn captureBindingSnapshot(self: *Interpreter, matches: *std.ArrayListUnmanaged(Binding)) !BindingSnapshot {
        var s = try std.ArrayListUnmanaged(Binding).initCapacity(self.allocator, matches.items.len);
        errdefer {
            for (s.items) |*b| b.value.destroy(self.allocator);
            s.deinit(self.allocator);
        }
        var h = std.hash.Wyhash.init(0);
        for (matches.items) |b| {
            s.appendAssumeCapacity(.{ .name = b.name, .value = try self.cloneValue(b.value) });
            h.update(std.mem.asBytes(&b.name.toRaw()));
            h.update(std.mem.asBytes(&comptime_mod.hashComptimeValue(b.value)));
        }
        return BindingSnapshot{ .bindings = s, .hash = h.final() };
    }

    pub fn specializeFunction(self: *Interpreter, decl: ast.DeclId, matches: *std.ArrayListUnmanaged(Binding)) !SpecializationResult {
        var h = std.hash.Wyhash.init(0);
        for (matches.items) |b| {
            h.update(std.mem.asBytes(&b.name.toRaw()));
            h.update(std.mem.asBytes(&comptime_mod.hashComptimeValue(b.value)));
        }
        const key = FunctionKey{ .decl_id = decl, .bindings_hash = h.final() };
        const map_hash = (@as(u128, key.bindings_hash) << 32) | key.decl_id.toRaw();

        if (self.specializations.getPtr(map_hash)) |e| if (e.key.decl_id.eq(key.decl_id) and e.key.bindings_hash == key.bindings_hash) {
            var c = try std.ArrayListUnmanaged(Binding).initCapacity(self.allocator, e.bindings.bindings.items.len);
            errdefer {
                for (c.items) |*b| b.value.destroy(self.allocator);
                c.deinit(self.allocator);
            }
            for (e.bindings.bindings.items) |b| c.appendAssumeCapacity(.{ .name = b.name, .value = try self.cloneValue(b.value) });
            return SpecializationResult{ .func = .{ .expr = e.func_expr, .ast = self.ast }, .snapshot = .{ .bindings = c, .hash = e.bindings.hash } };
        };
        var s = try self.captureBindingSnapshot(matches);
        errdefer s.destroy(self.allocator);
        var r = try std.ArrayListUnmanaged(Binding).initCapacity(self.allocator, s.bindings.items.len);
        errdefer {
            for (r.items) |*b| b.value.destroy(self.allocator);
            r.deinit(self.allocator);
        }
        for (s.bindings.items) |b| r.appendAssumeCapacity(.{ .name = b.name, .value = try self.cloneValue(b.value) });

        try self.specializations.put(map_hash, .{ .key = key, .func_expr = self.ast.exprs.Decl.get(decl).value, .bindings = s });
        return SpecializationResult{ .func = .{ .expr = self.ast.exprs.Decl.get(decl).value, .ast = self.ast }, .snapshot = .{ .bindings = r, .hash = s.hash } };
    }

    pub const BindingScope = struct {
        interp: *Interpreter,
        prev_len: usize,
        replaced: std.ArrayListUnmanaged(Binding),
        pub fn deinit(self: *BindingScope) void {
            if (self.interp.bindings.items.len > self.prev_len) {
                for (self.interp.bindings.items[self.prev_len..]) |*b| b.value.destroy(self.interp.allocator);
                self.interp.bindings.shrinkRetainingCapacity(self.prev_len);
            }
            for (self.replaced.items) |b| if (self.interp.findBinding(b.name)) |e| {
                e.value.destroy(self.interp.allocator);
                e.value = b.value;
            };
            self.replaced.deinit(self.interp.allocator);
        }
    };

    pub fn pushBindings(self: *Interpreter, matches: *std.ArrayListUnmanaged(Binding)) !BindingScope {
        var s = BindingScope{ .interp = self, .prev_len = self.bindings.items.len, .replaced = .{} };
        errdefer s.deinit();
        for (matches.items) |*b| {
            const v = b.value;
            b.value = .Void;
            if (self.findBinding(b.name)) |e| {
                try s.replaced.append(self.allocator, .{ .name = b.name, .value = try self.cloneValue(e.value) });
                e.value.destroy(self.allocator);
                e.value = v;
            } else try self.bindings.append(self.allocator, .{ .name = b.name, .value = v });
        }
        return s;
    }
};
