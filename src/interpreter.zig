const std = @import("std");
const ast = @import("ast.zig");
const comptime_mod = @import("comptime.zig");
const types = @import("types.zig");

const Value = comptime_mod.ComptimeValue;
const Sequence = comptime_mod.Sequence;
const StructField = comptime_mod.StructField;
const StructValue = comptime_mod.StructValue;
const RangeValue = comptime_mod.RangeValue;
const MapEntry = comptime_mod.MapEntry;
const MapValue = comptime_mod.MapValue;
/// Key identifying a method implementation by owner type + method name.
const MethodKey = struct {
    /// Owner type or module for this method entry.
    owner: ast.StrId,
    /// Method identifier within the owner.
    method: ast.StrId,
};
/// Mapping from method signatures to AST expression IDs.
const MethodMap = std.AutoHashMap(MethodKey, ast.ExprId);
const FunctionValue = comptime_mod.FunctionValue;
/// Helper type for comparing numeric values regardless of int/float representation.
const NumericValue = union(enum) {
    Int: i128,
    Float: f64,
};

/// Represents a single runtime binding (name → comptime value).
pub const Binding = struct {
    /// Interned identifier for the bound name.
    name: ast.StrId,
    /// Stored comptime value for the binding.
    value: Value,
};

/// Identifies a specialized function by its declaration and bound arguments.
const FunctionKey = struct {
    /// Declaration ID of the specialized function.
    decl_id: ast.DeclId,
    /// Hash of the binding snapshot driving the specialization.
    bindings_hash: u64,
};

/// Compare two function specialization keys for equality.
fn keysEqual(a: FunctionKey, b: FunctionKey) bool {
    return a.decl_id.eq(b.decl_id) and a.bindings_hash == b.bindings_hash;
}

/// Cache entry for a function specialization computed via its bindings.
const FunctionSpecializationEntry = struct {
    /// Signature that identifies this specialization.
    key: FunctionKey,
    /// Expression ID of the specialized function body.
    func_expr: ast.ExprId,
    /// Snapshot of bindings captured when the specialization was created.
    bindings: BindingSnapshot,

    /// Release resources held by this specialization entry.
    fn destroy(self: *FunctionSpecializationEntry, allocator: std.mem.Allocator) void {
        self.bindings.destroy(allocator);
    }
};

/// Result of specializing a function: the runtime function + binding snapshot.
pub const SpecializationResult = struct {
    /// Runtime `FunctionValue` that represents the specialized body.
    func: FunctionValue,
    /// Binding snapshot captured when the specialization was produced.
    snapshot: BindingSnapshot,
};

/// Immutable snapshot of bindings captured for memoizing function calls.
pub const BindingSnapshot = struct {
    /// Ordered list of bound names/values.
    bindings: std.ArrayList(Binding),
    /// Hash of the bindings used for quick lookup.
    hash: u64,

    /// Lookup a binding by its name inside the snapshot.
    pub fn lookup(self: *BindingSnapshot, name: ast.StrId) ?*Binding {
        for (self.bindings.items) |*binding| if (binding.name.eq(name)) return binding;
        return null;
    }

    /// Release all owned values and reset the hash.
    pub fn destroy(self: *BindingSnapshot, allocator: std.mem.Allocator) void {
        for (self.bindings.items) |*binding| binding.value.destroy(allocator);
        self.bindings.deinit(allocator);
        self.hash = 0;
    }
};

/// Light-weight interpreter used during `comptime` evaluation.
pub const Interpreter = struct {
    /// Allocator used for overriding temporaries and stored values.
    allocator: std.mem.Allocator,
    /// AST unit being interpreted.
    ast: *ast.Ast,
    /// Symbol table for resolver requiring package-level context.
    symtab: ?*@import("symbols.zig").SymbolStore,
    /// Compilation unit used for import resolution and exports.
    compilation_unit: ?*@import("package.zig").CompilationUnit,
    /// Top-level binding list managed by the interpreter.
    bindings: std.ArrayList(Binding),
    /// Registered methods available for dispatch.
    method_table: MethodMap,
    /// Cached function specializations keyed by binding states.
    specializations: std.AutoHashMap(u128, FunctionSpecializationEntry),

    /// Optional callback to retrieve the symbol table for a given file ID (used for imports).
    get_module_symtab: ?*const fn (ctx: *anyopaque, file_id: u32) ?*@import("symbols.zig").SymbolStore = null,
    /// Context pointer passed to `get_module_symtab`.
    checker_context: *anyopaque = undefined,

    /// Errors that the interpreter can emit when the AST is malformed or runtime errors occur.
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

    /// Initialize an interpreter for `ast_unit` with optional `symtab`/`compilation_unit`.
    pub fn init(
        allocator: std.mem.Allocator,
        ast_unit: *ast.Ast,
        symtab: ?*@import("symbols.zig").SymbolStore,
        compilation_unit: ?*@import("package.zig").CompilationUnit,
        get_module_symtab: ?*const fn (ctx: *anyopaque, file_id: u32) ?*@import("symbols.zig").SymbolStore,
        checker_context: *anyopaque,
    ) anyerror!Interpreter {
        var interp = Interpreter{
            .allocator = allocator,
            .ast = ast_unit,
            .symtab = symtab,
            .compilation_unit = compilation_unit,
            .get_module_symtab = get_module_symtab,
            .checker_context = checker_context,
            .bindings = std.ArrayList(Binding).empty,
            .method_table = .init(allocator),
            .specializations = .init(allocator),
        };
        var success = false;
        defer if (!success) interp.method_table.deinit();
        defer if (!success) interp.specializations.deinit();
        try interp.registerMethods();
        success = true;
        return interp;
    }

    /// Release all owned bindings, methods, and specialization caches.
    pub fn deinit(self: *Interpreter) void {
        for (self.bindings.items) |*binding| binding.value.destroy(self.allocator);
        self.bindings.deinit(self.allocator);
        self.method_table.deinit();
        var iter = self.specializations.iterator();
        while (iter.next()) |entry| entry.value_ptr.*.destroy(self.allocator);
        self.specializations.deinit();
    }

    /// Evaluate the AST expression `expr` and return its runtime value.
    pub fn evalExpr(self: *Interpreter, expr: ast.ExprId) anyerror!Value {
        return switch (self.ast.kind(expr)) {
            .Literal => self.evalLiteral(self.ast.exprs.get(.Literal, expr)),
            .NullLit => Value{ .Void = {} },
            .UndefLit => Value{ .Void = {} },
            .Ident => self.evalIdent(expr, self.ast.exprs.get(.Ident, expr)),
            .Import => self.evalImport(expr),
            .Block => self.evalBlock(self.ast.exprs.get(.Block, expr)),
            .ComptimeBlock => {
                const block_row = self.ast.exprs.get(.ComptimeBlock, expr);
                const block_expr = self.ast.exprs.get(.Block, block_row.block);
                return try self.evalBlock(block_expr);
            },
            .Binary => self.evalBinary(self.ast.exprs.get(.Binary, expr)),
            .Unary => self.evalUnary(self.ast.exprs.get(.Unary, expr)),
            .If => self.evalIf(self.ast.exprs.get(.If, expr)),
            .FunctionLit => self.evalFunctionLit(expr),
            .ArrayLit => self.evalSequence(self.ast.exprs.get(.ArrayLit, expr).elems),
            .TupleLit => self.evalSequence(self.ast.exprs.get(.TupleLit, expr).elems),
            .MapLit => self.evalMapLit(self.ast.exprs.get(.MapLit, expr)),
            .Call => self.evalCall(self.ast.exprs.get(.Call, expr)),
            .FieldAccess => self.evalFieldAccess(self.ast.exprs.get(.FieldAccess, expr)),
            .IndexAccess => self.evalIndexAccess(self.ast.exprs.get(.IndexAccess, expr)),
            .StructLit => self.evalStructLit(self.ast.exprs.get(.StructLit, expr)),
            .Range => self.evalRange(self.ast.exprs.get(.Range, expr)),
            .Match => self.evalMatch(self.ast.exprs.get(.Match, expr)),
            .For => self.evalFor(self.ast.exprs.get(.For, expr)),
            .While => self.evalWhile(self.ast.exprs.get(.While, expr)),
            .Return => self.evalReturn(self.ast.exprs.get(.Return, expr)),
            .EnumType => self.evalEnumType(self.ast.exprs.get(.EnumType, expr)),
            .ArrayType => self.evalArrayType(self.ast.exprs.get(.ArrayType, expr)),
            .DynArrayType => self.evalDynArrayType(self.ast.exprs.get(.DynArrayType, expr)),
            .SliceType => self.evalSliceType(self.ast.exprs.get(.SliceType, expr)),
            .MapType => self.evalMapType(self.ast.exprs.get(.MapType, expr)),
            .OptionalType => self.evalOptionalType(self.ast.exprs.get(.OptionalType, expr)),
            .VariantType => self.evalVariantType(self.ast.exprs.get(.VariantType, expr)),
            .ErrorType => self.evalVariantType(self.ast.exprs.get(.ErrorType, expr)),
            .ErrorSetType => self.evalErrorSetType(self.ast.exprs.get(.ErrorSetType, expr)),
            .StructType => self.evalStructType(self.ast.exprs.get(.StructType, expr)),
            .UnionType => self.evalUnionType(self.ast.exprs.get(.UnionType, expr)),
            .Cast => self.evalCast(self.ast.exprs.get(.Cast, expr)),
            .PointerType => self.evalPointerType(self.ast.exprs.get(.PointerType, expr)),
            .Deref => self.evalDeref(self.ast.exprs.get(.Deref, expr)),
            .SimdType => self.evalSimdType(self.ast.exprs.get(.SimdType, expr)),
            .TensorType => self.evalTensorType(self.ast.exprs.get(.TensorType, expr)),
            .TypeType => Value{ .Type = self.ast.type_info.store.tType() },
            .AnyType => Value{ .Type = self.ast.type_info.store.tAny() },
            .NoreturnType => Value{ .Type = self.ast.type_info.store.tNoreturn() },
            .Catch => self.evalCatch(self.ast.exprs.get(.Catch, expr)),
            .OptionalUnwrap => self.evalOptionalUnwrap(self.ast.exprs.get(.OptionalUnwrap, expr)),
            .ErrUnwrap => self.evalErrUnwrap(self.ast.exprs.get(.ErrUnwrap, expr)),
            .Defer => self.evalDefer(self.ast.exprs.get(.Defer, expr)),
            .TypeOf => self.evalTypeOf(self.ast.exprs.get(.TypeOf, expr)),
            .MlirBlock => self.evalMlirBlock(expr),
            .Await => Value{ .Void = {} },
            else => std.debug.panic("Unsupported expr: {}", .{self.ast.kind(expr)}),
        };
    }

    /// Evaluate an MLIR block by interpolating splices into the string.
    fn evalMlirBlock(self: *Interpreter, expr: ast.ExprId) anyerror!Value {
        const block = self.ast.exprs.get(.MlirBlock, expr);
        const pieces = self.ast.exprs.mlir_piece_pool.slice(block.pieces);

        var buf = std.ArrayList(u8){};
        defer buf.deinit(self.allocator);
        const writer = buf.writer(self.allocator);

        for (pieces) |pid| {
            const piece = self.ast.exprs.MlirPiece.get(pid);
            switch (piece.kind) {
                .literal => {
                    const text = self.ast.exprs.strs.get(piece.text);
                    try buf.appendSlice(self.allocator, text);
                },
                .splice => {
                    // Splice: lookup binding and format it
                    if (try self.lookup(piece.text)) |val| {
                        var temp_val = val;
                        defer temp_val.destroy(self.allocator);

                        switch (temp_val) {
                            .Type => |ty| try self.ast.type_info.store.fmt(ty, writer),
                            .Int => |i| try writer.print("{}", .{i}),
                            .Float => |f| try writer.print("{}", .{f}),
                            .Bool => |b| try writer.print("{}", .{b}),
                            .String => |s| try writer.print("{s}", .{s}),
                            else => return Error.InvalidType, // Unsupported splice value
                        }
                    } else return Error.BindingNotFound;
                },
            }
        }

        const final_str = self.ast.type_info.store.strs.intern(buf.items);

        return switch (block.kind) {
            .Type => Value{ .Type = self.ast.type_info.store.mkMlirType(final_str) },
            .Attribute => Value{ .Type = self.ast.type_info.store.mkMlirAttribute(final_str) },
            .Module => Value{ .Type = self.ast.type_info.store.tMlirModule() },
            else => Value{ .Void = {} },
        };
    }

    /// Insert or replace `value` into the interpreter’s binding table under `name`.
    pub fn bind(self: *Interpreter, name: ast.StrId, value: Value) !void {
        try self.setBinding(name, value);
    }

    /// Retrieve a binding value by `name`, cloning it for the caller.
    pub fn lookup(self: *Interpreter, name: ast.StrId) anyerror!?Value {
        for (self.bindings.items) |binding| {
            if (binding.name.eq(name)) return try self.cloneValue(binding.value);
        }
        return null;
    }

    /// Evaluate a block of statements, returning the last value or void.
    fn evalBlock(self: *Interpreter, block: ast.Rows.Block) anyerror!Value {
        var last_value: ?Value = null;
        const stmts = self.ast.stmts.stmt_pool.slice(block.items);
        for (stmts) |stmt_id| {
            if (try self.evalStatement(stmt_id, &last_value)) |value| {
                if (last_value) |*prev| prev.destroy(self.allocator);
                return value;
            }
        }
        if (last_value) |value| return value;
        return Value{ .Void = {} };
    }

    /// Execute a statement, updating `last_value` when expression statements occur.
    fn evalStatement(self: *Interpreter, stmt_id: ast.StmtId, last_value: *?Value) anyerror!?Value {
        switch (self.ast.kind(stmt_id)) {
            .Expr => {
                const row = self.ast.stmts.get(.Expr, stmt_id);
                const result = try self.evalExpr(row.expr);
                if (last_value.*) |*prev| prev.destroy(self.allocator);
                last_value.* = result;
                return null;
            },
            .Decl => {
                const row = self.ast.stmts.get(.Decl, stmt_id);
                const decl = self.ast.exprs.Decl.get(row.decl);
                if (decl.pattern.isNone()) return Error.InvalidStatement;
                const pat_id = decl.pattern.unwrap();
                if (self.ast.kind(pat_id) != .Binding) return Error.InvalidStatement;
                const binding = self.ast.pats.get(.Binding, pat_id);
                const value = try self.evalExpr(decl.value);
                try self.setBinding(binding.name, value);
                return null;
            },
            .Assign => {
                const row = self.ast.stmts.get(.Assign, stmt_id);
                try self.evalAssignment(row);
                return null;
            },
            .Return => {
                const row = self.ast.stmts.get(.Return, stmt_id);
                if (row.value.isNone()) return Value{ .Void = {} };
                return try self.evalExpr(row.value.unwrap());
            },
            else => return Error.InvalidStatement,
        }
    }

    /// Return a `FunctionValue` that refers back to `expr`.
    fn evalFunctionLit(self: *Interpreter, expr: ast.ExprId) anyerror!Value {
        return Value{ .Function = .{ .expr = expr, .ast = self.ast } };
    }

    /// Evaluate an assignment statement and update the corresponding binding.
    fn evalAssignment(self: *Interpreter, row: ast.StmtRows.Assign) anyerror!void {
        if (self.ast.kind(row.left) != .Ident) return Error.InvalidStatement;
        const ident = self.ast.exprs.get(.Ident, row.left);
        const value = try self.evalExpr(row.right);
        try self.setBinding(ident.name, value);
    }

    /// Evaluate a cast expression by delegating to its inner expression.
    fn evalCast(self: *Interpreter, row: ast.Rows.Cast) anyerror!Value {
        const value = try self.evalExpr(row.expr);
        const target_ty = self.typeIdFromTypeExpr(row.ty) catch return value;
        const ts = self.ast.type_info.store;
        const target_kind = ts.getKind(target_ty);

        switch (value) {
            .Float => |f| {
                // Simple check for integer target types
                const is_int = switch (target_kind) {
                    .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
                    else => false,
                };
                if (is_int) {
                    return Value{ .Int = @as(i128, @intFromFloat(f)) };
                }
            },
            .Int => |i| {
                if (target_kind == .F32 or target_kind == .F64) {
                    return Value{ .Float = @as(f64, @floatFromInt(i)) };
                }
            },
            else => {},
        }
        return value;
    }

    /// Evaluate a `catch` expression and clone the result.
    fn evalCatch(self: *Interpreter, row: ast.Rows.Catch) anyerror!Value {
        var value = try self.evalExpr(row.expr);
        const result = try self.cloneValue(value);
        value.destroy(self.allocator);
        return result;
    }

    /// Evaluate `optional.unwrap` by cloning the underlying value.
    fn evalOptionalUnwrap(self: *Interpreter, row: ast.Rows.OptionalUnwrap) anyerror!Value {
        var value = try self.evalExpr(row.expr);
        const result = try self.cloneValue(value);
        value.destroy(self.allocator);
        return result;
    }

    /// Evaluate a `defer` block by executing the expression and discarding the result.
    fn evalDefer(self: *Interpreter, row: ast.Rows.Defer) anyerror!Value {
        var value = try self.evalExpr(row.expr);
        value.destroy(self.allocator);
        return Value{ .Void = {} };
    }

    /// Evaluate `err` propagation by cloning the underlying success value.
    fn evalErrUnwrap(self: *Interpreter, row: ast.Rows.ErrUnwrap) anyerror!Value {
        var value = try self.evalExpr(row.expr);
        const result = try self.cloneValue(value);
        value.destroy(self.allocator);
        return result;
    }

    /// Evaluate `typeof(expr)` by returning the stored compile-time type.
    fn evalTypeOf(self: *Interpreter, row: ast.Rows.TypeOf) anyerror!Value {
        const idx = row.expr.toRaw();
        if (idx < self.ast.type_info.expr_types.items.len) {
            if (self.ast.type_info.expr_types.items[idx]) |type_id| {
                return Value{ .Type = type_id };
            }
        }
        return Error.InvalidType;
    }

    /// Evaluate a pointer type expression, returning its `TypeId`.
    fn evalPointerType(self: *Interpreter, row: ast.Rows.PointerType) anyerror!Value {
        var elem_value = try self.evalExpr(row.elem);
        defer elem_value.destroy(self.allocator);
        return switch (elem_value) {
            .Type => |elem_ty| {
                const ts = self.ast.type_info.store;
                return Value{ .Type = ts.mkPtr(elem_ty, row.is_const) };
            },
            else => Error.InvalidType,
        };
    }

    /// Evaluate a dereference expression by unwrapping the pointer value.
    fn evalDeref(self: *Interpreter, row: ast.Rows.Deref) anyerror!Value {
        var ptr_value = try self.evalExpr(row.expr);
        defer ptr_value.destroy(self.allocator);
        return switch (ptr_value) {
            .Pointer => |target| try self.cloneValue(target.*),
            else => Error.InvalidType,
        };
    }

    /// Evaluate a `simd` type expression and return its `TypeId`.
    fn evalSimdType(self: *Interpreter, row: ast.Rows.SimdType) anyerror!Value {
        const elem_ty = try self.typeIdFromTypeExpr(row.elem);
        var lanes_value = try self.evalExpr(row.lanes);
        defer lanes_value.destroy(self.allocator);
        const lanes = switch (lanes_value) {
            .Int => |val| std.math.cast(u16, val) orelse return Error.InvalidType,
            else => return Error.InvalidType,
        };
        const ts = self.ast.type_info.store;
        return Value{ .Type = ts.mkSimd(elem_ty, lanes) };
    }

    /// Evaluate a `tensor` type expression, collecting each dimension.
    fn evalTensorType(self: *Interpreter, row: ast.Rows.TensorType) anyerror!Value {
        const elem_ty = try self.typeIdFromTypeExpr(row.elem);
        const shape_exprs = self.ast.exprs.expr_pool.slice(row.shape);
        const ts = self.ast.type_info.store;

        var dims = try std.ArrayList(usize).initCapacity(self.allocator, shape_exprs.len);
        defer dims.deinit(self.allocator);

        var idx: usize = 0;
        while (idx < shape_exprs.len) : (idx += 1) {
            const dim_expr_id = shape_exprs[idx];

            // Check for spread syntax `..expr` (Range with no start)
            var is_spread = false;
            var expr_to_eval = dim_expr_id;

            if (self.ast.kind(dim_expr_id) == .Range) {
                const rng = self.ast.exprs.get(.Range, dim_expr_id);
                if (rng.start.isNone() and !rng.end.isNone()) {
                    is_spread = true;
                    expr_to_eval = rng.end.unwrap();
                }
            }

            var dim_value = try self.evalExpr(expr_to_eval);
            defer dim_value.destroy(self.allocator);

            if (is_spread) {
                switch (dim_value) {
                    .Sequence => |seq| {
                        for (seq.values.items) |item| {
                            switch (item) {
                                .Int => |val| {
                                    const dim = std.math.cast(usize, val) orelse return Error.InvalidType;
                                    try dims.append(self.allocator, dim);
                                },
                                else => return Error.InvalidType,
                            }
                        }
                    },
                    else => return Error.InvalidType, // Spread expects a sequence
                }
            } else {
                switch (dim_value) {
                    .Int => |val| {
                        const dim = std.math.cast(usize, val) orelse return Error.InvalidType;
                        try dims.append(self.allocator, dim);
                    },
                    .Sequence => |seq| {
                        // Also support flattening if passed directly without spread?
                        // For now, assume explicit spread is required or single Sequence expands?
                        // Existing logic supported flattening Sequence, let's keep it.
                        for (seq.values.items) |item| {
                            switch (item) {
                                .Int => |val| {
                                    const dim = std.math.cast(usize, val) orelse return Error.InvalidType;
                                    try dims.append(self.allocator, dim);
                                },
                                else => return Error.InvalidType,
                            }
                        }
                    },
                    else => return Error.InvalidType,
                }
            }
        }

        const dims_slice = try ts.gpa.alloc(usize, dims.items.len);
        defer ts.gpa.free(dims_slice);
        @memcpy(dims_slice, dims.items);
        return Value{ .Type = ts.mkTensor(elem_ty, dims_slice) };
    }

    /// Evaluate a fixed-size array type expression.
    fn evalArrayType(self: *Interpreter, row: ast.Rows.ArrayType) anyerror!Value {
        const elem_ty = try self.typeIdFromTypeExpr(row.elem);
        var size_value = try self.evalExpr(row.size);
        defer size_value.destroy(self.allocator);
        const len = switch (size_value) {
            .Int => |val| std.math.cast(usize, val) orelse return Error.InvalidType,
            else => return Error.InvalidType,
        };
        return Value{ .Type = self.ast.type_info.store.mkArray(elem_ty, len) };
    }

    /// Evaluate a dynamic array type expression.
    fn evalDynArrayType(self: *Interpreter, row: ast.Rows.DynArrayType) anyerror!Value {
        const elem_ty = try self.typeIdFromTypeExpr(row.elem);
        const ts = self.ast.type_info.store;
        return Value{ .Type = ts.mkDynArray(elem_ty) };
    }

    /// Evaluate a slice type expression, honoring the constness flag.
    fn evalSliceType(self: *Interpreter, row: ast.Rows.SliceType) anyerror!Value {
        const elem_ty = try self.typeIdFromTypeExpr(row.elem);
        const ts = self.ast.type_info.store;
        return Value{ .Type = ts.mkSlice(elem_ty, row.is_const) };
    }

    /// Evaluate a map type expression with key/value type parameters.
    fn evalMapType(self: *Interpreter, row: ast.Rows.MapType) anyerror!Value {
        const ts = self.ast.type_info.store;
        const key_ty = try self.typeIdFromTypeExpr(row.key);
        const val_ty = try self.typeIdFromTypeExpr(row.value);
        return Value{ .Type = ts.mkMap(key_ty, val_ty) };
    }

    /// Evaluate an optional type expression wrapping a single element type.
    fn evalOptionalType(self: *Interpreter, row: ast.Rows.OptionalType) anyerror!Value {
        const elem_ty = try self.typeIdFromTypeExpr(row.elem);
        const ts = self.ast.type_info.store;
        return Value{ .Type = ts.mkOptional(elem_ty) };
    }

    /// Construct a struct type from its named fields.
    fn evalStructType(self: *Interpreter, row: ast.Rows.StructType) anyerror!Value {
        const ts = self.ast.type_info.store;
        const sfs = self.ast.exprs.sfield_pool.slice(row.fields);
        var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
        defer ts.gpa.free(buf);
        var i: usize = 0;
        while (i < sfs.len) : (i += 1) {
            const field = self.ast.exprs.StructField.get(sfs[i]);
            const field_ty = try self.typeIdFromTypeExpr(field.ty);
            buf[i] = .{ .name = field.name, .ty = field_ty };
        }
        const struct_ty = ts.mkStruct(buf, 0);
        return Value{ .Type = struct_ty };
    }

    /// Evaluate a variant type expression by describing each field payload.
    fn evalVariantType(self: *Interpreter, row: ast.Rows.VariantType) anyerror!Value {
        const ts = self.ast.type_info.store;
        const vfs = self.ast.exprs.vfield_pool.slice(row.fields);
        var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
        defer ts.gpa.free(buf);
        var i: usize = 0;
        while (i < vfs.len) : (i += 1) {
            const vf = self.ast.exprs.VariantField.get(vfs[i]);
            const payload_ty = try self.evalVariantFieldPayloadType(vf);
            buf[i] = .{ .name = vf.name, .ty = payload_ty };
        }
        return Value{ .Type = ts.mkVariant(buf) };
    }

    /// Resolve the payload type for a variant field, supporting tuples/structs.
    fn evalVariantFieldPayloadType(self: *Interpreter, field: ast.Rows.VariantField) anyerror!types.TypeId {
        const ts = self.ast.type_info.store;
        return switch (field.payload_kind) {
            .none => ts.tVoid(),
            .tuple => blk_tuple: {
                if (field.payload_elems.isNone()) break :blk_tuple ts.tVoid();
                const elems = self.ast.exprs.expr_pool.slice(field.payload_elems.asRange());
                var tuple_buf = try ts.gpa.alloc(types.TypeId, elems.len);
                defer ts.gpa.free(tuple_buf);
                var j: usize = 0;
                while (j < elems.len) : (j += 1) {
                    tuple_buf[j] = try self.typeIdFromTypeExpr(elems[j]);
                }
                return ts.mkTuple(tuple_buf);
            },
            .@"struct" => blk_struct: {
                if (field.payload_fields.isNone()) break :blk_struct ts.tVoid();
                const fields = self.ast.exprs.sfield_pool.slice(field.payload_fields.asRange());
                var field_buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                defer ts.gpa.free(field_buf);
                var j: usize = 0;
                while (j < fields.len) : (j += 1) {
                    const sf = self.ast.exprs.StructField.get(fields[j]);
                    const ty = try self.typeIdFromTypeExpr(sf.ty);
                    field_buf[j] = .{ .name = sf.name, .ty = ty };
                }
                return ts.mkStruct(field_buf, 0);
            },
        };
    }

    /// Evaluate an error set type, returning its element/error pair.
    fn evalErrorSetType(self: *Interpreter, row: ast.Rows.ErrorSetType) anyerror!Value {
        const ts = self.ast.type_info.store;
        const value_ty = try self.typeIdFromTypeExpr(row.value);
        const err_ty = try self.typeIdFromTypeExpr(row.err);
        return Value{ .Type = ts.mkErrorSet(value_ty, err_ty) };
    }

    /// Evaluate an import expression by retrieving the type of the referenced module.
    fn evalImport(self: *Interpreter, expr: ast.ExprId) anyerror!Value {
        const idx = expr.toRaw();
        if (idx >= self.ast.type_info.expr_types.items.len) return Error.InvalidType;
        if (self.ast.type_info.expr_types.items[idx]) |ty| {
            return Value{ .Type = ty };
        }
        return Error.InvalidType;
    }

    /// Evaluate a union type expression by collecting variant fields.
    fn evalUnionType(self: *Interpreter, row: ast.Rows.UnionType) anyerror!Value {
        const ts = self.ast.type_info.store;
        const sfs = self.ast.exprs.sfield_pool.slice(row.fields);
        var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
        defer ts.gpa.free(buf);
        var i: usize = 0;
        while (i < sfs.len) : (i += 1) {
            const field = self.ast.exprs.StructField.get(sfs[i]);
            const field_ty = try self.typeIdFromTypeExpr(field.ty);
            buf[i] = .{ .name = field.name, .ty = field_ty };
        }
        const union_ty = ts.mkUnion(buf);
        return Value{ .Type = union_ty };
    }

    /// Evaluate an enum literal by emitting its tag type and member list.
    fn evalEnumType(self: *Interpreter, row: ast.Rows.EnumType) anyerror!Value {
        const ts = self.ast.type_info.store;
        var tag_ty = ts.tI32();
        if (!row.discriminant.isNone()) {
            tag_ty = try self.typeIdFromTypeExpr(row.discriminant.unwrap());
        }

        const efs = self.ast.exprs.efield_pool.slice(row.fields);
        var member_buf = try ts.gpa.alloc(types.TypeStore.EnumMemberArg, efs.len);
        defer ts.gpa.free(member_buf);
        var next_value: i128 = 0;
        var i: usize = 0;
        while (i < efs.len) : (i += 1) {
            const enum_field = self.ast.exprs.EnumField.get(efs[i]);
            var current_value: i128 = next_value;
            if (!enum_field.value.isNone()) {
                var val = try self.evalExpr(enum_field.value.unwrap());
                current_value = switch (val) {
                    .Int => |v| v,
                    else => {
                        val.destroy(self.allocator);
                        return Error.InvalidType;
                    },
                };
                val.destroy(self.allocator);
            }
            member_buf[i] = .{ .name = enum_field.name, .value = @intCast(current_value) };
            next_value = current_value + 1;
        }
        const enum_ty = ts.mkEnum(member_buf, tag_ty);
        return Value{ .Type = enum_ty };
    }

    /// Evaluate a type expression and return its `TypeId`, using `typeof` fallback when needed.
    fn typeIdFromTypeExpr(self: *Interpreter, expr: ast.ExprId) anyerror!types.TypeId {
        const expr_index = expr.toRaw();
        if (expr_index < self.ast.type_info.expr_types.items.len) {
            if (self.ast.type_info.expr_types.items[expr_index]) |type_ty| {
                if (self.ast.type_info.store.getKind(type_ty) == .TypeType) {
                    return self.ast.type_info.store.get(.TypeType, type_ty).of;
                }
            }
        }
        var value = try self.evalExpr(expr);
        defer value.destroy(self.allocator);
        return switch (value) {
            .Type => |ty| ty,
            else => Error.InvalidType,
        };
    }

    /// Evaluate a function call expression, handling methods and variadic dispatch.
    fn evalCall(self: *Interpreter, row: ast.Rows.Call) anyerror!Value {
        var callee_value: Value = .Void;
        var method_receiver: ?Value = null;
        defer if (method_receiver) |*recv| recv.destroy(self.allocator);

        if (self.ast.kind(row.callee) == .FieldAccess) {
            const field_row = self.ast.exprs.get(.FieldAccess, row.callee);
            var parent = try self.evalExpr(field_row.parent);
            if (structOwner(parent)) |owner_name| {
                if (self.lookupMethod(owner_name, field_row.field)) |expr| {
                    callee_value = Value{ .Function = .{ .expr = expr, .ast = self.ast } };
                    method_receiver = parent;
                } else {
                    callee_value = try self.evalFieldAccessWithParent(field_row, &parent, true);
                }
            } else {
                callee_value = try self.evalFieldAccessWithParent(field_row, &parent, true);
            }
        } else {
            callee_value = try self.evalExpr(row.callee);
        }
        defer callee_value.destroy(self.allocator);

        var args = try self.evalCallArgs(row.args);
        defer args.deinit(self.allocator);
        defer for (args.items) |*value| value.destroy(self.allocator);

        if (method_receiver) |recv| {
            try args.insert(self.allocator, 0, recv);
            method_receiver = null;
        }

        return switch (callee_value) {
            .Function => |func| try self.callFunction(func, &args),
            else => Error.InvalidCall,
        };
    }

    /// Evaluate a range of expressions used as call arguments.
    fn evalCallArgs(self: *Interpreter, range: ast.RangeExpr) anyerror!std.ArrayList(Value) {
        const exprs = self.ast.exprs.expr_pool.slice(range);
        if (exprs.len == 0) return .empty;
        var list: std.ArrayList(Value) = try .initCapacity(self.allocator, exprs.len);
        var success = false;
        defer if (!success) {
            for (list.items) |*value| value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < exprs.len) : (idx += 1) {
            list.appendAssumeCapacity(try self.evalExpr(exprs[idx]));
        }
        success = true;
        return list;
    }

    /// Bind arguments/bindings and execute the `FunctionValue` body.
    fn callFunction(self: *Interpreter, func: FunctionValue, args: *std.ArrayList(Value)) anyerror!Value {
        const row = func.ast.exprs.get(.FunctionLit, func.expr);
        const params = func.ast.exprs.param_pool.slice(row.params);
        if (!row.flags.is_variadic and args.items.len > params.len) return Error.TooManyArguments;
        var matches = std.ArrayList(Binding){};
        defer matches.deinit(self.allocator);
        var idx: usize = 0;
        while (idx < params.len) : (idx += 1) {
            const param = func.ast.exprs.Param.get(params[idx]);
            const is_variadic_param = row.flags.is_variadic and idx == params.len - 1;
            var value: Value = .Void;
            if (is_variadic_param) {
                value = try self.collectVariadicArgs(args, idx);
            } else if (idx < args.items.len) {
                value = args.items[idx];
                args.items[idx] = .Void;
            } else if (!param.value.isNone()) {
                value = try self.evalExpr(param.value.unwrap());
            } else {
                return Error.MissingArgument;
            }
            if (param.pat.isNone()) {
                value.destroy(self.allocator);
                continue;
            }
            const pattern = param.pat.unwrap();
            const before = matches.items.len;
            if (!try self.matchPattern(func.ast, value, pattern, &matches)) {
                self.rollbackBindings(&matches, before);
                value.destroy(self.allocator);
                return Error.InvalidCall;
            }
            value.destroy(self.allocator);
        }
        var scope = try self.pushBindings(&matches);
        defer scope.deinit();
        if (row.body.isNone()) return Value{ .Void = {} };

        // Temporarily switch to the function's AST for evaluating the body
        const saved_ast = self.ast;
        self.ast = func.ast;
        defer self.ast = saved_ast;

        return try self.evalExpr(row.body.unwrap());
    }

    /// Collect remaining arguments starting at `start_idx` into a sequence value.
    fn collectVariadicArgs(self: *Interpreter, args: *std.ArrayList(Value), start_idx: usize) anyerror!Value {
        if (start_idx >= args.items.len) return Value{ .Sequence = .{ .values = .empty } };
        const extra = args.items.len - start_idx;
        var list: std.ArrayList(Value) = try .initCapacity(self.allocator, extra);
        var success = false;
        defer if (!success) {
            for (list.items) |*value| value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = start_idx;
        while (idx < args.items.len) : (idx += 1) {
            list.appendAssumeCapacity(args.items[idx]);
            args.items[idx] = .Void;
        }
        success = true;
        return Value{ .Sequence = .{ .values = list } };
    }

    /// Evaluate a literal sequence expression and return a sequence value.
    fn evalSequence(self: *Interpreter, expr_range: ast.RangeExpr) anyerror!Value {
        const exprs = self.ast.exprs.expr_pool.slice(expr_range);
        if (exprs.len == 0) return Value{ .Sequence = .{ .values = .empty } };
        var list: std.ArrayList(Value) = try .initCapacity(self.allocator, exprs.len);
        var success = false;
        defer if (!success) {
            for (list.items) |*value| value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < exprs.len) : (idx += 1) {
            const value = try self.evalExpr(exprs[idx]);
            list.appendAssumeCapacity(value);
        }
        success = true;
        return Value{ .Sequence = .{ .values = list } };
    }

    /// Evaluate a struct literal by mapping field expressions to values.
    fn evalStructLit(self: *Interpreter, row: ast.Rows.StructLit) anyerror!Value {
        const field_ids = self.ast.exprs.sfv_pool.slice(row.fields);
        const count = field_ids.len;
        if (count == 0) return Value{ .Struct = .{ .fields = .empty, .owner = self.structTypeName(row.ty) } };
        var list: std.ArrayList(StructField) = try .initCapacity(self.allocator, count);
        var success = false;
        defer if (!success) {
            for (list.items) |*field| field.value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < count) : (idx += 1) {
            const field = self.ast.exprs.StructFieldValue.get(field_ids[idx]);
            if (field.name.isNone()) return Error.InvalidStatement;
            const value = try self.evalExpr(field.value);
            list.appendAssumeCapacity(StructField{
                .name = field.name.unwrap(),
                .value = value,
            });
        }
        const owner = self.structTypeName(row.ty);
        success = true;
        return Value{ .Struct = .{ .fields = list, .owner = owner } };
    }

    /// Evaluate a map literal by computing key/value pairs.
    fn evalMapLit(self: *Interpreter, row: ast.Rows.MapLit) anyerror!Value {
        const entries = self.ast.exprs.kv_pool.slice(row.entries);
        if (entries.len == 0) return Value{ .Map = .{ .entries = .empty } };
        var map: std.ArrayList(MapEntry) = try .initCapacity(self.allocator, entries.len);
        var success = false;
        defer if (!success) {
            for (map.items) |*entry| {
                entry.key.destroy(self.allocator);
                entry.value.destroy(self.allocator);
            }
            map.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < entries.len) : (idx += 1) {
            const kv = self.ast.exprs.KeyValue.get(entries[idx]);
            const key = try self.evalExpr(kv.key);
            const value = try self.evalExpr(kv.value);
            map.appendAssumeCapacity(MapEntry{
                .key = key,
                .value = value,
            });
        }
        success = true;
        return Value{ .Map = .{ .entries = map } };
    }

    /// Decode the owner’s identifier from a type expression, if present.
    fn structTypeName(self: *Interpreter, ty: ast.OptExprId) ?ast.StrId {
        if (ty.isNone()) return null;
        return self.exprName(ty.unwrap());
    }

    /// Extract an identifier or field name from `expr` when possible.
    fn exprName(self: *Interpreter, expr: ast.ExprId) ?ast.StrId {
        return switch (self.ast.kind(expr)) {
            .Ident => self.ast.exprs.get(.Ident, expr).name,
            .FieldAccess => self.ast.exprs.get(.FieldAccess, expr).field,
            else => null,
        };
    }

    /// Evaluate a range literal, returning start/end values.
    fn evalRange(self: *Interpreter, row: ast.Rows.Range) anyerror!Value {
        if (row.start.isNone() or row.end.isNone()) return Error.InvalidStatement;
        var start = try self.evalExpr(row.start.unwrap());
        defer start.destroy(self.allocator);
        var end = try self.evalExpr(row.end.unwrap());
        defer end.destroy(self.allocator);
        const start_int = try expectInt(start);
        const end_int = try expectInt(end);
        return Value{ .Range = RangeValue{ .start = start_int, .end = end_int, .inclusive = row.inclusive_right } };
    }

    /// Evaluate field access expressions for sequences, structs, pointer targets, or types.
    fn evalFieldAccess(self: *Interpreter, row: ast.Rows.FieldAccess) anyerror!Value {
        var parent = try self.evalExpr(row.parent);
        return self.evalFieldAccessWithParent(row, &parent, true);
    }

    fn findDeclInUnit(ast_unit: *ast.Ast, name: ast.StrId) ?ast.DeclId {
        const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
        for (decls) |did| {
            const row = ast_unit.exprs.Decl.get(did);
            if (row.pattern.isNone()) continue;
            const pat_id = row.pattern.unwrap();
            if (ast_unit.kind(pat_id) != .Binding) continue;
            const binding = ast_unit.pats.get(.Binding, pat_id);
            if (binding.name.eq(name)) return did;
        }
        return null;
    }

    /// Evaluate a field access using a pre-evaluated parent value.
    fn evalFieldAccessWithParent(
        self: *Interpreter,
        row: ast.Rows.FieldAccess,
        parent: *Value,
        destroy_parent: bool,
    ) anyerror!Value {
        const should_destroy = destroy_parent;
        defer if (should_destroy) parent.destroy(self.allocator);
        if (row.is_tuple) {
            const idx = try self.parseTupleIndex(row.field);
            return switch (parent.*) {
                .Sequence => |seq| {
                    if (idx >= seq.values.items.len) return Error.InvalidFieldAccess;
                    return try self.cloneValue(seq.values.items[idx]);
                },
                else => return Error.InvalidFieldAccess,
            };
        }
        const field_name = self.ast.exprs.strs.get(row.field);
        if (std.mem.eql(u8, field_name, "len")) {
            switch (parent.*) {
                .Sequence => |seq| return Value{ .Int = @intCast(seq.values.items.len) },
                .String => |s| return Value{ .Int = @intCast(s.len) },
                else => return Error.InvalidFieldAccess,
            }
        }
        return switch (parent.*) {
            .Pointer => |ptr| {
                var target = try self.cloneValue(ptr.*);
                return self.evalFieldAccessWithParent(row, &target, true);
            },
            .Struct => |sv| {
                const struct_field = findStructField(sv, row.field);
                if (struct_field) |field| {
                    return try self.cloneValue(field.*.value);
                }
                return Error.InvalidFieldAccess;
            },
            .Type => |type_id| {
                var id = type_id;
                const ts = self.ast.type_info.store;
                var kind = ts.getKind(id);
                if (kind == .TypeType) {
                    const type_type = ts.get(.TypeType, id);
                    id = type_type.of;
                }
                if (kind == .Ast) {
                    const ast_ty = ts.get(.Ast, id);
                    // Accessing a member from an imported module
                    if (self.compilation_unit) |compilation_unit| {
                        const pkg_name = self.ast.exprs.strs.get(ast_ty.pkg_name);
                        const filepath = self.ast.exprs.strs.get(ast_ty.filepath);
                        if (compilation_unit.packages.getPtr(pkg_name)) |pkg| {
                            if (pkg.sources.getPtr(filepath)) |parent_unit| {
                                if (parent_unit.ast) |a| {
                                    // Re-intern field name into the imported unit's interner
                                    const fname = self.ast.exprs.strs.get(row.field);
                                    const target_sid = a.exprs.strs.intern(fname);

                                    var decl_id: ?ast.DeclId = null;
                                    if (self.get_module_symtab) |get_symtab| {
                                        if (get_symtab(self.checker_context, parent_unit.file_id)) |symtab| {
                                            // Assuming the top-level scope is at index 0 (or bottom of stack)
                                            if (symtab.stack.items.len > 0) {
                                                const root_scope = symtab.stack.items[0].id;
                                                if (symtab.lookup(root_scope, target_sid)) |sid| {
                                                    const srow = symtab.syms.get(sid);
                                                    if (!srow.origin_decl.isNone()) {
                                                        decl_id = srow.origin_decl.unwrap();
                                                    }
                                                }
                                            }
                                        }
                                    }

                                    if (decl_id == null) {
                                        decl_id = findDeclInUnit(a, target_sid);
                                    }

                                    if (decl_id) |did| {
                                        const decl = a.exprs.Decl.get(did);
                                        // Try to get the comptime value for this declaration
                                        if (a.type_info.getComptimeValue(decl.value)) |val_ptr| {
                                            return try self.cloneValue(val_ptr.*);
                                        }
                                        // Fallback: if it's a function literal, just return the function value
                                        if (a.kind(decl.value) == .FunctionLit) {
                                            return Value{ .Function = .{ .expr = decl.value, .ast = a } };
                                        }
                                    }
                                }
                            }
                        }
                    }
                    return Error.InvalidFieldAccess;
                }
                kind = ts.getKind(id);
                if (kind == .Enum) {
                    const enum_type = ts.get(.Enum, id);
                    const members = ts.enum_member_pool.slice(enum_type.members);
                    for (members) |member_id| {
                        const member = ts.EnumMember.get(member_id);
                        if (member.name.eq(row.field)) {
                            return Value{ .Int = member.value };
                        }
                    }
                } else if (kind == .Struct) {
                    const struct_ty = ts.get(.Struct, id);
                    const fields = ts.field_pool.slice(struct_ty.fields);
                    for (fields) |field_id| {
                        const field = ts.Field.get(field_id);
                        if (field.name.eq(row.field)) {
                            // Return the field's type wrapped in TypeType
                            return Value{ .Type = ts.mkTypeType(field.ty) };
                        }
                    }
                }
                return Error.InvalidFieldAccess;
            },
            else => {
                return Error.InvalidFieldAccess;
            },
        };
    }

    /// Evaluate indices into sequences, strings, and maps.
    fn evalIndexAccess(self: *Interpreter, row: ast.Rows.IndexAccess) anyerror!Value {
        var collection = try self.evalExpr(row.collection);
        defer collection.destroy(self.allocator);
        var index_val = try self.evalExpr(row.index);
        defer index_val.destroy(self.allocator);
        return switch (collection) {
            .Sequence => |seq| {
                const idx = try expectIndex(index_val);
                if (idx >= seq.values.items.len) return Error.InvalidIndexAccess;
                return try self.cloneValue(seq.values.items[idx]);
            },
            .String => |s| {
                const idx = try expectIndex(index_val);
                if (idx >= s.len) return Error.InvalidIndexAccess;
                return Value{ .Int = @intCast(s[idx]) };
            },
            .Map => |map| {
                var idx: usize = 0;
                while (idx < map.entries.items.len) : (idx += 1) {
                    const entry = map.entries.items[idx];
                    if (valuesEqual(index_val, entry.key)) {
                        return try self.cloneValue(entry.value);
                    }
                }
                return Error.InvalidIndexAccess;
            },
            else => Error.InvalidIndexAccess,
        };
    }

    /// Parse a tuple literal field index from a string identifier.
    fn parseTupleIndex(self: *Interpreter, id: ast.StrId) anyerror!usize {
        const slice = self.ast.exprs.strs.get(id);
        return std.fmt.parseInt(usize, slice, 10) catch Error.InvalidFieldAccess;
    }

    /// Convert `value` to a non-negative integer suitable for an index.
    fn expectIndex(value: Value) anyerror!usize {
        return switch (value) {
            .Int => |int_val| {
                if (int_val < 0) return Error.InvalidIndexAccess;
                const max: i128 = std.math.maxInt(usize);
                if (int_val > max) return Error.InvalidIndexAccess;
                return @intCast(int_val);
            },
            else => return Error.InvalidIndexAccess,
        };
    }

    /// Evaluate a match expression by trying each arm sequentially.
    fn evalMatch(self: *Interpreter, row: ast.Rows.Match) anyerror!Value {
        var scrut = try self.evalExpr(row.expr);
        defer scrut.destroy(self.allocator);
        const arms = self.ast.exprs.arm_pool.slice(row.arms);
        for (arms) |arm_id| {
            const arm = self.ast.exprs.MatchArm.get(arm_id);
            var matches = std.ArrayList(Binding){};
            defer matches.deinit(self.allocator);
            if (!try self.matchPattern(self.ast, scrut, arm.pattern, &matches)) continue;
            var scope = try self.pushBindings(&matches);
            defer scope.deinit();
            if (!arm.guard.isNone()) {
                var guard_val = try self.evalExpr(arm.guard.unwrap());
                defer guard_val.destroy(self.allocator);
                if (!try valueToBool(guard_val)) continue;
            }
            return try self.evalExpr(arm.body);
        }
        return Value{ .Void = {} };
    }

    /// Return the owner name of a struct value, if any.
    fn structOwner(value: Value) ?ast.StrId {
        return switch (value) {
            .Struct => value.Struct.owner,
            else => null,
        };
    }

    /// Evaluate a `for` loop over a range or sequence.
    fn evalFor(self: *Interpreter, row: ast.Rows.For) anyerror!Value {
        var iterable = try self.evalExpr(row.iterable);
        defer iterable.destroy(self.allocator);
        const body = row.body;
        const pattern = row.pattern;
        switch (iterable) {
            .Range => |range| {
                var current = range.start;
                while (true) {
                    const done = if (range.inclusive) current > range.end else current >= range.end;
                    if (done) break;
                    _ = try self.runLoopIteration(pattern, body, Value{ .Int = current });
                    current += 1;
                }
            },
            .Sequence => |seq| {
                var idx: usize = 0;
                while (idx < seq.values.items.len) : (idx += 1) {
                    _ = try self.runLoopIteration(pattern, body, seq.values.items[idx]);
                }
            },
            else => return Error.InvalidType,
        }
        return Value{ .Void = {} };
    }

    /// Bind `value` to `pattern`, execute `body`, and clean up bindings.
    fn runLoopIteration(self: *Interpreter, pattern: ast.PatternId, body: ast.ExprId, value: Value) anyerror!bool {
        var matches = std.ArrayList(Binding){};
        defer matches.deinit(self.allocator);
        if (!try self.matchPattern(self.ast, value, pattern, &matches)) return false;
        var scope = try self.pushBindings(&matches);
        defer scope.deinit();
        var body_val = try self.evalExpr(body);
        body_val.destroy(self.allocator);
        return true;
    }

    /// Evaluate a `while` or `while pattern` loop.
    fn evalWhile(self: *Interpreter, row: ast.Rows.While) anyerror!Value {
        const body = row.body;
        while (true) {
            var cond_value: Value = if (row.cond.isNone()) Value{ .Bool = true } else try self.evalExpr(row.cond.unwrap());
            if (row.is_pattern and !row.pattern.isNone()) {
                var matches = std.ArrayList(Binding){};
                defer matches.deinit(self.allocator);
                if (!try self.matchPattern(self.ast, cond_value, row.pattern.unwrap(), &matches)) {
                    cond_value.destroy(self.allocator);
                    break;
                }
                cond_value.destroy(self.allocator);
                var scope = try self.pushBindings(&matches);
                defer scope.deinit();
                var body_val = try self.evalExpr(body);
                body_val.destroy(self.allocator);
                continue;
            }
            const cond_bool = try valueToBool(cond_value);
            cond_value.destroy(self.allocator);
            if (!cond_bool) break;
            var body_val = try self.evalExpr(body);
            body_val.destroy(self.allocator);
        }
        return Value{ .Void = {} };
    }

    /// Evaluate a literal expression (number, string, bool, etc.).
    fn evalLiteral(self: *Interpreter, literal: ast.Rows.Literal) anyerror!Value {
        return switch (literal.kind) {
            .int => Value{ .Int = @intCast(literal.data.int.value) },
            .float => Value{ .Float = literal.data.float.value },
            .bool => Value{ .Bool = literal.data.bool },
            .char => Value{ .Int = @intCast(literal.data.char) },
            .string => blk: {
                const slice = self.ast.exprs.strs.get(literal.data.string);
                const dup = try self.allocator.dupe(u8, slice);
                break :blk Value{ .String = dup };
            },
            .imaginary => Value{ .Float = literal.data.imaginary.value },
        };
    }

    /// Resolve an identifier to a binding, builtin type, or exported declaration.
    fn evalIdent(self: *Interpreter, expr_id: ast.ExprId, ident: ast.Rows.Ident) anyerror!Value {
        // 1. Check local comptime bindings
        if (try self.lookup(ident.name)) |value| {
            return value;
        }

        const ident_name = self.ast.exprs.strs.get(ident.name);

        // 2. Fallback to checker's symbol table if available
        if (self.symtab) |symtab| {
            if (symtab.lookup(symtab.currentId(), ident.name)) |sid| {
                const srow = symtab.syms.get(sid);
                if (!srow.origin_decl.isNone()) {
                    const did = srow.origin_decl.unwrap();
                    if (did.toRaw() < self.ast.type_info.decl_types.items.len) {
                        if (self.ast.type_info.decl_types.items[did.toRaw()]) |ty| {
                            const ts = self.ast.type_info.store;
                            if (ts.getKind(ty) == .TypeType) {
                                const tt = ts.get(.TypeType, ty);
                                return Value{ .Type = tt.of };
                            }
                        }
                    }
                }
            }
        }
        // 3. If the ident is already typed as TypeType, return the underlying type
        const expr_index = expr_id.toRaw();
        if (expr_index < self.ast.type_info.expr_types.items.len) {
            if (self.ast.type_info.expr_types.items[expr_index]) |type_ty| {
                const ts = self.ast.type_info.store;
                if (ts.getKind(type_ty) == .TypeType) {
                    const tt = ts.get(.TypeType, type_ty);
                    return Value{ .Type = tt.of };
                }
            }
        }

        if (self.ast.type_info.getExport(ident.name)) |entry|
            return Value{ .Type = entry.ty };

        if (self.lookupBuiltinType(ident_name)) |builtin_ty|
            return Value{ .Type = builtin_ty };

        if (self.findDeclByName(ident.name)) |did| {
            const row = self.ast.exprs.Decl.get(did);
            if (isTypeExprKind(self.ast.kind(row.value))) {
                return try self.evalExpr(row.value);
            }
        }

        return Error.BindingNotFound;
    }

    /// Look up the declaration that binds `name` within the current AST unit.
    fn findDeclByName(self: *Interpreter, name: ast.StrId) ?ast.DeclId {
        const decls = self.ast.exprs.decl_pool.slice(self.ast.unit.decls);
        for (decls) |did| {
            const row = self.ast.exprs.Decl.get(did);
            if (row.pattern.isNone()) continue;
            const pat_id = row.pattern.unwrap();
            if (self.ast.kind(pat_id) != .Binding) continue;
            const binding = self.ast.pats.get(.Binding, pat_id);
            if (binding.name.eq(name)) return did;
        }
        return null;
    }

    /// Return whether `kind` represents a type-level expression.
    fn isTypeExprKind(kind: ast.ExprKind) bool {
        return switch (kind) {
            .TupleType, .ArrayType, .DynArrayType, .MapType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType, .Literal, .Import, .Call, .FieldAccess, .MlirBlock => true,
            else => false,
        };
    }

    /// Map builtin type names to their `TypeId` equivalents.
    fn lookupBuiltinType(self: *Interpreter, name: []const u8) ?types.TypeId {
        const ts = self.ast.type_info.store;
        if (std.mem.eql(u8, name, "bool")) return ts.tBool();
        if (std.mem.eql(u8, name, "i8")) return ts.tI8();
        if (std.mem.eql(u8, name, "i16")) return ts.tI16();
        if (std.mem.eql(u8, name, "i32")) return ts.tI32();
        if (std.mem.eql(u8, name, "i64")) return ts.tI64();
        if (std.mem.eql(u8, name, "u8")) return ts.tU8();
        if (std.mem.eql(u8, name, "u16")) return ts.tU16();
        if (std.mem.eql(u8, name, "u32")) return ts.tU32();
        if (std.mem.eql(u8, name, "u64")) return ts.tU64();
        if (std.mem.eql(u8, name, "usize")) return ts.tUsize();
        if (std.mem.eql(u8, name, "f32")) return ts.tF32();
        if (std.mem.eql(u8, name, "f64")) return ts.tF64();
        if (std.mem.eql(u8, name, "void")) return ts.tVoid();
        if (std.mem.eql(u8, name, "string")) return ts.tString();
        if (std.mem.eql(u8, name, "any")) return ts.tAny();
        if (std.mem.eql(u8, name, "char")) return ts.tU32();
        if (std.mem.eql(u8, name, "Error")) return ts.tTestError();
        if (std.mem.eql(u8, name, "type")) return ts.mkTypeType(ts.tAny());
        return null;
    }

    /// Perform binary operations during interpretation.
    fn evalBinary(self: *Interpreter, row: ast.Rows.Binary) anyerror!Value {
        var left = try self.evalExpr(row.left);
        defer left.destroy(self.allocator);
        var right = try self.evalExpr(row.right);
        defer right.destroy(self.allocator);

        switch (row.op) {
            .add => {
                const l = try numericValue(left);
                const r = try numericValue(right);
                switch (l) {
                    .Int => switch (r) {
                        .Int => return Value{ .Int = l.Int + r.Int },
                        .Float => return Value{ .Float = @as(f64, @floatFromInt(l.Int)) + r.Float },
                    },
                    .Float => switch (r) {
                        .Int => return Value{ .Float = l.Float + @as(f64, @floatFromInt(r.Int)) },
                        .Float => return Value{ .Float = l.Float + r.Float },
                    },
                }
            },
            .sub => {
                const l = try numericValue(left);
                const r = try numericValue(right);
                switch (l) {
                    .Int => switch (r) {
                        .Int => return Value{ .Int = l.Int - r.Int },
                        .Float => return Value{ .Float = @as(f64, @floatFromInt(l.Int)) - r.Float },
                    },
                    .Float => switch (r) {
                        .Int => return Value{ .Float = l.Float - @as(f64, @floatFromInt(r.Int)) },
                        .Float => return Value{ .Float = l.Float - r.Float },
                    },
                }
            },
            .mul => {
                const l = try numericValue(left);
                const r = try numericValue(right);
                switch (l) {
                    .Int => switch (r) {
                        .Int => return Value{ .Int = l.Int * r.Int },
                        .Float => return Value{ .Float = @as(f64, @floatFromInt(l.Int)) * r.Float },
                    },
                    .Float => switch (r) {
                        .Int => return Value{ .Float = l.Float * @as(f64, @floatFromInt(r.Int)) },
                        .Float => return Value{ .Float = l.Float * r.Float },
                    },
                }
            },
            .div => {
                const l = try numericValue(left);
                const r = try numericValue(right);
                switch (l) {
                    .Int => switch (r) {
                        .Int => {
                            if (r.Int == 0) return Error.DivisionByZero;
                            return Value{ .Int = @divTrunc(l.Int, r.Int) };
                        },
                        .Float => return Value{ .Float = @as(f64, @floatFromInt(l.Int)) / r.Float },
                    },
                    .Float => switch (r) {
                        .Int => return Value{ .Float = l.Float / @as(f64, @floatFromInt(r.Int)) },
                        .Float => return Value{ .Float = l.Float / r.Float },
                    },
                }
            },
            .mod => {
                const divisor = try expectInt(right);
                if (divisor == 0) return Error.DivisionByZero;
                return Value{ .Int = @rem(try expectInt(left), divisor) };
            },
            .logical_and => {
                const l = try valueToBool(left);
                if (!l) return Value{ .Bool = false };
                const r = try valueToBool(right);
                return Value{ .Bool = r };
            },
            .logical_or => {
                const l = try valueToBool(left);
                if (l) return Value{ .Bool = true };
                const r = try valueToBool(right);
                return Value{ .Bool = r };
            },
            .shl => {
                const l = try expectInt(left);
                const r: u7 = @intCast(try expectInt(right));
                return Value{ .Int = l << r };
            },
            .shr => {
                const l = try expectInt(left);
                const r: u7 = @intCast(try expectInt(right));
                return Value{ .Int = l >> r };
            },
            .bit_and => return Value{ .Int = try expectInt(left) & try expectInt(right) },
            .bit_or => return Value{ .Int = try expectInt(left) | try expectInt(right) },
            .bit_xor => return Value{ .Int = try expectInt(left) ^ try expectInt(right) },
            .lt => return Value{ .Bool = try compareLt(left, right) },
            .lte => return Value{ .Bool = try compareLte(left, right) },
            .gt => return Value{ .Bool = try compareGt(left, right) },
            .gte => return Value{ .Bool = try compareGte(left, right) },
            .eq => return Value{ .Bool = valuesEqual(left, right) },
            .neq => return Value{ .Bool = !valuesEqual(left, right) },
            else => return Error.InvalidBinaryOperand,
        }
    }

    /// Perform unary operations (including `&` which produces a pointer).
    fn evalUnary(self: *Interpreter, row: ast.Rows.Unary) anyerror!Value {
        var value = try self.evalExpr(row.expr);
        if (row.op == .address_of) {
            return self.moveValueToPointer(value);
        }
        defer value.destroy(self.allocator);
        return switch (row.op) {
            .pos => Value{ .Int = try expectInt(value) },
            .neg => Value{ .Int = -try expectInt(value) },
            .logical_not => Value{ .Bool = !try valueToBool(value) },
            else => return Error.InvalidBinaryOperand,
        };
    }

    /// Allocate a pointer value that owns `value`.
    fn moveValueToPointer(self: *Interpreter, value: Value) anyerror!Value {
        const target = try self.allocator.create(Value);
        target.* = value;
        return Value{ .Pointer = target };
    }

    /// Evaluate an `if` expression and return the selected branch’s value.
    fn evalIf(self: *Interpreter, row: ast.Rows.If) anyerror!Value {
        var cond_val = try self.evalExpr(row.cond);
        defer cond_val.destroy(self.allocator);
        if (try valueToBool(cond_val)) {
            return try self.evalExpr(row.then_block);
        }
        if (row.else_block.isNone()) return Value{ .Void = {} };
        return try self.evalExpr(row.else_block.unwrap());
    }

    /// Evaluate a return statement by computing its optional value.
    fn evalReturn(self: *Interpreter, row: ast.Rows.Return) anyerror!Value {
        if (row.value.isNone()) return Value{ .Void = {} };
        return try self.evalExpr(row.value.unwrap());
    }

    /// Compare `left` and `right` for `<`.
    fn compareLt(left: Value, right: Value) anyerror!bool {
        const l = try numericValue(left);
        const r = try numericValue(right);
        return switch (l) {
            .Int => switch (r) {
                .Int => l.Int < r.Int,
                .Float => @as(f64, @floatFromInt(l.Int)) < r.Float,
            },
            .Float => switch (r) {
                .Int => l.Float < @as(f64, @floatFromInt(r.Int)),
                .Float => l.Float < r.Float,
            },
        };
    }

    /// Compare `left` and `right` for `<=`.
    fn compareLte(left: Value, right: Value) anyerror!bool {
        const l = try numericValue(left);
        const r = try numericValue(right);
        return switch (l) {
            .Int => switch (r) {
                .Int => l.Int <= r.Int,
                .Float => @as(f64, @floatFromInt(l.Int)) <= r.Float,
            },
            .Float => switch (r) {
                .Int => l.Float <= @as(f64, @floatFromInt(r.Int)),
                .Float => l.Float <= r.Float,
            },
        };
    }

    /// Compare `left` and `right` for `>`.
    fn compareGt(left: Value, right: Value) anyerror!bool {
        const l = try numericValue(left);
        const r = try numericValue(right);
        return switch (l) {
            .Int => switch (r) {
                .Int => l.Int > r.Int,
                .Float => @as(f64, @floatFromInt(l.Int)) > r.Float,
            },
            .Float => switch (r) {
                .Int => l.Float > @as(f64, @floatFromInt(r.Int)),
                .Float => l.Float > r.Float,
            },
        };
    }

    /// Compare `left` and `right` for `>=`.
    fn compareGte(left: Value, right: Value) anyerror!bool {
        const l = try numericValue(left);
        const r = try numericValue(right);
        return switch (l) {
            .Int => switch (r) {
                .Int => l.Int >= r.Int,
                .Float => @as(f64, @floatFromInt(l.Int)) >= r.Float,
            },
            .Float => switch (r) {
                .Int => l.Float >= @as(f64, @floatFromInt(r.Int)),
                .Float => l.Float >= r.Float,
            },
        };
    }

    /// Normalize a numeric `Value` to `NumericValue` for comparison.
    fn numericValue(value: Value) anyerror!NumericValue {
        return switch (value) {
            .Int => NumericValue{ .Int = value.Int },
            .Float => NumericValue{ .Float = value.Float },
            .Bool => NumericValue{ .Int = toInt(value.Bool) },
            else => return Error.InvalidBinaryOperand,
        };
    }

    /// Insert or update a top-level binding with `name`.
    pub fn setBinding(self: *Interpreter, name: ast.StrId, value: Value) !void {
        if (self.ast.type_info.lookupComptimeBindingType(name)) |ty| {
            const cloned = try comptime_mod.cloneComptimeValue(self.ast.type_info.gpa, value);
            try self.ast.type_info.setComptimeBinding(name, ty, cloned);
        }
        if (self.findBinding(name)) |binding| {
            binding.value.destroy(self.allocator);
            binding.value = value;
            return;
        }
        try self.bindings.append(self.allocator, .{ .name = name, .value = value });
    }

    /// Register all methods defined on structs so they can be looked up by name.
    fn registerMethods(self: *Interpreter) anyerror!void {
        const decl_ids = self.ast.exprs.decl_pool.slice(self.ast.unit.decls);
        for (decl_ids) |decl_id| {
            const decl = self.ast.exprs.Decl.get(decl_id);
            if (decl.method_path.isNone()) continue;
            const segs = self.ast.exprs.method_path_pool.slice(decl.method_path.asRange());
            if (segs.len < 2) continue;
            const owner_seg = self.ast.exprs.MethodPathSeg.get(segs[0]);
            const method_seg = self.ast.exprs.MethodPathSeg.get(segs[segs.len - 1]);
            const key = MethodKey{ .owner = owner_seg.name, .method = method_seg.name };
            if (self.method_table.get(key)) |_| continue;
            try self.method_table.put(key, decl.value);
        }
    }

    /// Return the expression ID implementing `owner.method` if registered.
    fn lookupMethod(self: *Interpreter, owner: ast.StrId, method: ast.StrId) ?ast.ExprId {
        const key = MethodKey{ .owner = owner, .method = method };
        if (self.method_table.get(key)) |entry| return entry;
        return null;
    }

    /// Return the binding entry for `name`, if already present.
    pub fn findBinding(self: *Interpreter, name: ast.StrId) ?*Binding {
        for (self.bindings.items) |*binding| if (binding.name.eq(name)) return binding;
        return null;
    }

    /// Produce a deep copy of `value` when ownership must be duplicated.
    pub fn cloneValue(self: *Interpreter, value: Value) !Value {
        return switch (value) {
            .String => |s| blk: {
                const dup = try self.allocator.dupe(u8, s);
                break :blk Value{ .String = dup };
            },
            .Sequence => |seq| try self.cloneSequence(seq),
            .Struct => |sv| try self.cloneStruct(sv),
            .Map => |mv| try self.cloneMap(mv),
            .Pointer => |ptr| try self.clonePointer(ptr),
            .Function => |func| Value{ .Function = func },
            else => value,
        };
    }

    /// Coerce `value` to an integer, erroring if non-numeric.
    fn expectInt(value: Value) anyerror!i128 {
        return switch (value) {
            .Int => value.Int,
            .Bool => if (value.Bool) 1 else 0,
            else => return Error.InvalidBinaryOperand,
        };
    }

    /// Convert `value` to boolean following builtin truthiness rules.
    fn valueToBool(value: Value) anyerror!bool {
        return switch (value) {
            .Bool => value.Bool,
            .Int => value.Int != 0,
            .Float => value.Float != 0.0,
            else => return Error.InvalidType,
        };
    }

    /// Small helper to convert bool to integer.
    fn toInt(value: bool) i128 {
        return @intFromBool(value);
    }

    /// Structural equality test used in patterns and comparisons.
    fn valuesEqual(left: Value, right: Value) bool {
        return switch (left) {
            .Int => |l| switch (right) {
                .Int => l == right.Int,
                .Float => @as(f64, @floatFromInt(l)) == right.Float,
                .Bool => l == toInt(right.Bool),
                else => false,
            },
            .Bool => |b| switch (right) {
                .Bool => b == right.Bool,
                .Int => toInt(b) == right.Int,
                .Float => @as(f64, @floatFromInt(toInt(b))) == right.Float,
                else => false,
            },
            .Float => |f| switch (right) {
                .Float => f == right.Float,
                .Int => f == @as(f64, @floatFromInt(right.Int)),
                .Bool => f == @as(f64, @floatFromInt(toInt(right.Bool))),
                else => false,
            },
            .String => |s| switch (right) {
                .String => std.mem.eql(u8, s, right.String),
                else => false,
            },
            .Sequence => |seq| switch (right) {
                .Sequence => sequencesEqual(seq, right.Sequence),
                else => false,
            },
            .Struct => |sv| switch (right) {
                .Struct => structValuesEqual(sv, right.Struct),
                else => false,
            },
            .Map => |mv| switch (right) {
                .Map => mapsEqual(mv, right.Map),
                else => false,
            },
            .Range => |rv| switch (right) {
                .Range => rv.start == right.Range.start and rv.end == right.Range.end and rv.inclusive == right.Range.inclusive,
                else => false,
            },
            .Function => |func| switch (right) {
                .Function => func.expr.eq(right.Function.expr),
                else => false,
            },
            else => false,
        };
    }

    /// Compare two sequences element-wise.
    fn sequencesEqual(a: Sequence, b: Sequence) bool {
        if (a.values.items.len != b.values.items.len) return false;
        if (a.values.items.len == 0) return true;
        var idx: usize = 0;
        while (idx < a.values.items.len) : (idx += 1) {
            if (!valuesEqual(a.values.items[idx], b.values.items[idx])) return false;
        }
        return true;
    }

    /// Compare two struct values including owner metadata.
    fn structValuesEqual(a: StructValue, b: StructValue) bool {
        if (a.fields.items.len != b.fields.items.len) return false;
        if (!ownersEqual(a.owner, b.owner)) return false;
        if (a.fields.items.len == 0) return true;
        var idx: usize = 0;
        while (idx < a.fields.items.len) : (idx += 1) {
            const left_field = a.fields.items[idx];
            const right_field = b.fields.items[idx];
            if (!left_field.name.eq(right_field.name)) return false;
            if (!valuesEqual(left_field.value, right_field.value)) return false;
        }
        return true;
    }

    /// Compare two maps by iterating entries.
    fn mapsEqual(a: MapValue, b: MapValue) bool {
        if (a.entries.items.len != b.entries.items.len) return false;
        if (a.entries.items.len == 0) return true;
        var idx: usize = 0;
        while (idx < a.entries.items.len) : (idx += 1) {
            const left = a.entries.items[idx];
            const right = b.entries.items[idx];
            if (!valuesEqual(left.key, right.key)) return false;
            if (!valuesEqual(left.value, right.value)) return false;
        }
        return true;
    }

    /// Whether two optional struct owners refer to the same module/type.
    fn ownersEqual(a: ?ast.StrId, b: ?ast.StrId) bool {
        if (a == null and b == null) return true;
        if (a == null or b == null) return false;
        return a.?.eq(b.?);
    }

    /// Clone a sequence value along with its entries.
    fn cloneSequence(self: *Interpreter, seq: Sequence) anyerror!Value {
        if (seq.values.items.len == 0) return Value{ .Sequence = .{ .values = .empty } };
        var list: std.ArrayList(Value) = try .initCapacity(self.allocator, seq.values.items.len);
        var success = false;
        defer if (!success) {
            for (list.items) |*value| value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < seq.values.items.len) : (idx += 1) {
            list.appendAssumeCapacity(try self.cloneValue(seq.values.items[idx]));
        }
        success = true;
        return Value{ .Sequence = .{ .values = list } };
    }

    /// Clone a struct value (fields + owner) for reuse in bindings.
    fn cloneStruct(self: *Interpreter, sv: StructValue) anyerror!Value {
        if (sv.fields.items.len == 0) return Value{ .Struct = .{ .fields = .empty, .owner = sv.owner } };
        var list: std.ArrayList(StructField) = try .initCapacity(self.allocator, sv.fields.items.len);
        var success = false;
        defer if (!success) {
            for (list.items) |*field| field.value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < sv.fields.items.len) : (idx += 1) {
            list.appendAssumeCapacity(StructField{
                .name = sv.fields.items[idx].name,
                .value = try self.cloneValue(sv.fields.items[idx].value),
            });
        }
        success = true;
        return Value{ .Struct = .{ .fields = list, .owner = sv.owner } };
    }

    /// Deep clone of a map value so lookups do not share mutable entries.
    fn cloneMap(self: *Interpreter, mv: MapValue) anyerror!Value {
        if (mv.entries.items.len == 0) return Value{ .Map = .{ .entries = .empty } };
        var list: std.ArrayList(MapEntry) = try .initCapacity(self.allocator, mv.entries.items.len);
        var success = false;
        defer if (!success) {
            for (list.items) |*entry| {
                entry.key.destroy(self.allocator);
                entry.value.destroy(self.allocator);
            }
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < mv.entries.items.len) : (idx += 1) {
            const entry = mv.entries.items[idx];
            list.appendAssumeCapacity(MapEntry{
                .key = try self.cloneValue(entry.key),
                .value = try self.cloneValue(entry.value),
            });
        }
        success = true;
        return Value{ .Map = .{ .entries = list } };
    }

    /// Clone a pointer value by cloning the pointee.
    fn clonePointer(self: *Interpreter, target: *Value) anyerror!Value {
        const cloned = try self.cloneValue(target.*);
        const ptr = try self.allocator.create(Value);
        ptr.* = cloned;
        return Value{ .Pointer = ptr };
    }

    /// Find a field entry by name within a struct value.
    fn findStructField(sv: StructValue, name: ast.StrId) ?*StructField {
        var idx: usize = 0;
        while (idx < sv.fields.items.len) : (idx += 1) {
            if (sv.fields.items[idx].name.eq(name)) return &sv.fields.items[idx];
        }
        return null;
    }

    /// Match `value` against pattern `pid`, recording bound identifiers.
    fn matchPattern(self: *Interpreter, pattern_ast: *ast.Ast, value: Value, pid: ast.PatternId, matches: *std.ArrayList(Binding)) anyerror!bool {
        switch (pattern_ast.kind(pid)) {
            .Wildcard => return true,
            .Literal => {
                const row = pattern_ast.pats.get(.Literal, pid);
                var literal = try self.evalExpr(row.expr);
                defer literal.destroy(self.allocator);
                return valuesEqual(value, literal);
            },
            .Binding => {
                const row = pattern_ast.pats.get(.Binding, pid);
                var binding_value = try self.cloneValue(value);
                var success = false;
                defer if (!success) binding_value.destroy(self.allocator);
                try matches.append(self.allocator, .{ .name = row.name, .value = binding_value });
                success = true;
                return true;
            },
            .Tuple => return try self.matchTuplePattern(pattern_ast, value, pattern_ast.pats.get(.Tuple, pid), matches),
            .Slice => return try self.matchSlicePattern(pattern_ast, value, pattern_ast.pats.get(.Slice, pid), matches),
            .Struct => return try self.matchStructPattern(pattern_ast, value, pattern_ast.pats.get(.Struct, pid), matches),
            .At => return try self.matchAtPattern(pattern_ast, value, pattern_ast.pats.get(.At, pid), matches),
            else => return false,
        }
    }

    /// Match a tuple pattern against a sequence value.
    fn matchTuplePattern(self: *Interpreter, pattern_ast: *ast.Ast, value: Value, row: ast.PatRows.Tuple, matches: *std.ArrayList(Binding)) anyerror!bool {
        return switch (value) {
            .Sequence => |seq| {
                const patterns = pattern_ast.pats.pat_pool.slice(row.elems);
                if (seq.values.items.len != patterns.len) return false;
                if (seq.values.items.len == 0) return true;
                const elems = seq.values.items[0..seq.values.items.len];
                var idx: usize = 0;
                while (idx < patterns.len) : (idx += 1) {
                    const before = matches.items.len;
                    if (!try self.matchPattern(pattern_ast, elems[idx], patterns[idx], matches)) {
                        self.rollbackBindings(matches, before);
                        return false;
                    }
                }
                return true;
            },
            else => false,
        };
    }

    /// Match a slice pattern, handling rest bindings.
    fn matchSlicePattern(self: *Interpreter, pattern_ast: *ast.Ast, value: Value, row: ast.PatRows.Slice, matches: *std.ArrayList(Binding)) anyerror!bool {
        return switch (value) {
            .Sequence => |seq| {
                const patterns = pattern_ast.pats.pat_pool.slice(row.elems);
                const fixed: usize = if (row.has_rest) @intCast(row.rest_index) else patterns.len;
                if (seq.values.items.len < fixed) return false;
                if (fixed > 0) {
                    const elems = seq.values.items[0..seq.values.items.len];
                    var idx: usize = 0;
                    while (idx < fixed) : (idx += 1) {
                        const before = matches.items.len;
                        if (!try self.matchPattern(pattern_ast, elems[idx], patterns[idx], matches)) {
                            self.rollbackBindings(matches, before);
                            return false;
                        }
                    }
                }
                if (!row.has_rest) return seq.values.items.len == patterns.len;
                const rest_index: usize = @intCast(row.rest_index);
                if (rest_index > seq.values.items.len) return false;
                if (row.rest_binding.isNone()) return true;
                const rest_pattern = row.rest_binding.unwrap();
                var rest_value = try self.cloneSequence(seq);
                const before_rest = matches.items.len;
                const matched_rest = try self.matchPattern(pattern_ast, rest_value, rest_pattern, matches);
                rest_value.destroy(self.allocator);
                if (!matched_rest) {
                    self.rollbackBindings(matches, before_rest);
                    return false;
                }
                return true;
            },
            else => false,
        };
    }

    /// Match a struct pattern by comparing fields and nested patterns.
    fn matchStructPattern(self: *Interpreter, pattern_ast: *ast.Ast, value: Value, row: ast.PatRows.Struct, matches: *std.ArrayList(Binding)) anyerror!bool {
        return switch (value) {
            .Struct => |sv| {
                const fields = pattern_ast.pats.field_pool.slice(row.fields);
                if (!row.has_rest and sv.fields.items.len != fields.len) return false;
                for (fields) |field_id| {
                    const field = pattern_ast.pats.StructField.get(field_id);
                    const struct_field = findStructField(sv, field.name);
                    if (struct_field == null) return false;
                    const before = matches.items.len;
                    if (!try self.matchPattern(pattern_ast, struct_field.?.value, field.pattern, matches)) {
                        self.rollbackBindings(matches, before);
                        return false;
                    }
                }
                return true;
            },
            else => false,
        };
    }

    /// Handle `@` patterns that bind the entire matched value.
    fn matchAtPattern(self: *Interpreter, pattern_ast: *ast.Ast, value: Value, row: ast.PatRows.At, matches: *std.ArrayList(Binding)) anyerror!bool {
        const before = matches.items.len;
        if (!try self.matchPattern(pattern_ast, value, row.pattern, matches)) {
            self.rollbackBindings(matches, before);
            return false;
        }
        var clone = try self.cloneValue(value);
        var success = false;
        defer if (!success) clone.destroy(self.allocator);
        try matches.append(self.allocator, .{ .name = row.binder, .value = clone });
        success = true;
        return true;
    }

    /// Revert `matches` back to `target_len`, freeing extra values.
    fn rollbackBindings(self: *Interpreter, matches: *std.ArrayList(Binding), target_len: usize) void {
        var current = matches.items.len;
        while (current > target_len) : (current -= 1) {
            matches.items[current - 1].value.destroy(self.allocator);
        }
        matches.shrinkRetainingCapacity(target_len);
    }

    /// Compute a hash over the provided bindings for memoization.
    fn bindingHash(bindings: []const Binding) u64 {
        var hasher: std.hash.Wyhash = .init(0);
        for (bindings) |binding| {
            const name_raw: u32 = binding.name.toRaw();
            hasher.update(std.mem.asBytes(&name_raw));
            const val_hash: u64 = comptime_mod.hashComptimeValue(binding.value);
            hasher.update(std.mem.asBytes(&val_hash));
        }
        return hasher.final();
    }

    /// Capture bindings into a snapshot alongside its hash for reuse.
    pub fn captureBindingSnapshot(self: *Interpreter, matches: *std.ArrayList(Binding)) anyerror!BindingSnapshot {
        var snapshot: std.ArrayList(Binding) = try .initCapacity(self.allocator, matches.items.len);
        var hasher: std.hash.Wyhash = .init(0);
        var success = false;
        defer if (!success) {
            for (snapshot.items) |*binding| binding.value.destroy(self.allocator);
            snapshot.deinit(self.allocator);
        };
        for (matches.items) |binding| {
            const cloned = try self.cloneValue(binding.value);
            try snapshot.append(self.allocator, .{ .name = binding.name, .value = cloned });
            const name_raw: u32 = binding.name.toRaw();
            hasher.update(std.mem.asBytes(&name_raw));
            const val_hash: u64 = comptime_mod.hashComptimeValue(binding.value);
            hasher.update(std.mem.asBytes(&val_hash));
        }
        success = true;
        return BindingSnapshot{ .bindings = snapshot, .hash = hasher.final() };
    }

    /// Clone an existing binding snapshot to keep a copy for future lookups.
    fn cloneSnapshot(self: *Interpreter, source: *BindingSnapshot) anyerror!BindingSnapshot {
        var cloned: std.ArrayList(Binding) = try .initCapacity(self.allocator, source.bindings.items.len);
        var success = false;
        defer if (!success) {
            for (cloned.items) |*binding| binding.value.destroy(self.allocator);
            cloned.deinit(self.allocator);
        };
        for (source.bindings.items) |binding| {
            const dup = try self.cloneValue(binding.value);
            try cloned.append(self.allocator, .{ .name = binding.name, .value = dup });
        }
        success = true;
        return BindingSnapshot{ .bindings = cloned, .hash = source.hash };
    }

    /// Pack a function key into a 128-bit hash for the specialization map.
    fn hashFunctionKey(key: FunctionKey) u128 {
        const decl_raw: u32 = key.decl_id.toRaw();
        return (@as(u128, key.bindings_hash) << 32) | @as(u128, decl_raw);
    }

    /// Create or reuse a specialized function definition using `matches`.
    pub fn specializeFunction(self: *Interpreter, decl_id: ast.DeclId, matches: *std.ArrayList(Binding)) anyerror!SpecializationResult {
        const binding_hash = bindingHash(matches.items);
        const key = FunctionKey{ .decl_id = decl_id, .bindings_hash = binding_hash };
        const map_hash = hashFunctionKey(key);
        if (self.specializations.getPtr(map_hash)) |existing| {
            if (keysEqual(existing.key, key)) {
                return SpecializationResult{
                    .func = FunctionValue{ .expr = existing.func_expr, .ast = self.ast },
                    .snapshot = try self.cloneSnapshot(&existing.bindings),
                };
            }
        }
        var snapshot = try self.captureBindingSnapshot(matches);
        const return_snapshot = try self.cloneSnapshot(&snapshot);
        var entry = FunctionSpecializationEntry{
            .key = key,
            .func_expr = self.ast.exprs.Decl.get(decl_id).value,
            .bindings = snapshot,
        };
        var success = false;
        defer if (!success) entry.destroy(self.allocator);
        try self.specializations.put(map_hash, entry);
        success = true;
        return SpecializationResult{
            .func = FunctionValue{ .expr = entry.func_expr, .ast = self.ast },
            .snapshot = return_snapshot,
        };
    }

    /// Tracks bound variables pushed during a function/pattern invocation.
    /// Temporary frame used when binding matched variables to new values.
    pub const BindingScope = struct {
        /// Interpreter owning the current scope.
        interpreter: *Interpreter,
        /// Length of the binding list before the scope began.
        prev_len: usize,
        /// Bindings that replaced existing entries.
        replaced: std.ArrayList(Binding),
        /// Whether the scope is still active and needs restoration.
        active: bool,

        /// Restore bindings to their prior state when the scope closes.
        fn restore(self: *BindingScope) void {
            if (!self.active) return;
            var len = self.interpreter.bindings.items.len;
            while (len > self.prev_len) : (len -= 1) {
                self.interpreter.bindings.items[len - 1].value.destroy(self.interpreter.allocator);
            }
            self.interpreter.bindings.shrinkRetainingCapacity(self.prev_len);
            for (self.replaced.items) |binding| {
                if (self.interpreter.findBinding(binding.name)) |existing| {
                    existing.value.destroy(self.interpreter.allocator);
                    existing.value = binding.value;
                }
            }
            self.replaced.clearRetainingCapacity();
            self.active = false;
        }

        /// Cleanup resources associated with the scope.
        pub fn deinit(self: *BindingScope) void {
            self.restore();
            self.replaced.deinit(self.interpreter.allocator);
        }
    };

    /// Push the `matches` bindings into the interpreter, saving replaced bindings.
    pub fn pushBindings(self: *Interpreter, matches: *std.ArrayList(Binding)) anyerror!BindingScope {
        var scope = BindingScope{
            .interpreter = self,
            .prev_len = self.bindings.items.len,
            .replaced = .empty,
            .active = true,
        };
        var success = false;
        defer if (!success) {
            scope.restore();
            scope.replaced.deinit(self.allocator);
        };
        for (matches.items) |*binding| {
            const value = binding.value;
            binding.value = .Void;
            if (self.findBinding(binding.name)) |existing| {
                const old_value = try self.cloneValue(existing.value);
                try scope.replaced.append(self.allocator, .{ .name = binding.name, .value = old_value });
                existing.value.destroy(self.allocator);
                existing.value = value;
            } else {
                try self.bindings.append(self.allocator, .{ .name = binding.name, .value = value });
            }
        }
        success = true;
        return scope;
    }
};
