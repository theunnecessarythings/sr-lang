const std = @import("std");
const Context = @import("compile.zig").Context;
const tir = @import("tir.zig");
const types = @import("types.zig");
const mlir = @import("mlir_bindings.zig");
const LowerTir = @import("lower_tir.zig");
const Pipeline = @import("pipeline.zig").Pipeline;
const checker = @import("checker.zig");
const ast = @import("ast.zig");
const interpreter = @import("interpreter.zig");
const List = std.ArrayList;

/// Handles the callback interface exposed to user-defined comptime evaluations.
pub const ComptimeApi = struct {
    /// Untyped context forwarded to each callback.
    context: ?*anyopaque,
    /// Callback used when the comptime script wants to print text.
    print: *const fn (context: ?*anyopaque, format: [*c]const u8, ...) callconv(.c) void,
    /// Callback that looks up a type id by name.
    get_type_by_name: *const fn (context: ?*anyopaque, name: [*c]const u8) callconv(.c) u32,
    /// Callback exposing `type_of(expr)` for debugging helpers.
    type_of: *const fn (context: ?*anyopaque, expr_id: u32) callconv(.c) u32,
};

/// Represents a reference to a function literal captured for comptime evaluation.
pub const FunctionValue = struct {
    /// Expression id pointing at the function literal.
    expr: ast.ExprId,
    /// AST containing the function definition.
    ast: *ast.Ast,
};

/// List wrapper used by comptime sequence literals.
pub const Sequence = struct {
    /// Values collected inside this sequence.
    values: std.ArrayList(ComptimeValue),
};

/// A single key/value pair stored inside a comptime map.
pub const MapEntry = struct {
    /// Key used to index the map.
    key: ComptimeValue,
    /// Value stored for the key.
    value: ComptimeValue,
};

/// Container for the entries inside a comptime map literal.
pub const MapValue = struct {
    /// Storage for individual map entries.
    entries: std.ArrayList(MapEntry),
};

/// Field descriptor used when building comptime struct values.
pub const StructField = struct {
    /// Field name stored in the struct.
    name: ast.StrId,
    /// Computed value assigned to this field.
    value: ComptimeValue,
};

/// Aggregate representation for comptime struct literals.
pub const StructValue = struct {
    /// Fields captured in declaration order.
    fields: std.ArrayList(StructField),
    /// Optional name of the struct type that owns these fields.
    owner: ?ast.StrId,
};

/// Captures the bounds of a `range` literal evaluated at comptime.
pub const RangeValue = struct {
    /// Inclusive start of the range.
    start: i128,
    /// Inclusive end of the range.
    end: i128,
    /// Whether `end` should be treated as inclusive (`..=`) or exclusive (`..`).
    inclusive: bool,
};

/// The universe of values that may be produced while executing comptime metadata.
pub const ComptimeValue = union(enum) {
    /// Represents the absence of a runtime value.
    Void,
    /// Signed integer literal captured at comptime.
    Int: i128,
    /// Floating-point literal captured at comptime.
    Float: f64,
    /// Boolean literal captured at comptime.
    Bool: bool,
    /// String literal stored as an owned slice.
    String: []const u8,
    /// Sequence (list) literal made of other `ComptimeValue` instances.
    Sequence: Sequence,
    /// Struct literal containing named fields.
    Struct: StructValue,
    /// Map literal collected as entries.
    Map: MapValue,
    /// Pointer to another `ComptimeValue` (used for aliasing during evaluation).
    Pointer: *ComptimeValue,
    /// Range literal with start/end/inclusivity metadata.
    Range: RangeValue,
    /// Embedded type reference.
    Type: types.TypeId,
    /// MLIR type handle produced by the interpreter.
    MlirType: mlir.Type,
    /// MLIR attribute handle produced by the interpreter.
    MlirAttribute: mlir.Attribute,
    /// MLIR module handle produced by the interpreter.
    MlirModule: mlir.Module,
    /// Function literal captured during evaluation.
    Function: FunctionValue,

    /// Free any allocator-backed contents inside `self`.
    pub fn destroy(self: *ComptimeValue, gpa: std.mem.Allocator) void {
        switch (self.*) {
            .String => |s| {
                gpa.free(s);
            },
            .Sequence => |*seq| {
                for (seq.values.items) |*item| {
                    item.destroy(gpa);
                }
                seq.values.deinit(gpa);
            },
            .Struct => |*sv| {
                for (sv.fields.items) |*field| {
                    field.value.destroy(gpa);
                }
                sv.fields.deinit(gpa);
            },
            .Map => |*map| {
                for (map.entries.items) |*entry| {
                    entry.key.destroy(gpa);
                    entry.value.destroy(gpa);
                }
                map.entries.deinit(gpa);
            },
            .Pointer => |ptr| {
                ptr.*.destroy(gpa);
                gpa.destroy(ptr);
            },
            .MlirModule => |*mod| {
                mod.destroy();
            },
            .Function => |_| {},
            else => {},
        }
        self.* = .Void;
    }
};

/// Holds the type/value pair used when binding comptime arguments.
pub const BindingValue = struct {
    /// The type id associated with this binding.
    ty: types.TypeId,
    /// The copied comptime value provided for the binding.
    value: ComptimeValue,

    /// Allocate and clone `value` so the binding owns its own copy.
    pub fn init(gpa: std.mem.Allocator, ty: types.TypeId, value: ComptimeValue) !BindingValue {
        return .{ .ty = ty, .value = try cloneComptimeValue(gpa, value) };
    }

    /// Clone the binding so the caller owns its own copy of the stored value.
    fn clone(self: BindingValue, gpa: std.mem.Allocator) !BindingValue {
        return .{ .ty = self.ty, .value = try cloneComptimeValue(gpa, self.value) };
    }

    /// Release storage held by the binding value.
    fn deinit(self: *BindingValue, gpa: std.mem.Allocator) void {
        self.value.destroy(gpa);
        self.* = .{ .ty = types.TypeId.fromRaw(0), .value = .Void };
    }
};

/// Describes a binding that the compiler can inject when running comptime code.
pub const BindingInfo = struct {
    /// Identifier used to refer to the binding in alias lookups.
    name: ast.StrId,
    /// Kind of binding (type, value, runtime).
    kind: Kind,

    /// Distinguishes between the binding forms that can be supplied at comptime.
    pub const Kind = union(enum) {
        /// A named type parameter.
        type_param: types.TypeId,
        /// A value parameter that holds a `ComptimeValue`.
        value_param: BindingValue,
        /// A runtime parameter provided by the runtime.
        runtime_param: types.TypeId,
    };

    /// Construct a type binding.
    pub fn typeParam(name: ast.StrId, ty: types.TypeId) BindingInfo {
        return .{ .name = name, .kind = .{ .type_param = ty } };
    }

    /// Clone `value` and bundle it with `name` and `ty` for a value binding.
    pub fn valueParam(gpa: std.mem.Allocator, name: ast.StrId, ty: types.TypeId, value: ComptimeValue) !BindingInfo {
        return .{ .name = name, .kind = .{ .value_param = try BindingValue.init(gpa, ty, value) } };
    }

    /// Create a runtime-only binding that forwards the provided `ty`.
    pub fn runtimeParam(name: ast.StrId, ty: types.TypeId) BindingInfo {
        return .{ .name = name, .kind = .{ .runtime_param = ty } };
    }

    /// Release owned resources (e.g., cloned values stored in `value_param`).
    pub fn deinit(self: *BindingInfo, gpa: std.mem.Allocator) void {
        switch (self.kind) {
            .value_param => |*vp| vp.deinit(gpa),
            else => {},
        }
        self.* = .{ .name = ast.StrId.fromRaw(0), .kind = .{ .type_param = types.TypeId.fromRaw(0) } };
    }

    /// Deep clone any owned resources inside `BindingInfo`.
    fn clone(self: BindingInfo, gpa: std.mem.Allocator) !BindingInfo {
        return switch (self.kind) {
            .type_param => |ty| BindingInfo.typeParam(self.name, ty),
            .value_param => |vp| blk: {
                const cloned = try vp.clone(gpa);
                break :blk .{ .name = self.name, .kind = .{ .value_param = cloned } };
            },
            .runtime_param => |ty| BindingInfo.runtimeParam(self.name, ty),
        };
    }
};

/// Exposed to C to report the kind of a type id for debugging.
pub fn type_of_impl(context: ?*anyopaque, type_id_raw: u32) callconv(.c) u32 {
    const ctx: *Context = @ptrCast(@alignCast(context.?));
    const type_id = types.TypeId.fromRaw(type_id_raw);
    const kind = ctx.type_store.getKind(type_id);
    std.debug.print("comptime> type_of_impl: type_id_raw={}, kind={s}\n", .{ type_id_raw, @tagName(kind) });
    return @intFromEnum(kind);
}

/// Print helper exposed to C so comptime scripts can emit diagnostics.
pub fn comptime_print_impl(context: ?*anyopaque, format: [*c]const u8, ...) callconv(.c) void {
    _ = context;
    std.debug.print("comptime> {s}\n", .{@as([]const u8, std.mem.sliceTo(format, 0))});
}

/// Lookup a built-in type name for the embedded runtime, returning its id.
pub fn get_type_by_name_impl(context: ?*anyopaque, name: [*c]const u8) callconv(.c) u32 {
    const ctx: *Context = @ptrCast(@alignCast(context.?));
    const name_slice = std.mem.sliceTo(name, 0);
    const ts = ctx.type_store;

    if (std.mem.eql(u8, name_slice, "bool")) return ts.tBool().toRaw();
    if (std.mem.eql(u8, name_slice, "i8")) return ts.tI8().toRaw();
    if (std.mem.eql(u8, name_slice, "i16")) return ts.tI16().toRaw();
    if (std.mem.eql(u8, name_slice, "i32")) return ts.tI32().toRaw();
    if (std.mem.eql(u8, name_slice, "i64")) return ts.tI64().toRaw();
    if (std.mem.eql(u8, name_slice, "u8")) return ts.tU8().toRaw();
    if (std.mem.eql(u8, name_slice, "u16")) return ts.tU16().toRaw();
    if (std.mem.eql(u8, name_slice, "u32")) return ts.tU32().toRaw();
    if (std.mem.eql(u8, name_slice, "u64")) return ts.tU64().toRaw();
    if (std.mem.eql(u8, name_slice, "f32")) return ts.tF32().toRaw();
    if (std.mem.eql(u8, name_slice, "f64")) return ts.tF64().toRaw();
    if (std.mem.eql(u8, name_slice, "usize")) return ts.tUsize().toRaw();
    if (std.mem.eql(u8, name_slice, "char")) return ts.tU32().toRaw();
    if (std.mem.eql(u8, name_slice, "string")) return ts.tString().toRaw();
    if (std.mem.eql(u8, name_slice, "void")) return ts.tVoid().toRaw();
    if (std.mem.eql(u8, name_slice, "any")) return ts.tAny().toRaw();

    return ts.tVoid().toRaw(); // Return void if not found
}

// =============================
// Comptime Lower TIR API
// =============================

/// Evaluate an AST expression as a type literal and return its computed `TypeId`.
fn evaluateTypeExpr(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    expr: ast.ExprId,
) anyerror!types.TypeId {
    switch (a.kind(expr)) {
        .Ident => {
            const ident = a.exprs.get(.Ident, expr);
            if (self.lookupComptimeAliasType(a, ident.name)) |ty| {
                return ty;
            }

            const name_slice = self.context.type_store.strs.get(ident.name);
            if (std.mem.eql(u8, name_slice, "bool")) return self.context.type_store.tBool();
            if (std.mem.eql(u8, name_slice, "i8")) return self.context.type_store.tI8();
            if (std.mem.eql(u8, name_slice, "i16")) return self.context.type_store.tI16();
            if (std.mem.eql(u8, name_slice, "i32")) return self.context.type_store.tI32();
            if (std.mem.eql(u8, name_slice, "i64")) return self.context.type_store.tI64();
            if (std.mem.eql(u8, name_slice, "u8")) return self.context.type_store.tU8();
            if (std.mem.eql(u8, name_slice, "u16")) return self.context.type_store.tU16();
            if (std.mem.eql(u8, name_slice, "u32")) return self.context.type_store.tU32();
            if (std.mem.eql(u8, name_slice, "u64")) return self.context.type_store.tU64();
            if (std.mem.eql(u8, name_slice, "f32")) return self.context.type_store.tF32();
            if (std.mem.eql(u8, name_slice, "f64")) return self.context.type_store.tF64();
            if (std.mem.eql(u8, name_slice, "usize")) return self.context.type_store.tUsize();
            if (std.mem.eql(u8, name_slice, "char")) return self.context.type_store.tU32();
            if (std.mem.eql(u8, name_slice, "string")) return self.context.type_store.tString();
            if (std.mem.eql(u8, name_slice, "void")) return self.context.type_store.tVoid();
            if (std.mem.eql(u8, name_slice, "any")) return self.context.type_store.tAny();

            return error.TypeNotFound;
        },
        .StructType => {
            const st = a.exprs.get(.StructType, expr);
            var fields: std.ArrayList(types.TypeStore.StructFieldArg) = .empty;
            defer fields.deinit(self.gpa);

            const field_ids = a.exprs.sfield_pool.slice(st.fields);
            for (field_ids) |field_id| {
                const field_def = a.exprs.StructField.get(field_id);
                const field_type = try evaluateTypeExpr(self, ctx, a, field_def.ty);
                try fields.append(self.gpa, .{ .name = field_def.name, .ty = field_type });
            }

            const fields_slice = try fields.toOwnedSlice(self.gpa);
            return self.context.type_store.mkStruct(fields_slice);
        },
        .Call => {
            const call = a.exprs.get(.Call, expr);
            const callee_expr = call.callee;

            const checker_ctx = &self.chk.checker_ctx.items[a.file_id];

            const proc_node = switch (a.kind(callee_expr)) {
                .Ident => blk: {
                    const ident = a.exprs.get(.Ident, callee_expr);
                    const sym_id = checker_ctx.symtab.lookup(checker_ctx.symtab.currentId(), ident.name) orelse return error.SymbolNotFound;
                    const sym = checker_ctx.symtab.syms.get(sym_id);
                    const decl_id = if (sym.origin_decl.isNone()) return error.NotAProcedure else sym.origin_decl.unwrap();
                    const decl = a.exprs.Decl.get(decl_id);
                    if (a.kind(decl.value) != .FunctionLit) return error.NotAProcedure;

                    break :blk a.exprs.get(.FunctionLit, decl.value);
                },
                else => return error.NotAProcedure,
            };

            var bindings_list = std.ArrayList(Pipeline.ComptimeBinding).empty;
            defer bindings_list.deinit(self.gpa);
            const params = a.exprs.param_pool.slice(proc_node.params);
            const args = a.exprs.expr_pool.slice(call.args);

            for (params, args) |param_id, arg_expr| {
                const param = a.exprs.Param.get(param_id);
                if (!param.is_comptime) continue;

                // Resolve the parameter name (must be a simple binding for comptime params)
                var param_name: ast.StrId = undefined;
                if (param.pat.isNone()) {
                    return error.MissingParameterName;
                } else {
                    const pattern_id = param.pat.unwrap();
                    if (a.kind(pattern_id) != .Binding) {
                        return error.UnsupportedPatternType;
                    }
                    param_name = a.pats.get(.Binding, pattern_id).name;
                }

                // Decide binding kind using the declared param type first.
                var is_type_param = false;
                if (!param.ty.isNone()) {
                    const ty_expr = param.ty.unwrap();
                    const ty_kind = a.kind(ty_expr);
                    // If the parameter type is `type`, it's a type-parameter.
                    if (ty_kind == .TypeType or ty_kind == .AnyType) {
                        is_type_param = true;
                    }
                }

                if (is_type_param) {
                    // Treat argument as a type expression regardless of getExprType result.
                    const arg_type_val = try evaluateTypeExpr(self, ctx, a, arg_expr);
                    try bindings_list.append(self.gpa, .{ .type_param = .{ .name = param_name, .ty = arg_type_val } });
                    continue;
                }

                // Fall back to previous behavior when param is not explicitly `type`.
                const arg_ty = self.getExprType(ctx, a, arg_expr);
                if (self.context.type_store.getKind(arg_ty) == .TypeType) {
                    const arg_type_val = try evaluateTypeExpr(self, ctx, a, arg_expr);
                    try bindings_list.append(self.gpa, .{ .type_param = .{ .name = param_name, .ty = arg_type_val } });
                } else {
                    const comptime_val = try runComptimeExpr(self, ctx, a, arg_expr, &[_]Pipeline.ComptimeBinding{});
                    try bindings_list.append(self.gpa, .{ .value_param = .{ .name = param_name, .ty = arg_ty, .value = comptime_val } });
                }
            }

            var body_expr: ast.ExprId = undefined;
            if (proc_node.body.isNone()) {
                return error.MissingFunctionBody;
            } else {
                body_expr = proc_node.body.unwrap();
            }

            const result_comptime_val = try runComptimeExpr(self, ctx, a, body_expr, bindings_list.items);

            return switch (result_comptime_val) {
                .Type => |t| t,
                else => error.UnsupportedComptimeType,
            };
        },
        .Block => {
            const block = a.exprs.get(.Block, expr);
            if (block.items.len == 0) return self.context.type_store.tVoid();
            const stmts = a.stmts.stmt_pool.slice(block.items);

            // Track how many temporary type-bindings we push for local aliases.
            var last_ty: ?types.TypeId = null;
            var alias_names: std.ArrayList(ast.StrId) = std.ArrayList(ast.StrId).empty;
            var alias_types: std.ArrayList(types.TypeId) = std.ArrayList(types.TypeId).empty;
            defer {
                alias_names.deinit(self.gpa);
                alias_types.deinit(self.gpa);
            }

            for (stmts) |stmt_id| {
                switch (a.kind(stmt_id)) {
                    .Decl => {
                        const d_stmt = a.stmts.get(.Decl, stmt_id);
                        const d = a.exprs.Decl.get(d_stmt.decl);
                        // Handle method declarations (Alias.method :: proc ...)
                        if (!d.method_path.isNone() and a.kind(d.value) == .FunctionLit) {
                            const seg_ids0 = a.exprs.method_path_pool.slice(d.method_path.asRange());
                            if (seg_ids0.len >= 2) {
                                const owner_seg0 = a.exprs.MethodPathSeg.get(seg_ids0[0]);
                                const method_seg0 = a.exprs.MethodPathSeg.get(seg_ids0[seg_ids0.len - 1]);
                                // resolve owner from recorded aliases first
                                var owner_ty0: types.TypeId = self.context.type_store.tAny();
                                var j: usize = 0;
                                var found_owner = false;
                                while (j < alias_names.items.len) : (j += 1) {
                                    if (alias_names.items[j].eq(owner_seg0.name)) {
                                        owner_ty0 = alias_types.items[j];
                                        found_owner = true;
                                        break;
                                    }
                                }
                                if (!found_owner) {
                                    if (self.lookupComptimeAliasType(a, owner_seg0.name)) |t0| {
                                        owner_ty0 = t0;
                                        found_owner = true;
                                    }
                                }
                                if (found_owner) {
                                    const fn_lit0 = a.exprs.get(.FunctionLit, d.value);
                                    const param_ids0 = a.exprs.param_pool.slice(fn_lit0.params);
                                    var param_types0 = std.ArrayList(types.TypeId).empty;
                                    defer param_types0.deinit(self.gpa);
                                    for (param_ids0) |pid0| {
                                        const p0 = a.exprs.Param.get(pid0);
                                        if (!p0.ty.isNone()) {
                                            const pty0 = evaluateTypeExpr(self, ctx, a, p0.ty.unwrap()) catch self.context.type_store.tAny();
                                            param_types0.append(self.gpa, pty0) catch {};
                                        } else {
                                            param_types0.append(self.gpa, self.context.type_store.tAny()) catch {};
                                        }
                                    }
                                    const res_ty0 = if (!fn_lit0.result_ty.isNone())
                                        (evaluateTypeExpr(self, ctx, a, fn_lit0.result_ty.unwrap()) catch self.context.type_store.tVoid())
                                    else
                                        self.context.type_store.tVoid();
                                    const fnty0 = self.context.type_store.mkFunction(param_types0.items, res_ty0, fn_lit0.flags.is_variadic, true, fn_lit0.flags.is_extern);
                                    const entry0: types.MethodEntry = .{
                                        .owner_type = owner_ty0,
                                        .method_name = method_seg0.name,
                                        .decl_id = d_stmt.decl,
                                        .decl_ast = a,
                                        .func_expr = d.value,
                                        .func_type = fnty0,
                                        .self_param_type = null,
                                        .receiver_kind = .none,
                                        .builtin = null,
                                    };
                                    _ = self.context.type_store.addMethod(entry0) catch {};
                                }
                            }
                            // Continue scanning; do not treat method decl as alias
                            continue;
                        }
                        // Type alias declaration
                        if (d.pattern.isNone()) break; // skip unnamed
                        const pat_id = d.pattern.unwrap();
                        if (a.kind(pat_id) != .Binding) break; // only simple names
                        const name = a.pats.get(.Binding, pat_id).name;
                        const ty = evaluateTypeExpr(self, ctx, a, d.value) catch |e| switch (e) {
                            error.UnsupportedComptimeType, error.TypeNotFound, error.NotAProcedure, error.MissingFunctionBody => break,
                            else => return e,
                        };
                        last_ty = ty; // remember most recent type value
                        alias_names.append(self.gpa, name) catch {};
                        alias_types.append(self.gpa, ty) catch {};
                    },
                    .Return => {
                        const ret = a.stmts.get(.Return, stmt_id);
                        if (!ret.value.isNone()) {
                            const ret_val_expr = ret.value.unwrap();
                            return try evaluateTypeExpr(self, ctx, a, ret_val_expr);
                        }
                    },
                    .Expr => {
                        const ex_stmt = a.stmts.get(.Expr, stmt_id);
                        if (a.kind(ex_stmt.expr) == .Return) {
                            const ret = a.exprs.get(.Return, ex_stmt.expr);
                            if (!ret.value.isNone()) {
                                const ret_val_expr = ret.value.unwrap();
                                return try evaluateTypeExpr(self, ctx, a, ret_val_expr);
                            }
                        } else {
                            // Try to interpret a bare expression statement as a type expression
                            const ty_try = evaluateTypeExpr(self, ctx, a, ex_stmt.expr) catch |e| switch (e) {
                                error.UnsupportedComptimeType, error.TypeNotFound, error.NotAProcedure, error.MissingFunctionBody => null,
                                else => return e,
                            };
                            if (ty_try) |t| last_ty = t;
                        }
                    },
                    else => {},
                }
            }
            if (last_ty) |t| return t;
            return error.NoReturnValueInBlock;
        },
        else => {
            std.debug.print("evaluateTypeExpr: Unhandled expr type {}\n", .{a.kind(expr)});
            return error.UnsupportedComptimeType;
        },
    }
}

/// Evaluate `expr` at comptime and return its resulting `ComptimeValue`.
pub fn runComptimeExpr(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    expr: ast.ExprId,
    bindings: []const Pipeline.ComptimeBinding,
) !ComptimeValue {
    _ = ctx;
    return self.chk.evalComptimeExpr(&self.chk.checker_ctx.items[a.file_id], a, expr, bindings);
}

/// Materialize a `tir.ValueId` for the supplied `ComptimeValue` in lowered code.
pub fn constValueFromComptime(
    self: *LowerTir,
    blk: *tir.Builder.BlockFrame,
    ty: types.TypeId,
    value: ComptimeValue,
) !tir.ValueId {
    // These values are synthesized from specialization metadata; no source location is available.
    return switch (value) {
        .Int => |val| blk: {
            const kind = self.context.type_store.getKind(ty);
            const u: u64 = switch (kind) {
                .I32 => blk32: {
                    const s: i32 = @intCast(val);
                    const bits: u32 = @bitCast(s);
                    break :blk32 @as(u64, bits);
                },
                .I64 => blk64: {
                    const s: i64 = @intCast(val);
                    const bits: u64 = @bitCast(s);
                    break :blk64 bits;
                },
                .U32 => @as(u64, @intCast(@as(u32, @intCast(val)))),
                .U64, .Usize => @as(u64, @intCast(val)),
                else => @as(u64, @intCast(val)),
            };
            break :blk blk.builder.tirValue(.ConstInt, blk, ty, .none(), .{ .value = u });
        },
        .Float => |val| blk.builder.tirValue(.ConstFloat, blk, ty, .none(), .{ .value = val }),
        .Bool => |val| blk.builder.tirValue(.ConstBool, blk, ty, .none(), .{ .value = val }),
        .Void => blk.builder.tirValue(.ConstUndef, blk, ty, .none(), .{}),
        .String => |s| blk.builder.tirValue(.ConstString, blk, ty, .none(), .{ .text = blk.builder.intern(s) }),
        .Sequence => return error.UnsupportedComptimeType,
        .Struct => return error.UnsupportedComptimeType,
        .Range => return error.UnsupportedComptimeType,
        .Function => return error.UnsupportedComptimeType,
        .Pointer => return error.UnsupportedComptimeType,
        .Map => return error.UnsupportedComptimeType,
        .Type => return error.UnsupportedComptimeType,
        .MlirType => blk.builder.tirValue(.ConstUndef, blk, ty, .none(), .{}),
        .MlirAttribute => blk.builder.tirValue(.ConstUndef, blk, ty, .none(), .{}),
        .MlirModule => blk.builder.tirValue(.ConstUndef, blk, ty, .none(), .{}),
    };
}

/// Deep-copy `value` so it can be reused safely by other code paths.
pub fn cloneComptimeValue(gpa: std.mem.Allocator, value: ComptimeValue) !ComptimeValue {
    return switch (value) {
        .Void => .Void,
        .Int => |v| .{ .Int = v },
        .Float => |v| .{ .Float = v },
        .Bool => |v| .{ .Bool = v },
        .String => |s| .{ .String = try gpa.dupe(u8, s) },
        .Sequence => |seq| blk: {
            var values = std.ArrayList(ComptimeValue){};
            try values.resize(gpa, seq.values.items.len);
            for (seq.values.items, 0..) |item, idx| {
                values.items[idx] = try cloneComptimeValue(gpa, item);
            }
            break :blk .{ .Sequence = .{ .values = values } };
        },
        .Struct => |sv| blk: {
            var fields = std.ArrayList(StructField){};
            try fields.resize(gpa, sv.fields.items.len);
            for (sv.fields.items, 0..) |item, idx| {
                fields.items[idx] = StructField{
                    .name = item.name,
                    .value = try cloneComptimeValue(gpa, item.value),
                };
            }
            break :blk .{ .Struct = .{ .fields = fields, .owner = sv.owner } };
        },
        .Map => |map| blk: {
            var entries = std.ArrayList(MapEntry){};
            try entries.resize(gpa, map.entries.items.len);
            for (map.entries.items, 0..) |entry, idx| {
                entries.items[idx] = MapEntry{
                    .key = try cloneComptimeValue(gpa, entry.key),
                    .value = try cloneComptimeValue(gpa, entry.value),
                };
            }
            break :blk .{ .Map = .{ .entries = entries } };
        },
        .Pointer => |ptr| blk: {
            const target_clone = try cloneComptimeValue(gpa, ptr.*);
            const target = try gpa.create(ComptimeValue);
            target.* = target_clone;
            break :blk .{ .Pointer = target };
        },
        .Type => |ty| .{ .Type = ty },
        .MlirType => |ty| .{ .MlirType = ty },
        .MlirAttribute => |attr| .{ .MlirAttribute = attr },
        .MlirModule => |mod| blk: {
            const cloned_op = mlir.Operation.clone(mod.getOperation());
            break :blk .{ .MlirModule = mlir.Module.fromOperation(cloned_op) };
        },
        .Range => |rng| .{ .Range = rng },
        .Function => |func| .{ .Function = func },
    };
}

/// Fingerprint `value`, used when mangling specialization identifiers.
pub fn hashComptimeValue(value: ComptimeValue) u64 {
    var hasher: std.hash.Wyhash = .init(0);
    const tag: u8 = @intFromEnum(value);
    hasher.update(&.{tag});
    switch (value) {
        .Void => {},
        .Int => |val| hasher.update(std.mem.asBytes(&val)),
        .Float => |val| {
            const bits: u64 = @bitCast(val);
            hasher.update(std.mem.asBytes(&bits));
        },
        .Bool => |val| {
            const b: u8 = if (val) 1 else 0;
            hasher.update(&.{b});
        },
        .String => |s| {
            const len: usize = s.len;
            hasher.update(std.mem.asBytes(&len));
            hasher.update(s);
        },
        .Type => |ty| {
            const raw = ty.toRaw();
            hasher.update(std.mem.asBytes(&raw));
        },
        .MlirType => |ty| hasher.update(std.mem.asBytes(&ty.handle)),
        .MlirAttribute => |attr| hasher.update(std.mem.asBytes(&attr.handle)),
        .MlirModule => |mod| hasher.update(std.mem.asBytes(&mod.handle)),
        .Sequence => |seq| {
            hasher.update(std.mem.asBytes(&seq.values.items.len));
            var idx: usize = 0;
            while (idx < seq.values.items.len) : (idx += 1) {
                const child_hash = hashComptimeValue(seq.values.items[idx]);
                hasher.update(std.mem.asBytes(&child_hash));
            }
        },
        .Struct => |sv| {
            hasher.update(std.mem.asBytes(&sv.fields.items.len));
            var idx: usize = 0;
            while (idx < sv.fields.items.len) : (idx += 1) {
                hasher.update(std.mem.asBytes(&sv.fields.items[idx].name));
                const child_hash = hashComptimeValue(sv.fields.items[idx].value);
                hasher.update(std.mem.asBytes(&child_hash));
            }
            if (sv.owner) |owner| hasher.update(std.mem.asBytes(&owner));
        },
        .Map => |map| {
            hasher.update(std.mem.asBytes(&map.entries.items.len));
            var idx: usize = 0;
            while (idx < map.entries.items.len) : (idx += 1) {
                const entry = map.entries.items[idx];
                const key_hash = hashComptimeValue(entry.key);
                const value_hash = hashComptimeValue(entry.value);
                hasher.update(std.mem.asBytes(&key_hash));
                hasher.update(std.mem.asBytes(&value_hash));
            }
        },
        .Pointer => |ptr| {
            const target_hash = hashComptimeValue(ptr.*);
            hasher.update(std.mem.asBytes(&target_hash));
        },
        .Function => |func| {
            const raw: u32 = func.expr.toRaw();
            hasher.update(std.mem.asBytes(&raw));
        },
        .Range => |rng| hasher.update(std.mem.asBytes(&.{ rng.start, rng.end, rng.inclusive })),
    }
    return hasher.final();
}

/// Append specialization metadata onto `base` to build a unique monomorph name.
pub fn mangleMonomorphName(
    self: *LowerTir,
    base: tir.StrId,
    bindings: []const BindingInfo,
) !tir.StrId {
    var buf: List(u8) = .empty;
    defer buf.deinit(self.gpa);

    try buf.appendSlice(self.gpa, self.context.type_store.strs.get(base));
    if (bindings.len == 0) return self.context.type_store.strs.intern(buf.items);

    try buf.appendSlice(self.gpa, "_M");
    for (bindings) |info| {
        try buf.append(self.gpa, '_');
        var w = buf.writer(self.gpa);
        switch (info.kind) {
            .type_param => |ty| try w.print("T{}", .{ty.toRaw()}),
            .value_param => |vp| {
                const hash = hashComptimeValue(vp.value);
                try w.print("V{}x{X}", .{ vp.ty.toRaw(), hash });
            },
            .runtime_param => |ty| try w.print("R{}", .{ty.toRaw()}),
        }
    }

    return self.context.type_store.strs.intern(buf.items);
}

/// Carries metadata for the current specialization being lowered.
pub const SpecializationContext = struct {
    /// Type that we are instantiating.
    specialized_ty: types.TypeId,
    /// Number of leading parameters that should be skipped (already baked in).
    skip_params: usize,
    /// Bindings that override comptime arguments for this specialization.
    bindings: []const BindingInfo,
};

/// Request generated by the pipeline to specialize a function for `specialized_ty`.
pub const SpecializationRequest = struct {
    /// Declaration that should be lowered with substitutions.
    decl_id: ast.DeclId,
    /// Monomorphized symbol name to emit for the specialized function.
    mangled_name: tir.StrId,
    /// Type for which the function is specialized.
    specialized_ty: types.TypeId,
    /// Number of parameters already satisfied by the specialization.
    skip_params: usize,
    /// Bindings that drive the specialization (type/value/runtime).
    bindings: []const BindingInfo,
};

/// Lower the function referenced by `req` using the provided specialization metadata.
pub fn lowerSpecializedFunction(
    self: *LowerTir,
    ctx: *LowerTir.LowerContext,
    a: *ast.Ast,
    b: *tir.Builder,
    req: *const SpecializationRequest,
) !void {
    const decl = a.exprs.Decl.get(req.decl_id);

    if (a.kind(decl.value) == .FunctionLit) {
        const fn_lit = a.exprs.get(.FunctionLit, decl.value);
        if (!fn_lit.body.isNone()) {
            const body_eid = fn_lit.body.unwrap();
            if (a.kind(body_eid) == .Block) {
                const blk = a.exprs.get(.Block, body_eid);
                const stmts = a.stmts.stmt_pool.slice(blk.items);

                var alias_names: std.ArrayList(ast.StrId) = std.ArrayList(ast.StrId).empty;
                var alias_types: std.ArrayList(types.TypeId) = std.ArrayList(types.TypeId).empty;
                defer {
                    alias_names.deinit(self.gpa);
                    alias_types.deinit(self.gpa);
                }

                for (stmts) |sid| {
                    if (a.kind(sid) != .Decl) continue;
                    const sd = a.stmts.get(.Decl, sid);
                    const d2 = a.exprs.Decl.get(sd.decl);

                    if (!d2.pattern.isNone()) {
                        const pid = d2.pattern.unwrap();
                        if (a.kind(pid) == .Binding) {
                            const bname = a.pats.get(.Binding, pid).name;
                            const ty_opt = evaluateTypeExpr(self, ctx, a, d2.value) catch |e| switch (e) {
                                error.UnsupportedComptimeType, error.TypeNotFound, error.MissingFunctionBody, error.NotAProcedure => null,
                                else => return e,
                            };
                            if (ty_opt) |tval| {
                                alias_names.append(self.gpa, bname) catch {};
                                alias_types.append(self.gpa, tval) catch {};
                            }
                        }
                    }

                    if (!d2.method_path.isNone() and a.kind(d2.value) == .FunctionLit) {
                        const seg_ids = a.exprs.method_path_pool.slice(d2.method_path.asRange());
                        if (seg_ids.len < 2) continue;
                        const owner_seg = a.exprs.MethodPathSeg.get(seg_ids[0]);
                        const method_seg = a.exprs.MethodPathSeg.get(seg_ids[seg_ids.len - 1]);

                        var owner_ty: types.TypeId = self.context.type_store.tAny();
                        var found = false;
                        var i: usize = 0;
                        while (i < alias_names.items.len) : (i += 1) {
                            if (alias_names.items[i].eq(owner_seg.name)) {
                                owner_ty = alias_types.items[i];
                                found = true;
                                break;
                            }
                        }
                        if (!found) {
                            if (self.lookupComptimeAliasType(a, owner_seg.name)) |t| {
                                owner_ty = t;
                                found = true;
                            }
                        }
                        if (!found) continue;

                        const mfn = a.exprs.get(.FunctionLit, d2.value);
                        const param_ids = a.exprs.param_pool.slice(mfn.params);
                        var param_types = std.ArrayList(types.TypeId).empty;
                        defer param_types.deinit(self.gpa);
                        for (param_ids) |pid2| {
                            const p = a.exprs.Param.get(pid2);
                            if (!p.ty.isNone()) {
                                const pty = evaluateTypeExpr(self, ctx, a, p.ty.unwrap()) catch self.context.type_store.tAny();
                                param_types.append(self.gpa, pty) catch {};
                            } else {
                                param_types.append(self.gpa, self.context.type_store.tAny()) catch {};
                            }
                        }
                        const res_ty = if (!mfn.result_ty.isNone())
                            (evaluateTypeExpr(self, ctx, a, mfn.result_ty.unwrap()) catch self.context.type_store.tVoid())
                        else
                            self.context.type_store.tVoid();
                        const fnty = self.context.type_store.mkFunction(param_types.items, res_ty, mfn.flags.is_variadic, true, mfn.flags.is_extern);

                        var receiver_kind: types.MethodReceiverKind = .none;
                        if (param_ids.len > 0) {
                            const first_p = a.exprs.Param.get(param_ids[0]);
                            if (!first_p.pat.isNone()) {
                                const pat_id = first_p.pat.unwrap();
                                if (a.kind(pat_id) == .Binding) {
                                    const sb = a.pats.get(.Binding, pat_id);
                                    if (std.mem.eql(u8, a.exprs.strs.get(sb.name), "self")) {
                                        if (!first_p.ty.isNone()) {
                                            const self_ty = evaluateTypeExpr(self, ctx, a, first_p.ty.unwrap()) catch self.context.type_store.tAny();
                                            const k = self.context.type_store.getKind(self_ty);
                                            if (k == .Ptr) {
                                                const pr = self.context.type_store.get(.Ptr, self_ty);
                                                if (pr.elem.eq(owner_ty)) {
                                                    receiver_kind = if (pr.is_const) .pointer_const else .pointer;
                                                }
                                            } else if (self_ty.eq(owner_ty)) {
                                                receiver_kind = .value;
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        const entry: types.MethodEntry = .{
                            .owner_type = owner_ty,
                            .method_name = method_seg.name,
                            .decl_id = sd.decl,
                            .decl_ast = a,
                            .func_expr = d2.value,
                            .func_type = fnty,
                            .self_param_type = null,
                            .receiver_kind = receiver_kind,
                            .builtin = null,
                        };
                        _ = self.context.type_store.addMethod(entry) catch {};
                    }
                }
            }
        }
    }

    try self.lowerFunction(ctx, a, b, req.mangled_name, decl.value);
}
