const std = @import("std");
const Context = @import("compile.zig").Context;
const tir = @import("tir.zig");
const types = @import("types.zig");
const mlir = @import("mlir_bindings.zig");
const LowerTir = @import("lower_tir.zig");
const Pipeline = @import("pipeline.zig").Pipeline;
const checker = @import("checker.zig");
const ast = @import("ast.zig");
const cst = @import("cst.zig");
const interpreter = @import("interpreter.zig");
const List = std.ArrayList;

/// Handles the callback interface exposed to user-defined comptime evaluations.
pub const ComptimeApi = struct {
    context: ?*anyopaque,
    print: *const fn (context: ?*anyopaque, format: [*c]const u8, ...) callconv(.c) void,
    get_type_by_name: *const fn (context: ?*anyopaque, name: [*c]const u8) callconv(.c) u32,
    type_of: *const fn (context: ?*anyopaque, expr_id: u32) callconv(.c) u32,
};

////////////////////////////////////////////////////////////////////////////////
//              Data-Oriented Design (DOD) Value Representation
////////////////////////////////////////////////////////////////////////////////

pub const ValueTag = struct {};
pub const ValueId = cst.Index(ValueTag);
pub const OptValueId = cst.SentinelIndex(ValueTag);

pub const CodeBindingId = cst.Index(ValueRows.CodeBinding);
pub const StructFieldId = cst.Index(ValueRows.StructField);
pub const MapEntryId = cst.Index(ValueRows.MapEntry);

pub const ValueKind = enum(u8) {
    Void,
    Int,
    Float,
    Bool,
    String,
    Sequence,
    Struct,
    Variant,
    Map,
    Pointer,
    Range,
    Type,
    MlirType,
    MlirAttribute,
    MlirModule,
    Function,
    Code,
};

pub const ValueRows = struct {
    pub const Void = struct {};
    pub const Int = struct { value: i128 };
    pub const Float = struct { value: f64 };
    pub const Bool = struct { value: bool };
    pub const String = struct { value: []const u8 };

    pub const Sequence = struct { elems: cst.RangeOf(ValueId) };

    pub const StructField = struct { name: cst.StrId, value: ValueId };
    pub const Struct = struct { fields: cst.RangeOf(StructFieldId), owner: cst.OptStrId };

    pub const Variant = struct { tag: cst.StrId, payload: OptValueId };

    pub const MapEntry = struct { key: ValueId, value: ValueId };
    pub const Map = struct { entries: cst.RangeOf(MapEntryId) };

    pub const Pointer = struct { pointee: ValueId };

    pub const Range = struct { start: i128, end: i128, inclusive: bool };

    pub const Type = struct { ty: types.TypeId };

    pub const MlirType = struct { ty: mlir.Type };
    pub const MlirAttribute = struct { attr: mlir.Attribute };
    pub const MlirModule = struct { module: mlir.Module };

    pub const Function = struct { expr: ast.ExprId, ast: *ast.Ast };

    pub const CodeBinding = struct { name: cst.StrId, value: ValueId };
    pub const Code = struct { block: ast.ExprId, ast: *ast.Ast, captures: cst.RangeOf(CodeBindingId) };
};

/// Convenience alias for code values stored in the value store.
pub const CodeValue = ValueRows.Code;

pub inline fn ValueRowT(comptime K: ValueKind) type {
    return switch (K) {
        .Void => ValueRows.Void,
        .Int => ValueRows.Int,
        .Float => ValueRows.Float,
        .Bool => ValueRows.Bool,
        .String => ValueRows.String,
        .Sequence => ValueRows.Sequence,
        .Struct => ValueRows.Struct,
        .Variant => ValueRows.Variant,
        .Map => ValueRows.Map,
        .Pointer => ValueRows.Pointer,
        .Range => ValueRows.Range,
        .Type => ValueRows.Type,
        .MlirType => ValueRows.MlirType,
        .MlirAttribute => ValueRows.MlirAttribute,
        .MlirModule => ValueRows.MlirModule,
        .Function => ValueRows.Function,
        .Code => ValueRows.Code,
    };
}

pub const ValueStore = struct {
    gpa: std.mem.Allocator,
    arena: std.heap.ArenaAllocator,
    index: cst.StoreIndex(ValueKind) = .{},

    Int: cst.Table(ValueRows.Int) = .{},
    Float: cst.Table(ValueRows.Float) = .{},
    Bool: cst.Table(ValueRows.Bool) = .{},
    String: cst.Table(ValueRows.String) = .{},
    Sequence: cst.Table(ValueRows.Sequence) = .{},
    Struct: cst.Table(ValueRows.Struct) = .{},
    Variant: cst.Table(ValueRows.Variant) = .{},
    Map: cst.Table(ValueRows.Map) = .{},
    Pointer: cst.Table(ValueRows.Pointer) = .{},
    Range: cst.Table(ValueRows.Range) = .{},
    Type: cst.Table(ValueRows.Type) = .{},
    MlirType: cst.Table(ValueRows.MlirType) = .{},
    MlirAttribute: cst.Table(ValueRows.MlirAttribute) = .{},
    MlirModule: cst.Table(ValueRows.MlirModule) = .{},
    Function: cst.Table(ValueRows.Function) = .{},
    Code: cst.Table(ValueRows.Code) = .{},
    Void: cst.Table(ValueRows.Void) = .{},

    val_pool: cst.Pool(ValueId) = .{},
    struct_field_pool: cst.Pool(StructFieldId) = .{},
    map_entry_pool: cst.Pool(MapEntryId) = .{},
    code_binding_pool: cst.Pool(CodeBindingId) = .{},

    StructField: cst.Table(ValueRows.StructField) = .{},
    MapEntry: cst.Table(ValueRows.MapEntry) = .{},
    CodeBinding: cst.Table(ValueRows.CodeBinding) = .{},

    pub fn init(gpa: std.mem.Allocator) ValueStore {
        return .{ .gpa = gpa, .arena = std.heap.ArenaAllocator.init(gpa) };
    }

    pub fn deinit(self: *@This()) void {
        const gpa = self.gpa;
        self.index.deinit(gpa);
        inline for (@typeInfo(ValueKind).@"enum".fields) |f| @field(self, f.name).deinit(gpa);
        inline for (.{ "val_pool", "struct_field_pool", "map_entry_pool", "code_binding_pool" }) |n| @field(self, n).deinit(gpa);
        inline for (.{ "StructField", "MapEntry", "CodeBinding" }) |n| @field(self, n).deinit(gpa);
        self.arena.deinit();
    }

    pub fn add(self: *@This(), comptime K: ValueKind, row: ValueRowT(K)) ValueId {
        if (K == .Sequence) {
            const seq = row;
            const items = self.val_pool.slice(seq.elems);
            for (items, 0..) |item, i| {
                const raw = item.toRaw();
                if (raw >= self.index.kinds.items.len) {
                    std.debug.print(
                        "comptime> add Sequence invalid elem: index={}, elem_id={}, store_len={}\n",
                        .{ i, raw, self.index.kinds.items.len },
                    );
                    @panic("add Sequence: invalid element id");
                }
            }
        }
        const r = @field(self, @tagName(K)).add(self.gpa, row);
        return self.index.newId(self.gpa, K, r.toRaw(), ValueId);
    }

    pub fn get(self: *@This(), comptime K: ValueKind, id: ValueId) ValueRowT(K) {
        std.debug.assert(self.kind(id) == K);
        return @field(self, @tagName(K)).get(.{ .index = self.index.rows.items[id.toRaw()] });
    }

    pub fn kind(self: *const ValueStore, id: ValueId) ValueKind {
        return self.index.kinds.items[id.toRaw()];
    }

    pub fn addStructFields(self: *@This(), fields: []const ValueRows.StructField) cst.RangeOf(StructFieldId) {
        var ids = std.ArrayList(StructFieldId){};
        defer ids.deinit(self.gpa);
        for (fields) |f| ids.append(self.gpa, self.StructField.add(self.gpa, f)) catch @panic("OOM");
        return self.struct_field_pool.pushMany(self.gpa, ids.items);
    }

    pub fn addMapEntries(self: *@This(), entries: []const ValueRows.MapEntry) cst.RangeOf(MapEntryId) {
        var ids = std.ArrayList(MapEntryId){};
        defer ids.deinit(self.gpa);
        for (entries) |e| ids.append(self.gpa, self.MapEntry.add(self.gpa, e)) catch @panic("OOM");
        return self.map_entry_pool.pushMany(self.gpa, ids.items);
    }

    pub fn addCodeBindings(self: *@This(), bindings: []const ValueRows.CodeBinding) cst.RangeOf(CodeBindingId) {
        var ids = std.ArrayList(CodeBindingId){};
        defer ids.deinit(self.gpa);
        for (bindings) |b| ids.append(self.gpa, self.CodeBinding.add(self.gpa, b)) catch @panic("OOM");
        return self.code_binding_pool.pushMany(self.gpa, ids.items);
    }

    pub fn cloneValue(self: *ValueStore, other: *ValueStore, id: ValueId) !ValueId {
        const raw = id.toRaw();
        if (raw >= other.index.kinds.items.len) {
            std.debug.print("comptime> cloneValue invalid id: id={}, other_len={}\n", .{ raw, other.index.kinds.items.len });
            @panic("cloneValue: id out of bounds");
        }
        switch (other.kind(id)) {
            .Void => return self.add(.Void, .{}),
            .Int => return self.add(.Int, other.get(.Int, id)),
            .Float => return self.add(.Float, other.get(.Float, id)),
            .Bool => return self.add(.Bool, other.get(.Bool, id)),
            .String => {
                const s = other.get(.String, id).value;
                const copy = try self.arena.allocator().dupe(u8, s);
                return self.add(.String, .{ .value = copy });
            },
            .Type => return self.add(.Type, other.get(.Type, id)),
            .MlirType => return self.add(.MlirType, other.get(.MlirType, id)),
            .MlirAttribute => return self.add(.MlirAttribute, other.get(.MlirAttribute, id)),
            .MlirModule => {
                const mod = other.get(.MlirModule, id).module;
                return self.add(.MlirModule, .{ .module = mlir.Module.fromOperation(mlir.Operation.clone(mod.getOperation())) });
            },
            .Range => return self.add(.Range, other.get(.Range, id)),
            .Pointer => {
                const p = other.get(.Pointer, id);
                return self.add(.Pointer, .{ .pointee = try self.cloneValue(other, p.pointee) });
            },
            .Function => return self.add(.Function, other.get(.Function, id)),
            .Sequence => {
                const seq = other.get(.Sequence, id);
                const elems_copy = try self.gpa.dupe(ValueId, other.val_pool.slice(seq.elems));
                defer self.gpa.free(elems_copy);

                var new_elems = try std.ArrayList(ValueId).initCapacity(self.gpa, elems_copy.len);
                defer new_elems.deinit(self.gpa);
                for (elems_copy, 0..) |e, i| {
                    const e_raw = e.toRaw();
                    if (e_raw >= other.index.kinds.items.len) {
                        std.debug.print(
                            "comptime> cloneValue invalid sequence elem: parent_id={}, index={}, elem_id={}, other_len={}\n",
                            .{ raw, i, e_raw, other.index.kinds.items.len },
                        );
                        @panic("cloneValue: sequence elem out of bounds");
                    }
                    new_elems.appendAssumeCapacity(try self.cloneValue(other, e));
                }
                return self.add(.Sequence, .{ .elems = self.val_pool.pushMany(self.gpa, new_elems.items) });
            },
            .Struct => {
                const st = other.get(.Struct, id);
                const fields_copy = try self.gpa.dupe(StructFieldId, other.struct_field_pool.slice(st.fields));
                defer self.gpa.free(fields_copy);

                var new_fields = try std.ArrayList(ValueRows.StructField).initCapacity(self.gpa, fields_copy.len);
                defer new_fields.deinit(self.gpa);
                for (fields_copy) |fid| {
                    const f = other.StructField.get(fid);
                    new_fields.appendAssumeCapacity(.{ .name = f.name, .value = try self.cloneValue(other, f.value) });
                }
                return self.add(.Struct, .{ .fields = self.addStructFields(new_fields.items), .owner = st.owner });
            },
            .Variant => {
                const v = other.get(.Variant, id);
                const payload = if (v.payload.isNone()) OptValueId.none() else OptValueId.some(try self.cloneValue(other, v.payload.unwrap()));
                return self.add(.Variant, .{ .tag = v.tag, .payload = payload });
            },
            .Map => {
                const m = other.get(.Map, id);
                const entries_copy = try self.gpa.dupe(MapEntryId, other.map_entry_pool.slice(m.entries));
                defer self.gpa.free(entries_copy);

                var new_entries = try std.ArrayList(ValueRows.MapEntry).initCapacity(self.gpa, entries_copy.len);
                defer new_entries.deinit(self.gpa);
                for (entries_copy) |eid| {
                    const e = other.MapEntry.get(eid);
                    new_entries.appendAssumeCapacity(.{ .key = try self.cloneValue(other, e.key), .value = try self.cloneValue(other, e.value) });
                }
                return self.add(.Map, .{ .entries = self.addMapEntries(new_entries.items) });
            },
            .Code => {
                const c = other.get(.Code, id);
                const captures_copy = try self.gpa.dupe(CodeBindingId, other.code_binding_pool.slice(c.captures));
                defer self.gpa.free(captures_copy);

                var new_captures = try std.ArrayList(ValueRows.CodeBinding).initCapacity(self.gpa, captures_copy.len);
                defer new_captures.deinit(self.gpa);
                for (captures_copy) |cid| {
                    const cb = other.CodeBinding.get(cid);
                    new_captures.appendAssumeCapacity(.{ .name = cb.name, .value = try self.cloneValue(other, cb.value) });
                }
                return self.add(.Code, .{ .block = c.block, .ast = c.ast, .captures = self.addCodeBindings(new_captures.items) });
            },
        }
    }

    pub fn hashValue(self: *ValueStore, id: ValueId) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const k = self.kind(id);
        hasher.update(&.{@intFromEnum(k)});
        switch (k) {
            .Void => {},
            .Int => hasher.update(std.mem.asBytes(&self.get(.Int, id).value)),
            .Float => hasher.update(std.mem.asBytes(&self.get(.Float, id).value)),
            .Bool => hasher.update(std.mem.asBytes(&self.get(.Bool, id).value)),
            .String => hasher.update(self.get(.String, id).value),
            .Type => hasher.update(std.mem.asBytes(&self.get(.Type, id).ty.toRaw())),
            .MlirType => hasher.update(std.mem.asBytes(&self.get(.MlirType, id).ty.handle)),
            .MlirAttribute => hasher.update(std.mem.asBytes(&self.get(.MlirAttribute, id).attr.handle)),
            .MlirModule => hasher.update(std.mem.asBytes(&self.get(.MlirModule, id).module.handle)),
            .Range => hasher.update(std.mem.asBytes(&self.get(.Range, id))),
            .Pointer => hasher.update(std.mem.asBytes(&self.hashValue(self.get(.Pointer, id).pointee))),
            .Function => hasher.update(std.mem.asBytes(&self.get(.Function, id).expr.toRaw())),
            .Sequence => {
                const elems = self.val_pool.slice(self.get(.Sequence, id).elems);
                hasher.update(std.mem.asBytes(&elems.len));
                for (elems) |e| hasher.update(std.mem.asBytes(&self.hashValue(e)));
            },
            .Struct => {
                const fields = self.struct_field_pool.slice(self.get(.Struct, id).fields);
                hasher.update(std.mem.asBytes(&fields.len));
                for (fields) |fid| {
                    const f = self.StructField.get(fid);
                    hasher.update(std.mem.asBytes(&f.name));
                    hasher.update(std.mem.asBytes(&self.hashValue(f.value)));
                }
            },
            .Variant => {
                const v = self.get(.Variant, id);
                hasher.update(std.mem.asBytes(&v.tag));
                if (!v.payload.isNone()) hasher.update(std.mem.asBytes(&self.hashValue(v.payload.unwrap())));
            },
            .Map => {
                const entries = self.map_entry_pool.slice(self.get(.Map, id).entries);
                hasher.update(std.mem.asBytes(&entries.len));
                for (entries) |eid| {
                    const e = self.MapEntry.get(eid);
                    hasher.update(std.mem.asBytes(&self.hashValue(e.key)));
                    hasher.update(std.mem.asBytes(&self.hashValue(e.value)));
                }
            },
            .Code => {
                const c = self.get(.Code, id);
                hasher.update(std.mem.asBytes(&c.block.toRaw()));
                const captures = self.code_binding_pool.slice(c.captures);
                hasher.update(std.mem.asBytes(&captures.len));
                for (captures) |cid| {
                    const cb = self.CodeBinding.get(cid);
                    hasher.update(std.mem.asBytes(&cb.name));
                    hasher.update(std.mem.asBytes(&self.hashValue(cb.value)));
                }
            },
        }
        return hasher.final();
    }
};

/// Extract a single expression from a code value when it represents a one-expression block.
pub fn codeExprFromCodeValue(ast_unit: *ast.Ast, code: CodeValue) ?ast.ExprId {
    if (ast_unit.kind(code.block) != .Block) return code.block;
    const block = ast_unit.exprs.get(.Block, code.block);
    const stmts = ast_unit.stmts.stmt_pool.slice(block.items);
    if (stmts.len != 1) return null;
    if (ast_unit.kind(stmts[0]) != .Expr) return null;
    return ast_unit.stmts.get(.Expr, stmts[0]).expr;
}

pub const BindingInfo = struct {
    name: ast.StrId,
    kind: Kind,

    pub const Kind = union(enum) {
        type_param: types.TypeId,
        value_param: BindingValue,
        runtime_param: types.TypeId,
    };

    pub fn typeParam(name: ast.StrId, ty: types.TypeId) BindingInfo {
        return .{ .name = name, .kind = .{ .type_param = ty } };
    }

    pub fn valueParam(name: ast.StrId, ty: types.TypeId, value: ValueId) BindingInfo {
        return .{ .name = name, .kind = .{ .value_param = .{ .ty = ty, .value = value } } };
    }

    pub fn runtimeParam(name: ast.StrId, ty: types.TypeId) BindingInfo {
        return .{ .name = name, .kind = .{ .runtime_param = ty } };
    }
};

pub const BindingValue = struct {
    ty: types.TypeId,
    value: ValueId,
};

pub const SpecializationContext = struct {
    specialized_ty: types.TypeId,
    skip_params: usize,
    bindings: []const BindingInfo,
};

pub const SpecializationRequest = struct {
    decl_id: ast.DeclId,
    mangled_name: tir.StrId,
    specialized_ty: types.TypeId,
    skip_params: usize,
    bindings: []const BindingInfo,
};

// =============================
// Helper: Builtin Type Map
// =============================

const BuiltinTypeTag = enum { Bool, I8, I16, I32, I64, U8, U16, U32, U64, F32, F64, Usize, Char, String, Void, Any, Code };

const builtin_type_map = std.StaticStringMap(BuiltinTypeTag).initComptime(.{
    .{ "bool", .Bool }, .{ "i8", .I8 },         .{ "i16", .I16 },   .{ "i32", .I32 },
    .{ "i64", .I64 },   .{ "u8", .U8 },         .{ "u16", .U16 },   .{ "u32", .U32 },
    .{ "u64", .U64 },   .{ "f32", .F32 },       .{ "f64", .F64 },   .{ "usize", .Usize },
    .{ "char", .Char }, .{ "string", .String }, .{ "void", .Void }, .{ "any", .Any },
    .{ "Code", .Code },
});

pub fn builtinTypeId(ts: *types.TypeStore, name: []const u8) ?types.TypeId {
    const tag = builtin_type_map.get(name) orelse return null;
    return switch (tag) {
        .Bool => ts.tBool(),
        .I8 => ts.tI8(),
        .I16 => ts.tI16(),
        .I32 => ts.tI32(),
        .I64 => ts.tI64(),
        .U8 => ts.tU8(),
        .U16 => ts.tU16(),
        .U32 => ts.tU32(),
        .U64 => ts.tU64(),
        .F32 => ts.tF32(),
        .F64 => ts.tF64(),
        .Usize => ts.tUsize(),
        .Char => ts.tU32(),
        .String => ts.tString(),
        .Void => ts.tVoid(),
        .Any => ts.tAny(),
        .Code => ts.tCode(),
    };
}

// =============================
// C API Implementations
// =============================

pub fn type_of_impl(context: ?*anyopaque, type_id_raw: u32) callconv(.c) u32 {
    const ctx: *Context = @ptrCast(@alignCast(context.?));
    const kind = ctx.type_store.getKind(types.TypeId.fromRaw(type_id_raw));
    std.debug.print("comptime> type_of_impl: type_id_raw={}, kind={s}\n", .{ type_id_raw, @tagName(kind) });
    return @intFromEnum(kind);
}

pub fn comptime_print_impl(context: ?*anyopaque, format: [*c]const u8, ...) callconv(.c) void {
    _ = context;
    std.debug.print("comptime> {s}\n", .{@as([]const u8, std.mem.sliceTo(format, 0))});
}

pub fn get_type_by_name_impl(context: ?*anyopaque, name: [*c]const u8) callconv(.c) u32 {
    const ctx: *Context = @ptrCast(@alignCast(context.?));
    if (builtinTypeId(ctx.type_store, std.mem.sliceTo(name, 0))) |ty| {
        return ty.toRaw();
    }
    return ctx.type_store.tVoid().toRaw();
}

// =============================
// Comptime Lower TIR API
// =============================

pub fn runComptimeExpr(self: *LowerTir, ctx: *LowerTir.LowerContext, a: *ast.Ast, expr: ast.ExprId, bindings: []const Pipeline.ComptimeBinding) !ValueId {
    _ = ctx;
    return self.chk.evalComptimeExpr(&self.chk.checker_ctx.items[a.file_id], a, expr, bindings);
}

pub fn constValueFromComptime(self: *LowerTir, store: *ValueStore, blk: *tir.Builder.BlockFrame, ty: types.TypeId, value: ValueId) !tir.ValueId {
    switch (store.kind(value)) {
        .Int => {
            const val = store.get(.Int, value).value;
            return blk.builder.tirValue(.ConstInt, blk, ty, .none(), .{
                .value = switch (self.context.type_store.getKind(ty)) {
                    .I32 => @as(u64, @as(u32, @bitCast(@as(i32, @intCast(val))))),
                    .I64 => @as(u64, @bitCast(@as(i64, @intCast(val)))),
                    else => @as(u64, @intCast(val)),
                },
            });
        },
        .Float => return blk.builder.tirValue(.ConstFloat, blk, ty, .none(), .{ .value = store.get(.Float, value).value }),
        .Bool => return blk.builder.tirValue(.ConstBool, blk, ty, .none(), .{ .value = store.get(.Bool, value).value }),
        .Void => return blk.builder.tirValue(.ConstUndef, blk, ty, .none(), .{}),
        .String => return blk.builder.tirValue(.ConstString, blk, ty, .none(), .{ .text = blk.builder.intern(store.get(.String, value).value) }),
        .Sequence => {
            const seq = store.get(.Sequence, value);
            const ts = self.context.type_store;
            const kind = ts.getKind(ty);
            const items = store.val_pool.slice(seq.elems);
            switch (kind) {
                .Tuple => {
                    const tr = ts.get(.Tuple, ty);
                    const elem_tys = ts.type_pool.slice(tr.elems);
                    if (elem_tys.len != items.len) return error.UnsupportedComptimeType;
                    var elems = try self.gpa.alloc(tir.ValueId, elem_tys.len);
                    defer self.gpa.free(elems);
                    for (elem_tys, 0..) |ety, i| {
                        elems[i] = try constValueFromComptime(self, store, blk, ety, items[i]);
                    }
                    return blk.builder.tupleMake(blk, ty, elems, .none());
                },
                .Array => {
                    const ar = ts.get(.Array, ty);
                    if (ar.len != items.len) return error.UnsupportedComptimeType;
                    var elems = try self.gpa.alloc(tir.ValueId, ar.len);
                    defer self.gpa.free(elems);
                    for (items, 0..) |item, i| {
                        elems[i] = try constValueFromComptime(self, store, blk, ar.elem, item);
                    }
                    return blk.builder.arrayMake(blk, ty, elems, .none());
                },
                .Slice => {
                    const slice = ts.get(.Slice, ty);
                    const array_ty = ts.mkArray(slice.elem, items.len);
                    var elems = try self.gpa.alloc(tir.ValueId, items.len);
                    defer self.gpa.free(elems);
                    for (items, 0..) |item, i| {
                        elems[i] = try constValueFromComptime(self, store, blk, slice.elem, item);
                    }
                    const array_val = blk.builder.arrayMake(blk, array_ty, elems, .none());
                    return coerceArrayToSliceConst(self, blk, array_val, array_ty, ty);
                },
                else => {
                    if (items.len == 1) {
                        return constValueFromComptime(self, store, blk, ty, items[0]);
                    }
                    return error.UnsupportedComptimeType;
                },
            }
        },
        .Struct => {
            const sv = store.get(.Struct, value);
            if (self.context.type_store.getKind(ty) != .Struct) return error.UnsupportedComptimeType;
            const struct_row = self.context.type_store.get(.Struct, ty);
            const type_fields = self.context.type_store.field_pool.slice(struct_row.fields);
            var inits = try self.gpa.alloc(tir.Rows.StructFieldInit, type_fields.len);
            defer self.gpa.free(inits);

            const value_fields = store.struct_field_pool.slice(sv.fields);

            for (type_fields, 0..) |fid, i| {
                const fdef = self.context.type_store.Field.get(fid);
                var val: ?ValueId = null;
                for (value_fields) |sfid| {
                    const sf = store.StructField.get(sfid);
                    if (sf.name.eq(fdef.name)) {
                        val = sf.value;
                        break;
                    }
                }
                const field_val = if (val) |v| try constValueFromComptime(self, store, blk, fdef.ty, v) else blk.builder.tirValue(.ConstUndef, blk, fdef.ty, .none(), .{});
                inits[i] = .{ .index = @intCast(i), .name = .some(fdef.name), .value = field_val };
            }
            return blk.builder.structMake(blk, ty, inits, .none());
        },
        .Variant => {
            const vv = store.get(.Variant, value);
            const ts = self.context.type_store;
            const kind = ts.getKind(ty);
            if (kind != .Variant and kind != .Error) return error.UnsupportedComptimeType;
            const fields = if (kind == .Variant) ts.field_pool.slice(ts.get(.Variant, ty).variants) else ts.field_pool.slice(ts.get(.Error, ty).variants);
            var tag_idx: u32 = 0;
            var payload_ty: types.TypeId = ts.tVoid();
            var found = false;

            var fields_buf: [64]types.TypeStore.StructFieldArg = undefined;
            var fields_slice: []types.TypeStore.StructFieldArg = &.{};
            var heap_fields: ?[]types.TypeStore.StructFieldArg = null;
            defer if (heap_fields) |ptr| self.gpa.free(ptr);

            if (fields.len <= fields_buf.len) {
                fields_slice = fields_buf[0..fields.len];
            } else {
                heap_fields = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                fields_slice = heap_fields.?;
            }

            for (fields, 0..) |fid, i| {
                const f = ts.Field.get(fid);
                fields_slice[i] = .{ .name = f.name, .ty = f.ty };
                if (f.name.eq(vv.tag)) {
                    tag_idx = @intCast(i);
                    payload_ty = f.ty;
                    found = true;
                }
            }
            if (!found) return error.UnsupportedComptimeType;

            const payload_val: ?tir.ValueId = blk_payload: {
                if (ts.getKind(payload_ty) == .Void) break :blk_payload null;
                if (vv.payload.isNone()) return error.UnsupportedComptimeType;
                break :blk_payload try constValueFromComptime(self, store, blk, payload_ty, vv.payload.unwrap());
            };

            const tag_val = blk.builder.tirValue(.ConstInt, blk, ts.tI32(), .none(), .{ .value = tag_idx });
            const union_ty = ts.mkUnion(fields_slice);
            const union_val: tir.ValueId = if (payload_val) |pv|
                blk.builder.tirValue(.UnionMake, blk, union_ty, .none(), .{ .field_index = tag_idx, .value = pv })
            else
                blk.builder.tirValue(.ConstUndef, blk, union_ty, .none(), .{});

            return blk.builder.structMake(blk, ty, &[_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = tag_val },
                .{ .index = 1, .name = .none(), .value = union_val },
            }, .none());
        },
        .MlirType, .MlirAttribute, .MlirModule => return blk.builder.tirValue(.ConstUndef, blk, ty, .none(), .{}),
        else => return error.UnsupportedComptimeType,
    }
}

fn coerceArrayToSliceConst(self: *LowerTir, blk: *tir.Builder.BlockFrame, array_value: tir.ValueId, array_ty: types.TypeId, slice_ty: types.TypeId) tir.ValueId {
    const ts = self.context.type_store;
    const arr = ts.get(.Array, array_ty);
    const slice = ts.get(.Slice, slice_ty);
    const ptr_array_ty = ts.mkPtr(array_ty, false);

    var name_buf: [64]u8 = undefined;
    const name = std.fmt.bufPrint(&name_buf, "__sr_const_slice_{d}", .{self.const_slice_counter}) catch unreachable;
    self.const_slice_counter += 1;
    const name_id = blk.builder.intern(name);
    _ = blk.builder.addGlobalWithInit(name_id, array_ty, .none);
    const slot = blk.builder.tirValue(.GlobalAddr, blk, ptr_array_ty, .none(), .{ .name = name_id });
    _ = blk.builder.tirValue(.Store, blk, array_ty, .none(), .{ .ptr = slot, .value = array_value, .@"align" = 0 });

    return blk.builder.structMake(blk, slice_ty, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = blk.builder.tirValue(.CastBit, blk, ts.mkPtr(slice.elem, slice.is_const), .none(), .{ .value = slot }) },
        .{ .index = 1, .name = .none(), .value = blk.builder.tirValue(.ConstInt, blk, ts.tUsize(), .none(), .{ .value = @as(u64, @intCast(arr.len)) }) },
    }, .none());
}

pub fn mangleMonomorphName(self: *LowerTir, store: *ValueStore, base: tir.StrId, bindings: []const BindingInfo) !tir.StrId {
    var buf = List(u8).init(self.gpa);
    defer buf.deinit();
    try buf.appendSlice(self.context.type_store.strs.get(base));
    if (bindings.len == 0) return self.context.type_store.strs.intern(buf.items);
    try buf.appendSlice("_M");
    for (bindings) |info| {
        try buf.append('_');
        var w = buf.writer();
        switch (info.kind) {
            .type_param => |ty| try w.print("T{}", .{ty.toRaw()}),
            .value_param => |vp| try w.print("V{}x{X}", .{ vp.ty.toRaw(), store.hashValue(vp.value) }),
            .runtime_param => |ty| try w.print("R{}", .{ty.toRaw()}),
        }
    }
    return self.context.type_store.strs.intern(buf.items);
}
