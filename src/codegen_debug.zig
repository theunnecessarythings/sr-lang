const codegen = @import("codegen_main.zig");
const Codegen = codegen.Codegen;
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const std = @import("std");
const abi = @import("abi.zig");

/// DWARF tag value for basic scalar types.
const DW_TAG_base_type: u32 = 0x24;
/// DWARF tag value used when describing pointer types.
const DW_TAG_pointer_type: u32 = 0x0f;
const DW_TAG_array_type: u32 = 0x01;
const DW_TAG_structure_type: u32 = 0x13;
const DW_TAG_member: u32 = 0x0d;
const POINTER_SIZE_BITS: u64 = 64;

pub const DebugFileInfo = struct {
    file_attr: mlir.Attribute,
    compile_unit_attr: mlir.Attribute,
};

pub const DebugSubprogramInfo = struct {
    attr: mlir.Attribute,
    file_id: u32,
    line: u32,
    scope_line: u32,
    loc: tir.OptLocId,
};

/// Clear the per-module debug caches so they can be rebuilt (used between compilations).
pub fn resetDebugCaches(self: *Codegen) void {
    _ = self.debug_arena.reset(.retain_capacity);
    self.di_files.clearRetainingCapacity();
    self.di_subprograms.clearRetainingCapacity();
    self.di_null_type_attr = mlir.Attribute.empty();
    self.di_subroutine_null_type_attr = mlir.Attribute.empty();
    self.di_empty_expr_attr = mlir.Attribute.empty();
    self.di_type_cache.clearRetainingCapacity();
    self.di_recursive_ids.clearRetainingCapacity();
    self.next_di_id = 0;
    self.debug_module_attrs_initialized = false;

    var mod_op = self.module.getOperation();
    const attrs_to_clear = [_][]const u8{ "llvm.dbg.cu", "llvm.module.flags", "llvm.ident" };
    for (attrs_to_clear) |name| {
        _ = mod_op.removeDiscardableAttributeByName(mlir.StringRef.from(name));
    }
}

/// Generate a new monotonic ID for naming debug metadata nodes.
inline fn nextDistinctId(self: *Codegen) usize {
    defer self.next_di_id += 1;
    return self.next_di_id;
}

const PrintCtx = struct {
    list: std.ArrayListUnmanaged(u8),
    alloc: std.mem.Allocator,
    err: bool,
};

fn printCb(str: mlir.c.MlirStringRef, ctx_ptr: ?*anyopaque) callconv(.c) void {
    const ctx: *PrintCtx = @ptrCast(@alignCast(ctx_ptr));
    ctx.list.appendSlice(ctx.alloc, str.data[0..str.length]) catch {
        ctx.err = true;
    };
}

fn getAttrText(self: *Codegen, attr: mlir.Attribute) ![]const u8 {
    var ctx = PrintCtx{ .list = .{}, .alloc = self.debug_arena.allocator(), .err = false };
    attr.print(printCb, &ctx);
    if (ctx.err) return error.DebugAttrParseFailed;
    return ctx.list.items;
}

/// Create or reuse the debug metadata entry that describes `file_id`'s source file.
fn ensureDebugFile(self: *Codegen, file_id: u32) !*DebugFileInfo {
    if (self.di_files.getPtr(file_id)) |info| return info;

    const path = self.context.source_manager.get(file_id) orelse "unknown";
    const file_attr = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr(std.fs.path.basename(path)), self.strAttr(std.fs.path.dirname(path) orelse "."));
    if (file_attr.isNull()) return error.DebugAttrParseFailed;

    const cu_attr = try buildDICompileUnit(self, file_attr);
    try addCompileUnitToModule(self, cu_attr);

    try self.di_files.put(file_id, .{ .file_attr = file_attr, .compile_unit_attr = cu_attr });
    return self.di_files.getPtr(file_id).?;
}

/// Serialize a `llvm.di.compile_unit` attribute for the given file.
fn buildDICompileUnit(self: *Codegen, file_attr: mlir.Attribute) !mlir.Attribute {
    const alloc = self.debug_arena.allocator();
    const id_str = try std.fmt.allocPrint(alloc, "cu_{d}", .{nextDistinctId(self)});
    const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_str));

    const file_txt = try getAttrText(self, file_attr);
    const prod_txt = try getAttrText(self, self.strAttr("sr-lang"));
    const id_txt = try getAttrText(self, id_attr);

    const cu_txt = try std.fmt.allocPrint(
        alloc,
        "#llvm.di_compile_unit<id = {s}, sourceLanguage = DW_LANG_C11, file = {s}, producer = {s}, isOptimized = false, emissionKind = Full>",
        .{ id_txt, file_txt, prod_txt },
    );

    const cu_attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(cu_txt));
    if (cu_attr.isNull()) return error.DebugAttrParseFailed;
    return cu_attr;
}

/// Attach `cu_attr` to the module-level debug `llvm.dbg.cu` attribute list, avoiding duplicates.
fn addCompileUnitToModule(self: *Codegen, cu_attr: mlir.Attribute) !void {
    var mod_op = self.module.getOperation();
    const name = mlir.StringRef.from("llvm.dbg.cu");
    const existing = mod_op.getDiscardableAttributeByName(name);

    if (existing.isNull()) {
        mod_op.setDiscardableAttributeByName(name, mlir.Attribute.arrayAttrGet(self.mlir_ctx, &.{cu_attr}));
        return;
    }

    var elems = std.ArrayList(mlir.Attribute){};
    defer elems.deinit(self.gpa);

    var present = false;
    const count = existing.arrayAttrGetNumElements();
    for (0..count) |i| {
        const e = existing.arrayAttrGetElement(i);
        if (e.equal(&cu_attr)) present = true;
        try elems.append(self.gpa, e);
    }

    if (!present) {
        try elems.append(self.gpa, cu_attr);
        mod_op.setDiscardableAttributeByName(name, mlir.Attribute.arrayAttrGet(self.mlir_ctx, elems.items));
    }
}

/// Build the `llvm.disubprogram` attribute for `f_id` and cache it for reused emissions.
pub fn ensureDebugSubprogram(self: *Codegen, f_id: tir.FuncId, func_name: []const u8, line: u32, file_id: u32, loc: tir.OptLocId, ret_ty: types.TypeId, params: []const tir.ParamId, t: *tir.TIR) !*DebugSubprogramInfo {
    if (self.di_subprograms.getPtr(f_id)) |info| return info;

    const fi = try ensureDebugFile(self, file_id);
    const name_attr = self.strAttr(func_name);

    const id_str = try std.fmt.allocPrint(self.debug_arena.allocator(), "sp_{d}", .{nextDistinctId(self)});
    const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_str));
    const rec_attr = mlir.Attribute.distinctAttrCreate(mlir.Attribute.unitAttrGet(self.mlir_ctx));

    // Note: buildDISubroutineTypeAttr must be provided by the context (same file or imported)
    const type_attr = try buildDISubroutineTypeAttr(self, ret_ty, params, t);

    const attr = mlir.LLVMAttributes.getLLVMDISubprogramAttr(
        self.mlir_ctx,
        rec_attr,
        false,
        id_attr,
        fi.compile_unit_attr,
        fi.file_attr,
        name_attr,
        name_attr,
        fi.file_attr,
        line,
        line,
        1 << 3,
        type_attr,
        &[_]mlir.Attribute{},
        &[_]mlir.Attribute{},
    );
    if (attr.isNull()) return error.DebugAttrParseFailed;

    try self.di_subprograms.put(f_id, .{ .attr = attr, .file_id = file_id, .line = line, .scope_line = line, .loc = loc });
    return self.di_subprograms.getPtr(f_id).?;
}

/// Set the LLVM target triple/data layout attributes emitted via MLIR.
pub fn attachTargetInfo(self: *Codegen) !void {
    var mod_op = self.module.getOperation();
    mod_op.setDiscardableAttributeByName(mlir.StringRef.from("llvm.target_triple"), self.strAttr("x86_64-unknown-linux-gnu"));
    mod_op.setDiscardableAttributeByName(mlir.StringRef.from("llvm.data_layout"), self.strAttr("e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"));
}

const KEY_DB_VER = ", \"Debug Info Version\",";
const KEY_DW_VER = ", \"Dwarf Version\",";

fn appendModuleFlag(self: *Codegen, list: *std.ArrayList(mlir.Attribute), behavior: []const u8, key: []const u8, val: []const u8) !void {
    const txt = try std.fmt.allocPrint(self.debug_arena.allocator(), "#llvm.mlir.module_flag<{s}, \"{s}\", {s}>", .{ behavior, key, val });
    const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(txt));
    if (attr.isNull()) return error.DebugAttrParseFailed;
    try list.append(self.gpa, attr);
}

/// Configure module-level debug attributes (flags, identifiers) once per module.
pub fn ensureDebugModuleAttrs(self: *Codegen) !void {
    if (!codegen.enable_debug_info or self.debug_module_attrs_initialized) return;

    var mod_op = self.module.getOperation();
    const flags_name = mlir.StringRef.from("llvm.module.flags");
    const existing = mod_op.getDiscardableAttributeByName(flags_name);

    var flags = std.ArrayList(mlir.Attribute){};
    defer flags.deinit(self.gpa);

    var has_db = false;
    var has_dw = false;

    if (!existing.isNull()) {
        const count = existing.arrayAttrGetNumElements();
        for (0..count) |i| {
            const elem = existing.arrayAttrGetElement(i);
            try flags.append(self.gpa, elem);
            if (!has_db or !has_dw) {
                const txt = try getAttrText(self, elem);
                if (!has_db and std.mem.indexOf(u8, txt, KEY_DB_VER) != null) has_db = true;
                if (!has_dw and std.mem.indexOf(u8, txt, KEY_DW_VER) != null) has_dw = true;
            }
        }
    }

    if (!has_db) try appendModuleFlag(self, &flags, "warning", "Debug Info Version", "3 : i32");
    if (!has_dw) try appendModuleFlag(self, &flags, "max", "Dwarf Version", "5 : i32");

    if (flags.items.len > 0) {
        mod_op.setDiscardableAttributeByName(flags_name, mlir.Attribute.arrayAttrGet(self.mlir_ctx, flags.items));
    }

    const ident_name = mlir.StringRef.from("llvm.ident");
    if (mod_op.getDiscardableAttributeByName(ident_name).isNull()) {
        mod_op.setDiscardableAttributeByName(ident_name, mlir.Attribute.arrayAttrGet(self.mlir_ctx, &.{self.strAttr("sr-lang compiler")}));
    }
    self.debug_module_attrs_initialized = true;
}

/// Lazily fetch the MLIR attribute that represents a null debug type.
fn ensureDINullTypeAttr(self: *Codegen) !mlir.Attribute {
    if (!self.di_null_type_attr.isNull()) return self.di_null_type_attr;
    const attr = mlir.LLVMAttributes.getLLVMDINullTypeAttr(self.mlir_ctx);
    if (attr.isNull()) return error.DebugAttrParseFailed;
    self.di_null_type_attr = attr;
    return attr;
}

/// Map SR `ty` to an LLVM DI attribute, caching the result after creation.
pub fn ensureDIType(self: *Codegen, ty: types.TypeId) !mlir.Attribute {
    if (self.di_type_cache.get(ty)) |cached| return cached;

    // Helper: Create basic integer/float types
    const diBasic = struct {
        fn make(cg: *Codegen, name: []const u8, bits: u64, enc: mlir.LLVMTypeEncoding) mlir.Attribute {
            return mlir.LLVMAttributes.getLLVMDIBasicTypeAttr(cg.mlir_ctx, DW_TAG_base_type, cg.strAttr(name), bits, enc);
        }
    }.make;

    // Helper: Format a derived type string (pointer, member, etc.)
    const diDerived = struct {
        fn make(cg: *Codegen, tag: []const u8, name: []const u8, base: mlir.Attribute, size: u64, @"align": u64, offset: u64) ![]const u8 {
            const base_txt = try getAttrText(cg, base);
            return std.fmt.allocPrint(cg.debug_arena.allocator(), "#llvm.di_derived_type<tag = {s}, name = \"{s}\", baseType = {s}, sizeInBits = {d}, alignInBits = {d}, offset = {d}>", .{ tag, name, base_txt, size, @"align", offset });
        }
    }.make;

    // Helper: Parse a composite type string
    const diComposite = struct {
        fn make(cg: *Codegen, tag: []const u8, name: []const u8, id: mlir.Attribute, file: mlir.Attribute, size: u64, @"align": u64, flags: []const u8, elems: []const u8) !mlir.Attribute {
            const id_txt = try getAttrText(cg, id);
            const f_txt = try getAttrText(cg, file);
            const txt = try std.fmt.allocPrint(cg.debug_arena.allocator(), "#llvm.di_composite_type<recId = {s}, tag = {s}, name = \"{s}\", file = {s}, line = 0, sizeInBits = {d}, alignInBits = {d}, flags = {s}, elements = #llvm.di_node_array<[{s}]>>", .{ id_txt, tag, name, f_txt, size, @"align", flags, elems });
            return mlir.Attribute.parseGet(cg.mlir_ctx, mlir.StringRef.from(txt));
        }
    }.make;

    const kind = self.context.type_store.getKind(ty);
    const attr: mlir.Attribute = switch (kind) {
        .Void, .Noreturn => try ensureDINullTypeAttr(self),
        .Bool => diBasic(self, "bool", 1, .Boolean),
        .I8 => diBasic(self, "i8", 8, .Signed),
        .I16 => diBasic(self, "i16", 16, .Signed),
        .I32 => diBasic(self, "i32", 32, .Signed),
        .I64 => diBasic(self, "i64", 64, .Signed),
        .U8 => diBasic(self, "u8", 8, .Unsigned),
        .U16 => diBasic(self, "u16", 16, .Unsigned),
        .U32 => diBasic(self, "u32", 32, .Unsigned),
        .U64 => diBasic(self, "u64", 64, .Unsigned),
        .Usize => diBasic(self, "usize", POINTER_SIZE_BITS, .Unsigned),
        .F32 => diBasic(self, "f32", 32, .FloatT),
        .F64 => diBasic(self, "f64", 64, .FloatT),
        .Undef, .MlirModule, .MlirAttribute, .MlirType, .TypeType, .Future, .Ast, .TypeError, .Code => try ensureDINullTypeAttr(self),

        .Ptr => blk: {
            const inner = try ensureDIType(self, self.context.type_store.get(.Ptr, ty).elem);
            const txt = try diDerived(self, "DW_TAG_pointer_type", "", inner, 64, 64, 0);
            break :blk mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(txt));
        },

        .Slice, .String, .DynArray => blk: {
            const is_str = kind == .String;
            const is_dyn = kind == .DynArray;
            const elem_ty = if (is_str) self.context.type_store.tU8() else if (is_dyn) self.context.type_store.get(.DynArray, ty).elem else self.context.type_store.get(.Slice, ty).elem;

            const scratch = self.debug_arena.allocator();
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(try std.fmt.allocPrint(scratch, "slice_{d}_{s}", .{ nextDistinctId(self), @tagName(kind) })));

            const elem_di = try ensureDIType(self, elem_ty);
            const ptr_txt = try diDerived(self, "DW_TAG_pointer_type", "", elem_di, 64, 64, 0);
            const ptr_di = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(ptr_txt));

            const m_ptr = try diDerived(self, "DW_TAG_member", "ptr", ptr_di, 64, 64, 0);
            const m_len = try diDerived(self, "DW_TAG_member", "len", diBasic(self, "i64", 64, .Signed), 64, 64, 64);

            var elems_txt = try std.fmt.allocPrint(scratch, "{s}, {s}", .{ m_ptr, m_len });
            var size: u64 = 128;

            if (is_dyn) {
                const m_cap = try diDerived(self, "DW_TAG_member", "cap", diBasic(self, "i64", 64, .Signed), 64, 64, 128);
                elems_txt = try std.fmt.allocPrint(scratch, "{s}, {s}", .{ elems_txt, m_cap });
                size = 192;
            }

            break :blk try diComposite(self, "DW_TAG_structure_type", if (is_str) "string" else if (is_dyn) "dyn[]" else "[]", id_attr, try ensureDINullTypeAttr(self), size, 64, "", elems_txt);
        },

        .Struct, .Tuple, .Complex, .Union, .Variant, .Error, .ErrorSet, .Closure => blk: {
            if (self.di_recursive_ids.get(ty)) |recId| break :blk mlir.LLVMAttributes.getLLVMDICompositeTypeAttrRecSelf(recId);

            const scratch = self.debug_arena.allocator();
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(try std.fmt.allocPrint(scratch, "comp_{d}_{s}", .{ nextDistinctId(self), @tagName(kind) })));
            try self.di_recursive_ids.put(ty, id_attr);

            var elems_list = std.ArrayListUnmanaged(u8){};
            var offset: u64 = 0;
            var max_align: u64 = 1;
            var name: []const u8 = "struct";
            var tag: []const u8 = "DW_TAG_structure_type";

            switch (kind) {
                .Struct => {
                    const s = self.context.type_store.get(.Struct, ty);
                    for (self.context.type_store.field_pool.slice(s.fields), 0..) |fid, i| {
                        const f = self.context.type_store.Field.get(fid);
                        const sa = abi.abiSizeAlign(self, f.ty);
                        offset = std.mem.alignForward(u64, offset, sa.alignment);
                        if (sa.alignment > max_align) max_align = @intCast(sa.alignment);
                        if (i > 0) try elems_list.appendSlice(scratch, ", ");
                        try elems_list.appendSlice(scratch, try diDerived(self, "DW_TAG_member", self.context.type_store.strs.get(f.name), try ensureDIType(self, f.ty), sa.size * 8, sa.alignment * 8, offset * 8));
                        offset += sa.size;
                    }
                    offset = std.mem.alignForward(u64, offset, max_align);
                },
                .Tuple, .Complex => {
                    name = if (kind == .Complex) "complex" else "tuple";
                    const is_c = kind == .Complex;
                    const c_ty = if (is_c) self.context.type_store.get(.Complex, ty) else undefined;
                    const c_len = if (is_c) 2 else self.context.type_store.get(.Tuple, ty).elems.len;

                    for (0..c_len) |i| {
                        const et = if (is_c) c_ty.elem else self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, ty).elems)[i];
                        const sa = abi.abiSizeAlign(self, et);
                        offset = std.mem.alignForward(u64, offset, sa.alignment);
                        if (sa.alignment > max_align) max_align = @intCast(sa.alignment);
                        const fname = if (is_c) (if (i == 0) "re" else "im") else try std.fmt.allocPrint(scratch, "{d}", .{i});
                        if (i > 0) try elems_list.appendSlice(scratch, ", ");
                        try elems_list.appendSlice(scratch, try diDerived(self, "DW_TAG_member", fname, try ensureDIType(self, et), sa.size * 8, sa.alignment * 8, offset * 8));
                        offset += sa.size;
                    }
                    offset = std.mem.alignForward(u64, offset, max_align);
                },
                .Union, .Variant, .Error, .ErrorSet => {
                    name = if (kind == .Union) "union" else if (kind == .ErrorSet) "errorset" else if (kind == .Variant) "variant" else "error";
                    tag = if (kind == .Union) "DW_TAG_union_type" else "DW_TAG_structure_type";

                    // Tags for Tagged Unions
                    if (kind != .Union) {
                        try elems_list.appendSlice(scratch, try diDerived(self, "DW_TAG_member", "tag", diBasic(self, "i32", 32, .Signed), 32, 32, 0));
                        offset = 4; // tag size
                    }

                    const fields = if (kind == .ErrorSet) &[_]types.FieldId{} else if (kind == .Union) self.context.type_store.field_pool.slice(self.context.type_store.get(.Union, ty).fields) else if (kind == .Variant) self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, ty).variants) else self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, ty).variants);

                    var payload_align: u64 = if (kind == .Union) 1 else 4;
                    var max_size: u64 = 0;

                    if (kind == .ErrorSet) {
                        const es = self.context.type_store.get(.ErrorSet, ty);
                        const v_sa = abi.abiSizeAlign(self, es.value_ty);
                        const e_sa = abi.abiSizeAlign(self, es.error_ty);
                        payload_align = @max(v_sa.alignment, e_sa.alignment);
                        offset = std.mem.alignForward(u64, offset, payload_align);
                        try elems_list.appendSlice(scratch, ", ");
                        try elems_list.appendSlice(scratch, try diDerived(self, "DW_TAG_member", "Ok", try ensureDIType(self, es.value_ty), v_sa.size * 8, v_sa.alignment * 8, offset * 8));
                        try elems_list.appendSlice(scratch, ", ");
                        try elems_list.appendSlice(scratch, try diDerived(self, "DW_TAG_member", "Err", try ensureDIType(self, es.error_ty), e_sa.size * 8, e_sa.alignment * 8, offset * 8));
                        offset += @max(v_sa.size, e_sa.size);
                        max_align = payload_align;
                    } else {
                        for (fields) |fid| {
                            const sa = abi.abiSizeAlign(self, self.context.type_store.Field.get(fid).ty);
                            if (sa.alignment > payload_align) payload_align = @intCast(sa.alignment);
                            if (sa.size > max_size) max_size = sa.size;
                        }
                        if (kind != .Union) offset = std.mem.alignForward(u64, offset, payload_align);

                        for (fields) |fid| {
                            const f = self.context.type_store.Field.get(fid);
                            const sa = abi.abiSizeAlign(self, f.ty);
                            if (elems_list.items.len > 0) try elems_list.appendSlice(scratch, ", ");
                            try elems_list.appendSlice(scratch, try diDerived(self, "DW_TAG_member", self.context.type_store.strs.get(f.name), try ensureDIType(self, f.ty), sa.size * 8, sa.alignment * 8, offset * 8));
                        }
                        offset = if (kind == .Union) std.mem.alignForward(u64, max_size, payload_align) else std.mem.alignForward(u64, offset + max_size, payload_align);
                        max_align = payload_align;
                    }
                },
                .Closure => {
                    name = "closure";
                    const cl = self.context.type_store.get(.Closure, ty);
                    const fn_ptr_ty = self.context.type_store.mkPtr(cl.func, false);
                    const env_ptr_ty = self.context.type_store.mkPtr(cl.env, false);
                    const fields = [_]types.TypeId{ fn_ptr_ty, env_ptr_ty };
                    const field_names = [_][]const u8{ "fn", "env" };

                    for (fields, 0..) |fty, i| {
                        const sa = abi.abiSizeAlign(self, fty);
                        offset = std.mem.alignForward(u64, offset, sa.alignment);
                        if (sa.alignment > max_align) max_align = @intCast(sa.alignment);
                        if (i > 0) try elems_list.appendSlice(scratch, ", ");
                        try elems_list.appendSlice(scratch, try diDerived(self, "DW_TAG_member", field_names[i], try ensureDIType(self, fty), sa.size * 8, sa.alignment * 8, offset * 8));
                        offset += sa.size;
                    }
                    offset = std.mem.alignForward(u64, offset, max_align);
                },
                else => unreachable,
            }

            const res = try diComposite(self, tag, name, id_attr, try ensureDINullTypeAttr(self), offset * 8, max_align * 8, if (kind == .Map) "Declaration" else "", elems_list.items);
            _ = self.di_recursive_ids.remove(ty);
            break :blk res;
        },
        .Array => blk: {
            const arr = self.context.type_store.get(.Array, ty);
            const sa = abi.abiSizeAlign(self, ty);
            const elem_di = try ensureDIType(self, arr.elem);
            const elem_txt = try getAttrText(self, elem_di);
            const sub = try std.fmt.allocPrint(self.debug_arena.allocator(), "#llvm.di_subrange<count = {d}>", .{arr.len});
            const sub_attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(sub));
            const sub_txt = try getAttrText(self, sub_attr);

            const scratch = self.debug_arena.allocator();
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(try std.fmt.allocPrint(scratch, "arr_{d}", .{nextDistinctId(self)})));

            // Manual construction required because standard diComposite helper doesn't support 'baseType' field needed for arrays
            const id_txt = try getAttrText(self, id_attr);
            const txt = try std.fmt.allocPrint(scratch, "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_array_type, baseType = {s}, sizeInBits = {d}, alignInBits = {d}, elements = #llvm.di_node_array<[{s}]>>", .{ id_txt, elem_txt, sa.size * 8, sa.alignment * 8, sub_txt });
            break :blk mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(txt));
        },

        .Enum => blk: {
            const e = self.context.type_store.get(.Enum, ty);
            const tag_di = try ensureDIType(self, e.tag_type);
            const tag_txt = try getAttrText(self, tag_di);

            const scratch = self.debug_arena.allocator();
            var elems = std.ArrayListUnmanaged(u8){};
            for (self.context.type_store.enum_member_pool.slice(e.members), 0..) |mid, i| {
                const mem = self.context.type_store.EnumMember.get(mid);
                if (i > 0) try elems.appendSlice(scratch, ", ");
                try elems.appendSlice(scratch, try std.fmt.allocPrint(scratch, "#llvm.di_derived_type<tag = DW_TAG_enumerator, name = \"{s}\", value = {d}>", .{ self.context.type_store.strs.get(mem.name), mem.value }));
            }

            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(try std.fmt.allocPrint(scratch, "enum_{d}", .{nextDistinctId(self)})));
            const id_txt = try getAttrText(self, id_attr);
            const txt = try std.fmt.allocPrint(scratch, "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_enumeration_type, name = \"enum\", file = {s}, line = 0, baseType = {s}, sizeInBits = 64, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>", .{ id_txt, try getAttrText(self, try ensureDINullTypeAttr(self)), tag_txt, elems.items });
            break :blk mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(txt));
        },

        .Optional => blk: {
            if (self.context.type_store.isOptionalPointer(ty)) {
                break :blk try ensureDIType(self, self.context.type_store.get(.Optional, ty).elem);
            }
            const opt = self.context.type_store.get(.Optional, ty);
            const sa = abi.abiSizeAlign(self, ty);
            const elem_sa = abi.abiSizeAlign(self, opt.elem);

            const scratch = self.debug_arena.allocator();
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(try std.fmt.allocPrint(scratch, "opt_{d}", .{nextDistinctId(self)})));

            const m_pres = try diDerived(self, "DW_TAG_member", "present", diBasic(self, "bool", 8, .Boolean), 8, 8, 0);
            const val_off = std.mem.alignForward(u64, 1, elem_sa.alignment);
            const m_val = try diDerived(self, "DW_TAG_member", "val", try ensureDIType(self, opt.elem), elem_sa.size * 8, elem_sa.alignment * 8, val_off * 8);

            break :blk try diComposite(self, "DW_TAG_structure_type", "optional", id_attr, try ensureDINullTypeAttr(self), sa.size * 8, sa.alignment * 8, "", try std.fmt.allocPrint(scratch, "{s}, {s}", .{ m_pres, m_val }));
        },

        .Function => blk: {
            const f = self.context.type_store.get(.Function, ty);
            const scratch = self.debug_arena.allocator();
            var types_list = std.ArrayListUnmanaged(mlir.Attribute){};

            try types_list.append(self.gpa, try ensureDIType(self, f.result));
            for (self.context.type_store.type_pool.slice(f.params)) |p| try types_list.append(self.gpa, try ensureDIType(self, p));

            const sub = mlir.LLVMAttributes.getLLVMDISubroutineTypeAttr(self.mlir_ctx, 0, types_list.items);
            const sub_txt = try getAttrText(self, sub);
            const txt = try std.fmt.allocPrint(scratch, "#llvm.di_derived_type<tag = DW_TAG_pointer_type, baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>", .{sub_txt});
            break :blk mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(txt));
        },

        .Simd => blk: {
            const s = self.context.type_store.get(.Simd, ty);
            const scratch = self.debug_arena.allocator();
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(try std.fmt.allocPrint(scratch, "simd_{d}", .{nextDistinctId(self)})));
            const elem_di = try ensureDIType(self, s.elem);
            var elems = std.ArrayListUnmanaged(u8){};
            for (0..s.lanes) |i| {
                if (i > 0) try elems.appendSlice(scratch, ", ");
                try elems.appendSlice(scratch, try diDerived(self, "DW_TAG_member", try std.fmt.allocPrint(scratch, "{d}", .{i}), elem_di, 64, 64, i * 64));
            }
            break :blk try diComposite(self, "DW_TAG_structure_type", "simd", id_attr, try ensureDINullTypeAttr(self), s.lanes * 64, 64, "", elems.items);
        },

        // Map, Any, etc. fallback to simple stubs or handled above in composite generic
        .Map => blk: {
            const scratch = self.debug_arena.allocator();
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(try std.fmt.allocPrint(scratch, "map_{d}", .{nextDistinctId(self)})));
            break :blk try diComposite(self, "DW_TAG_structure_type", "map", id_attr, try ensureDINullTypeAttr(self), 64, 64, "Declaration", "");
        },

        .Any => blk: {
            const scratch = self.debug_arena.allocator();
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(try std.fmt.allocPrint(scratch, "any_{d}", .{nextDistinctId(self)})));
            const ptr_void = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from("#llvm.di_derived_type<tag = DW_TAG_pointer_type, baseType = null, sizeInBits = 64, alignInBits = 64, offset = 0>"));
            const m_ptr = try diDerived(self, "DW_TAG_member", "ptr", ptr_void, 64, 64, 0);
            const m_id = try diDerived(self, "DW_TAG_member", "type_id", diBasic(self, "u64", 64, .Unsigned), 64, 64, 64);
            break :blk try diComposite(self, "DW_TAG_structure_type", "any", id_attr, try ensureDINullTypeAttr(self), 128, 64, "", try std.fmt.allocPrint(scratch, "{s}, {s}", .{ m_ptr, m_id }));
        },
        .Tensor => blk: {
            // Treat Tensor as opaque struct of elements for now, similar to original but flattened
            const t = self.context.type_store.get(.Tensor, ty);
            var len: u64 = 1;
            for (t.dims) |d| len *= d;
            const scratch = self.debug_arena.allocator();
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(try std.fmt.allocPrint(scratch, "tensor_{d}", .{nextDistinctId(self)})));
            const elem_di = try ensureDIType(self, t.elem);
            var elems = std.ArrayListUnmanaged(u8){};
            for (0..len) |i| {
                if (i > 0) try elems.appendSlice(scratch, ", ");
                try elems.appendSlice(scratch, try diDerived(self, "DW_TAG_member", try std.fmt.allocPrint(scratch, "{d}", .{i}), elem_di, 64, 64, i * 64));
            }
            break :blk try diComposite(self, "DW_TAG_structure_type", "tensor", id_attr, try ensureDINullTypeAttr(self), len * 64, 64, "", elems.items);
        },
    };

    if (!attr.isNull()) try self.di_type_cache.put(ty, attr);
    return attr;
}

/// Construct the DI subroutine type attribute for a function given its return/param types.
fn buildDISubroutineTypeAttr(self: *Codegen, ret_ty: types.TypeId, params: []const tir.ParamId, t: *tir.TIR) !mlir.Attribute {
    var types_buf = std.ArrayListUnmanaged(mlir.Attribute){};
    defer types_buf.deinit(self.gpa);

    const null_attr = try ensureDINullTypeAttr(self);

    // Return type
    const ret_attr = ensureDIType(self, ret_ty) catch null_attr;
    try types_buf.append(self.gpa, if (ret_attr.isNull()) null_attr else ret_attr);

    // Parameter types
    for (params) |pid| {
        const param_attr = ensureDIType(self, t.funcs.Param.get(pid).ty) catch null_attr;
        try types_buf.append(self.gpa, if (param_attr.isNull()) null_attr else param_attr);
    }

    const attr = mlir.LLVMAttributes.getLLVMDISubroutineTypeAttr(self.mlir_ctx, 0, types_buf.items);
    if (attr.isNull()) return error.DebugAttrParseFailed;
    return attr;
}

/// Get (caching) an empty DI expression used for fixed locations.
fn ensureEmptyDIExpression(self: *Codegen) !mlir.Attribute {
    if (!self.di_empty_expr_attr.isNull()) return self.di_empty_expr_attr;
    const attr = mlir.LLVMAttributes.getLLVMDIExpressionAttr(self.mlir_ctx, &[_]mlir.Attribute{});
    if (attr.isNull()) return error.DebugAttrParseFailed;
    self.di_empty_expr_attr = attr;
    return attr;
}

/// Emit `llvm.dbg.value` intrinsics for each named parameter of `f_id`.
pub fn emitParameterDebugInfo(self: *Codegen, f_id: tir.FuncId, params: []const tir.ParamId, entry_block: mlir.Block, t: *tir.TIR) !void {
    if (!codegen.enable_debug_info) return;
    const subp = self.di_subprograms.getPtr(f_id) orelse return;

    // Fast check if any parameter is named
    var has_named = false;
    for (params) |pid| if (!t.funcs.Param.get(pid).name.isNone()) {
        has_named = true;
        break;
    };
    if (!has_named) return;

    const file_info = ensureDebugFile(self, subp.file_id) catch return;
    const expr_attr = ensureEmptyDIExpression(self) catch return;
    const null_attr = ensureDINullTypeAttr(self) catch return;

    defer self.loc = self.pushLocation(subp.loc);

    for (params, 0..) |pid, idx| {
        const p = t.funcs.Param.get(pid);
        if (p.name.isNone()) continue;

        var di_type = ensureDIType(self, p.ty) catch null_attr;
        if (di_type.isNull() or di_type.equal(&null_attr)) continue;

        const name = t.instrs.strs.get(p.name.unwrap());
        const var_attr = mlir.LLVMAttributes.getLLVMDILocalVariableAttr(self.mlir_ctx, subp.attr, self.strAttr(name), file_info.file_attr, subp.line, @intCast(idx + 1), 0, di_type, 0);
        if (var_attr.isNull()) continue;

        _ = self.appendOp("llvm.intr.dbg.value", .{
            .operands = &.{entry_block.getArgument(idx)},
            .attributes = &.{ self.named("varInfo", var_attr), self.named("locationExpr", expr_attr) },
        });
    }
}

/// Emit debug info for a local variable (either stack slot or SSA value).
pub fn emitLocalVariable(self: *Codegen, value: mlir.Value, val_id: tir.ValueId, t: *tir.TIR, name: []const u8, loc: tir.OptLocId) !void {
    if (!codegen.enable_debug_info or self.current_scope == null or loc.isNone()) return;

    const loc_rec = self.context.loc_store.get(loc.unwrap());
    const file_info = ensureDebugFile(self, loc_rec.file_id) catch return;
    const expr_attr = ensureEmptyDIExpression(self) catch return;

    const ty = self.val_types.get(val_id) orelse return;
    var di_type = ensureDIType(self, ty) catch ensureDINullTypeAttr(self) catch return;
    if (di_type.isNull()) di_type = ensureDINullTypeAttr(self) catch return;

    const var_attr = mlir.LLVMAttributes.getLLVMDILocalVariableAttr(self.mlir_ctx, self.current_scope.?, self.strAttr(name), file_info.file_attr, 0, 0, 0, di_type, 0);
    if (var_attr.isNull()) return;

    const is_alloca = if (self.def_instr.get(val_id)) |instr_id| t.kind(instr_id) == .Alloca else false;

    _ = self.appendOp(if (is_alloca) "llvm.intr.dbg.declare" else "llvm.intr.dbg.value", .{
        .operands = &.{value},
        .attributes = &.{ self.named("varInfo", var_attr), self.named("locationExpr", expr_attr) },
    });
}
