const codegen = @import("codegen_main.zig");
const Codegen = codegen.Codegen;
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const std = @import("std");

/// DWARF tag value for basic scalar types.
const DW_TAG_base_type: u32 = 0x24;
/// DWARF tag value used when describing pointer types.
const DW_TAG_pointer_type: u32 = 0x0f;
const DW_TAG_array_type: u32 = 0x01;
const DW_TAG_structure_type: u32 = 0x13;
const DW_TAG_member: u32 = 0x0d;
/// Pointer width assumed when emitting LLVM Debug info (64 bits for the target triple).
const POINTER_SIZE_BITS: u64 = 64;

/// Cache for the MLIR attributes describing a source file and its compile unit.
pub const DebugFileInfo = struct {
    /// `llvm.di.file` attribute that encodes basename/directory.
    file_attr: mlir.Attribute,
    /// Compile unit attribute referencing the file-level metadata.
    compile_unit_attr: mlir.Attribute,
};

/// Represents the DWARF metadata attached to a function definition.
pub const DebugSubprogramInfo = struct {
    /// `llvm.disubprogram` attribute describing the function signature/scope.
    attr: mlir.Attribute,
    /// Source file identifier for `attr`.
    file_id: u32,
    /// Line number where the function begins.
    line: u32,
    /// Line number where the lexical scope starts (usually same as `line`).
    scope_line: u32,
    /// Optional location ID for the prologue.
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
    _ = mod_op.removeDiscardableAttributeByName(mlir.StringRef.from("llvm.dbg.cu"));
    _ = mod_op.removeDiscardableAttributeByName(mlir.StringRef.from("llvm.module.flags"));
    _ = mod_op.removeDiscardableAttributeByName(mlir.StringRef.from("llvm.ident"));
}

/// Generate a new monotonic ID for naming debug metadata nodes.
fn nextDistinctId(self: *Codegen) usize {
    const id = self.next_di_id;
    self.next_di_id += 1;
    return id;
}

const MyPrintBuffer = struct {
    list: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    had_error: *bool,
};

fn myPrintCallback(str: mlir.c.MlirStringRef, user_data: ?*anyopaque) callconv(.c) void {
    const buf: *MyPrintBuffer = @ptrCast(@alignCast(user_data));
    const bytes = str.data[0..str.length];
    buf.list.appendSlice(buf.allocator, bytes) catch {
        buf.had_error.* = true;
    };
}

fn getAttrText(self: *Codegen, attr: mlir.Attribute) ![]const u8 {
    var buffer = std.ArrayListUnmanaged(u8){};
    const scratch = self.debug_arena.allocator();
    var had_error = false;
    var pb = MyPrintBuffer{ .list = &buffer, .allocator = scratch, .had_error = &had_error };
    attr.print(myPrintCallback, &pb);
    if (had_error) return error.DebugAttrParseFailed;
    return buffer.items;
}

/// Create or reuse the debug metadata entry that describes `file_id`'s source file.
fn ensureDebugFile(self: *Codegen, file_id: u32) !*DebugFileInfo {
    if (self.di_files.getPtr(file_id)) |info| return info;

    const path = self.context.source_manager.get(file_id) orelse "unknown";
    const base = std.fs.path.basename(path);
    const dir = std.fs.path.dirname(path) orelse ".";

    const base_attr = self.strAttr(base);
    const dir_attr = self.strAttr(dir);
    const file_attr = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, base_attr, dir_attr);
    if (file_attr.isNull()) return error.DebugAttrParseFailed;

    const cu_attr = try buildDICompileUnit(self, file_attr);
    try addCompileUnitToModule(self, cu_attr);

    try self.di_files.put(file_id, .{
        .file_attr = file_attr,
        .compile_unit_attr = cu_attr,
    });
    return self.di_files.getPtr(file_id).?;
}

/// Serialize a `llvm.di.compile_unit` attribute for the given file.
fn buildDICompileUnit(self: *Codegen, file_attr: mlir.Attribute) !mlir.Attribute {
    const producer_attr = self.strAttr("sr-lang");
    const scratch = self.debug_arena.allocator();
    const id_payload = try std.fmt.allocPrint(scratch, "cu_{d}", .{nextDistinctId(self)});
    const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

    const file_text = try getAttrText(self, file_attr);
    const producer_text = try getAttrText(self, producer_attr);
    const id_text = try getAttrText(self, id_attr);

    const cu_text = try std.fmt.allocPrint(
        scratch,
        "#llvm.di_compile_unit<id = {s}, sourceLanguage = DW_LANG_C11, file = {s}, producer = {s}, isOptimized = false, emissionKind = Full>",
        .{ id_text, file_text, producer_text },
    );

    const cu_attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(cu_text));
    if (cu_attr.isNull()) return error.DebugAttrParseFailed;
    return cu_attr;
}

/// Attach `cu_attr` to the module-level debug `llvm.dbg.cu` attribute list, avoiding duplicates.
fn addCompileUnitToModule(self: *Codegen, cu_attr: mlir.Attribute) !void {
    var mod_op = self.module.getOperation();
    const dbg_name = mlir.StringRef.from("llvm.dbg.cu");
    const existing = mod_op.getDiscardableAttributeByName(dbg_name);
    if (existing.isNull()) {
        const array_attr = mlir.Attribute.arrayAttrGet(self.mlir_ctx, &.{cu_attr});
        mod_op.setDiscardableAttributeByName(dbg_name, array_attr);
        return;
    }

    const count = existing.arrayAttrGetNumElements();
    var already_present = false;
    var elements: std.ArrayList(mlir.Attribute) = .empty;
    defer elements.deinit(self.gpa);
    var idx: usize = 0;
    while (idx < count) : (idx += 1) {
        const elem = existing.arrayAttrGetElement(idx);
        if (!already_present and elem.equal(&cu_attr)) {
            already_present = true;
        }
        try elements.append(self.gpa, elem);
    }

    if (!already_present) {
        try elements.append(self.gpa, cu_attr);
        const array_attr = mlir.Attribute.arrayAttrGet(self.mlir_ctx, elements.items);
        mod_op.setDiscardableAttributeByName(dbg_name, array_attr);
    }
}

/// Build the `llvm.disubprogram` attribute for `f_id` and cache it for reused emissions.
/// `loc` represents the initial location, and `params` describe the signature in `t`.
pub fn ensureDebugSubprogram(
    self: *Codegen,
    f_id: tir.FuncId,
    func_name: []const u8,
    line: u32,
    file_id: u32,
    loc: tir.OptLocId,
    ret_ty: types.TypeId,
    params: []const tir.ParamId,
    t: *tir.TIR,
) !*DebugSubprogramInfo {
    if (self.di_subprograms.getPtr(f_id)) |info| return info;

    const file_info = try ensureDebugFile(self, file_id);
    const func_name_attr = self.strAttr(func_name);
    const linkage_name_attr = func_name_attr;
    const scratch = self.debug_arena.allocator();
    const id_payload = try std.fmt.allocPrint(scratch, "sp_{d}", .{nextDistinctId(self)});
    const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

    const flags_definition: u64 = 1 << 3; // DISPFlagDefinition
    const type_attr = try buildDISubroutineTypeAttr(self, ret_ty, params, t);
    const rec_attr = mlir.Attribute.distinctAttrCreate(mlir.Attribute.unitAttrGet(self.mlir_ctx));

    const attr = mlir.LLVMAttributes.getLLVMDISubprogramAttr(
        self.mlir_ctx,
        rec_attr,
        false,
        id_attr,
        file_info.compile_unit_attr,
        file_info.file_attr,
        func_name_attr,
        linkage_name_attr,
        file_info.file_attr,
        line,
        line,
        flags_definition,
        type_attr,
        &[_]mlir.Attribute{},
        &[_]mlir.Attribute{},
    );
    if (attr.isNull()) return error.DebugAttrParseFailed;

    try self.di_subprograms.put(f_id, .{
        .attr = attr,
        .file_id = file_id,
        .line = line,
        .scope_line = line,
        .loc = loc,
    });
    return self.di_subprograms.getPtr(f_id).?;
}

/// Set the LLVM target triple/data layout attributes emitted via MLIR.
pub fn attachTargetInfo(self: *Codegen) !void {
    const triple = self.strAttr("x86_64-unknown-linux-gnu");
    const dl = self.strAttr("e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128");
    var mod_op = self.module.getOperation();
    mod_op.setDiscardableAttributeByName(mlir.StringRef.from("llvm.target_triple"), triple);
    mod_op.setDiscardableAttributeByName(mlir.StringRef.from("llvm.data_layout"), dl);
}

const KEY_DEBUG_INFO_VERSION = ", \"Debug Info Version\",";
const KEY_DWARF_VERSION = ", \"Dwarf Version\",";

/// Format a module-flag attribute for the given `behavior`, `key`, and `value_repr`.
fn moduleFlagAttr(self: *Codegen, behavior: []const u8, key: []const u8, value_repr: []const u8) !mlir.Attribute {
    const scratch = self.debug_arena.allocator();
    const text = try std.fmt.allocPrint(
        scratch,
        "#llvm.mlir.module_flag<{s}, \"{s}\", {s}>",
        .{ behavior, key, value_repr },
    );
    const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(text));
    if (attr.isNull()) return error.DebugAttrParseFailed;
    return attr;
}

/// Check whether `attr` already encodes a module flag with the given `key`.
fn moduleFlagMatchesKey(self: *Codegen, attr: mlir.Attribute, key: []const u8) !bool {
    const scratch = self.debug_arena.allocator();
    const text = try getAttrText(self, attr);
    const needle = try std.fmt.allocPrint(scratch, ", \"{s}\",", .{key});
    return std.mem.indexOf(u8, text, needle) != null;
}
fn moduleFlagHasKey(self: *Codegen, attr: mlir.Attribute, needle: []const u8) !bool {
    const text = try getAttrText(self, attr);
    return std.mem.indexOf(u8, text, needle) != null;
}

/// Append a new module flag entry; caller ensures key is missing already.
fn appendModuleFlag(
    self: *Codegen,
    flags: *std.ArrayList(mlir.Attribute),
    behavior: []const u8,
    key: []const u8,
    value_repr: []const u8,
) !void {
    const attr = try moduleFlagAttr(self, behavior, key, value_repr);
    try flags.append(self.gpa, attr);
}

/// Configure module-level debug attributes (flags, identifiers) once per module.
pub fn ensureDebugModuleAttrs(self: *Codegen) !void {
    if (!codegen.enable_debug_info) return;
    if (self.debug_module_attrs_initialized) return;

    var mod_op = self.module.getOperation();
    const flags_name = mlir.StringRef.from("llvm.module.flags");
    const existing_flags = mod_op.getDiscardableAttributeByName(flags_name);

    var flags: std.ArrayList(mlir.Attribute) = .empty;
    defer flags.deinit(self.gpa);
    var has_debug_info = false;
    var has_dwarf = false;
    if (!existing_flags.isNull()) {
        const count = existing_flags.arrayAttrGetNumElements();
        var idx: usize = 0;
        while (idx < count) : (idx += 1) {
            const elem = existing_flags.arrayAttrGetElement(idx);
            try flags.append(self.gpa, elem);
            if (!has_debug_info) has_debug_info = try moduleFlagHasKey(self, elem, KEY_DEBUG_INFO_VERSION);
            if (!has_dwarf) has_dwarf = try moduleFlagHasKey(self, elem, KEY_DWARF_VERSION);
        }
    }

    if (!has_debug_info) {
        try appendModuleFlag(self, &flags, "warning", "Debug Info Version", "3 : i32");
    }
    if (!has_dwarf) {
        try appendModuleFlag(self, &flags, "max", "Dwarf Version", "5 : i32");
    }

    if (flags.items.len > 0) {
        const array_attr = mlir.Attribute.arrayAttrGet(self.mlir_ctx, flags.items);
        mod_op.setDiscardableAttributeByName(flags_name, array_attr);
    }

    const ident_name = mlir.StringRef.from("llvm.ident");
    if (mod_op.getDiscardableAttributeByName(ident_name).isNull()) {
        const ident_attr = self.strAttr("sr-lang compiler");
        const ident_array = mlir.Attribute.arrayAttrGet(self.mlir_ctx, &.{ident_attr});
        mod_op.setDiscardableAttributeByName(ident_name, ident_array);
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
fn ensureDIType(self: *Codegen, ty: types.TypeId) !mlir.Attribute {
    if (self.di_type_cache.get(ty)) |cached| return cached;

    const kind = self.context.type_store.getKind(ty);
    const attr: mlir.Attribute = switch (kind) {
        // .Void => return mlir.Attribute.getNull(),
        .Bool => mlir.LLVMAttributes.getLLVMDIBasicTypeAttr(
            self.mlir_ctx,
            DW_TAG_base_type,
            self.strAttr("bool"),
            1,
            mlir.LLVMTypeEncoding.Boolean,
        ),
        .I8 => diSignedIntType(self, "i8", 8),
        .I16 => diSignedIntType(self, "i16", 16),
        .I32 => diSignedIntType(self, "i32", 32),
        .I64 => diSignedIntType(self, "i64", 64),
        .U8 => diUnsignedIntType(self, "u8", 8),
        .U16 => diUnsignedIntType(self, "u16", 16),
        .U32 => diUnsignedIntType(self, "u32", 32),
        .U64 => diUnsignedIntType(self, "u64", 64),
        .Usize => diUnsignedIntType(self, "usize", POINTER_SIZE_BITS),
        .F32 => mlir.LLVMAttributes.getLLVMDIBasicTypeAttr(
            self.mlir_ctx,
            DW_TAG_base_type,
            self.strAttr("f32"),
            32,
            mlir.LLVMTypeEncoding.FloatT,
        ),
        .F64 => mlir.LLVMAttributes.getLLVMDIBasicTypeAttr(
            self.mlir_ctx,
            DW_TAG_base_type,
            self.strAttr("f64"),
            64,
            mlir.LLVMTypeEncoding.FloatT,
        ),
        .Void, .Noreturn => try ensureDINullTypeAttr(self),
                .Ptr => blk: {
                    const ptr = self.context.type_store.get(.Ptr, ty);
                    var base_attr = ensureDIType(self, ptr.elem) catch try ensureDINullTypeAttr(self);
                    if (base_attr.isNull()) base_attr = try ensureDINullTypeAttr(self);
                    
                    const base_text = try getAttrText(self, base_attr);
                    const scratch = self.debug_arena.allocator();
        
                    const attr_text = try std.fmt.allocPrint(scratch,
                        "#llvm.di_derived_type<tag = DW_TAG_pointer_type, baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                        .{base_text}
                    );
        
                    const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
                    if (attr.isNull()) return error.DebugAttrParseFailed;
                    break :blk attr;
                },
                .Slice => blk: {
                    const slice = self.context.type_store.get(.Slice, ty);
                    const scratch = self.debug_arena.allocator();
                    const id_payload = try std.fmt.allocPrint(scratch, "slice_{d}", .{nextDistinctId(self)});
                    const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));
        
                    // Element type
                    var elem_attr = ensureDIType(self, slice.elem) catch try ensureDINullTypeAttr(self);
                    if (elem_attr.isNull()) elem_attr = try ensureDINullTypeAttr(self);
                    const elem_text = try getAttrText(self, elem_attr);
        
                    // Pointer to Element Type
                    const ptr_to_elem_text = try std.fmt.allocPrint(scratch,
                        "#llvm.di_derived_type<tag = DW_TAG_pointer_type, baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                        .{elem_text}
                    );
                    const ptr_type = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(ptr_to_elem_text));
        
                    // ptr member
                    const ptr_type_text = try getAttrText(self, ptr_type);
                    const ptr_member_text = try std.fmt.allocPrint(scratch,
                        "#llvm.di_derived_type<tag = DW_TAG_member, name = \"ptr\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                        .{ptr_type_text}
                    );
        
                    // len type (i64)
                    const len_type = diSignedIntType(self, "i64", 64);
                    const len_type_text = try getAttrText(self, len_type);
        
                    // len member
                    const len_member_text = try std.fmt.allocPrint(scratch,
                        "#llvm.di_derived_type<tag = DW_TAG_member, name = \"len\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 64>",
                        .{len_type_text}
                    );
        
                    // Elements array
                    const elements_text = try std.fmt.allocPrint(scratch, "{s}, {s}", .{ptr_member_text, len_member_text});
                    
                    const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
                    const file_text = try getAttrText(self, unknown_file);
                    const id_text = try getAttrText(self, id_attr);
        
                    const attr_text = try std.fmt.allocPrint(scratch,
                        "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"[]\", file = {s}, line = 0, sizeInBits = 128, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                        .{ id_text, file_text, elements_text }
                    );
        
                    const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
                    if (attr.isNull()) return error.DebugAttrParseFailed;
                    break :blk attr;
                },
                .Struct => blk: {
                    if (self.di_recursive_ids.get(ty)) |recId| {
                        break :blk mlir.LLVMAttributes.getLLVMDICompositeTypeAttrRecSelf(recId);
                    }
        
                    const scratch = self.debug_arena.allocator();
                    const id_payload = try std.fmt.allocPrint(scratch, "struct_{d}", .{nextDistinctId(self)});
                    const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));
                    try self.di_recursive_ids.put(ty, id_attr);
        
                    const s = self.context.type_store.get(.Struct, ty);
                    const fields = self.context.type_store.field_pool.slice(s.fields);
        
                    var elements_text = std.ArrayListUnmanaged(u8){};
        
                    var offset: u64 = 0;
                    for (fields, 0..) |fid, i| {
                        const f = self.context.type_store.Field.get(fid);
                        const field_name = self.context.type_store.strs.get(f.name);
        
                        var field_ty_attr = ensureDIType(self, f.ty) catch try ensureDINullTypeAttr(self);
                        if (field_ty_attr.isNull()) field_ty_attr = try ensureDINullTypeAttr(self);
        
                        const field_ty_text = try getAttrText(self, field_ty_attr);
        
                        const member_text = try std.fmt.allocPrint(scratch,
                            "#llvm.di_derived_type<tag = DW_TAG_member, name = \"{s}\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = {d}>",
                            .{field_name, field_ty_text, offset}
                        );
        
                        if (i > 0) try elements_text.appendSlice(scratch, ", ");
                        try elements_text.appendSlice(scratch, member_text);
        
                        offset += 64;
                    }
        
                    const id_text = try getAttrText(self, id_attr);
        
                    const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
                    const file_text = try getAttrText(self, unknown_file);
        
                    const attr_text = try std.fmt.allocPrint(scratch,
                        "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"struct\", file = {s}, line = 0, sizeInBits = {d}, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                        .{ id_text, file_text, offset, elements_text.items }
                    );
        
                    const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
                    _ = self.di_recursive_ids.remove(ty);
                    
                    if (attr.isNull()) return error.DebugAttrParseFailed;
                    break :blk attr;
                },
        .Tuple => blk: {
            const tuple = self.context.type_store.get(.Tuple, ty);
            const elems = self.context.type_store.type_pool.slice(tuple.elems);

            const scratch = self.debug_arena.allocator();
            const id_payload = try std.fmt.allocPrint(scratch, "tuple_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

            if (self.di_recursive_ids.get(ty)) |recId| {
                break :blk mlir.LLVMAttributes.getLLVMDICompositeTypeAttrRecSelf(recId);
            }
            try self.di_recursive_ids.put(ty, id_attr);

            var elements_text = std.ArrayListUnmanaged(u8){};
            // arena allocation, no deinit needed

            var offset: u64 = 0;

            for (elems, 0..) |elem_ty, i| {
                var elem_attr = ensureDIType(self, elem_ty) catch try ensureDINullTypeAttr(self);
                if (elem_attr.isNull()) elem_attr = try ensureDINullTypeAttr(self);

                const field_name = try std.fmt.allocPrint(scratch, "{d}", .{i});

                const elem_text = try getAttrText(self, elem_attr);
                const member_text = try std.fmt.allocPrint(scratch,
                    "#llvm.di_derived_type<tag = DW_TAG_member, name = \"{s}\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = {d}>",
                    .{field_name, elem_text, offset}
                );

                if (i > 0) try elements_text.appendSlice(scratch, ", ");
                try elements_text.appendSlice(scratch, member_text);
                offset += 64;
            }

            const id_text = try getAttrText(self, id_attr);

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"tuple\", file = {s}, line = 0, sizeInBits = {d}, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, offset, elements_text.items }
            );

            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            _ = self.di_recursive_ids.remove(ty);

            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .Array => blk: {
            const arr = self.context.type_store.get(.Array, ty);
            const len = arr.len;

            const scratch = self.debug_arena.allocator();
            var elements_text = std.ArrayListUnmanaged(u8){};
            var offset: u64 = 0;

            var elem_attr = ensureDIType(self, arr.elem) catch try ensureDINullTypeAttr(self);
            if (elem_attr.isNull()) elem_attr = try ensureDINullTypeAttr(self);
            const elem_text = try getAttrText(self, elem_attr);

            var i: usize = 0;
            while (i < len) : (i += 1) {
                const member_text = try std.fmt.allocPrint(scratch,
                    "#llvm.di_derived_type<tag = DW_TAG_member, name = \"{d}\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = {d}>",
                    .{i, elem_text, offset}
                );

                if (i > 0) try elements_text.appendSlice(scratch, ", ");
                try elements_text.appendSlice(scratch, member_text);
                offset += 64;
            }

            const id_payload = try std.fmt.allocPrint(scratch, "array_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));
            const id_text = try getAttrText(self, id_attr);

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"array\", file = {s}, line = 0, sizeInBits = {d}, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, offset, elements_text.items }
            );

            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
                .Enum => blk: {
                    const e = self.context.type_store.get(.Enum, ty);
                    const members = self.context.type_store.enum_member_pool.slice(e.members);
                    
                    var tag_attr = ensureDIType(self, e.tag_type) catch try ensureDINullTypeAttr(self);
                    if (tag_attr.isNull()) tag_attr = try ensureDINullTypeAttr(self);
                    const tag_text = try getAttrText(self, tag_attr);
        
                    const scratch = self.debug_arena.allocator();
                    var elements_text = std.ArrayListUnmanaged(u8){};
        
                    for (members, 0..) |mid, i| {
                        const member = self.context.type_store.EnumMember.get(mid);
                        const name = self.context.type_store.strs.get(member.name);
                        const val = member.value;
        
                        const enumerator_text = try std.fmt.allocPrint(scratch,
                             "#llvm.di_derived_type<tag = DW_TAG_enumerator, name = \"{s}\", value = {d}>",
                             .{name, val}
                        );
        
                        if (i > 0) try elements_text.appendSlice(scratch, ", ");
                        try elements_text.appendSlice(scratch, enumerator_text);
                    }
        
                    const id_payload = try std.fmt.allocPrint(scratch, "enum_{d}", .{nextDistinctId(self)});
                    const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));
                    const id_text = try getAttrText(self, id_attr);
        
                    const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
                    const file_text = try getAttrText(self, unknown_file);
        
                    const attr_text = try std.fmt.allocPrint(scratch,
                        "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_enumeration_type, name = \"enum\", file = {s}, line = 0, baseType = {s}, sizeInBits = 64, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                        .{ id_text, file_text, tag_text, elements_text.items }
                    );
        
                    const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
                    if (attr.isNull()) return error.DebugAttrParseFailed;
                    break :blk attr;
                },
                .Union => blk: {
                    if (self.di_recursive_ids.get(ty)) |recId| {
                        break :blk mlir.LLVMAttributes.getLLVMDICompositeTypeAttrRecSelf(recId);
                    }
        
                    const scratch = self.debug_arena.allocator();
                    const id_payload = try std.fmt.allocPrint(scratch, "union_{d}", .{nextDistinctId(self)});
                    const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));
                    try self.di_recursive_ids.put(ty, id_attr);
        
                    const u = self.context.type_store.get(.Union, ty);
                    const fields = self.context.type_store.field_pool.slice(u.fields);
        
                    var elements_text = std.ArrayListUnmanaged(u8){};
        
                    for (fields, 0..) |fid, i| {
                        const f = self.context.type_store.Field.get(fid);
                        const field_name = self.context.type_store.strs.get(f.name);
        
                        var field_ty_attr = ensureDIType(self, f.ty) catch try ensureDINullTypeAttr(self);
                        if (field_ty_attr.isNull()) field_ty_attr = try ensureDINullTypeAttr(self);
        
                        const field_ty_text = try getAttrText(self, field_ty_attr);
        
                        // Union members usually share offset 0
                        const member_text = try std.fmt.allocPrint(scratch,
                            "#llvm.di_derived_type<tag = DW_TAG_member, name = \"{s}\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                            .{field_name, field_ty_text}
                        );
        
                        if (i > 0) try elements_text.appendSlice(scratch, ", ");
                        try elements_text.appendSlice(scratch, member_text);
                    }
        
                    const id_text = try getAttrText(self, id_attr);
        
                    const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
                    const file_text = try getAttrText(self, unknown_file);
        
                    const attr_text = try std.fmt.allocPrint(scratch,
                        "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_union_type, name = \"union\", file = {s}, line = 0, sizeInBits = 64, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                        .{ id_text, file_text, elements_text.items }
                    );
        
                    const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
                    _ = self.di_recursive_ids.remove(ty);
        
                    if (attr.isNull()) return error.DebugAttrParseFailed;
                    break :blk attr;
                },
        .String => blk: {
            const scratch = self.debug_arena.allocator();
            const id_payload = try std.fmt.allocPrint(scratch, "string_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

            // u8 type
            const u8_type = diUnsignedIntType(self, "u8", 8);
            const u8_text = try getAttrText(self, u8_type);

            // Pointer to u8
            const ptr_to_u8_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_pointer_type, baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{u8_text}
            );
            const ptr_type = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(ptr_to_u8_text));
            const ptr_type_text = try getAttrText(self, ptr_type);

            // ptr member
            const ptr_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"ptr\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{ptr_type_text}
            );

            // len type (i64)
            const len_type = diSignedIntType(self, "i64", 64);
            const len_type_text = try getAttrText(self, len_type);

            // len member
            const len_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"len\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 64>",
                .{len_type_text}
            );

            const elements_text = try std.fmt.allocPrint(scratch, "{s}, {s}", .{ptr_member_text, len_member_text});

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);
            const id_text = try getAttrText(self, id_attr);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"string\", file = {s}, line = 0, sizeInBits = 128, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, elements_text }
            );

            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .Optional => blk: {
            const opt = self.context.type_store.get(.Optional, ty);
            
            // Check if it's an optional pointer (optimization)
            if (self.context.type_store.isOptionalPointer(ty)) {
                // Just emit the pointer debug info
                var ptr_attr = ensureDIType(self, opt.elem) catch try ensureDINullTypeAttr(self);
                if (ptr_attr.isNull()) ptr_attr = try ensureDINullTypeAttr(self);
                break :blk ptr_attr;
            }

            const scratch = self.debug_arena.allocator();
            const id_payload = try std.fmt.allocPrint(scratch, "optional_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

            // Element type
            var elem_attr = ensureDIType(self, opt.elem) catch try ensureDINullTypeAttr(self);
            if (elem_attr.isNull()) elem_attr = try ensureDINullTypeAttr(self);
            const elem_text = try getAttrText(self, elem_attr);

            // val member
            const val_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"val\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{elem_text}
            );

            // bool type
            const bool_type = mlir.LLVMAttributes.getLLVMDIBasicTypeAttr(
                self.mlir_ctx,
                DW_TAG_base_type,
                self.strAttr("bool"),
                1,
                mlir.LLVMTypeEncoding.Boolean,
            );
            const bool_text = try getAttrText(self, bool_type);

            // present member
            const present_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"present\", baseType = {s}, sizeInBits = 8, alignInBits = 8, offset = 64>",
                .{bool_text}
            );

            const elements_text = try std.fmt.allocPrint(scratch, "{s}, {s}", .{val_member_text, present_member_text});

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);
            const id_text = try getAttrText(self, id_attr);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"optional\", file = {s}, line = 0, sizeInBits = 128, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, elements_text }
            );

            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .Complex => blk: {
            const cplx = self.context.type_store.get(.Complex, ty);
            
            const scratch = self.debug_arena.allocator();
            const id_payload = try std.fmt.allocPrint(scratch, "complex_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

            var elem_attr = ensureDIType(self, cplx.elem) catch try ensureDINullTypeAttr(self);
            if (elem_attr.isNull()) elem_attr = try ensureDINullTypeAttr(self);
            const elem_text = try getAttrText(self, elem_attr);

            // re member
            const re_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"re\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{elem_text}
            );

            // im member
            const im_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"im\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 64>",
                .{elem_text}
            );

            const elements_text = try std.fmt.allocPrint(scratch, "{s}, {s}", .{re_member_text, im_member_text});

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);
            const id_text = try getAttrText(self, id_attr);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"complex\", file = {s}, line = 0, sizeInBits = 128, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, elements_text }
            );

            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .DynArray => blk: {
            const da = self.context.type_store.get(.DynArray, ty);
            const scratch = self.debug_arena.allocator();
            const id_payload = try std.fmt.allocPrint(scratch, "dynarray_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

            // Element type
            var elem_attr = ensureDIType(self, da.elem) catch try ensureDINullTypeAttr(self);
            if (elem_attr.isNull()) elem_attr = try ensureDINullTypeAttr(self);
            const elem_text = try getAttrText(self, elem_attr);

            // Pointer to Element Type
            const ptr_to_elem_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_pointer_type, baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{elem_text}
            );
            const ptr_type = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(ptr_to_elem_text));

            // ptr member
            const ptr_type_text = try getAttrText(self, ptr_type);
            const ptr_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"ptr\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{ptr_type_text}
            );

            // i64 type
            const i64_type = diSignedIntType(self, "i64", 64);
            const i64_type_text = try getAttrText(self, i64_type);

            // len member
            const len_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"len\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 64>",
                .{i64_type_text}
            );

            // cap member
            const cap_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"cap\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 128>",
                .{i64_type_text}
            );

            // Elements array
            const elements_text = try std.fmt.allocPrint(scratch, "{s}, {s}, {s}", .{ptr_member_text, len_member_text, cap_member_text});
            
            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);
            const id_text = try getAttrText(self, id_attr);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"dyn[]\", file = {s}, line = 0, sizeInBits = 192, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, elements_text }
            );

            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .Simd => blk: {
            const simd = self.context.type_store.get(.Simd, ty);
            const len = simd.lanes;
            
            const scratch = self.debug_arena.allocator();
            var elements_text = std.ArrayListUnmanaged(u8){};
            var offset: u64 = 0;

            var elem_attr = ensureDIType(self, simd.elem) catch try ensureDINullTypeAttr(self);
            if (elem_attr.isNull()) elem_attr = try ensureDINullTypeAttr(self);
            const elem_text = try getAttrText(self, elem_attr);

            var i: usize = 0;
            while (i < len) : (i += 1) {
                const member_text = try std.fmt.allocPrint(scratch,
                    "#llvm.di_derived_type<tag = DW_TAG_member, name = \"{d}\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = {d}>",
                    .{i, elem_text, offset}
                );
                if (i > 0) try elements_text.appendSlice(scratch, ", ");
                try elements_text.appendSlice(scratch, member_text);
                offset += 64;
            }

            const id_payload = try std.fmt.allocPrint(scratch, "simd_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));
            const id_text = try getAttrText(self, id_attr);

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"simd\", file = {s}, line = 0, sizeInBits = {d}, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, offset, elements_text.items }
            );
            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .Tensor => blk: {
            const tensor = self.context.type_store.get(.Tensor, ty);
            var len: usize = 1;
            for (tensor.dims) |d| {
                if (d > 0) len *= d;
            }
            if (tensor.dims.len == 0) len = 0;

            const scratch = self.debug_arena.allocator();
            var elements_text = std.ArrayListUnmanaged(u8){};
            var offset: u64 = 0;

            var elem_attr = ensureDIType(self, tensor.elem) catch try ensureDINullTypeAttr(self);
            if (elem_attr.isNull()) elem_attr = try ensureDINullTypeAttr(self);
            const elem_text = try getAttrText(self, elem_attr);

            var i: usize = 0;
            while (i < len) : (i += 1) {
                const member_text = try std.fmt.allocPrint(scratch,
                    "#llvm.di_derived_type<tag = DW_TAG_member, name = \"{d}\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = {d}>",
                    .{i, elem_text, offset}
                );
                if (i > 0) try elements_text.appendSlice(scratch, ", ");
                try elements_text.appendSlice(scratch, member_text);
                offset += 64;
            }

            const id_payload = try std.fmt.allocPrint(scratch, "tensor_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));
            const id_text = try getAttrText(self, id_attr);

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"tensor\", file = {s}, line = 0, sizeInBits = {d}, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, offset, elements_text.items }
            );
            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .Any => blk: {
            const scratch = self.debug_arena.allocator();
            const id_payload = try std.fmt.allocPrint(scratch, "any_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

            // ptr member
            const ptr_to_void_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_pointer_type, baseType = null, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{}
            );
            const ptr_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"ptr\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{ptr_to_void_text}
            );

            // type_id member (u64)
            const u64_type = diUnsignedIntType(self, "u64", 64);
            const u64_text = try getAttrText(self, u64_type);
            const id_member_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"type_id\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 64>",
                .{u64_text}
            );

            const elements_text = try std.fmt.allocPrint(scratch, "{s}, {s}", .{ptr_member_text, id_member_text});

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);
            const id_text = try getAttrText(self, id_attr);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"any\", file = {s}, line = 0, sizeInBits = 128, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, elements_text }
            );

            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .Map => blk: {
             // Placeholder for map: opaque struct
            const scratch = self.debug_arena.allocator();
            const id_payload = try std.fmt.allocPrint(scratch, "map_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));
            const id_text = try getAttrText(self, id_attr);

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);

             const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_structure_type, name = \"map\", file = {s}, line = 0, sizeInBits = 64, alignInBits = 64, flags = Declaration>",
                .{ id_text, file_text }
            );
            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .Variant, .Error => blk: {
            // Same as Union
            if (self.di_recursive_ids.get(ty)) |recId| {
                break :blk mlir.LLVMAttributes.getLLVMDICompositeTypeAttrRecSelf(recId);
            }

            const scratch = self.debug_arena.allocator();
            const id_payload = try std.fmt.allocPrint(scratch, "variant_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));
            try self.di_recursive_ids.put(ty, id_attr);

            var fields: []const types.FieldId = &.{};
            if (kind == .Variant) {
                fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, ty).variants);
            } else {
                fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, ty).variants);
            }

            var elements_text = std.ArrayListUnmanaged(u8){};

            for (fields, 0..) |fid, i| {
                const f = self.context.type_store.Field.get(fid);
                const field_name = self.context.type_store.strs.get(f.name);

                var field_ty_attr = ensureDIType(self, f.ty) catch try ensureDINullTypeAttr(self);
                if (field_ty_attr.isNull()) field_ty_attr = try ensureDINullTypeAttr(self);

                const field_ty_text = try getAttrText(self, field_ty_attr);

                const member_text = try std.fmt.allocPrint(scratch,
                    "#llvm.di_derived_type<tag = DW_TAG_member, name = \"{s}\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                    .{field_name, field_ty_text}
                );

                if (i > 0) try elements_text.appendSlice(scratch, ", ");
                try elements_text.appendSlice(scratch, member_text);
            }

            const id_text = try getAttrText(self, id_attr);

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_union_type, name = \"variant\", file = {s}, line = 0, sizeInBits = 64, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, elements_text.items }
            );

            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            _ = self.di_recursive_ids.remove(ty);

            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .ErrorSet => blk: {
             // Treat as Error (union)
             // Or just struct { value: V, error: E } ?
             // ErrorSet is usually `!T` -> union { value: T, error: E } (conceptually)
             // Implementation detail: it's a union.
            const es = self.context.type_store.get(.ErrorSet, ty);
            const scratch = self.debug_arena.allocator();
            
            const id_payload = try std.fmt.allocPrint(scratch, "errorset_{d}", .{nextDistinctId(self)});
            const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

            // value type
            var val_attr = ensureDIType(self, es.value_ty) catch try ensureDINullTypeAttr(self);
            if (val_attr.isNull()) val_attr = try ensureDINullTypeAttr(self);
            const val_text = try getAttrText(self, val_attr);

            const val_member = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"value\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{val_text}
            );

            // error type
            var err_attr = ensureDIType(self, es.error_ty) catch try ensureDINullTypeAttr(self);
            if (err_attr.isNull()) err_attr = try ensureDINullTypeAttr(self);
            const err_text = try getAttrText(self, err_attr);

            const err_member = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_member, name = \"error\", baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{err_text}
            );

            const elements_text = try std.fmt.allocPrint(scratch, "{s}, {s}", .{val_member, err_member});

            const unknown_file = mlir.LLVMAttributes.getLLVMDIFileAttr(self.mlir_ctx, self.strAttr("<unknown>"), self.strAttr("."));
            const file_text = try getAttrText(self, unknown_file);
            const id_text = try getAttrText(self, id_attr);

            const attr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_composite_type<recId = {s}, tag = DW_TAG_union_type, name = \"errorset\", file = {s}, line = 0, sizeInBits = 64, alignInBits = 64, elements = #llvm.di_node_array<[{s}]>>",
                .{ id_text, file_text, elements_text }
            );
            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(attr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        .Function => blk: {
            const finfo = self.context.type_store.get(.Function, ty);
            
            // Create the subroutine type
            var types_buf = std.ArrayListUnmanaged(mlir.Attribute){};
            defer types_buf.deinit(self.gpa);

            var ret_attr = ensureDIType(self, finfo.result) catch blk_ret: {
                break :blk_ret try ensureDINullTypeAttr(self);
            };
            if (ret_attr.isNull()) ret_attr = try ensureDINullTypeAttr(self);
            try types_buf.append(self.gpa, ret_attr);

            const params = self.context.type_store.type_pool.slice(finfo.params);
            for (params) |param_ty| {
                var param_attr = ensureDIType(self, param_ty) catch try ensureDINullTypeAttr(self);
                if (param_attr.isNull()) param_attr = try ensureDINullTypeAttr(self);
                try types_buf.append(self.gpa, param_attr);
            }

            const sub_ty = mlir.LLVMAttributes.getLLVMDISubroutineTypeAttr(
                self.mlir_ctx,
                0,
                types_buf.items,
            );
            if (sub_ty.isNull()) return error.DebugAttrParseFailed;

            // Wrap in pointer type
            const scratch = self.debug_arena.allocator();
            const sub_ty_text = try getAttrText(self, sub_ty);
            
            const ptr_text = try std.fmt.allocPrint(scratch,
                "#llvm.di_derived_type<tag = DW_TAG_pointer_type, baseType = {s}, sizeInBits = 64, alignInBits = 64, offset = 0>",
                .{sub_ty_text}
            );

            const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(ptr_text));
            if (attr.isNull()) return error.DebugAttrParseFailed;
            break :blk attr;
        },
        else => try ensureDINullTypeAttr(self),
    };

    if (!attr.isNull()) try self.di_type_cache.put(ty, attr);
    return attr;
}

/// Helper to build a signed integer debug descriptor for `bits` width.
fn diSignedIntType(self: *Codegen, name: []const u8, bits: u64) mlir.Attribute {
    return mlir.LLVMAttributes.getLLVMDIBasicTypeAttr(
        self.mlir_ctx,
        DW_TAG_base_type,
        self.strAttr(name),
        bits,
        mlir.LLVMTypeEncoding.Signed,
    );
}

/// Helper to build an unsigned integer debug descriptor for `bits` width.
fn diUnsignedIntType(self: *Codegen, name: []const u8, bits: u64) mlir.Attribute {
    return mlir.LLVMAttributes.getLLVMDIBasicTypeAttr(
        self.mlir_ctx,
        DW_TAG_base_type,
        self.strAttr(name),
        bits,
        mlir.LLVMTypeEncoding.Unsigned,
    );
}

/// Construct the DI subroutine type attribute for a function given its return/param types.
fn buildDISubroutineTypeAttr(
    self: *Codegen,
    ret_ty: types.TypeId,
    params: []const tir.ParamId,
    t: *tir.TIR,
) !mlir.Attribute {
    var types_buf: std.ArrayList(mlir.Attribute) = .empty;
    defer types_buf.deinit(self.gpa);

    const ret_attr = ensureDIType(self, ret_ty) catch try ensureDINullTypeAttr(self);
    const norm_ret = if (!ret_attr.isNull()) ret_attr else try ensureDINullTypeAttr(self);
    try types_buf.append(self.gpa, norm_ret);

    for (params) |pid| {
        const param = t.funcs.Param.get(pid);
        const param_attr = ensureDIType(self, param.ty) catch try ensureDINullTypeAttr(self);
        const norm_param = if (!param_attr.isNull()) param_attr else try ensureDINullTypeAttr(self);
        try types_buf.append(self.gpa, norm_param);
    }

    const attr = mlir.LLVMAttributes.getLLVMDISubroutineTypeAttr(
        self.mlir_ctx,
        0,
        types_buf.items,
    );
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
pub fn emitParameterDebugInfo(
    self: *Codegen,
    f_id: tir.FuncId,
    params: []const tir.ParamId,
    entry_block: mlir.Block,
    t: *tir.TIR,
) !void {
    if (!codegen.enable_debug_info) return;
    const subp_ptr = self.di_subprograms.getPtr(f_id) orelse return;
    const subp = subp_ptr.*;

    var has_named = false;
    for (params) |pid| {
        const p = t.funcs.Param.get(pid);
        if (!p.name.isNone()) {
            has_named = true;
            break;
        }
    }
    if (!has_named) return;

    const file_info = ensureDebugFile(self, subp.file_id) catch return;
    const expr_attr = ensureEmptyDIExpression(self) catch return;

    const prev_loc = self.pushLocation(subp.loc);
    defer self.loc = prev_loc;

    for (params, 0..) |pid, idx| {
        const p = t.funcs.Param.get(pid);
        if (p.name.isNone()) continue;
        const name = t.instrs.strs.get(p.name.unwrap());
        var di_type = ensureDIType(self, p.ty) catch ensureDINullTypeAttr(self) catch continue;
        if (di_type.isNull()) di_type = ensureDINullTypeAttr(self) catch continue;

        // Skip emitting debug info for types we don't handle yet (pointers, structs, etc.)
        // to avoid crashing LLVM.
        const null_attr = ensureDINullTypeAttr(self) catch continue;
        if (di_type.equal(&null_attr)) continue;

        const var_attr = mlir.LLVMAttributes.getLLVMDILocalVariableAttr(
            self.mlir_ctx,
            subp.attr,
            self.strAttr(name),
            file_info.file_attr,
            subp.line,
            @intCast(idx + 1),
            0,
            di_type,
            0,
        );
        if (var_attr.isNull()) continue;

        const arg_val = entry_block.getArgument(idx);
        const attrs = [_]mlir.NamedAttribute{
            self.named("varInfo", var_attr),
            self.named("locationExpr", expr_attr),
        };
        _ = self.appendOp("llvm.intr.dbg.value", .{
            .operands = &.{arg_val},
            .attributes = &attrs,
        });
    }
}
