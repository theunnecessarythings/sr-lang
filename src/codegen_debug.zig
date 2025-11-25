const codegen = @import("codegen_main.zig");
const Codegen = codegen.Codegen;
const OpBuilder = Codegen.OpBuilder;
const mlir = @import("mlir_bindings.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const std = @import("std");

/// DWARF tag value for basic scalar types.
const DW_TAG_base_type: u32 = 0x24;
/// DWARF tag value used when describing pointer types.
const DW_TAG_pointer_type: u32 = 0x0f;
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
    self.di_files.clearRetainingCapacity();
    self.di_subprograms.clearRetainingCapacity();
    self.di_null_type_attr = mlir.Attribute.empty();
    self.di_subroutine_null_type_attr = mlir.Attribute.empty();
    self.di_empty_expr_attr = mlir.Attribute.empty();
    self.di_type_cache.clearRetainingCapacity();
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
    const id_payload = try std.fmt.allocPrint(self.gpa, "cu_{d}", .{nextDistinctId(self)});
    defer self.gpa.free(id_payload);
    const id_attr = mlir.Attribute.distinctAttrCreate(self.strAttr(id_payload));

    const file_text = try self.ownedAttributeText(file_attr);
    defer self.gpa.free(file_text);
    const producer_text = try self.ownedAttributeText(producer_attr);
    defer self.gpa.free(producer_text);
    const id_text = try self.ownedAttributeText(id_attr);
    defer self.gpa.free(id_text);

    const cu_text = try std.fmt.allocPrint(
        self.gpa,
        "#llvm.di_compile_unit<id = {s}, sourceLanguage = DW_LANG_C11, file = {s}, producer = {s}, isOptimized = false, emissionKind = Full>",
        .{ id_text, file_text, producer_text },
    );
    defer self.gpa.free(cu_text);

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
    const id_payload = try std.fmt.allocPrint(self.gpa, "sp_{d}", .{nextDistinctId(self)});
    defer self.gpa.free(id_payload);
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

/// Format a module-flag attribute for the given `behavior`, `key`, and `value_repr`.
fn moduleFlagAttr(self: *Codegen, behavior: []const u8, key: []const u8, value_repr: []const u8) !mlir.Attribute {
    const text = try std.fmt.allocPrint(
        self.gpa,
        "#llvm.mlir.module_flag<{s}, \"{s}\", {s}>",
        .{ behavior, key, value_repr },
    );
    defer self.gpa.free(text);
    const attr = mlir.Attribute.parseGet(self.mlir_ctx, mlir.StringRef.from(text));
    if (attr.isNull()) return error.DebugAttrParseFailed;
    return attr;
}

/// Check whether `attr` already encodes a module flag with the given `key`.
fn moduleFlagMatchesKey(self: *Codegen, attr: mlir.Attribute, key: []const u8) !bool {
    const text = try self.ownedAttributeText(attr);
    defer self.gpa.free(text);
    const needle = try std.fmt.allocPrint(self.gpa, ", \"{s}\",", .{key});
    defer self.gpa.free(needle);
    return std.mem.indexOf(u8, text, needle) != null;
}
/// Append a new module flag entry if a flag with `key` is not already present.
fn appendModuleFlag(
    self: *Codegen,
    flags: *std.ArrayList(mlir.Attribute),
    behavior: []const u8,
    key: []const u8,
    value_repr: []const u8,
) !void {
    for (flags.items) |existing| {
        if (try moduleFlagMatchesKey(self, existing, key)) return;
    }
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
    if (!existing_flags.isNull()) {
        const count = existing_flags.arrayAttrGetNumElements();
        var idx: usize = 0;
        while (idx < count) : (idx += 1) {
            try flags.append(self.gpa, existing_flags.arrayAttrGetElement(idx));
        }
    }

    try appendModuleFlag(self, &flags, "warning", "Debug Info Version", "3 : i32");
    try appendModuleFlag(self, &flags, "max", "Dwarf Version", "5 : i32");

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
        .Function => blk: {
            const finfo = self.context.type_store.get(.Function, ty);
            var types_buf: std.ArrayList(mlir.Attribute) = .empty;
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
            if (sub_ty.isNull()) break :blk try ensureDINullTypeAttr(self);
            break :blk sub_ty;
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
        const dbg = OpBuilder.init("llvm.intr.dbg.value", self.loc).builder()
            .operands(&.{arg_val})
            .attributes(&attrs)
            .build();
        self.append(dbg);
    }
}
