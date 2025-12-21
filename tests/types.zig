const std = @import("std");
const compiler = @import("compiler");
const types = compiler.types;
const cst = compiler.cst;

fn withStore(
    body: fn (store: *types.TypeStore, interner: *cst.StringInterner) anyerror!void,
) !void {
    const allocator = std.testing.allocator;
    var interner = cst.StringInterner.init(allocator);
    var store = types.TypeStore.init(allocator, &interner);
    defer store.deinit();
    defer interner.deinit();
    try body(&store, &interner);
}

fn expectFormatted(
    actual: []const u8,
    expected: []const u8,
) !void {
    try std.testing.expectEqualStrings(expected, actual);
}

fn expectFmt(store: *types.TypeStore, ty: types.TypeId, expected: []const u8) !void {
    var buffer: [512]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);
    try store.fmt(ty, stream.writer());
    try expectFormatted(stream.getWritten(), expected);
}

fn expectDiagnostic(
    store: *types.TypeStore,
    ty: types.TypeId,
    options: types.FormatOptions,
    expected: []const u8,
) !void {
    var buffer: [512]u8 = undefined;
    var stream = std.io.fixedBufferStream(&buffer);
    try store.formatTypeForDiagnostic(ty, options, stream.writer());
    try expectFormatted(stream.getWritten(), expected);
}

fn runQualifiedNameDiagnostics(store: *types.TypeStore, interner: *cst.StringInterner) !void {
    const bool_ty = store.tBool();
    const qualified_name = interner.intern("main_pkg.module.BoolType");
    const other_name = interner.intern("main_pkg.module.BoolType.Old");
    try store.setQualifiedName(bool_ty, qualified_name);
    try store.setQualifiedName(bool_ty, other_name);
    try std.testing.expectEqual(store.getQualifiedName(bool_ty).?, qualified_name);

    try expectDiagnostic(store, bool_ty, types.FormatOptions{ .prefer_names = true }, "main_pkg.module.BoolType");
    try expectDiagnostic(store, bool_ty, types.FormatOptions{ .prefer_names = false }, "bool");
}

fn runTypeStoreFmt(store: *types.TypeStore, interner: *cst.StringInterner) !void {
    const void_ty = store.tVoid();
    const bool_ty = store.tBool();
    const i8_ty = store.tI8();
    const i16_ty = store.tI16();
    const i32_ty = store.tI32();
    const i64_ty = store.tI64();
    const u8_ty = store.tU8();
    const u16_ty = store.tU16();
    const u32_ty = store.tU32();
    const u64_ty = store.tU64();
    const f32_ty = store.tF32();
    const f64_ty = store.tF64();
    const usize_ty = store.tUsize();
    const string_ty = store.tString();
    const any_ty = store.tAny();
    const noreturn_ty = store.tNoreturn();
    const undef_ty = store.tUndef();
    const complex_ty = store.add(types.TypeKind.Complex, .{ .elem = bool_ty });
    const tensor_ty = store.mkTensor(i32_ty, &.{ 2, 3 });
    const simd_ty = store.mkSimd(f32_ty, 16);
    const ptr_ty = store.mkPtr(bool_ty, false);
    const slice_ty = store.mkSlice(bool_ty, false);
    const array_ty = store.mkArray(bool_ty, 4);
    const dynarray_ty = store.mkDynArray(bool_ty);
    const map_ty = store.mkMap(bool_ty, i32_ty);
    const optional_ty = store.mkOptional(bool_ty);
    const tuple_ty = store.mkTuple(&.{ bool_ty, i32_ty });
    const fn_ty = store.mkFunction(&.{ bool_ty, i32_ty }, bool_ty, false, true, false);
    const proc_ty = store.mkFunction(&.{ bool_ty }, string_ty, false, false, false);
    const variadic_ty = store.mkFunction(&.{ bool_ty }, bool_ty, true, true, false);
    const mlir_module = store.add(types.TypeKind.MlirModule, .{});
    const mlir_attribute = store.mkMlirAttribute(interner.intern("test_attr"));
    const mlir_type = store.mkMlirType(interner.intern("test_type"));

    const field_a = interner.intern("a");
    const field_b = interner.intern("b");
    const field_c = interner.intern("c");
    const struct_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = field_a, .ty = bool_ty },
        .{ .name = field_b, .ty = i32_ty },
        .{ .name = field_c, .ty = bool_ty },
    };
    const struct_ty = store.mkStruct(&struct_fields, 0);
    const union_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = field_a, .ty = bool_ty },
        .{ .name = field_b, .ty = f32_ty },
    };
    const union_ty = store.mkUnion(&union_fields);
    const variant_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = field_b, .ty = bool_ty },
    };
    const variant_ty = store.mkVariant(&variant_fields);
    const enum_members = [_]types.TypeStore.EnumMemberArg{
        .{ .name = interner.intern("First"), .value = 1 },
        .{ .name = interner.intern("Second"), .value = 2 },
    };
    const enum_ty = store.mkEnum(&enum_members, i32_ty);
    const error_fields = [_]types.TypeStore.StructFieldArg{
        .{ .name = field_c, .ty = bool_ty },
    };
    const error_ty = store.mkError(&error_fields);
    const error_set_ty = store.mkErrorSet(bool_ty, i32_ty);
    const type_type_ty = store.mkTypeType(bool_ty);
    const pkg_name = interner.intern("main_pkg");
    const filepath = interner.intern("main.sr");
    const ast_ty = store.mkAst(pkg_name, filepath);
    const type_error_ty = store.tTypeError();

    try expectFmt(store, void_ty, "void");
    try expectFmt(store, bool_ty, "bool");
    try expectFmt(store, i8_ty, "i8");
    try expectFmt(store, i16_ty, "i16");
    try expectFmt(store, i32_ty, "i32");
    try expectFmt(store, i64_ty, "i64");
    try expectFmt(store, u8_ty, "u8");
    try expectFmt(store, u16_ty, "u16");
    try expectFmt(store, u32_ty, "u32");
    try expectFmt(store, u64_ty, "u64");
    try expectFmt(store, f32_ty, "f32");
    try expectFmt(store, f64_ty, "f64");
    try expectFmt(store, usize_ty, "usize");
    try expectFmt(store, string_ty, "string");
    try expectFmt(store, any_ty, "any");
    try expectFmt(store, noreturn_ty, "noreturn");
    try expectFmt(store, undef_ty, "undef");
    try expectFmt(store, complex_ty, "complex@bool");
    try expectFmt(store, tensor_ty, "tensor2@i32[2 x 3]");
    try expectFmt(store, simd_ty, "simd16@f32");
    try expectFmt(store, ptr_ty, "*bool");
    try expectFmt(store, slice_ty, "[]bool");
    try expectFmt(store, array_ty, "[4]bool");
    try expectFmt(store, dynarray_ty, "dyn[]bool");
    try expectFmt(store, optional_ty, "?bool");
    try expectFmt(store, tuple_ty, "(bool, i32)");
    try expectFmt(store, map_ty, "map[bool] i32");
    try expectFmt(store, fn_ty, "fn(bool, i32) bool");
    try expectFmt(store, proc_ty, "proc(bool) string");
    try expectFmt(store, variadic_ty, "fn(bool) bool variadic");
    try expectFmt(store, struct_ty, "struct { a: bool, b: i32, c: bool }");
    try expectFmt(store, union_ty, "union { a: bool, b: f32 }");
    try expectFmt(store, variant_ty, "variant { b: bool }");
    try expectFmt(store, enum_ty, "enum(i32) { First = 1, Second = 2 }");
    try expectFmt(store, error_ty, "error { c: bool }");
    try expectFmt(store, error_set_ty, "error(i32, bool)");
    try expectFmt(store, type_type_ty, "type(bool)");
    try expectFmt(store, ast_ty, "ast(main_pkg#main.sr)");
    try expectFmt(store, mlir_module, "mlir.module");
    try expectFmt(store, mlir_attribute, "mlir.attribute");
    try expectFmt(store, mlir_type, "mlir.type");
    try expectFmt(store, type_error_ty, "<type error>");
}

fn runDiagnosticLimits(store: *types.TypeStore, interner: *cst.StringInterner) !void {
    _ = interner;
    const bool_ty = store.tBool();
    const deep_tuple = store.mkTuple(&.{ bool_ty, bool_ty, bool_ty, bool_ty, bool_ty });
    const deep_fn = store.mkFunction(&.{ bool_ty, bool_ty, bool_ty, bool_ty, bool_ty }, bool_ty, false, true, false);
    const deep_ptr = store.mkPtr(store.mkPtr(store.mkPtr(bool_ty, true), true), true);

    try expectDiagnostic(store, deep_tuple, types.FormatOptions{ .max_fields = 2 }, "(bool, bool, ... (3 more))");
    try expectDiagnostic(store, deep_fn, types.FormatOptions{ .max_params = 2 }, "fn(bool, bool, ... (3 more)) bool");
    try expectDiagnostic(store, deep_ptr, types.FormatOptions{ .max_depth = 2 }, "*const *const ...");
}

test "TypeStore fmt covers every kind" {
    try withStore(runTypeStoreFmt);
}

test "formatTypeForDiagnostic respects limits" {
    try withStore(runDiagnosticLimits);
}

test "qualifies type names when stored" {
    try withStore(runQualifiedNameDiagnostics);
}
