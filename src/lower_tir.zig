const std = @import("std");
const ast = @import("ast.zig");
const cst = @import("cst.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const check_pattern_matching = @import("check_pattern_matching.zig");
const checker = @import("checker.zig");
const mlir = @import("mlir_bindings.zig");
const compile = @import("compile.zig");
const codegen = @import("codegen_main.zig");
const comp = @import("comptime.zig");
const check_types = @import("check_types.zig");
const pipeline_mod = @import("pipeline.zig");
const cf = @import("lower_cf_tir.zig");
const package = @import("package.zig");
const call_resolution = @import("call_resolution.zig");
const Loc = @import("lexer.zig").Token.Loc;

const StrId = @import("cst.zig").StrId;
const OptStrId = @import("cst.zig").OptStrId;
const Context = @import("compile.zig").Context;
const Pipeline = pipeline_mod.Pipeline;
const Builder = tir.Builder;
const List = std.ArrayList;

/// Metadata for a value binding tracked during lowering.
pub const ValueBinding = struct {
    value: tir.ValueId,
    ty: types.TypeId,
    is_slot: bool,
};

/// Snapshot entry showing the previous binding for a name.
pub const EnvBindingSnapshot = struct {
    name: ast.StrId,
    prev: ?ValueBinding,
};

const ExprTypeOverrideFrame = struct {
    map: std.AutoArrayHashMapUnmanaged(u32, types.TypeId) = .{},
    fn deinit(self: *ExprTypeOverrideFrame, gpa: std.mem.Allocator) void {
        self.map.deinit(gpa);
    }
};

const FunctionDeclContext = call_resolution.FunctionDeclContext;
pub const LowerTir = @This();

gpa: std.mem.Allocator,
context: *Context,
pipeline: *Pipeline,
chk: *checker.Checker,
lower_context: List(*LowerContext) = .{},
test_mode: bool = false,
test_funcs: std.ArrayList(TestFunc) = .{},
harness_emitted: bool = false,
entry_pkg_name: StrId,
entry_pkg_locked: bool = false,
const_slice_counter: u32 = 0,

const TestFunc = struct { sym: StrId, ty: types.TypeId, name: ?ast.StrId };

pub const LowerContext = struct {
    loop_stack: List(cf.LoopCtx) = .{},
    expr_type_override_stack: List(ExprTypeOverrideFrame) = .{},
    pattern_binding_names: List(ast.StrId) = .{},
    binding_snapshots: List(EnvBindingSnapshot) = .{},
    // Scratch buffers to reduce allocs in hot loops
    mlir_scratch_pieces: List(tir.MlirPieceId) = .{},
    mlir_scratch_values: List(tir.ValueId) = .{},

    gpa: std.mem.Allocator,
    builder: ?*tir.Builder = null,

    pub fn deinit(self: *LowerContext, gga: std.mem.Allocator) void {
        self.loop_stack.deinit(gga);
        while (self.expr_type_override_stack.pop()) |frame| {
            var f = frame;
            f.deinit(gga);
        }
        self.expr_type_override_stack.deinit(gga);
        self.pattern_binding_names.deinit(gga);
        self.binding_snapshots.deinit(gga);
        self.mlir_scratch_pieces.deinit(gga);
        self.mlir_scratch_values.deinit(gga);
    }
};

pub fn qualifySymbolName(self: *LowerTir, a: *ast.Ast, base: StrId) !StrId {
    if (a.unit.package_name.isNone()) return base;

    const ts = self.context.type_store;
    const pkg_id = a.unit.package_name.unwrap();
    const pkg_name = ts.strs.get(pkg_id);

    if (std.mem.eql(u8, pkg_name, "main")) return base;

    const base_name = ts.strs.get(base);
    const symbol = try std.fmt.allocPrint(self.gpa, "{s}__{s}", .{ pkg_name, base_name });
    defer self.gpa.free(symbol);
    return ts.strs.intern(symbol);
}

fn astForFileId(self: *LowerTir, file_id: u32) ?*ast.Ast {
    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var source_iter = pkg.value_ptr.sources.iterator();
        while (source_iter.next()) |entry| {
            if (entry.value_ptr.file_id == file_id) return entry.value_ptr.ast;
        }
    }
    return null;
}

pub var g_mlir_inited: bool = false;
pub var g_mlir_ctx: mlir.Context = undefined;

pub fn init(gpa: std.mem.Allocator, context: *Context, pipeline: *Pipeline, chk: *checker.Checker, test_mode: bool) LowerTir {
    return .{
        .gpa = gpa,
        .context = context,
        .pipeline = pipeline,
        .chk = chk,
        .lower_context = .{},
        .test_mode = test_mode,
        .entry_pkg_name = context.type_store.strs.intern("main"),
    };
}

pub fn deinit(self: *LowerTir) void {
    self.test_funcs.deinit(self.gpa);
}

fn throwErr(self: *LowerTir, loc: Loc) anyerror {
    std.debug.dumpCurrentStackTrace(null);
    try self.context.diags.addError(loc, .tir_lowering_failed, .{});
    return error.LoweringBug;
}

pub fn run(self: *LowerTir, levels: *const compile.DependencyLevels) !*tir.TIR {
    var unit_by_file: std.AutoHashMap(u32, *package.FileUnit) = .init(self.gpa);
    defer unit_by_file.deinit();

    // Populate lookup map
    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var source_iter = pkg.value_ptr.sources.iterator();
        while (source_iter.next()) |unit| {
            try unit_by_file.put(unit.value_ptr.file_id, unit.value_ptr);
        }
    }

    if (self.test_mode) try self.collectTestFunctions(&unit_by_file);

    // Process levels
    for (levels.levels.items) |level| {
        for (level.items) |file_id| {
            try self.lowerFileUnit(file_id, &unit_by_file);
        }
    }

    // Resolve entry package
    const entry_pkg_name_str = self.context.type_store.strs.get(self.entry_pkg_name);
    const entry_pkg = self.context.compilation_unit.packages.getPtr(entry_pkg_name_str) orelse blk: {
        var it = self.context.compilation_unit.packages.iterator();
        const first = it.next() orelse return error.PackageNotFound;
        self.entry_pkg_name = self.context.type_store.strs.intern(first.value_ptr.name);
        break :blk first.value_ptr;
    };

    return entry_pkg.sources.entries.get(0).value.tir.?;
}

fn lowerFileUnit(self: *LowerTir, file_id: u32, unit_by_file: *std.AutoHashMap(u32, *package.FileUnit)) !void {
    const unit = unit_by_file.get(file_id) orelse return;
    const ast_ptr = unit.ast orelse return;

    const t = try self.gpa.create(tir.TIR);
    t.* = tir.TIR.init(self.gpa, self.context.type_store);

    const ctx = try self.gpa.create(LowerContext);
    ctx.* = LowerContext{ .gpa = self.gpa };
    defer {
        ctx.deinit(self.gpa);
        self.gpa.destroy(ctx);
    }

    self.runAst(ast_ptr, t, ctx) catch {
        t.deinit();
        self.gpa.destroy(t);
        return self.throwErr(.init(file_id, 0, 0));
    };
    unit.tir = t;
}

fn collectTestFunctions(self: *LowerTir, unit_by_file: *std.AutoHashMap(u32, *package.FileUnit)) !void {
    const ts = self.context.type_store;
    const test_sid = ts.strs.intern("test");

    var it = unit_by_file.iterator();
    while (it.next()) |entry| {
        const unit = entry.value_ptr.*;
        const ast_unit = unit.ast orelse continue;
        const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);

        for (decls) |did| {
            const decl = ast_unit.exprs.Decl.get(did);
            if (ast_unit.kind(decl.value) != .FunctionLit) continue;

            const fnr = ast_unit.exprs.get(.FunctionLit, decl.value);
            if (!fnr.flags.is_test) continue;

            const raw_did = did.toRaw();
            if (raw_did >= ast_unit.type_info.decl_types.items.len) continue;

            const ty_opt = ast_unit.type_info.decl_types.items[raw_did] orelse continue;
            if (ts.getKind(ty_opt) == .TypeError) continue;

            const sym = (try self.symbolNameForDecl(ast_unit, did)) orelse continue;
            var test_name: ?ast.StrId = null;

            if (!fnr.attrs.isNone()) {
                const attrs = ast_unit.exprs.attr_pool.slice(fnr.attrs.asRange());
                for (attrs) |aid| {
                    const arow = ast_unit.exprs.Attribute.get(aid);
                    if (arow.name.eq(test_sid) and !arow.value.isNone()) {
                        const val_id = arow.value.unwrap();
                        if (ast_unit.kind(val_id) == .Literal) {
                            const lit = ast_unit.exprs.get(.Literal, val_id);
                            if (lit.kind == .string) {
                                test_name = lit.data.string;
                                break;
                            }
                        }
                    }
                }
            }

            if (!self.entry_pkg_locked) {
                self.entry_pkg_name = if (!ast_unit.unit.package_name.isNone())
                    ast_unit.unit.package_name.unwrap()
                else
                    ts.strs.intern("main");
                self.entry_pkg_locked = true;
            }

            try self.test_funcs.append(self.gpa, .{ .sym = sym, .ty = ty_opt, .name = test_name });
        }
    }
}

fn emitTestHarness(self: *LowerTir, _: *LowerContext, _: *ast.Ast, b: *Builder) !void {
    if (self.test_funcs.items.len == 0) return;

    const ts = self.context.type_store;
    const i32_ty = ts.tI32();
    var f = try b.beginFunction(self.context, ts.strs.intern("main"), i32_ty, false, false, .empty(), false, false, .none());
    var blk = try b.beginBlock(&f);

    const zero = b.tirValue(.ConstInt, &blk, i32_ty, .none(), .{ .value = 0 });
    var failures = zero;

    const ptr_u8_const = ts.mkPtr(ts.tU8(), true);
    const rt_print_sym = ts.strs.intern("rt_print");
    const printf_sym = ts.strs.intern("printf");

    for (self.test_funcs.items) |tf| {
        if (ts.getKind(tf.ty) != .Function) continue;
        const fn_info = ts.get(.Function, tf.ty);
        const call_v = b.call(&blk, fn_info.result, tf.sym, &.{}, .none());
        try self.emitTestResult(b, &f, &blk, call_v, fn_info.result, ts.strs.get(tf.name orelse tf.sym), &failures, ptr_u8_const, rt_print_sym);
    }

    try self.emitTestSummary(b, &blk, failures, ptr_u8_const, printf_sym);
    try b.setReturnVal(&blk, failures, .none());
    try b.endBlock(&f, blk);
    try b.endFunction(f);
    self.harness_emitted = true;
}

fn emitTestResult(
    self: *LowerTir,
    b: *Builder,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    call_v: tir.ValueId,
    ret_ty: types.TypeId,
    test_name: []const u8,
    failures: *tir.ValueId,
    ptr_u8_ty: types.TypeId,
    rt_print_sym: StrId,
) !void {
    const ts = self.context.type_store;
    const i32_ty = ts.tI32();
    const usize_ty = ts.tUsize();

    const pass_msg_bytes = try std.fmt.allocPrint(self.gpa, "\x1b[32mTest '{s}' passed\x1b[0m\n", .{test_name});
    defer self.gpa.free(pass_msg_bytes);
    const pass_msg = b.tirValue(.ConstString, blk, ts.tString(), .none(), .{ .text = ts.strs.intern(pass_msg_bytes) });

    if (ts.getKind(ret_ty) == .ErrorSet) {
        const fail_msg_bytes = try std.fmt.allocPrint(self.gpa, "\x1b[31mTest '{s}' failed\x1b[0m\n", .{test_name});
        defer self.gpa.free(fail_msg_bytes);
        const fail_msg = b.tirValue(.ConstString, blk, ts.tString(), .none(), .{ .text = ts.strs.intern(fail_msg_bytes) });

        const is_err = b.binBool(blk, .CmpNe, b.extractField(blk, i32_ty, call_v, 0, .none()), b.tirValue(.ConstInt, blk, i32_ty, .none(), .{ .value = 0 }), .none());

        failures.* = b.bin(blk, .Add, i32_ty, failures.*, b.un1(blk, .CastNormal, i32_ty, is_err, .none()), .none());

        var pass_blk = try b.beginBlock(f);
        var fail_blk = try b.beginBlock(f);
        const cont_blk = try b.beginBlock(f);

        try b.condBr(blk, is_err, fail_blk.id, &.{}, pass_blk.id, &.{}, .none());
        try b.endBlock(f, blk.*);

        // Fail Path
        _ = b.call(&fail_blk, ts.tVoid(), rt_print_sym, &.{ b.extractField(&fail_blk, ptr_u8_ty, fail_msg, 0, .none()), b.extractField(&fail_blk, usize_ty, fail_msg, 1, .none()) }, .none());
        try b.br(&fail_blk, cont_blk.id, &.{}, .none());
        try b.endBlock(f, fail_blk);

        // Pass Path
        _ = b.call(&pass_blk, ts.tVoid(), rt_print_sym, &.{ b.extractField(&pass_blk, ptr_u8_ty, pass_msg, 0, .none()), b.extractField(&pass_blk, usize_ty, pass_msg, 1, .none()) }, .none());
        try b.br(&pass_blk, cont_blk.id, &.{}, .none());
        try b.endBlock(f, pass_blk);

        blk.* = cont_blk;
    } else {
        _ = b.call(blk, ts.tVoid(), rt_print_sym, &.{ b.extractField(blk, ptr_u8_ty, pass_msg, 0, .none()), b.extractField(blk, usize_ty, pass_msg, 1, .none()) }, .none());
    }
}

fn emitTestSummary(self: *LowerTir, b: *Builder, blk: *Builder.BlockFrame, failures: tir.ValueId, ptr_u8_ty: types.TypeId, printf_sym: StrId) !void {
    const ts = self.context.type_store;
    const i32_ty = ts.tI32();
    const passed = b.bin(blk, .Sub, i32_ty, b.tirValue(.ConstInt, blk, i32_ty, .none(), .{ .value = self.test_funcs.items.len }), failures, .none());
    const summary_fmt = b.tirValue(.ConstString, blk, ts.tString(), .none(), .{ .text = ts.strs.intern("\x1b[36mSummary:\x1b[0m \x1b[32m%d passed\x1b[0m; \x1b[31m%d failed\x1b[0m\n") });
    _ = b.call(blk, i32_ty, printf_sym, &.{ b.extractField(blk, ptr_u8_ty, summary_fmt, 0, .none()), passed, failures }, .none());
}

pub fn optionalPayload(self: *LowerTir, blk: *Builder.BlockFrame, opt_ty: types.TypeId, opt_val: tir.ValueId, loc: tir.OptLocId) tir.ValueId {
    const ts = self.context.type_store;
    const opt = ts.get(.Optional, opt_ty);
    if (ts.isOptionalPointer(opt_ty)) return blk.builder.tirValue(.CastBit, blk, opt.elem, loc, .{ .value = opt_val });
    const ek = ts.getKind(opt.elem);
    if (ek == .Void or ek == .Any) return self.safeUndef(blk, opt.elem, loc);
    return blk.builder.extractField(blk, opt.elem, opt_val, 1, loc);
}

pub fn optionalFlag(self: *LowerTir, blk: *Builder.BlockFrame, opt_ty: types.TypeId, opt_val: tir.ValueId, loc: tir.OptLocId) tir.ValueId {
    const ts = self.context.type_store;
    if (ts.isOptionalPointer(opt_ty)) {
        const payload = blk.builder.tirValue(.CastBit, blk, ts.get(.Optional, opt_ty).elem, loc, .{ .value = opt_val });
        const usize_ty = ts.tUsize();
        return blk.builder.binBool(blk, .CmpNe, blk.builder.tirValue(.CastBit, blk, usize_ty, loc, .{ .value = payload }), blk.builder.constNull(blk, usize_ty, loc), loc);
    }
    return blk.builder.extractField(blk, ts.tBool(), opt_val, 0, loc);
}

pub fn optionalWrapWithFlag(self: *LowerTir, blk: *Builder.BlockFrame, opt_ty: types.TypeId, flag: tir.ValueId, payload: tir.ValueId, loc: tir.OptLocId) tir.ValueId {
    const ts = self.context.type_store;
    if (ts.isOptionalPointer(opt_ty)) {
        return blk.builder.tirValue(.Select, blk, opt_ty, loc, .{
            .cond = flag,
            .then_value = blk.builder.tirValue(.CastBit, blk, opt_ty, loc, .{ .value = payload }),
            .else_value = blk.builder.constNull(blk, opt_ty, loc),
        });
    }
    const elem_ty = ts.get(.Optional, opt_ty).elem;
    const ek = ts.getKind(elem_ty);

    if (ek == .Void or ek == .Any) {
        return blk.builder.structMake(blk, opt_ty, &[_]tir.Rows.StructFieldInit{.{ .index = 0, .name = .none(), .value = flag }}, loc);
    }
    return blk.builder.structMake(blk, opt_ty, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = flag },
        .{ .index = 1, .name = .none(), .value = payload },
    }, loc);
}

pub fn optionalWrapSome(self: *LowerTir, blk: *Builder.BlockFrame, opt_ty: types.TypeId, payload: tir.ValueId, loc: tir.OptLocId) tir.ValueId {
    const ts = self.context.type_store;
    if (ts.isOptionalPointer(opt_ty)) return blk.builder.tirValue(.CastBit, blk, opt_ty, loc, .{ .value = payload });

    const some_flag = blk.builder.tirValue(.ConstBool, blk, ts.tBool(), loc, .{ .value = true });
    const elem_ty = ts.get(.Optional, opt_ty).elem;
    const ek = ts.getKind(elem_ty);

    if (ek == .Void or ek == .Any) {
        return blk.builder.structMake(blk, opt_ty, &[_]tir.Rows.StructFieldInit{.{ .index = 0, .name = .none(), .value = some_flag }}, loc);
    }
    return blk.builder.structMake(blk, opt_ty, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = some_flag },
        .{ .index = 1, .name = .none(), .value = payload },
    }, loc);
}

fn isMainPackageName(self: *const LowerTir, ast_unit: *ast.Ast) bool {
    if (ast_unit.unit.package_name.isNone()) return true;
    const ts = self.context.type_store;
    return std.mem.eql(u8, ts.strs.get(ast_unit.unit.package_name.unwrap()), ts.strs.get(self.entry_pkg_name));
}

pub fn runAst(self: *LowerTir, ast_unit: *ast.Ast, t: *tir.TIR, ctx: *LowerContext) !void {
    var b: Builder = .init(self.gpa, t);
    ctx.builder = &b;

    try self.lowerGlobalMlir(ctx, ast_unit, &b);
    for (ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls)) |did| try self.lowerTopDecl(ctx, ast_unit, &b, did);
    try self.lowerRegisteredMethods(ctx, ast_unit, &b);
    try self.lowerSyntheticDecls(ctx, ast_unit, &b);

    if (self.test_mode and !self.harness_emitted and self.isMainPackageName(ast_unit)) {
        try self.emitTestHarness(ctx, ast_unit, &b);
    }
}

fn shouldSkipGenericMethod(self: *const LowerTir, fn_ty: types.TypeId) bool {
    const ts = self.context.type_store;
    if (ts.getKind(fn_ty) != .Function) return false;
    const info = ts.get(.Function, fn_ty);
    if (self.isType(info.result, .Any)) return true;
    for (ts.type_pool.slice(info.params)) |param| {
        if (self.isType(param, .Any)) return true;
    }
    return false;
}

fn hasTrailingAnyRuntimeParam(self: *const LowerTir, fty: types.TypeId) bool {
    const ts = self.context.type_store;
    if (ts.getKind(fty) != .Function) return false;
    const info = ts.get(.Function, fty);
    if (info.is_extern) return false;
    const params = ts.type_pool.slice(info.params);
    return if (params.len > 0) self.isType(params[params.len - 1], .Any) else false;
}

fn pushExprTypeOverrideFrame(self: *LowerTir, ctx: *LowerContext) !void {
    try ctx.expr_type_override_stack.append(self.gpa, .{});
}

fn popExprTypeOverrideFrame(self: *LowerTir, ctx: *LowerContext) void {
    var frame = ctx.expr_type_override_stack.pop() orelse return;
    frame.deinit(self.gpa);
}

pub fn noteExprType(self: *LowerTir, ctx: *LowerContext, expr: ast.ExprId, ty: types.TypeId) !void {
    if (ctx.expr_type_override_stack.items.len == 0 or self.isType(ty, .Any)) return;
    try ctx.expr_type_override_stack.items[ctx.expr_type_override_stack.items.len - 1].map.put(self.gpa, expr.toRaw(), ty);
}

fn lookupExprTypeOverride(_: *const LowerTir, ctx: *LowerContext, expr: ast.ExprId) ?types.TypeId {
    var i: usize = ctx.expr_type_override_stack.items.len;
    while (i > 0) {
        i -= 1;
        if (ctx.expr_type_override_stack.items[i].map.get(expr.toRaw())) |entry| return entry;
    }
    return null;
}

fn constInitFromLiteral(self: *LowerTir, a: *ast.Ast, expr: ast.ExprId, ty: types.TypeId) ?tir.ConstInit {
    if (a.kind(expr) != .Literal) return null;
    const lit = a.exprs.get(.Literal, expr);

    switch (self.context.type_store.getKind(ty)) {
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => {
            const info = if (lit.data == .int) lit.data.int else return null;
            if (!info.valid or info.value > std.math.maxInt(i64)) return null;
            return tir.ConstInit{ .int = @intCast(info.value) };
        },
        .F32, .F64 => {
            const info = if (lit.data == .float) lit.data.float else return null;
            if (!info.valid) return null;
            return tir.ConstInit{ .float = info.value };
        },
        .Bool => return if (lit.data == .bool) tir.ConstInit{ .bool = lit.data.bool } else null,
        else => return null,
    }
}

fn lowerDynArrayAppend(
    self: *LowerTir,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    loc: tir.OptLocId,
    binding: types.MethodBinding,
    args: []const tir.ValueId,
) !tir.ValueId {
    std.debug.assert(binding.builtin != null and binding.builtin.? == .dynarray_append);
    const ts = self.context.type_store;
    const dyn_info = ts.get(.DynArray, binding.owner_type);
    const usize_ty = ts.tUsize();

    const ptr_elem_ty = ts.mkPtr(dyn_info.elem, false);
    const ptr_ptr_elem_ty = ts.mkPtr(ptr_elem_ty, false);
    const ptr_usize_ty = ts.mkPtr(usize_ty, false);

    // Cached constants
    const idx0 = blk.builder.gepConst(0);
    const array_ptr = args[0];

    const data_ptr_ptr = blk.builder.gep(blk, ptr_ptr_elem_ty, array_ptr, &.{ idx0, idx0 }, loc);
    const len_ptr = blk.builder.gep(blk, ptr_usize_ty, array_ptr, &.{ idx0, blk.builder.gepConst(1) }, loc);
    const cap_ptr = blk.builder.gep(blk, ptr_usize_ty, array_ptr, &.{ idx0, blk.builder.gepConst(2) }, loc);

    const len_val = blk.builder.tirValue(.Load, blk, usize_ty, loc, .{ .ptr = len_ptr, .@"align" = 0 });
    const cap_val = blk.builder.tirValue(.Load, blk, usize_ty, loc, .{ .ptr = cap_ptr, .@"align" = 0 });

    var grow_blk = try f.builder.beginBlock(f);
    const cont_blk = try f.builder.beginBlock(f);

    const grow_cond = self.forceLocalCond(blk, blk.builder.binBool(blk, .CmpEq, len_val, cap_val, loc), loc);
    try f.builder.condBr(blk, grow_cond, grow_blk.id, &.{}, cont_blk.id, &.{}, loc);
    try f.builder.endBlock(f, blk.*);

    {
        // Growth path
        const data_ptr = grow_blk.builder.tirValue(.Load, &grow_blk, ptr_elem_ty, loc, .{ .ptr = data_ptr_ptr, .@"align" = 0 });
        const zero_const = grow_blk.builder.tirValue(.ConstInt, &grow_blk, usize_ty, loc, .{ .value = 0 });
        const new_cap = grow_blk.builder.tirValue(.Select, &grow_blk, usize_ty, loc, .{
            .cond = grow_blk.builder.binBool(&grow_blk, .CmpEq, cap_val, zero_const, loc),
            .then_value = grow_blk.builder.tirValue(.ConstInt, &grow_blk, usize_ty, loc, .{ .value = 1 }),
            .else_value = grow_blk.builder.bin(&grow_blk, .Mul, usize_ty, cap_val, grow_blk.builder.tirValue(.ConstInt, &grow_blk, usize_ty, loc, .{ .value = 2 }), loc),
        });

        const elem_size = grow_blk.builder.tirValue(.ConstInt, &grow_blk, usize_ty, loc, .{ .value = @as(u64, @intCast(check_types.typeSize(self.context, dyn_info.elem))) });
        const new_bytes = grow_blk.builder.bin(&grow_blk, .Mul, usize_ty, new_cap, elem_size, loc);

        const new_data_void = self.callRuntimeReallocPtr(&grow_blk, grow_blk.builder.tirValue(.CastBit, &grow_blk, ts.mkPtr(ts.tVoid(), false), loc, .{ .value = data_ptr }), new_bytes, loc);
        _ = grow_blk.builder.tirValue(.Store, &grow_blk, ptr_elem_ty, loc, .{ .ptr = data_ptr_ptr, .value = grow_blk.builder.tirValue(.CastBit, &grow_blk, ptr_elem_ty, loc, .{ .value = new_data_void }), .@"align" = 0 });
        _ = grow_blk.builder.tirValue(.Store, &grow_blk, usize_ty, loc, .{ .ptr = cap_ptr, .value = new_cap, .@"align" = 0 });

        try f.builder.br(&grow_blk, cont_blk.id, &.{}, loc);
        try f.builder.endBlock(f, grow_blk);
    }

    blk.* = cont_blk;
    const data_ptr_cur = blk.builder.tirValue(.Load, blk, ptr_elem_ty, loc, .{ .ptr = data_ptr_ptr, .@"align" = 0 });
    const slot_ptr = blk.builder.gep(blk, ptr_elem_ty, data_ptr_cur, &.{blk.builder.gepValue(len_val)}, loc);
    _ = blk.builder.tirValue(.Store, blk, dyn_info.elem, loc, .{ .ptr = slot_ptr, .value = args[1], .@"align" = 0 });

    const new_len = blk.builder.bin(blk, .Add, usize_ty, len_val, blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = 1 }), loc);
    _ = blk.builder.tirValue(.Store, blk, usize_ty, loc, .{ .ptr = len_ptr, .value = new_len, .@"align" = 0 });

    return self.safeUndef(blk, ts.tVoid(), loc);
}

fn constInitFromExpr(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, expr_id: ast.ExprId, ty: types.TypeId) !?tir.ConstInit {
    if (self.constInitFromLiteral(a, expr_id, ty)) |ci| return ci;

    switch (self.context.type_store.getKind(ty)) {
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64, .Bool => {
            if (try self.getCachedComptimeValue(a, expr_id)) |val| {
                var vl = val;
                defer vl.destroy(self.gpa);
                return switch (val) {
                    .Int => |v| tir.ConstInit{ .int = @intCast(v) },
                    .Float => |v| tir.ConstInit{ .float = v },
                    .Bool => |v| tir.ConstInit{ .bool = v },
                    else => null,
                };
            }
        },
        else => {},
    }

    if (a.kind(expr_id) == .StructLit) {
        const struct_lit = a.exprs.get(.StructLit, expr_id);
        const struct_ty = self.context.type_store.get(.Struct, ty);
        const field_decls = self.context.type_store.field_pool.slice(struct_ty.fields);
        const field_inits = a.exprs.sfv_pool.slice(struct_lit.fields);

        var field_const_inits = std.ArrayList(tir.ConstInit){};
        defer field_const_inits.deinit(self.gpa);

        for (field_inits, 0..) |sfv_id, i| {
            if (try self.constInitFromExpr(ctx, a, a.exprs.StructFieldValue.get(sfv_id).value, self.context.type_store.Field.get(field_decls[i]).ty)) |field_ci| {
                try field_const_inits.append(self.gpa, field_ci);
            } else return null;
        }
        return tir.ConstInit{ .aggregate = try field_const_inits.toOwnedSlice(self.gpa) };
    }
    return null;
}

fn lowerGlobalMlir(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, b: *Builder) !void {
    var decls = std.ArrayList(ast.DeclId){};
    defer decls.deinit(self.gpa);

    for (a.exprs.decl_pool.slice(a.unit.decls)) |did| {
        const d = a.exprs.Decl.get(did);
        if (a.kind(d.value) == .MlirBlock and d.pattern.isNone()) try decls.append(self.gpa, did);
    }
    if (decls.items.len == 0) return;

    var f = try b.beginFunction(self.context, b.intern("__sr_global_mlir_init"), self.context.type_store.tVoid(), false, false, .empty(), false, false, .none());
    var blk = try b.beginBlock(&f);
    var env = cf.Env{};
    defer env.deinit(self.gpa);

    for (decls.items) |did| _ = try self.lowerExpr(ctx, a, &env, &f, &blk, a.exprs.Decl.get(did).value, null, .rvalue);

    if (blk.term.isNone()) try b.setReturn(&blk, .none(), .none());
    try b.endBlock(&f, blk);
    try b.endFunction(f);
}

fn lowerMlirBlock(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    loc: tir.OptLocId,
) !tir.ValueId {
    const row = a.exprs.get(.MlirBlock, id);
    const ts = self.context.type_store;
    var ty0 = self.getExprType(ctx, a, id);

    if (self.isType(ty0, .Any)) {
        ty0 = switch (row.kind) {
            .Module => ts.tMlirModule(),
            .Attribute => ts.mkMlirAttribute(row.text),
            .Type => ts.mkTypeType(ts.mkMlirType(row.text)),
            .Operation => ty0,
        };
    }
    if (expected_ty) |want| {
        if (self.isType(ty0, .Any) and !self.isType(want, .Any)) ty0 = want;
    }

    ctx.mlir_scratch_pieces.clearRetainingCapacity();
    for (a.exprs.mlir_piece_pool.slice(row.pieces)) |pid| {
        const piece = a.exprs.MlirPiece.get(pid);
        var splice_value: comp.ComptimeValue = .Void;
        var splice_ty: ?types.TypeId = null;

        if (piece.kind == .splice) {
            splice_value = try self.resolveMlirSpliceOrCached(ctx, a, pid, piece.text, row.loc);
            if (a.type_info.getMlirSpliceInfo(pid)) |info| {
                splice_ty = switch (info) {
                    .value_param => |vp| vp.ty,
                    .type_param => info.type_param.ty,
                    else => null,
                };
            }
        }
        try ctx.mlir_scratch_pieces.append(self.gpa, blk.builder.t.instrs.MlirPiece.add(blk.builder.t.instrs.allocator, .{ .kind = piece.kind, .text = piece.text, .value = splice_value, .ty = splice_ty }));
    }

    ctx.mlir_scratch_values.clearRetainingCapacity();
    const arg_ids = a.exprs.expr_pool.slice(row.args);
    try ctx.mlir_scratch_values.ensureTotalCapacity(self.gpa, arg_ids.len);
    for (arg_ids) |arg_id| ctx.mlir_scratch_values.appendAssumeCapacity(try self.lowerExpr(ctx, a, env, f, blk, arg_id, null, .rvalue));

    const result_id = blk.builder.freshValue();
    try blk.instrs.append(self.gpa, blk.builder.t.instrs.add(.MlirBlock, .{
        .result = .some(result_id),
        .ty = ty0,
        .kind = row.kind,
        .expr = id,
        .text = row.text,
        .pieces = blk.builder.t.instrs.mlir_piece_pool.pushMany(self.gpa, ctx.mlir_scratch_pieces.items),
        .args = blk.builder.t.instrs.value_pool.pushMany(self.gpa, ctx.mlir_scratch_values.items),
        .loc = loc,
    }));

    if (expected_ty) |want| {
        if (!ty0.eq(want)) return self.emitCoerce(blk, result_id, ty0, want, loc);
    }
    return result_id;
}

fn resolveMlirSpliceOrCached(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, pid: ast.MlirPieceId, text: StrId, loc: ast.LocId) !comp.ComptimeValue {
    if (ctx.expr_type_override_stack.items.len == 0) {
        if (a.type_info.getMlirSpliceValue(pid)) |cached| return try comp.cloneComptimeValue(self.gpa, cached.*);
    }
    return self.resolveMlirSpliceValue(ctx, a, pid, text, loc);
}

fn resolveMlirSpliceValue(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, piece_id: ast.MlirPieceId, name: StrId, loc_id: ast.LocId) !comp.ComptimeValue {
    const info = a.type_info.getMlirSpliceInfo(piece_id) orelse unreachable;
    const diag_loc = a.exprs.locs.get(loc_id);

    switch (info) {
        .decl => |decl_info| {
            const decl = a.exprs.Decl.get(decl_info.decl_id);
            const decl_value_ty = self.getExprType(ctx, a, decl.value);
            const ts = self.context.type_store;

            if (ts.getKind(decl_value_ty) == .TypeType) {
                return comp.ComptimeValue{ .Type = ts.get(.TypeType, decl_value_ty).of };
            }
            if (try self.getCachedComptimeValue(a, decl.value)) |value| return value;
            try self.context.diags.addError(diag_loc, .mlir_splice_not_comptime, .{a.exprs.strs.get(name)});
            return error.LoweringBug;
        },
        .value_param => |param_info| {
            if (try self.cloneComptimeAliasValue(a, param_info.name)) |value| return value;
            try self.context.diags.addError(diag_loc, .mlir_splice_unbound, .{a.exprs.strs.get(name)});
            return error.LoweringBug;
        },
        .type_param => |param_info| {
            if (self.lookupComptimeAliasType(a, param_info.name)) |ty| return comp.ComptimeValue{ .Type = ty };
            try self.context.diags.addError(diag_loc, .mlir_splice_unbound, .{a.exprs.strs.get(name)});
            return error.LoweringBug;
        },
    }
}

fn getCachedComptimeValue(self: *LowerTir, a: *ast.Ast, expr: ast.ExprId) !?comp.ComptimeValue {
    if (a.type_info.getComptimeValue(expr)) |cached| return try comp.cloneComptimeValue(self.gpa, cached.*);
    return null;
}

const LowerMode = enum { rvalue, lvalue_addr };

pub fn isVoid(self: *const LowerTir, ty: types.TypeId) bool {
    return self.context.type_store.getKind(ty) == .Void;
}

pub fn optLoc(a: *ast.Ast, id: anytype) tir.OptLocId {
    const T = @TypeOf(id);
    var store = if (T == ast.ExprId) a.exprs else if (T == ast.PatternId) a.pats else a.stmts;
    const kind_val = store.index.kinds.items[id.toRaw()];

    // Generic loc extraction dependent on kind enum
    const KindEnum = if (T == ast.ExprId) ast.ExprKind else if (T == ast.PatternId) ast.PatternKind else ast.StmtKind;
    inline for (@typeInfo(KindEnum).@"enum".fields) |field| {
        if (@intFromEnum(kind_val) == field.value) {
            const row = store.get(@enumFromInt(field.value), id);
            if (comptime @hasField(@TypeOf(row), "loc")) return .some(row.loc);
            return .none();
        }
    }
    return .none();
}

pub fn safeUndef(self: *LowerTir, blk: *Builder.BlockFrame, ty: types.TypeId, loc: tir.OptLocId) tir.ValueId {
    if (self.isVoid(ty) or self.context.type_store.getKind(ty) == .Any) {
        return blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false });
    }
    return blk.builder.tirValue(.ConstUndef, blk, ty, loc, .{});
}

fn exprDiagLoc(a: *ast.Ast, id: ast.ExprId) Loc {
    const loc_id = optLoc(a, id);
    return if (!loc_id.isNone()) a.exprs.locs.get(loc_id.unwrap()) else Loc{ .file_id = @intCast(a.file_id), .start = 0, .end = 0 };
}

fn ensureExprTypeNotError(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, id: ast.ExprId) anyerror!void {
    if (self.context.type_store.getKind(self.getExprType(ctx, a, id)) == .TypeError) {
        try self.context.diags.addError(exprDiagLoc(a, id), .tir_lowering_failed, .{});
        return error.LoweringBug;
    }
}

fn ensureExprTypeStamped(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, id: ast.ExprId) anyerror!void {
    if (self.lookupExprTypeOverride(ctx, id) != null) return;
    const idx = id.toRaw();
    if (idx >= a.type_info.expr_types.items.len or a.type_info.expr_types.items[idx] == null) return self.throwErr(exprDiagLoc(a, id));
}

fn callRuntimeAllocPtr(self: *LowerTir, blk: *Builder.BlockFrame, size_bytes: tir.ValueId, loc: tir.OptLocId) tir.ValueId {
    const ts = self.context.type_store;
    const opt_ptr_ty = ts.mkOptional(ts.mkPtr(ts.tVoid(), false));
    return self.optionalPayload(blk, opt_ptr_ty, blk.builder.call(blk, opt_ptr_ty, blk.builder.intern("rt_alloc"), &.{size_bytes}, loc), loc);
}

fn callRuntimeReallocPtr(self: *LowerTir, blk: *Builder.BlockFrame, old_ptr: tir.ValueId, size_bytes: tir.ValueId, loc: tir.OptLocId) tir.ValueId {
    const ts = self.context.type_store;
    const opt_ptr_ty = ts.mkOptional(ts.mkPtr(ts.tVoid(), false));
    return self.optionalPayload(blk, opt_ptr_ty, blk.builder.call(blk, opt_ptr_ty, blk.builder.intern("rt_realloc"), &.{ old_ptr, size_bytes }, loc), loc);
}

fn coerceArrayToDynArray(self: *LowerTir, blk: *Builder.BlockFrame, array_value: tir.ValueId, array_ty: types.TypeId, dyn_ty: types.TypeId, loc: tir.OptLocId) ?tir.ValueId {
    const ts = self.context.type_store;
    const arr = ts.get(.Array, array_ty);
    const dyn = ts.get(.DynArray, dyn_ty);
    const ptr_ty = ts.mkPtr(dyn.elem, false);
    const usize_ty = ts.tUsize();

    if (arr.len == 0) {
        const zero = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = 0 });
        return blk.builder.structMake(blk, dyn_ty, &[_]tir.Rows.StructFieldInit{
            .{ .index = 0, .name = .none(), .value = blk.builder.constNull(blk, ptr_ty, loc) },
            .{ .index = 1, .name = .none(), .value = zero },
            .{ .index = 2, .name = .none(), .value = zero },
        }, loc);
    }

    const len_u64 = @as(u64, @intCast(arr.len));
    const elem_size_u64 = @as(u64, @intCast(check_types.typeSize(self.context, dyn.elem)));
    const total_bytes = std.math.mul(u64, elem_size_u64, len_u64) catch return null;

    const data_ptr = blk.builder.tirValue(.CastBit, blk, ptr_ty, loc, .{ .value = self.callRuntimeAllocPtr(blk, blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = total_bytes }), loc) });

    for (0..arr.len) |idx| {
        const idx_u64 = @as(u64, @intCast(idx));
        var elem_val = blk.builder.indexOp(blk, arr.elem, array_value, blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = idx_u64 }), loc);
        if (!arr.elem.eq(dyn.elem)) elem_val = self.emitCoerce(blk, elem_val, arr.elem, dyn.elem, loc);
        _ = blk.builder.tirValue(.Store, blk, dyn.elem, loc, .{ .ptr = blk.builder.gep(blk, ptr_ty, data_ptr, &.{blk.builder.gepConst(idx_u64)}, loc), .value = elem_val, .@"align" = 0 });
    }

    const len_const = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = len_u64 });
    return blk.builder.structMake(blk, dyn_ty, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = data_ptr },
        .{ .index = 1, .name = .none(), .value = len_const },
        .{ .index = 2, .name = .none(), .value = len_const },
    }, loc);
}

fn coerceArrayToSlice(self: *LowerTir, blk: *Builder.BlockFrame, array_value: tir.ValueId, array_ty: types.TypeId, slice_ty: types.TypeId, loc: tir.OptLocId) tir.ValueId {
    const ts = self.context.type_store;
    const arr = ts.get(.Array, array_ty);
    const slice = ts.get(.Slice, slice_ty);
    const ptr_array_ty = ts.mkPtr(array_ty, false);

    // Spill array to stack
    const slot = blk.builder.tirValue(.Alloca, blk, ptr_array_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });
    _ = blk.builder.tirValue(.Store, blk, array_ty, loc, .{ .ptr = slot, .value = array_value, .@"align" = 0 });

    return blk.builder.structMake(blk, slice_ty, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = blk.builder.tirValue(.CastBit, blk, ts.mkPtr(slice.elem, slice.is_const), loc, .{ .value = slot }) },
        .{ .index = 1, .name = .none(), .value = blk.builder.tirValue(.ConstInt, blk, ts.tUsize(), loc, .{ .value = @as(u64, @intCast(arr.len)) }) },
    }, loc);
}
/// Insert an explicit coercion that realizes what the checker proved assignable/castable.
pub fn emitCoerce(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    v: tir.ValueId,
    got: types.TypeId,
    want: types.TypeId,
    loc: tir.OptLocId,
) tir.ValueId {
    if (got.eq(want)) return v;

    const ts = self.context.type_store;
    const gk = ts.getKind(got);
    const wk = ts.getKind(want);

    // Special-case: coercions between type handles (TypeType) are no-ops.
    if (gk == .TypeType and wk == .TypeType) return v;

    switch (wk) {
        .ErrorSet => return self.coerceToErrorSet(blk, v, got, want, loc),
        .Optional => return self.coerceToOptional(blk, v, got, want, loc),
        .DynArray => if (gk == .Array) {
            if (self.coerceArrayToDynArray(blk, v, got, want, loc)) |dyn_val| return dyn_val;
        },
        .Slice => if (gk == .Array) {
            return self.coerceArrayToSlice(blk, v, got, want, loc);
        },
        .Ptr => if (gk == .Ptr) {
            return blk.builder.tirValue(.CastBit, blk, want, loc, .{ .value = v });
        },
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64 => {
            switch (gk) {
                .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize, .F32, .F64 => {
                    return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = v });
                },
                else => {},
            }
        },
        else => {},
    }
    // Fallback: materialize/assignable
    return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = v });
}

fn coerceToErrorSet(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    v: tir.ValueId,
    got: types.TypeId,
    want: types.TypeId,
    loc: tir.OptLocId,
) tir.ValueId {
    const ts = self.context.type_store;
    const es = ts.get(.ErrorSet, want);

    // Determine tag and index directly
    var tag_value: u32 = 0;
    var field_index: u32 = 0;

    if (got.eq(es.error_ty)) {
        tag_value = 1;
        field_index = 1;
    } else if (!got.eq(es.value_ty)) {
        // Fallback if neither matches perfectly (e.g. coerce subtype)
        return blk.builder.tirValue(.CastNormal, blk, want, loc, .{ .value = v });
    }

    const payload_union_ty = ts.mkUnion(&[_]types.TypeStore.StructFieldArg{
        .{ .name = blk.builder.intern("Ok"), .ty = es.value_ty },
        .{ .name = blk.builder.intern("Err"), .ty = es.error_ty },
    });

    const tag = blk.builder.tirValue(.ConstInt, blk, ts.tI32(), loc, .{ .value = tag_value });
    const payload = blk.builder.tirValue(.UnionMake, blk, payload_union_ty, loc, .{
        .field_index = field_index,
        .value = v,
    });

    return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = tag },
        .{ .index = 1, .name = .none(), .value = payload },
    }, loc);
}

fn coerceToOptional(
    self: *LowerTir,
    blk: *Builder.BlockFrame,
    v: tir.ValueId,
    got: types.TypeId,
    want: types.TypeId,
    loc: tir.OptLocId,
) tir.ValueId {
    const ts = self.context.type_store;
    const opt = ts.get(.Optional, want);
    const want_ptr = ts.isOptionalPointer(want);

    if (ts.getKind(got) == .Optional) {
        const got_opt = ts.get(.Optional, got);
        // Case: ?U -> ?T. If elements match and ptr-ness matches, it's a no-op.
        if (got_opt.elem.eq(opt.elem) and want_ptr == ts.isOptionalPointer(got)) return v;

        if (want_ptr) {
            if (ts.isOptionalPointer(got)) {
                // Ptr -> Ptr bitcast/coerce
                var payload = blk.builder.tirValue(.CastBit, blk, got_opt.elem, loc, .{ .value = v });
                if (!got_opt.elem.eq(opt.elem)) {
                    payload = self.emitCoerce(blk, payload, got_opt.elem, opt.elem, loc);
                }
                return blk.builder.tirValue(.CastBit, blk, want, loc, .{ .value = payload });
            }
            // Struct -> Ptr
            const flag = self.optionalFlag(blk, got, v, loc);
            var payload = self.optionalPayload(blk, got, v, loc);
            payload = self.emitCoerce(blk, payload, got_opt.elem, opt.elem, loc);
            return self.optionalWrapWithFlag(blk, want, flag, payload, loc);
        }

        // Standard Struct Optional
        const flag = blk.builder.extractField(blk, ts.tBool(), v, 0, loc);
        var payload = blk.builder.extractField(blk, got_opt.elem, v, 1, loc);

        if (ts.getKind(got_opt.elem) == .Any) {
            payload = blk.builder.tirValue(.ConstUndef, blk, opt.elem, loc, .{});
        } else {
            payload = self.emitCoerce(blk, payload, got_opt.elem, opt.elem, loc);
        }

        return blk.builder.structMake(blk, want, &[_]tir.Rows.StructFieldInit{
            .{ .index = 0, .name = .none(), .value = flag },
            .{ .index = 1, .name = .none(), .value = payload },
        }, loc);
    }

    // Case: U -> ?T (Wrap Some)
    const payload = self.emitCoerce(blk, v, got, opt.elem, loc);
    return self.optionalWrapSome(blk, want, payload, loc);
}

// ============================
// Top-level lowering
// ============================

fn tryLowerNamedFunction(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    b: *Builder,
    did: ast.DeclId,
    base_name: StrId,
    should_mangle: bool,
    sig_override: ?types.TypeId,
) !void {
    const decl = a.exprs.Decl.get(did);
    if (a.kind(decl.value) != .FunctionLit) return;

    const fn_ty = sig_override orelse self.getExprType(ctx, a, decl.value);
    if (self.context.type_store.getKind(fn_ty) != .Function) return;

    const fn_lit = a.exprs.get(.FunctionLit, decl.value);
    if (fn_lit.flags.is_test) {
        _ = self.context.type_store.tTestError();
    }

    // Check for comptime parameters
    const params = a.exprs.param_pool.slice(fn_lit.params);
    for (params) |pid| {
        if (a.exprs.Param.get(pid).is_comptime) return;
    }

    const name = if (should_mangle) try self.qualifySymbolName(a, base_name) else base_name;
    try self.lowerFunction(ctx, a, b, name, decl.value, sig_override);
}

fn bindingNameOfPattern(a: *ast.Ast, pid: ast.PatternId) ?StrId {
    if (a.kind(pid) == .Binding) return a.pats.get(.Binding, pid).name;
    return null;
}

fn lowerSyntheticDecls(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, b: *Builder) !void {
    const syn_decls = a.type_info.synthetic_decls.items;
    for (syn_decls) |raw_id| {
        try self.lowerSingleSyntheticDecl(ctx, a, b, raw_id);
    }
}

const CallSpecSnapshotGuard = struct {
    backups: List(struct { raw: u32, prev: ?types.CallSpecialization }) = .{},
    applied: bool = false,

    fn init(self: *CallSpecSnapshotGuard, gpa: std.mem.Allocator, a: *ast.Ast, syn_did: ast.DeclId) !void {
        if (a.type_info.getSpecializationCallSnapshot(syn_did)) |call_snapshot| {
            self.applied = true;
            try self.backups.ensureTotalCapacity(gpa, call_snapshot.expr_ids.len);
            for (call_snapshot.expr_ids, 0..) |raw, idx| {
                const spec = call_snapshot.specs[idx];
                if (a.type_info.call_specializations.getEntry(raw)) |entry| {
                    self.backups.appendAssumeCapacity(.{ .raw = raw, .prev = entry.value_ptr.* });
                    entry.value_ptr.* = spec;
                } else {
                    self.backups.appendAssumeCapacity(.{ .raw = raw, .prev = null });
                    try a.type_info.call_specializations.put(gpa, raw, spec);
                }
            }
        }
    }

    fn deinit(self: *CallSpecSnapshotGuard, gpa: std.mem.Allocator, a: *ast.Ast) void {
        if (!self.applied) return;
        for (self.backups.items) |backup| {
            if (backup.prev) |prev_spec| {
                if (a.type_info.call_specializations.getEntry(backup.raw)) |entry| {
                    entry.value_ptr.* = prev_spec;
                }
            } else {
                _ = a.type_info.call_specializations.swapRemove(backup.raw);
            }
        }
        self.backups.deinit(gpa);
    }
};

const ComptimeExprSnapshotGuard = struct {
    backups: List(struct { raw: u32, prev: ?comp.ComptimeValue }) = .{},
    applied: bool = false,

    fn init(self: *ComptimeExprSnapshotGuard, gpa: std.mem.Allocator, a: *ast.Ast, syn_did: ast.DeclId) !void {
        if (a.type_info.getSpecializationComptimeExprSnapshot(syn_did)) |snapshot| {
            self.applied = true;
            try self.backups.ensureTotalCapacity(gpa, snapshot.expr_ids.len);
            for (snapshot.expr_ids, 0..) |raw, idx| {
                const expr_id = ast.ExprId.fromRaw(raw);
                const prev = if (a.type_info.getComptimeValue(expr_id)) |val| val.* else null;
                self.backups.appendAssumeCapacity(.{ .raw = raw, .prev = prev });

                const cloned = try comp.cloneComptimeValue(a.type_info.gpa, snapshot.values[idx]);
                if (a.type_info.comptime_values.getEntry(expr_id)) |entry| {
                    entry.value_ptr.* = cloned;
                } else {
                    try a.type_info.setComptimeValue(expr_id, cloned);
                }
            }
        }
    }

    fn deinit(self: *ComptimeExprSnapshotGuard, gpa: std.mem.Allocator, a: *ast.Ast) void {
        if (!self.applied) return;
        for (self.backups.items) |backup| {
            const expr_id = ast.ExprId.fromRaw(backup.raw);
            if (backup.prev) |prev_val| {
                if (a.type_info.comptime_values.getEntry(expr_id)) |entry| {
                    entry.value_ptr.* = prev_val;
                } else {
                    a.type_info.setComptimeValue(expr_id, prev_val) catch @panic("OOM");
                }
            } else {
                _ = a.type_info.comptime_values.swapRemove(expr_id);
            }
        }
        self.backups.deinit(gpa);
    }
};

const ComptimeBindingSnapshotGuard = struct {
    backups: List(struct { name: StrId, prev_ty: ?types.TypeId, prev_val: ?comp.ComptimeValue }) = .{},
    applied: bool = false,

    fn init(self: *ComptimeBindingSnapshotGuard, gpa: std.mem.Allocator, a: *ast.Ast, syn_did: ast.DeclId) !void {
        if (a.type_info.getSpecializationComptimeSnapshot(syn_did)) |snapshot| {
            self.applied = true;
            const names = snapshot.names;
            try self.backups.ensureTotalCapacity(gpa, names.len);

            for (names, 0..) |name, idx| {
                const prev_ty = a.type_info.lookupComptimeBindingType(name);
                const prev_val = a.type_info.cloneComptimeBindingValue(gpa, name) catch null;
                self.backups.appendAssumeCapacity(.{ .name = name, .prev_ty = prev_ty, .prev_val = prev_val });

                const cloned_val = try comp.cloneComptimeValue(gpa, snapshot.values[idx]);
                try a.type_info.setComptimeBinding(name, snapshot.types[idx], cloned_val);
            }
        }
    }

    fn deinit(self: *ComptimeBindingSnapshotGuard, gpa: std.mem.Allocator, a: *ast.Ast) void {
        if (!self.applied) return;
        for (self.backups.items) |backup| {
            a.type_info.removeComptimeBinding(backup.name);
            if (backup.prev_ty) |pty| {
                if (backup.prev_val) |*pval| {
                    const cloned = comp.cloneComptimeValue(gpa, pval.*) catch @panic("OOM");
                    a.type_info.setComptimeBinding(backup.name, pty, cloned) catch @panic("OOM");
                }
            }
            if (backup.prev_val) |pval| {
                var val = pval;
                val.destroy(gpa);
            }
        }
        self.backups.deinit(gpa);
    }
};

fn lowerSingleSyntheticDecl(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, b: *Builder, raw_id: u32) !void {
    const syn_did = ast.DeclId.fromRaw(raw_id);
    const orig_did = self.findOriginalDeclForSynthetic(a, syn_did) orelse return;
    const decl = a.exprs.Decl.get(orig_did);

    if (a.kind(decl.value) != .FunctionLit) return;

    var base_name: ?StrId = null;
    if (!decl.pattern.isNone()) {
        base_name = bindingNameOfPattern(a, decl.pattern.unwrap());
    } else if (!decl.method_path.isNone()) {
        base_name = try self.methodSymbolShortName(a, orig_did);
    }
    const base = base_name orelse return;

    // Generate specialized name
    const spec_name_str = try std.fmt.allocPrint(self.gpa, "{s}_spec_{d}", .{ self.context.type_store.strs.get(base), raw_id });
    defer self.gpa.free(spec_name_str);
    const qualified_name = try self.qualifySymbolName(a, self.context.type_store.strs.intern(spec_name_str));

    if (raw_id >= a.type_info.decl_types.items.len) return;
    const spec_sig = a.type_info.decl_types.items[raw_id] orelse return;

    // 1. Apply Expression Type Overrides
    var pushed_override = false;
    if (a.type_info.getSpecializationExprSnapshot(syn_did)) |snapshot| {
        try self.pushExprTypeOverrideFrame(ctx);
        pushed_override = true;
        for (snapshot.expr_ids, 0..) |raw_expr_id, i| {
            try self.noteExprType(ctx, ast.ExprId.fromRaw(raw_expr_id), snapshot.expr_types[i]);
        }
    }
    defer if (pushed_override) self.popExprTypeOverrideFrame(ctx);

    // 2. Apply Call Specialization Snapshot
    var call_spec_guard = CallSpecSnapshotGuard{};
    try call_spec_guard.init(self.gpa, a, syn_did);
    defer call_spec_guard.deinit(self.gpa, a);

    // 3. Apply Comptime Expr Snapshot
    var comptime_expr_guard = ComptimeExprSnapshotGuard{};
    try comptime_expr_guard.init(self.gpa, a, syn_did);
    defer comptime_expr_guard.deinit(self.gpa, a);

    // 4. Apply Comptime Binding Snapshot
    var comptime_guard = ComptimeBindingSnapshotGuard{};
    try comptime_guard.init(self.gpa, a, syn_did);
    defer comptime_guard.deinit(self.gpa, a);

    try self.lowerFunction(ctx, a, b, qualified_name, decl.value, spec_sig);
}

fn isTopLevelDecl(a: *ast.Ast, did: ast.DeclId) bool {
    const decls = a.exprs.decl_pool.slice(a.unit.decls);
    for (decls) |top| {
        if (top.eq(did)) return true;
    }
    return false;
}

fn lowerRegisteredMethods(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, b: *Builder) !void {
    var it = self.context.type_store.method_table.iterator();
    while (it.next()) |entry| {
        try self.lowerSingleRegisteredMethod(ctx, a, b, entry.value_ptr.*);
    }
}

fn lowerSingleRegisteredMethod(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, b: *Builder, method: types.MethodEntry) !void {
    if (method.decl_ast != a) return;
    if (method.builtin != null) return;
    if (isTopLevelDecl(a, method.decl_id)) return;

    _ = a.type_info.applyMethodExprSnapshot(method.owner_type, method.method_name);

    const decl = a.exprs.Decl.get(method.decl_id);
    if (a.kind(decl.value) != .FunctionLit) return;

    const base_name = try self.methodSymbolName(a, method.decl_id, method.owner_type);
    try self.tryLowerNamedFunction(ctx, a, b, method.decl_id, base_name, true, method.func_type);
}

fn lowerTopDecl(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, b: *Builder, did: ast.DeclId) !void {
    const d = a.exprs.Decl.get(did);
    const kind = a.kind(d.value);

    // 1. MLIR Blocks
    if (kind == .MlirBlock and d.pattern.isNone()) return;

    // 2. Functions (Methods or Standard Functions)
    if (kind == .FunctionLit and !a.exprs.get(.FunctionLit, d.value).flags.is_extern) {
        var name_opt: ?StrId = null;
        if (!d.method_path.isNone()) {
            name_opt = try methodSymbolShortName(self, a, did);
        } else if (!d.pattern.isNone()) {
            name_opt = bindingNameOfPattern(a, d.pattern.unwrap());
        }

        if (name_opt) |nm| {
            if (self.test_mode and self.isMainPackageName(a)) {
                if (std.mem.eql(u8, self.context.type_store.strs.get(nm), "main")) return;
            }

            const is_method = !d.method_path.isNone();
            const method_entry = if (is_method) self.methodEntryForDecl(a, did) else null;
            var owner_ty_fallback: ?types.TypeId = null;

            if (is_method and method_entry == null) {
                const fn_ty = self.getExprType(ctx, a, d.value);
                const ts = self.context.type_store;
                if (ts.getKind(fn_ty) == .Function) {
                    const fn_info = ts.get(.Function, fn_ty);
                    const params = ts.type_pool.slice(fn_info.params);
                    if (params.len > 0) {
                        const p0 = params[0];
                        owner_ty_fallback = if (ts.getKind(p0) == .Ptr) ts.get(.Ptr, p0).elem else p0;
                    }
                }
                if (owner_ty_fallback == null) return;
            } else if (method_entry) |entry| {
                owner_ty_fallback = entry.owner_type;
            }

            if (is_method and owner_ty_fallback == null) return;

            const base_name = if (owner_ty_fallback) |oty|
                try self.methodSymbolName(a, did, oty)
            else
                nm;

            try self.tryLowerNamedFunction(ctx, a, b, did, base_name, true, null);
        }
        return;
    }

    // 3. Globals
    if (!d.pattern.isNone()) {
        const nm = try self.symbolNameForDecl(a, did) orelse return;
        const ty = getDeclType(a, did) orelse return;

        if (self.context.type_store.getKind(ty) == .TypeType) return;

        if (try self.constInitFromExpr(ctx, a, d.value, ty)) |ci| {
            _ = b.addGlobalWithInit(nm, ty, ci);
        } else {
            _ = b.addGlobal(nm, ty);
        }
    }
}

fn lowerAttrs(self: *LowerTir, a: *ast.Ast, b: *Builder, range: ast.OptRangeAttr) !tir.RangeAttribute {
    if (range.isNone()) return .empty();

    const attrs = a.exprs.attr_pool.slice(range.asRange());
    var attr_list: List(tir.AttributeId) = .empty;
    defer attr_list.deinit(self.gpa);

    for (attrs) |aid| {
        const arow = a.exprs.Attribute.get(aid);
        const val_id = if (!arow.value.isNone()) try self.lowerAttributeValue(a, b, arow.value.unwrap()) else tir.OptValueId.none();
        try attr_list.append(self.gpa, b.t.instrs.Attribute.add(self.gpa, .{ .name = arow.name, .value = val_id }));
    }
    return b.t.instrs.attribute_pool.pushMany(self.gpa, attr_list.items);
}

fn lowerAttributeValue(self: *LowerTir, a: *ast.Ast, b: *Builder, val_expr: ast.ExprId) !tir.OptValueId {
    if (try self.getCachedComptimeValue(a, val_expr)) |cv| {
        var owned_cv = cv;
        defer owned_cv.destroy(self.gpa);

        const vid = b.freshValue();
        const ts = self.context.type_store;
        const iid: tir.InstrId = switch (owned_cv) {
            .Int => |v| b.t.instrs.add(.ConstInt, .{ .result = vid, .ty = ts.tI64(), .value = v, .loc = .none() }),
            .Float => |v| b.t.instrs.add(.ConstFloat, .{ .result = vid, .ty = ts.tF64(), .value = v, .loc = .none() }),
            .Bool => |v| b.t.instrs.add(.ConstBool, .{ .result = vid, .ty = ts.tBool(), .value = v, .loc = .none() }),
            .String => |s| b.t.instrs.add(.ConstString, .{ .result = vid, .ty = ts.tString(), .text = b.intern(s), .loc = .none() }),
            else => return .none(),
        };

        const raw_vid = vid.toRaw();
        try b.t.value_defs.ensureTotalCapacity(b.allocator, raw_vid + 1);
        if (b.t.value_defs.items.len <= raw_vid) {
            // Using maxInt as placeholder for undefined/uninitialized
            b.t.value_defs.appendNTimesAssumeCapacity(tir.InstrId.fromRaw(std.math.maxInt(u32)), raw_vid + 1 - b.t.value_defs.items.len);
        }
        b.t.value_defs.items[raw_vid] = iid;

        return .some(vid);
    }
    return .none();
}

pub fn lowerFunction(
    self: *LowerTir,
    lower_ctx: *LowerContext,
    a: *ast.Ast,
    b: *Builder,
    name: StrId,
    fun_eid: ast.ExprId,
    sig_override: ?types.TypeId,
) !void {
    const fid = sig_override orelse self.getExprType(lower_ctx, a, fun_eid);
    const ts = self.context.type_store;
    if (ts.getKind(fid) != .Function) return;
    const fnty = ts.get(.Function, fid);

    const fnr = a.exprs.get(.FunctionLit, fun_eid);
    const fn_loc = tir.OptLocId.some(fnr.loc);

    try self.pushExprTypeOverrideFrame(lower_ctx);
    defer self.popExprTypeOverrideFrame(lower_ctx);

    const flags = self.parseFunctionAttributes(a, fnr.attrs);
    if (flags.is_mlir_fn) return;

    if (!fnr.body.isNone()) {
        if (!self.shouldLowerBody(lower_ctx, a, fnr.body.unwrap())) return;
    }

    const attrs = try self.lowerAttrs(a, b, fnr.attrs);
    const raw_asm: cst.OptStrId = if (fnr.raw_asm.isNone()) .none() else .some(b.intern(a.exprs.strs.get(fnr.raw_asm.unwrap())));

    var f = try b.beginFunction(
        self.context,
        name,
        fnty.result,
        fnty.is_variadic,
        fnty.is_extern,
        attrs,
        flags.is_triton,
        fnr.flags.is_async,
        raw_asm,
    );

    const params = a.exprs.param_pool.slice(fnr.params);
    const runtime_param_tys = ts.type_pool.slice(fnty.params);

    try self.setupFunctionParams(a, b, &f, params, runtime_param_tys);

    var blk = try b.beginBlock(&f);
    var env = cf.Env{};
    defer env.deinit(self.gpa);

    try self.bindFunctionParams(a, b, &env, &f, &blk, params, runtime_param_tys);

    if (!fnr.body.isNone()) {
        const body_id = fnr.body.unwrap();
        try env.pushScope(self.gpa);
        defer _ = env.popScope(self.gpa);
        try self.lowerExprAsStmtList(lower_ctx, a, &env, &f, &blk, body_id);
    }

    if (blk.term.isNone()) {
        try b.setReturn(&blk, .none(), fn_loc);
    }

    try b.endBlock(&f, blk);
    try b.endFunction(f);
}

const FnFlags = struct { is_triton: bool, is_mlir_fn: bool };

fn parseFunctionAttributes(_: *LowerTir, a: *ast.Ast, attrs_opt: ast.OptRangeAttr) FnFlags {
    if (attrs_opt.isNone()) return .{ .is_triton = false, .is_mlir_fn = false };
    const attrs = a.exprs.attr_pool.slice(attrs_opt.asRange());
    const mlir_fn_str = a.exprs.strs.intern("mlir_fn");
    const triton_fn_sid = a.exprs.strs.intern("triton");
    const triton_kernel_sid = a.exprs.strs.intern("triton_kernel");

    var flags = FnFlags{ .is_triton = false, .is_mlir_fn = false };
    for (attrs) |aid| {
        const name = a.exprs.Attribute.get(aid).name;
        if (name.eq(mlir_fn_str)) flags.is_mlir_fn = true;
        if (name.eq(triton_fn_sid) or name.eq(triton_kernel_sid)) flags.is_triton = true;
    }
    return flags;
}

fn shouldLowerBody(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, body_id: ast.ExprId) bool {
    const has_override = self.lookupExprTypeOverride(ctx, body_id) != null;
    const raw = body_id.toRaw();
    // Use unsafe access if we can guarantee bounds, otherwise standard check
    if (raw < a.type_info.expr_types.items.len) {
        return has_override or a.type_info.expr_types.items[raw] != null;
    }
    return has_override;
}

fn setupFunctionParams(_: *LowerTir, a: *ast.Ast, b: *Builder, f: *Builder.FunctionFrame, params: []const ast.ParamId, runtime_tys: []const types.TypeId) !void {
    for (params, 0..) |pid, i| {
        const p = a.exprs.Param.get(pid);
        const pname = if (!p.pat.isNone()) bindingNameOfPattern(a, p.pat.unwrap()) else null;
        _ = try b.addParam(f, pname, runtime_tys[i]);
    }
}

fn bindFunctionParams(self: *LowerTir, a: *ast.Ast, b: *Builder, env: *cf.Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, params: []const ast.ParamId, runtime_tys: []const types.TypeId) !void {
    const param_vals = f.param_vals.items;
    for (params, 0..) |pid, i| {
        const p = a.exprs.Param.get(pid);
        if (!p.pat.isNone()) {
            if (bindingNameOfPattern(a, p.pat.unwrap())) |pname| {
                try env.bind(self.gpa, pname, .{ .value = param_vals[i], .ty = runtime_tys[i], .is_slot = false }, b, blk, optLoc(a, p.pat.unwrap()));
            }
        }
    }
}

pub fn lowerExprAsStmtList(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
) !void {
    if (a.kind(id) != .Block) {
        _ = try self.lowerExpr(ctx, a, env, f, blk, id, null, .rvalue);
        return;
    }

    const b_node = a.exprs.get(.Block, id);
    const start: u32 = @intCast(env.defers.items.len);

    try env.pushScope(self.gpa);
    defer _ = env.popScope(self.gpa);

    for (a.stmts.stmt_pool.slice(b_node.items)) |sid| {
        if (!blk.term.isNone()) break;
        try self.lowerStmt(ctx, a, env, f, blk, sid);
    }

    if (blk.term.isNone()) {
        const slice = env.defers.items[start..];
        if (slice.len > 0) try cf.emitDefers(self, ctx, a, env, f, blk, slice, false);
    }
    env.defers.items.len = start;
}

fn lowerDecl(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    const drow = a.stmts.get(.Decl, sid);
    const d = a.exprs.Decl.get(drow.decl);

    if (!d.method_path.isNone() and a.kind(d.value) == .FunctionLit) return;

    const value_ty = self.getExprType(ctx, a, d.value);
    const decl_ty = getDeclType(a, drow.decl) orelse value_ty;

    if (!d.pattern.isNone()) {
        try self.destructureDeclFromExpr(ctx, a, env, f, blk, d.pattern.unwrap(), d.value, decl_ty, !d.flags.is_const);
    } else {
        if (!d.method_path.isNone() and a.kind(d.value) == .FunctionLit) return;
        _ = try self.lowerExpr(ctx, a, env, f, blk, d.value, decl_ty, .rvalue);
    }
}

fn lowerReturn(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    try self.lowerReturnCommon(ctx, a, env, f, blk, a.stmts.get(.Return, sid).value, optLoc(a, sid));
}

fn lowerReturnCommon(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    value_opt: ast.OptExprId,
    stmt_loc: tir.OptLocId,
) !void {
    if (value_opt.isNone()) {
        try cf.runNormalDefersFrom(self, ctx, a, env, f, blk, 0);
        try f.builder.setReturnVoid(blk, stmt_loc);
        return;
    }

    const value_expr = value_opt.unwrap();
    var expect = f.builder.t.funcs.Function.get(f.id).result;
    const ts = self.context.type_store;

    // Unwrap future result type if async
    if (f.builder.t.funcs.Function.get(f.id).is_async and ts.getKind(expect) == .Future) {
        expect = ts.get(.Future, expect).elem;
    }

    const v = try self.lowerExpr(ctx, a, env, f, blk, value_expr, expect, .rvalue);
    const value_loc = optLoc(a, value_expr);

    if (ts.getKind(expect) == .ErrorSet and cf.hasErrDefersFrom(self, env, 0)) {
        try self.emitReturnWithErrDefers(ctx, a, env, f, blk, v, value_loc, stmt_loc, 0);
    } else {
        try cf.runNormalDefersFrom(self, ctx, a, env, f, blk, 0);
        try f.builder.setReturnVal(blk, v, stmt_loc);
    }
}

fn emitReturnWithErrDefers(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    v: tir.ValueId,
    value_loc: tir.OptLocId,
    stmt_loc: tir.OptLocId,
    defer_mark: u32,
) !void {
    var err_blk = try f.builder.beginBlock(f);
    var ok_blk = try f.builder.beginBlock(f);

    const tag_ty = self.context.type_store.tI32();
    const tag = blk.builder.extractField(blk, tag_ty, v, 0, value_loc);
    const zero = blk.builder.tirValue(.ConstInt, blk, tag_ty, value_loc, .{ .value = 0 });
    const is_err = blk.builder.binBool(blk, .CmpNe, tag, zero, value_loc);

    try f.builder.condBr(blk, self.forceLocalCond(blk, is_err, value_loc), err_blk.id, &.{}, ok_blk.id, &.{}, stmt_loc);

    const defer_slice = env.defers.items[defer_mark..];

    // Error Path: run both normal and error defers
    try cf.emitDefers(self, ctx, a, env, f, &err_blk, defer_slice, true);
    try cf.emitDefers(self, ctx, a, env, f, &err_blk, defer_slice, false);
    try f.builder.setReturnVal(&err_blk, v, stmt_loc);
    try f.builder.endBlock(f, err_blk);

    // OK Path: run only normal defers
    try cf.emitDefers(self, ctx, a, env, f, &ok_blk, defer_slice, false);
    try f.builder.setReturnVal(&ok_blk, v, stmt_loc);
    try f.builder.endBlock(f, ok_blk);

    env.defers.items.len = defer_mark;
}

pub fn sliceRestValue(
    self: *LowerTir,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    value: tir.ValueId,
    vty: types.TypeId,
    elem_ty: types.TypeId,
    rest_index: u32,
    loc: tir.OptLocId,
) struct { val: tir.ValueId, ty: types.TypeId } {
    const ts = self.context.type_store;
    const slice_ty = ts.mkSlice(elem_ty, if (ts.getKind(vty) == .Slice) ts.get(.Slice, vty).is_const else false);
    const len_val = if (ts.getKind(vty) == .Array)
        blk.builder.tirValue(.ConstInt, blk, ts.tUsize(), loc, .{ .value = ts.get(.Array, vty).len })
    else
        blk.builder.extractFieldNamed(blk, ts.tUsize(), value, f.builder.intern("len"), loc);
    const range_val = blk.builder.rangeMake(
        blk,
        ts.mkSlice(ts.tUsize(), false),
        blk.builder.tirValue(.ConstInt, blk, ts.tUsize(), loc, .{ .value = rest_index }),
        len_val,
        blk.builder.tirValue(.ConstBool, blk, ts.tBool(), loc, .{ .value = false }),
        loc,
    );
    return .{ .val = blk.builder.indexOp(blk, slice_ty, value, range_val, loc), .ty = slice_ty };
}

fn lowerAssignPattern(
    self: *LowerTir,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    pid: ast.PatternId,
    value: tir.ValueId,
    vty: types.TypeId,
) anyerror!void {
    switch (a.kind(pid)) {
        .Wildcard => return,
        .Binding => {
            const name = a.pats.get(.Binding, pid).name;
            const loc = optLoc(a, pid);
            const ptr = try self.lowerIdentAddrByName(a, env, f, blk, name, vty, vty, loc);
            _ = f.builder.tirValue(.Store, blk, vty, loc, .{ .ptr = ptr, .value = value, .@"align" = 0 });
        },
        .Tuple => {
            const elems = a.pats.pat_pool.slice(a.pats.get(.Tuple, pid).elems);
            const tuple_elems = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, vty).elems);
            for (elems, 0..) |e, i| {
                const ety = tuple_elems[i];
                const elem_loc = optLoc(a, e);
                const elem_val = blk.builder.extractElem(blk, ety, value, @intCast(i), elem_loc);
                try self.lowerAssignPattern(a, env, f, blk, e, elem_val, ety);
            }
        },
        .Struct => {
            const fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, vty).fields);
            for (a.pats.field_pool.slice(a.pats.get(.Struct, pid).fields)) |fid| {
                const pf = a.pats.StructField.get(fid);
                const idx = self.getFieldIndex(vty, pf.name) orelse return error.LoweringBug;
                const fty = self.context.type_store.Field.get(fields[idx]).ty;
                const field_loc = optLoc(a, pf.pattern);
                const elem_val = blk.builder.extractField(blk, fty, value, idx, field_loc);
                try self.lowerAssignPattern(a, env, f, blk, pf.pattern, elem_val, fty);
            }
        },
        .Slice => {
            const ts = self.context.type_store;
            const elem_ty = switch (ts.getKind(vty)) {
                .Array => ts.get(.Array, vty).elem,
                .Slice => ts.get(.Slice, vty).elem,
                .DynArray => ts.get(.DynArray, vty).elem,
                else => ts.tAny(),
            };
            const sl = a.pats.get(.Slice, pid);
            const elems = a.pats.pat_pool.slice(sl.elems);
            for (elems, 0..) |e, i| {
                if (sl.has_rest and i == sl.rest_index) continue;
                const elem_loc = optLoc(a, e);
                const idx_val = blk.builder.tirValue(.ConstInt, blk, ts.tUsize(), elem_loc, .{ .value = @as(u64, @intCast(i)) });
                const elem_val = blk.builder.indexOp(blk, elem_ty, value, idx_val, elem_loc);
                try self.lowerAssignPattern(a, env, f, blk, e, elem_val, elem_ty);
            }
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const loc = optLoc(a, pid);
                const rest = self.sliceRestValue(f, blk, value, vty, elem_ty, sl.rest_index, loc);
                try self.lowerAssignPattern(a, env, f, blk, sl.rest_binding.unwrap(), rest.val, rest.ty);
            }
        },
        else => return error.LoweringBug,
    }
}

fn lowerAssign(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    const as = a.stmts.get(.Assign, sid);

    switch (as.left) {
        .expr => |left_expr| {
            // 1. Handle discard: `_ = rhs`
            if (a.kind(left_expr) == .Ident) {
                if (std.mem.eql(u8, a.exprs.strs.get(a.exprs.get(.Ident, left_expr).name), "_")) {
                    _ = try self.lowerExpr(ctx, a, env, f, blk, as.right, null, .rvalue);
                    return;
                }
            }

            const rty = self.getExprType(ctx, a, left_expr);
            const stmt_loc = optLoc(a, sid);

            // 2. Handle simple local assignment optimization
            if (a.kind(left_expr) == .Ident) {
                const name = a.exprs.get(.Ident, left_expr).name;
                if (env.lookup(name)) |bnd| {
                    if (!bnd.is_slot) {
                        const rhs = try self.lowerExpr(ctx, a, env, f, blk, as.right, rty, .rvalue);
                        try env.bind(self.gpa, name, .{ .value = rhs, .ty = rty, .is_slot = false }, f.builder, blk, stmt_loc);
                        return;
                    }
                }
            }

            // 3. General L-Value Store
            const lhs_ptr = try self.lowerExpr(ctx, a, env, f, blk, left_expr, null, .lvalue_addr);
            const rhs = try self.lowerExpr(ctx, a, env, f, blk, as.right, rty, .rvalue);
            _ = f.builder.tirValue(.Store, blk, rty, stmt_loc, .{ .ptr = lhs_ptr, .value = rhs, .@"align" = 0 });
        },
        .pattern => |pid| {
            const rhs_ty = self.getExprType(ctx, a, as.right);
            const rhs_val = try self.lowerExpr(ctx, a, env, f, blk, as.right, rhs_ty, .rvalue);
            try self.lowerAssignPattern(a, env, f, blk, pid, rhs_val, rhs_ty);
        },
    }
}

fn lowerStmt(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    sid: ast.StmtId,
) !void {
    switch (a.kind(sid)) {
        .Expr => _ = try self.lowerExpr(ctx, a, env, f, blk, a.stmts.get(.Expr, sid).expr, null, .rvalue),
        .Defer => try env.defers.append(self.gpa, .{ .expr = a.stmts.get(.Defer, sid).expr, .is_err = false }),
        .ErrDefer => try env.defers.append(self.gpa, .{ .expr = a.stmts.get(.ErrDefer, sid).expr, .is_err = true }),
        .Break => try cf.lowerBreak(self, ctx, a, env, f, blk, sid),
        .Continue => try cf.lowerContinue(self, ctx, a, env, f, blk, sid),
        .Decl => try self.lowerDecl(ctx, a, env, f, blk, sid),
        .Assign => try self.lowerAssign(ctx, a, env, f, blk, sid),
        .Return => try self.lowerReturn(ctx, a, env, f, blk, sid),
        .Unreachable => try f.builder.setUnreachable(blk, optLoc(a, sid)),
        else => @panic("unhandled stmt kind"),
    }
}

// ============================
// Expressions
// ============================

const CalleeInfo = struct {
    name: StrId,
    qualified_name: ?StrId,
    fty: ?types.TypeId,
    expr: ast.ExprId,
};

fn resolveTypeArg(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, expr: ast.ExprId) ?types.TypeId {
    const ty = self.getExprType(ctx, a, expr);
    if (self.context.type_store.getKind(ty) == .TypeType) {
        return self.context.type_store.get(.TypeType, ty).of;
    }
    return null;
}

fn methodSymbolShortName(self: *LowerTir, a: *ast.Ast, did: ast.DeclId) !StrId {
    const decl = a.exprs.Decl.get(did);
    const seg_ids = a.exprs.method_path_pool.slice(decl.method_path.asRange());
    const owner_name = a.exprs.strs.get(a.exprs.MethodPathSeg.get(seg_ids[0]).name);
    const method_name = a.exprs.strs.get(a.exprs.MethodPathSeg.get(seg_ids[seg_ids.len - 1]).name);
    const symbol = try std.fmt.allocPrint(self.gpa, "{s}__{s}", .{ owner_name, method_name });
    defer self.gpa.free(symbol);
    return self.context.type_store.strs.intern(symbol);
}

fn findOriginalDeclForSynthetic(self: *LowerTir, a: *ast.Ast, syn_id: ast.DeclId) ?ast.DeclId {
    if (a.file_id >= self.chk.checker_ctx.items.len) return null;
    if (self.chk.checker_ctx.items[a.file_id]) |ctx| {
        var it = ctx.specialization_cache.iterator();
        while (it.next()) |entry| {
            if (entry.value_ptr.*.eq(syn_id)) return ast.DeclId.fromRaw(entry.key_ptr.original_decl_id);
        }
    }
    return null;
}

/// Compute a lowered symbol name for method `did` bound to `owner_type`, ensuring uniqueness.
pub fn methodSymbolName(
    self: *LowerTir,
    a: *ast.Ast,
    did: ast.DeclId,
    owner_type: types.TypeId,
) !StrId {
    const short_name = try methodSymbolShortName(self, a, did);
    const short_str = self.context.type_store.strs.get(short_name);

    var buf: [256]u8 = undefined;
    const text = std.fmt.bufPrint(&buf, "{s}_T{d}", .{ short_str, owner_type.toRaw() }) catch |err| switch (err) {
        error.NoSpaceLeft => {
            const allocated = try std.fmt.allocPrint(self.gpa, "{s}_T{d}", .{ short_str, owner_type.toRaw() });
            defer self.gpa.free(allocated);
            return self.context.type_store.strs.intern(allocated);
        },
        else => return err,
    };

    return self.context.type_store.strs.intern(text);
}

fn methodEntryForDecl(self: *LowerTir, a: *ast.Ast, decl_id: ast.DeclId) ?*types.MethodEntry {
    var it = self.context.type_store.method_table.iterator();
    while (it.next()) |entry| {
        const method = entry.value_ptr;
        if (method.decl_id.eq(decl_id) and method.decl_ast == a) return method;
    }
    return null;
}

/// Arrange arguments and runtime metadata before lowering a method or builtin call.
fn prepareMethodCall(
    self: *LowerTir,
    a: *ast.Ast,
    row: ast.Rows.Call,
    binding: types.MethodBinding,
    callee: *CalleeInfo,
    callee_name: *[]const u8,
    method_decl_id: *?ast.DeclId,
    method_binding_out: *?types.MethodBinding,
    arg_ids: *[]const ast.ExprId,
    method_arg_buf: *[]ast.ExprId,
) !void {
    if (binding.builtin) |_| {
        callee.fty = binding.func_type;
        method_decl_id.* = null;
        method_binding_out.* = binding;

        if (!binding.requires_implicit_receiver) return;

        std.debug.assert(a.kind(row.callee) == .FieldAccess);
        const field_expr = a.exprs.get(.FieldAccess, row.callee);

        const req_len = arg_ids.*.len + 1;
        if (method_arg_buf.*.len < req_len) {
            if (method_arg_buf.*.len > 0) self.gpa.free(method_arg_buf.*);
            method_arg_buf.* = try self.gpa.alloc(ast.ExprId, req_len);
        }

        method_arg_buf.*[0] = field_expr.parent;
        @memcpy(method_arg_buf.*[1..], arg_ids.*);
        arg_ids.* = method_arg_buf.*;
        return;
    }

    const symbol_ast = binding.decl_ast;
    const base_symbol = try self.methodSymbolName(symbol_ast, binding.decl_id, binding.owner_type);
    const symbol = try self.qualifySymbolName(symbol_ast, base_symbol);

    callee.name = symbol;
    callee.fty = binding.func_type;
    method_binding_out.* = binding;
    callee_name.* = self.context.type_store.strs.get(callee.name);
    method_decl_id.* = binding.decl_id;

    if (!binding.requires_implicit_receiver) return;

    std.debug.assert(a.kind(row.callee) == .FieldAccess);
    const field_expr = a.exprs.get(.FieldAccess, row.callee);

    const req_len = arg_ids.*.len + 1;
    if (method_arg_buf.*.len < req_len) {
        if (method_arg_buf.*.len > 0) self.gpa.free(method_arg_buf.*);
        method_arg_buf.* = try self.gpa.alloc(ast.ExprId, req_len);
    }

    method_arg_buf.*[0] = field_expr.parent;
    @memcpy(method_arg_buf.*[1..], arg_ids.*);
    arg_ids.* = method_arg_buf.*;
}

/// Try to resolve the binding represented by a field-access into an actual method entry.
fn synthesizeMethodBinding(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    field_expr_id: ast.ExprId,
) !?types.MethodBinding {
    if (a.kind(field_expr_id) != .FieldAccess) return null;

    const field_expr = a.exprs.get(.FieldAccess, field_expr_id);
    try self.ensureExprTypeStamped(ctx, a, field_expr.parent);

    const raw_ty = self.getExprType(ctx, a, field_expr.parent);
    const receiver_ty = (try self.refineExprType(ctx, a, env, field_expr.parent, raw_ty)) orelse return null;

    var owner_ty = receiver_ty;
    const parent_kind = self.context.type_store.getKind(receiver_ty);

    switch (parent_kind) {
        .Ptr => owner_ty = self.context.type_store.get(.Ptr, receiver_ty).elem,
        .TypeType => owner_ty = self.context.type_store.get(.TypeType, receiver_ty).of,
        else => {},
    }

    const entry = self.context.type_store.getMethod(owner_ty, field_expr.field) orelse return null;

    const wants_receiver = entry.receiver_kind != .none;
    const implicit_receiver = wants_receiver and parent_kind != .TypeType;
    var needs_addr_of = false;

    if (implicit_receiver) {
        switch (entry.receiver_kind) {
            .none => {},
            .value => if (!receiver_ty.eq(owner_ty)) return null,
            .pointer, .pointer_const => {
                if (parent_kind == .Ptr) {
                    const ptr_row = self.context.type_store.get(.Ptr, receiver_ty);
                    if (!ptr_row.elem.eq(owner_ty)) return null;
                } else if (receiver_ty.eq(owner_ty)) {
                    needs_addr_of = true;
                } else return null;
            },
        }
    }

    return types.MethodBinding{
        .owner_type = entry.owner_type,
        .method_name = entry.method_name,
        .decl_id = entry.decl_id,
        .decl_ast = entry.decl_ast,
        .func_type = entry.func_type,
        .self_param_type = entry.self_param_type,
        .receiver_kind = entry.receiver_kind,
        .requires_implicit_receiver = implicit_receiver,
        .needs_addr_of = needs_addr_of,
        .builtin = entry.builtin,
    };
}

/// Resolve the name that should be used when calling `field_expr_id`, accounting for imports.
fn resolveFieldAccessName(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, field_expr_id: ast.ExprId) ast.StrId {
    const field_access = a.exprs.get(.FieldAccess, field_expr_id);
    const parent_ty = self.getExprType(ctx, a, field_access.parent);

    if (self.context.type_store.getKind(parent_ty) != .Ast) return field_access.field;

    const ast_ty = self.context.type_store.get(.Ast, parent_ty);
    const pkg_name = self.context.interner.get(ast_ty.pkg_name);
    const filepath = self.context.interner.get(ast_ty.filepath);

    const pkg = self.context.compilation_unit.packages.getPtr(pkg_name) orelse unreachable;
    const parent_unit = pkg.sources.getPtr(filepath) orelse unreachable;
    const imported_ast = parent_unit.ast orelse return field_access.field;

    const field_name = a.exprs.strs.get(field_access.field);
    const target_sid = imported_ast.exprs.strs.intern(field_name);

    const ex = imported_ast.type_info.getExport(target_sid) orelse return field_access.field;
    const drow = imported_ast.exprs.Decl.get(ex.decl_id);

    return switch (imported_ast.kind(drow.value)) {
        .Ident => imported_ast.exprs.get(.Ident, drow.value).name,
        .FieldAccess => self.resolveFieldAccessName(ctx, imported_ast, drow.value),
        else => field_access.field,
    };
}

/// Trace a call expression to identify the callee symbol plus qualified name if any.
fn resolveCallee(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, f: *Builder.FunctionFrame, row: ast.Rows.Call) !CalleeInfo {
    const cctx = self.chk.checker_ctx.items[a.file_id] orelse unreachable;
    var current = row.callee;

    var depth: usize = 0;
    while (depth < 32) : (depth += 1) {
        switch (a.kind(current)) {
            .Ident => {
                const ident = a.exprs.get(.Ident, current);
                const sid = cctx.symtab.lookup(cctx.symtab.currentId(), ident.name) orelse {
                    return CalleeInfo{ .name = ident.name, .qualified_name = null, .fty = self.getExprType(ctx, a, row.callee), .expr = current };
                };

                const srow = cctx.symtab.syms.get(sid);
                if (srow.origin_decl.isNone()) {
                    return CalleeInfo{ .name = ident.name, .qualified_name = null, .fty = self.getExprType(ctx, a, row.callee), .expr = current };
                }

                const did = srow.origin_decl.unwrap();
                const drow = a.exprs.Decl.get(did);
                const val_kind = a.kind(drow.value);

                if (val_kind == .Ident or val_kind == .FieldAccess) {
                    if (drow.flags.is_const) {
                        current = drow.value;
                        continue;
                    }
                    return CalleeInfo{ .name = ident.name, .qualified_name = null, .fty = self.getExprType(ctx, a, row.callee), .expr = current };
                }

                return CalleeInfo{ .name = ident.name, .qualified_name = null, .fty = self.getExprType(ctx, a, row.callee), .expr = current };
            },
            .FieldAccess => {
                const resolved_name = self.resolveFieldAccessName(ctx, a, current);
                return CalleeInfo{ .name = resolved_name, .qualified_name = null, .fty = self.getExprType(ctx, a, row.callee), .expr = current };
            },
            else => break,
        }
    }

    return CalleeInfo{ .name = f.builder.intern("<indirect>"), .qualified_name = null, .fty = self.getExprType(ctx, a, row.callee), .expr = row.callee };
}

/// Create the payload value for a variant literal call based on the variant type `ety`.
fn buildVariantItem(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    row: ast.Rows.Call,
    ety: types.TypeId,
    k: types.TypeKind,
    loc: tir.OptLocId,
) !tir.ValueId {
    var cur = row.callee;
    var first_field: ?StrId = null;
    while (a.kind(cur) == .FieldAccess) {
        const fr = a.exprs.get(.FieldAccess, cur);
        if (first_field == null) first_field = fr.field;
        cur = fr.parent;
    }
    std.debug.assert(first_field != null);
    const lname = first_field.?;

    const fields = if (k == .Variant)
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, ety).variants)
    else
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, ety).variants);

    var tag_idx: u32 = 0;
    var payload_ty: types.TypeId = self.context.type_store.tVoid();
    var found = false;

    var stack_fields_buf: [64]types.TypeStore.StructFieldArg = undefined;
    var union_fields_args_slice: []types.TypeStore.StructFieldArg = &.{};
    var heap_fields_alloc: ?[]types.TypeStore.StructFieldArg = null;
    defer if (heap_fields_alloc) |ptr| self.gpa.free(ptr);

    if (fields.len <= 64) {
        union_fields_args_slice = stack_fields_buf[0..fields.len];
    } else {
        heap_fields_alloc = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
        union_fields_args_slice = heap_fields_alloc.?;
    }

    for (fields, 0..) |fld_id, i| {
        const fld = self.context.type_store.Field.get(fld_id);
        union_fields_args_slice[i] = .{ .name = fld.name, .ty = fld.ty };

        if (fld.name.eq(lname)) {
            tag_idx = @intCast(i);
            payload_ty = fld.ty;
            found = true;
        }
    }

    if (!found) {
        const where: Loc = if (!loc.isNone()) a.exprs.locs.get(loc.unwrap()) else .init(@intCast(a.file_id), 0, 0);
        var msg_buf: [256]u8 = undefined;
        var fbs = std.io.fixedBufferStream(&msg_buf);

        fbs.writer().print("tag '{s}' in ", .{a.exprs.strs.get(lname)}) catch {};
        try self.context.type_store.formatTypeForDiagnostic(ety, types.FormatOptions{}, fbs.writer());

        const sid = self.context.interner.intern(fbs.getWritten());
        _ = self.context.diags.addError(where, .tir_variant_tag_not_found, .{self.context.interner.get(sid)}) catch {};
        return error.LoweringBug;
    }

    const args = a.exprs.expr_pool.slice(row.args);
    const payload_kind = self.context.type_store.getKind(payload_ty);

    const payload_val: ?tir.ValueId = switch (payload_kind) {
        .Void => null,
        .Tuple => blk_t: {
            const tr = self.context.type_store.get(.Tuple, payload_ty);
            const subtys = self.context.type_store.type_pool.slice(tr.elems);

            var elem_buf: [16]tir.ValueId = undefined;
            var elems_slice: []tir.ValueId = undefined;
            var heap_elems: ?[]tir.ValueId = null;
            defer if (heap_elems) |p| self.gpa.free(p);

            if (subtys.len <= 16) {
                elems_slice = elem_buf[0..subtys.len];
            } else {
                heap_elems = try self.gpa.alloc(tir.ValueId, subtys.len);
                elems_slice = heap_elems.?;
            }

            for (subtys, 0..) |sty, i| {
                const arg_id = if (i < args.len) args[i] else args[args.len - 1];
                elems_slice[i] = try self.lowerExpr(ctx, a, env, f, blk, arg_id, sty, .rvalue);
            }
            break :blk_t blk.builder.tupleMake(blk, payload_ty, elems_slice, loc);
        },
        else => try self.lowerExpr(ctx, a, env, f, blk, args[0], payload_ty, .rvalue),
    };

    const tag_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), loc, .{ .value = tag_idx });
    const union_ty = self.context.type_store.mkUnion(union_fields_args_slice);

    const union_val: tir.ValueId = if (payload_val) |pv|
        blk.builder.tirValue(.UnionMake, blk, union_ty, loc, .{ .field_index = tag_idx, .value = pv })
    else
        blk.builder.tirValue(.ConstUndef, blk, union_ty, loc, .{});

    return blk.builder.structMake(blk, ety, &[_]tir.Rows.StructFieldInit{
        .{ .index = 0, .name = .none(), .value = tag_val },
        .{ .index = 1, .name = .none(), .value = union_val },
    }, loc);
}

/// Convert a literal AST node into a `ComptimeValue` when possible.
fn constValueFromLiteral(self: *LowerTir, a: *ast.Ast, expr: ast.ExprId) !?comp.ComptimeValue {
    if (a.kind(expr) != .Literal) return null;
    const lit = a.exprs.get(.Literal, expr);

    return switch (lit.kind) {
        .int => if (lit.data == .int and lit.data.int.valid) comp.ComptimeValue{ .Int = @as(i128, @intCast(lit.data.int.value)) } else null,
        .float => if (lit.data == .float and lit.data.float.valid) comp.ComptimeValue{ .Float = lit.data.float.value } else null,
        .bool => if (lit.data == .bool) comp.ComptimeValue{ .Bool = lit.data.bool } else null,
        .string => blk: {
            if (lit.data != .string) return null;
            const s = a.exprs.strs.get(lit.data.string);
            const owned_s = try self.gpa.dupe(u8, s);
            break :blk comp.ComptimeValue{ .String = owned_s };
        },
        else => null,
    };
}

/// Attempt to evaluate a call expression at comptime so it can be folded into the lowered IR.
fn tryComptimeCall(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
) !?tir.ValueId {
    const row = a.exprs.get(.Call, id);
    const ck = a.kind(row.callee);
    const callee_name = switch (ck) {
        .Ident => a.exprs.strs.get(a.exprs.get(.Ident, row.callee).name),
        .FieldAccess => a.exprs.strs.get(a.exprs.get(.FieldAccess, row.callee).field),
        else => return null,
    };

    const len = callee_name.len;
    if (len < 6 or len > 16) return null;

    const loc = optLoc(a, id);
    const arg_ids = a.exprs.expr_pool.slice(row.args);

    if (len == 6 and std.mem.eql(u8, callee_name, "sizeof")) {
        if (arg_ids.len != 1) return null;
        const target_ty = self.getExprType(ctx, a, arg_ids[0]);
        const sz: u64 = @intCast(check_types.typeSize(self.context, target_ty));
        const want = self.getExprType(ctx, a, id);
        return blk.builder.tirValue(.ConstInt, blk, want, loc, .{ .value = sz });
    }
    if (len == 8 and std.mem.eql(u8, callee_name, "typeinfo")) {
        if (arg_ids.len != 1) return null;
        if (try self.getCachedComptimeValue(a, id)) |cval| {
            var tmp = cval;
            defer tmp.destroy(self.gpa);
            return try comp.constValueFromComptime(self, blk, self.getExprType(ctx, a, id), cval);
        }
        return null;
    }

    const is_print = len == 14 and std.mem.eql(u8, callee_name, "comptime_print");
    const is_get_type = len == 16 and std.mem.eql(u8, callee_name, "get_type_by_name");
    const is_type_of = len == 7 and std.mem.eql(u8, callee_name, "type_of");

    if (!(is_print or is_get_type or is_type_of)) return null;

    const api_ptr_bnd = env.lookup(f.builder.intern("comptime_api_ptr")) orelse {
        if (!loc.isNone()) {
            const where = a.exprs.locs.get(loc.unwrap());
            _ = self.context.diags.addError(where, .comptime_type_not_supported, .{}) catch {};
        }
        return error.LoweringBug;
    };
    const api_ptr = api_ptr_bnd.value;

    const ptr_ty = self.context.type_store.mkPtr(self.context.type_store.tU8(), false);
    const fn_ptr_ty = self.context.type_store.mkPtr(self.context.type_store.tVoid(), false);

    const comptime_api_struct_ty = self.context.type_store.mkStruct(&.{
        .{ .name = f.builder.intern("context"), .ty = ptr_ty },
        .{ .name = f.builder.intern("print"), .ty = fn_ptr_ty },
        .{ .name = f.builder.intern("get_type_by_name"), .ty = fn_ptr_ty },
        .{ .name = f.builder.intern("type_of"), .ty = fn_ptr_ty },
    }, 0);

    const comptime_api_ptr_ty = self.context.type_store.mkPtr(comptime_api_struct_ty, false);
    const typed_api_ptr = blk.builder.tirValue(.CastBit, blk, comptime_api_ptr_ty, loc, .{ .value = api_ptr });

    const ctx_ptr_ptr = blk.builder.gep(blk, self.context.type_store.mkPtr(ptr_ty, false), typed_api_ptr, &.{ blk.builder.gepConst(0), blk.builder.gepConst(0) }, loc);
    const ctx_ptr = blk.builder.tirValue(.Load, blk, ptr_ty, loc, .{ .ptr = ctx_ptr_ptr, .@"align" = 0 });

    const fn_ptr_idx: u64 = if (is_print) 1 else if (is_get_type) 2 else 3;
    const fn_ptr_ptr = blk.builder.gep(blk, self.context.type_store.mkPtr(fn_ptr_ty, false), typed_api_ptr, &.{ blk.builder.gepConst(0), blk.builder.gepConst(fn_ptr_idx) }, loc);
    const fn_ptr = blk.builder.tirValue(.Load, blk, fn_ptr_ty, loc, .{ .ptr = fn_ptr_ptr, .@"align" = 0 });

    var args_buf: [8]tir.ValueId = undefined;
    args_buf[0] = ctx_ptr;
    var arg_cursor: usize = 1;

    if (is_type_of) {
        std.debug.assert(arg_ids.len == 1);
        const arg_type_id = self.getExprType(ctx, a, arg_ids[0]);
        args_buf[arg_cursor] = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tU32(), loc, .{ .value = arg_type_id.toRaw() });
        arg_cursor += 1;
    } else {
        if (1 + arg_ids.len > args_buf.len) return error.TooManyArguments;
        for (arg_ids) |arg_id| {
            args_buf[arg_cursor] = try self.lowerExpr(ctx, a, env, f, blk, arg_id, null, .rvalue);
            arg_cursor += 1;
        }
    }

    return blk.builder.indirectCall(blk, self.getExprType(ctx, a, id), fn_ptr, args_buf[0..arg_cursor], loc);
}

/// Emit the TIR form of a call expression, handling attributes, comptime args, and lowering the callee.
fn lowerCall(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected: ?types.TypeId,
    mode: LowerMode,
) !tir.ValueId {
    if (try self.tryComptimeCall(ctx, a, env, f, blk, id)) |v| return v;

    const row = a.exprs.get(.Call, id);
    const loc = optLoc(a, id);

    if (expected) |ety| {
        const k = self.context.type_store.getKind(ety);
        if ((k == .Variant or k == .Error) and a.kind(row.callee) == .FieldAccess) {
            const fr = a.exprs.get(.FieldAccess, row.callee);
            const parent_ty = self.getExprType(ctx, a, fr.parent);
            if (self.context.type_store.getKind(parent_ty) == .TypeType and
                self.context.type_store.get(.TypeType, parent_ty).of.eq(ety))
            {
                return try self.buildVariantItem(ctx, a, env, f, blk, row, ety, k, loc);
            }
        }
    }

    var callee = try self.resolveCallee(ctx, a, f, row);
    var callee_name = a.exprs.strs.get(callee.name);
    const callee_expr = callee.expr;
    if (callee.fty == null) callee.fty = self.getExprType(ctx, a, callee_expr);

    var specialization_pack_args = false;
    var specialization_pack_start: usize = 0;

    if (a.type_info.call_specializations.get(id.toRaw())) |spec| {
        if (spec.target_decl != 0) {
            const target_ast = if (spec.target_file_id == std.math.maxInt(u32) or spec.target_file_id == a.file_id)
                a
            else
                self.astForFileId(spec.target_file_id) orelse a;

            const is_extern = if (callee.fty) |fty|
                self.context.type_store.getKind(fty) == .Function and self.context.type_store.get(.Function, fty).is_extern
            else
                false;

            if (!is_extern) {
                var spec_name = callee.name;
                const orig_decl = self.findOriginalDeclForSynthetic(target_ast, ast.DeclId.fromRaw(spec.target_decl));

                if (orig_decl) |odid| {
                    const decl_row = target_ast.exprs.Decl.get(odid);
                    const base = if (!decl_row.pattern.isNone())
                        bindingNameOfPattern(target_ast, decl_row.pattern.unwrap())
                    else if (!decl_row.method_path.isNone())
                        try self.methodSymbolShortName(target_ast, odid)
                    else
                        null;

                    if (base) |b| {
                        const base_str = self.context.type_store.strs.get(b);
                        const spec_name_str = try std.fmt.allocPrint(self.gpa, "{s}_spec_{d}", .{ base_str, spec.target_decl });
                        defer self.gpa.free(spec_name_str);
                        spec_name = self.context.type_store.strs.intern(spec_name_str);
                    }
                }

                callee.name = spec_name;
                callee.qualified_name = if (spec_name.eq(callee.name) and callee.qualified_name != null)
                    callee.qualified_name.?
                else
                    try self.qualifySymbolName(target_ast, spec_name);

                if (spec.target_decl < target_ast.type_info.decl_types.items.len) {
                    if (target_ast.type_info.decl_types.items[spec.target_decl]) |sig| callee.fty = sig;
                }
                callee_name = self.context.type_store.strs.get(spec_name);
            }
        }
        if (spec.pack_args) {
            specialization_pack_args = true;
            specialization_pack_start = spec.pack_start_index;
        }
    }

    var arg_ids = a.exprs.expr_pool.slice(row.args);
    var method_arg_buf: []ast.ExprId = &.{};
    var method_decl_id: ?ast.DeclId = null;
    var method_binding: ?types.MethodBinding = null;
    defer if (method_arg_buf.len != 0) self.gpa.free(method_arg_buf);

    // Consolidated method binding logic
    if (a.kind(callee_expr) == .FieldAccess) {
        const existing_binding = a.type_info.getMethodBinding(callee_expr);
        const binding = existing_binding orelse try self.synthesizeMethodBinding(ctx, a, env, callee_expr);

        if (binding) |b| {
            try self.prepareMethodCall(
                a,
                row,
                b,
                &callee,
                &callee_name,
                &method_decl_id,
                &method_binding,
                &arg_ids,
                &method_arg_buf,
            );
        }
    }

    var param_tys: []const types.TypeId = &.{};
    var treat_trailing_any = specialization_pack_args;
    var trailing_any_tuple_ty: ?types.TypeId = null;

    if (callee.fty) |fty| {
        if (self.hasTrailingAnyRuntimeParam(fty)) treat_trailing_any = true;
    }

    if (callee.qualified_name == null and method_decl_id == null) {
        if (call_resolution.findFunctionDeclForCall(self.context, a, callee_expr, callee.name)) |decl_ctx| {
            if (try symbolNameForDecl(self, decl_ctx.ast, decl_ctx.decl_id)) |sym| callee.qualified_name = sym;
        }
    }

    var vals_list: List(tir.ValueId) = .empty;
    defer vals_list.deinit(self.gpa);
    try vals_list.ensureTotalCapacity(self.gpa, arg_ids.len + 2); // heuristic pre-allocation

    var fixed_params_count: usize = 0;
    var is_variadic_extern = false;
    if (callee.fty) |fty| {
        if (self.context.type_store.getKind(fty) == .Function) {
            const fnrow = self.context.type_store.get(.Function, fty);
            param_tys = self.context.type_store.type_pool.slice(fnrow.params);
            is_variadic_extern = fnrow.is_variadic and fnrow.is_extern;
            fixed_params_count = if (specialization_pack_args) specialization_pack_start else param_tys.len;
            if (is_variadic_extern and fixed_params_count > 0) fixed_params_count -= 1;
        }
    }

    const is_non_extern_any_variadic_candidate = treat_trailing_any;
    if (is_non_extern_any_variadic_candidate and fixed_params_count > 0 and !specialization_pack_args) {
        fixed_params_count -= 1;
    }

    var i: usize = 0;
    while (i < arg_ids.len) : (i += 1) {
        if (is_non_extern_any_variadic_candidate and i >= fixed_params_count) break;

        const want: ?types.TypeId = if (i < fixed_params_count) param_tys[i] else null;
        const lower_mode: LowerMode = if (method_binding) |mb|
            if (mb.requires_implicit_receiver and mb.needs_addr_of and i == 0) .lvalue_addr else .rvalue
        else
            .rvalue;

        try vals_list.append(self.gpa, try self.lowerExpr(ctx, a, env, f, blk, arg_ids[i], want, lower_mode));
    }

    try self.lowerRemainingArgs(
        ctx,
        a,
        env,
        f,
        blk,
        arg_ids,
        param_tys,
        &vals_list,
        fixed_params_count,
        is_non_extern_any_variadic_candidate,
        &trailing_any_tuple_ty,
        method_binding,
        loc,
        i,
    );

    try self.synthesizeDefaultTrailingArgs(
        ctx,
        a,
        env,
        f,
        blk,
        &callee,
        callee_expr,
        method_decl_id,
        param_tys,
        &vals_list,
        is_variadic_extern,
        is_non_extern_any_variadic_candidate,
        method_binding,
    );

    if (param_tys.len == vals_list.items.len + 1) {
        const last_ty = param_tys[param_tys.len - 1];
        if (self.context.type_store.getKind(last_ty) == .Tuple) {
            const rrow = self.context.type_store.get(.Tuple, last_ty);
            if (self.context.type_store.type_pool.slice(rrow.elems).len == 0) {
                try vals_list.append(self.gpa, blk.builder.tupleMake(blk, last_ty, &.{}, optLoc(a, id)));
            }
        }
    }

    if (is_variadic_extern and vals_list.items.len > fixed_params_count) {
        try self.handleExternVariadicArgs(
            ctx,
            a,
            env,
            f,
            blk,
            id,
            arg_ids,
            &vals_list,
            fixed_params_count,
        );
    }

    if (method_binding) |mb| {
        if (mb.builtin) |builtin_kind| {
            if (builtin_kind == .dynarray_append) {
                std.debug.assert(mode != .lvalue_addr);
                return try self.lowerDynArrayAppend(f, blk, loc, mb, vals_list.items);
            }
        }
    }

    return self.emitCallValue(
        ctx,
        a,
        env,
        f,
        blk,
        id,
        row,
        &callee,
        callee_expr,
        expected,
        mode,
        vals_list.items,
        loc,
    );
}

/// Lower the remaining argument expressions, injecting a packed tuple for `any` trailing parameters.
fn lowerRemainingArgs(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    arg_ids: []const ast.ExprId,
    param_tys: []const types.TypeId,
    vals_list: *List(tir.ValueId),
    fixed_params_count: usize,
    is_non_extern_any_variadic_candidate: bool,
    trailing_any_tuple_ty_ptr: *?types.TypeId,
    method_binding: ?types.MethodBinding,
    loc: tir.OptLocId,
    start_index: usize,
) !void {
    if (is_non_extern_any_variadic_candidate) {
        const trailing_len = if (arg_ids.len > start_index) arg_ids.len - start_index else 0;
        if (trailing_len == 1) {
            const idx = start_index;
            if (!self.isSpreadArgExpr(ctx, a, env, arg_ids[idx])) {
                try vals_list.append(self.gpa, try self.lowerExpr(ctx, a, env, f, blk, arg_ids[idx], null, .rvalue));
                return;
            }
        }

        var extra_vals: List(tir.ValueId) = .empty;
        defer extra_vals.deinit(self.gpa);
        try extra_vals.ensureTotalCapacity(self.gpa, trailing_len);

        var j = fixed_params_count;
        while (j < arg_ids.len) : (j += 1) {
            try extra_vals.append(self.gpa, try self.lowerExpr(ctx, a, env, f, blk, arg_ids[j], null, .rvalue));
        }

        const packed_tuple_ty = trailing_any_tuple_ty_ptr.* orelse blk_t: {
            const ty = try self.computeTrailingAnyTupleType(ctx, a, env, arg_ids, fixed_params_count);
            trailing_any_tuple_ty_ptr.* = ty;
            break :blk_t ty;
        };

        try vals_list.append(self.gpa, blk.builder.tupleMake(blk, packed_tuple_ty, extra_vals.items, loc));
        return;
    }

    var idx = start_index;
    while (idx < arg_ids.len) : (idx += 1) {
        const want: ?types.TypeId = if (idx < fixed_params_count) param_tys[idx] else null;
        const lower_mode: LowerMode = if (method_binding) |mb|
            if (mb.requires_implicit_receiver and mb.needs_addr_of and idx == 0) .lvalue_addr else .rvalue
        else
            .rvalue;

        try vals_list.append(self.gpa, try self.lowerExpr(ctx, a, env, f, blk, arg_ids[idx], want, lower_mode));
    }
}

/// Inject default trailing args for methods/functions when the caller omits them.
fn synthesizeDefaultTrailingArgs(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    callee: *CalleeInfo,
    callee_expr: ast.ExprId,
    method_decl_id: ?ast.DeclId,
    param_tys: []const types.TypeId,
    vals_list: *List(tir.ValueId),
    is_variadic_extern: bool,
    is_non_extern_any_variadic_candidate: bool,
    method_binding: ?types.MethodBinding,
) !void {
    if (is_variadic_extern or is_non_extern_any_variadic_candidate or param_tys.len <= vals_list.items.len) return;

    const dctx = if (method_binding) |mb|
        FunctionDeclContext{ .ast = mb.decl_ast, .decl_id = mb.decl_id }
    else if (method_decl_id) |mid|
        FunctionDeclContext{ .ast = a, .decl_id = mid }
    else if (callee.fty) |_|
        call_resolution.findFunctionDeclForCall(self.context, a, callee_expr, callee.name) orelse return
    else
        return;

    const decl_ast = dctx.ast;
    const decl = decl_ast.exprs.Decl.get(dctx.decl_id);
    if (decl_ast.kind(decl.value) != .FunctionLit) return;

    const fnr = decl_ast.exprs.get(.FunctionLit, decl.value);
    const params2 = decl_ast.exprs.param_pool.slice(fnr.params);
    try env.pushScope(self.gpa);
    defer _ = env.popScope(self.gpa);

    var j: usize = 0;
    while (j < vals_list.items.len and j < params2.len and j < param_tys.len) : (j += 1) {
        const p = decl_ast.exprs.Param.get(params2[j]);
        if (!p.pat.isNone()) {
            if (bindingNameOfPattern(decl_ast, p.pat.unwrap())) |pname| {
                try env.bind(self.gpa, pname, .{
                    .value = vals_list.items[j],
                    .ty = param_tys[j],
                    .is_slot = false,
                }, f.builder, blk, optLoc(decl_ast, p.pat.unwrap()));
            }
        }
    }

    while (vals_list.items.len < param_tys.len) {
        const idx: usize = vals_list.items.len;
        if (idx >= params2.len) break;

        const p = decl_ast.exprs.Param.get(params2[idx]);
        if (p.value.isNone()) break;

        const def_expr = p.value.unwrap();
        const want_ty = if (idx < param_tys.len) param_tys[idx] else null;
        const def_v = try self.lowerExpr(ctx, decl_ast, env, f, blk, def_expr, want_ty, .rvalue);

        try vals_list.append(self.gpa, def_v);

        if (!p.pat.isNone()) {
            if (bindingNameOfPattern(decl_ast, p.pat.unwrap())) |pname| {
                const bind_ty = if (want_ty) |wt| wt else self.getExprType(ctx, decl_ast, def_expr);
                try env.bind(self.gpa, pname, .{ .value = def_v, .ty = bind_ty, .is_slot = false }, f.builder, blk, optLoc(decl_ast, p.pat.unwrap()));
            }
        }
    }
}

/// Detect whether `expr` references an imported module member via dotted access.
fn isImportMemberExpr(a: *ast.Ast, expr: ast.ExprId) bool {
    var current = expr;
    while (true) {
        switch (a.kind(current)) {
            .FieldAccess => current = a.exprs.get(.FieldAccess, current).parent,
            .Ident => {
                const ident = a.exprs.get(.Ident, current);
                return call_resolution.findDeclId(a, ident.name) != null;
            },
            .Import => return true,
            else => return false,
        }
    }
}

/// Emit the actual call instruction (direct or indirect) and adjust for `.lvalue_addr` mode.
fn emitCallValue(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    row: ast.Rows.Call,
    callee: *CalleeInfo,
    callee_expr: ast.ExprId,
    expected: ?types.TypeId,
    mode: LowerMode,
    vals: []tir.ValueId,
    loc: tir.OptLocId,
) !tir.ValueId {
    const ret_ty = blk: {
        if (callee.fty) |fty| {
            if (self.context.type_store.getKind(fty) == .Function) {
                const rt = self.context.type_store.get(.Function, fty).result;
                if (!self.isVoid(rt) and !self.isType(rt, .Any)) break :blk rt;
            }
        }
        if (expected) |e| if (!self.isVoid(e) and !self.isType(e, .Any)) break :blk e;
        break :blk self.getExprType(ctx, a, id);
    };

    if (!self.isType(ret_ty, .Any)) {
        a.type_info.setExprType(id, ret_ty);
        try self.noteExprType(ctx, id, ret_ty);
    }

    const callee_ty = self.getExprType(ctx, a, row.callee);
    var call_val: tir.ValueId = undefined;

    // Determine if indirect call is forced
    const should_force_indirect = switch (a.kind(callee_expr)) {
        .Ident => blk: {
            const ident = a.exprs.get(.Ident, callee_expr);
            if (env.lookup(ident.name)) |bnd| {
                const bnd_ty = if (!self.isType(callee_ty, .Any)) callee_ty else bnd.ty;
                if (self.context.type_store.getKind(bnd_ty) == .Function) break :blk true;
                if (self.context.type_store.getKind(bnd_ty) == .Ptr and
                    self.context.type_store.getKind(self.context.type_store.get(.Ptr, bnd_ty).elem) == .Function)
                {
                    break :blk true;
                }
            }
            break :blk false;
        },
        .FieldAccess => !isImportMemberExpr(a, callee_expr) and a.type_info.getMethodBinding(callee_expr) == null,
        else => true,
    };

    const is_ptr_to_func = self.context.type_store.getKind(callee_ty) == .Ptr and
        self.context.type_store.getKind(self.context.type_store.get(.Ptr, callee_ty).elem) == .Function;

    if (should_force_indirect or is_ptr_to_func) {
        const fn_ptr_val = try self.lowerExpr(ctx, a, env, f, blk, row.callee, callee_ty, .rvalue);
        call_val = blk.builder.indirectCall(blk, ret_ty, fn_ptr_val, vals, loc);
    } else if (self.context.type_store.strs.get(callee.name).len == 10 and std.mem.eql(u8, self.context.type_store.strs.get(callee.name), "<indirect>")) {
        const want_ptr_ty = self.context.type_store.mkPtr(callee_ty, false);
        const fn_ptr_val = try self.lowerExpr(ctx, a, env, f, blk, row.callee, want_ptr_ty, .lvalue_addr);
        call_val = blk.builder.indirectCall(blk, ret_ty, fn_ptr_val, vals, loc);
    } else {
        const callee_sym = callee.qualified_name orelse callee.name;
        call_val = blk.builder.call(blk, ret_ty, callee_sym, vals, loc);
    }

    if (mode == .lvalue_addr) {
        const want_ptr_ty_opt = if (expected) |want|
            if (self.context.type_store.getKind(want) == .Ptr) want else null
        else
            null;

        const elem_ty = if (want_ptr_ty_opt) |want_ptr_ty|
            self.context.type_store.get(.Ptr, want_ptr_ty).elem
        else
            ret_ty;

        const slot_ty = self.context.type_store.mkPtr(elem_ty, false);
        const slot = f.builder.tirValue(.Alloca, blk, slot_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });

        const stored = if (!elem_ty.eq(ret_ty)) self.emitCoerce(blk, call_val, ret_ty, elem_ty, loc) else call_val;
        _ = f.builder.tirValue(.Store, blk, elem_ty, loc, .{ .ptr = slot, .value = stored, .@"align" = 0 });

        if (want_ptr_ty_opt) |want_ptr_ty| {
            if (!want_ptr_ty.eq(slot_ty)) return self.emitCoerce(blk, slot, slot_ty, want_ptr_ty, loc);
        }
        return slot;
    }

    return call_val;
}

fn handleExternVariadicArgs(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    arg_ids: []const ast.ExprId,
    vals_list: *List(tir.ValueId),
    fixed_params_count: usize,
) !void {
    const VarArgEntry = struct {
        value: tir.ValueId,
        ty: types.TypeId,
        loc: tir.OptLocId,
        expr: ?ast.ExprId,
    };

    var var_entries: List(VarArgEntry) = .empty;
    defer var_entries.deinit(self.gpa);

    // 1. Extract variadic args
    const total_len = vals_list.items.len;
    if (total_len > fixed_params_count) {
        const count = total_len - fixed_params_count;
        try var_entries.ensureTotalCapacity(self.gpa, count);

        var i: usize = 0;
        while (i < count) : (i += 1) {
            const arg_pos = fixed_params_count + i;
            const expr_id = if (arg_pos < arg_ids.len) arg_ids[arg_pos] else null;

            var_entries.appendAssumeCapacity(.{
                .value = vals_list.items[arg_pos],
                .ty = if (expr_id) |eid| self.exprTypeWithEnv(ctx, a, env, eid) else self.exprTypeWithEnv(ctx, a, env, id),
                .loc = if (expr_id) |eid| optLoc(a, eid) else optLoc(a, id),
                .expr = expr_id,
            });
        }
        vals_list.items.len = fixed_params_count;
    }

    // 2. Expand spreads and promote types
    // We use a new list for the final output to avoid O(N^2) shifting
    var final_entries: List(VarArgEntry) = .empty;
    defer final_entries.deinit(self.gpa);
    try final_entries.ensureTotalCapacity(self.gpa, var_entries.items.len);

    for (var_entries.items) |*entry| {
        var curr_ty = entry.ty;
        var curr_kind = self.context.type_store.getKind(curr_ty);

        // Handle Any -> Tuple/Literal expansion
        if (curr_kind == .Any and entry.expr != null and self.isSpreadArgExpr(ctx, a, env, entry.expr)) {
            const range_row = a.exprs.get(.Range, entry.expr.?);
            if (!range_row.end.isNone()) {
                const payload_expr = range_row.end.unwrap();
                const payload_ty = self.exprTypeWithEnv(ctx, a, env, payload_expr);
                if (self.context.type_store.getKind(payload_ty) == .Tuple) {
                    entry.value = try self.lowerExpr(ctx, a, env, f, blk, payload_expr, payload_ty, .rvalue);
                    entry.ty = payload_ty;
                    curr_ty = payload_ty;
                    curr_kind = .Tuple;
                }
            }
        }

        // Expand Tuples
        if (curr_kind == .Tuple and self.isSpreadArgExpr(ctx, a, env, entry.expr)) {
            const tuple_row = self.context.type_store.get(.Tuple, curr_ty);
            const elem_types = self.context.type_store.type_pool.slice(tuple_row.elems);

            for (elem_types, 0..) |elem_ty, elem_idx| {
                const resolved_elem_ty = if (self.context.type_store.getKind(elem_ty) == .Any)
                    self.context.type_store.tUsize()
                else
                    elem_ty;

                const elem_val = blk.builder.extractElem(blk, resolved_elem_ty, entry.value, @intCast(elem_idx), entry.loc);
                try final_entries.append(self.gpa, .{
                    .value = elem_val,
                    .ty = elem_ty,
                    .loc = entry.loc,
                    .expr = null, // Consumed spread
                });
            }
            continue;
        }

        try final_entries.append(self.gpa, entry.*);
    }

    // 3. Promote scalars and append to vals_list
    for (final_entries.items) |*entry| {
        const k = self.context.type_store.getKind(entry.ty);
        const promoted_ty: ?types.TypeId = switch (k) {
            .Bool, .I8, .U8, .I16, .U16 => self.context.type_store.tI32(),
            .F32 => self.context.type_store.tF64(),
            .Any => blk_any: {
                if (entry.expr) |eid| {
                    if (a.kind(eid) == .Literal) {
                        break :blk_any switch (a.exprs.get(.Literal, eid).kind) {
                            .int, .char => self.context.type_store.tI64(),
                            .float, .imaginary => self.context.type_store.tF64(),
                            .bool => self.context.type_store.tI32(),
                            .string => self.context.type_store.tString(),
                        };
                    }
                }
                break :blk_any self.context.type_store.tUsize();
            },
            else => null,
        };

        if (promoted_ty) |pty| {
            if (k == .Any) {
                if (entry.expr) |eid| {
                    entry.value = try self.lowerExpr(ctx, a, env, f, blk, eid, pty, .rvalue);
                }
            } else {
                entry.value = self.emitCoerce(blk, entry.value, entry.ty, pty, entry.loc);
            }
        }

        try vals_list.append(self.gpa, entry.value);
    }
}

fn isSpreadRangeExpr(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, env: *cf.Env, expr: ast.ExprId) bool {
    if (a.kind(expr) != .Range) return false;
    if (a.type_info.isRangeSpread(expr)) return true;

    const row = a.exprs.get(.Range, expr);
    if (!row.start.isNone() or row.end.isNone()) return false;

    const end_expr = row.end.unwrap();
    const refined_ty = self.exprTypeWithEnv(ctx, a, env, end_expr);
    const refined_kind = self.context.type_store.getKind(refined_ty);

    if (refined_kind == .Tuple or refined_kind == .Any) return true;
    return self.context.type_store.getKind(self.getExprType(ctx, a, end_expr)) == .Any;
}

fn isSpreadArgExpr(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, env: *cf.Env, expr: ?ast.ExprId) bool {
    return if (expr) |eid| self.isSpreadRangeExpr(ctx, a, env, eid) else false;
}

fn computeTrailingAnyTupleType(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    args: []const ast.ExprId,
    start_index: usize,
) !types.TypeId {
    if (start_index >= args.len) return self.context.type_store.mkTuple(&.{});

    const trailing_len = args.len - start_index;
    if (trailing_len == 1 and !self.isSpreadArgExpr(ctx, a, env, args[start_index])) {
        return self.exprTypeWithEnv(ctx, a, env, args[start_index]);
    }

    var elem_types = try std.ArrayList(types.TypeId).initCapacity(self.gpa, trailing_len);
    defer elem_types.deinit(self.gpa);

    var idx = start_index;
    while (idx < args.len) : (idx += 1) {
        elem_types.appendAssumeCapacity(self.exprTypeWithEnv(ctx, a, env, args[idx]));
    }

    return self.context.type_store.mkTuple(elem_types.items);
}

fn lowerTypeExprOpaque(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) tir.ValueId {
    const loc = optLoc(a, id);
    return self.safeUndef(blk, expected_ty orelse self.getExprType(ctx, a, id), loc);
}

fn lowerTypeOf(self: *LowerTir, ctx: *LowerContext, a: *ast.Ast, blk: *Builder.BlockFrame, id: ast.ExprId) tir.ValueId {
    const target_ty = self.getExprType(ctx, a, a.exprs.get(.TypeOf, id).expr);
    return blk.builder.tirValue(.ConstInt, blk, self.getExprType(ctx, a, id), optLoc(a, id), .{ .value = @as(u64, @intCast(target_ty.toRaw())) });
}

fn lowerLiteral(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const lit = a.exprs.get(.Literal, id);
    const ty0 = self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const base_ty = if (self.context.type_store.getKind(ty0) == .Optional)
        self.context.type_store.get(.Optional, ty0).elem
    else
        ty0;

    var literal_ty = base_ty;
    const v = switch (lit.kind) {
        .int => blk_int: {
            if (lit.data != .int or !lit.data.int.valid) break :blk_int blk.builder.tirValue(.ConstUndef, blk, base_ty, loc, .{});
            break :blk_int blk.builder.tirValue(.ConstInt, blk, base_ty, loc, .{ .value = @as(u64, @intCast(lit.data.int.value)) });
        },
        .imaginary => blk_img: {
            if (self.context.type_store.getKind(base_ty) != .Complex or lit.data != .imaginary)
                break :blk_img blk.builder.tirValue(.ConstUndef, blk, ty0, loc, .{});

            const crow = self.context.type_store.get(.Complex, base_ty);
            literal_ty = base_ty;
            const re0 = blk.builder.tirValue(.ConstFloat, blk, crow.elem, loc, .{ .value = 0.0 });
            const imv = blk.builder.tirValue(.ConstFloat, blk, crow.elem, loc, .{ .value = lit.data.imaginary.value });
            break :blk_img blk.builder.tirValue(.ComplexMake, blk, base_ty, loc, .{ .re = re0, .im = imv });
        },
        .float => blk_flt: {
            if (lit.data != .float or !lit.data.float.valid) break :blk_flt blk.builder.tirValue(.ConstUndef, blk, base_ty, loc, .{});
            const k = self.context.type_store.getKind(base_ty);
            literal_ty = if (k == .F32 or k == .F64) base_ty else self.context.type_store.tF64();
            break :blk_flt blk.builder.tirValue(.ConstFloat, blk, literal_ty, loc, .{ .value = lit.data.float.value });
        },
        .bool => blk.builder.tirValue(.ConstBool, blk, base_ty, loc, .{ .value = lit.data.bool }),
        .string => blk.builder.tirValue(.ConstString, blk, base_ty, loc, .{ .text = lit.data.string }),
        .char => blk.builder.tirValue(.ConstInt, blk, base_ty, loc, .{ .value = @as(u64, @intCast(lit.data.char)) }),
    };

    const want_ty = expected_ty orelse ty0;
    return if (!want_ty.eq(literal_ty)) self.emitCoerce(blk, v, literal_ty, want_ty, loc) else v;
}

fn lowerUnary(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Unary, id);
    const loc = optLoc(a, id);

    if (row.op == .address_of or mode == .lvalue_addr) {
        const ptr = try self.lowerExpr(ctx, a, env, f, blk, row.expr, self.getExprType(ctx, a, row.expr), .lvalue_addr);
        return if (row.op == .address_of) ptr else ptr; // lvalue fallthrough implicitly handled
    }

    var ty0 = self.getExprType(ctx, a, id);
    const is_num = self.isNumeric(ty0);

    // Fallback typing for numeric ops on void/any
    if ((row.op == .pos or row.op == .neg) and (!is_num or self.isType(ty0, .Any) or self.isVoid(ty0))) {
        const et = self.getExprType(ctx, a, row.expr);
        ty0 = if (self.isNumeric(et)) et else self.context.type_store.tI64();
    }

    const operand_expect: ?types.TypeId = switch (row.op) {
        .pos, .neg => ty0,
        .logical_not => self.context.type_store.tBool(),
        .address_of => unreachable,
    };

    var v0 = try self.lowerExpr(ctx, a, env, f, blk, row.expr, operand_expect, .rvalue);

    const v = switch (row.op) {
        .pos => v0,
        .neg => blk_neg: {
            const zero = blk_z: {
                if (self.context.type_store.getKind(ty0) == .Complex) {
                    const crow = self.context.type_store.get(.Complex, ty0);
                    const zero_elem = blk.builder.tirValue(.ConstFloat, blk, crow.elem, loc, .{ .value = 0.0 });
                    break :blk_z blk.builder.tirValue(.ComplexMake, blk, ty0, loc, .{ .re = zero_elem, .im = zero_elem });
                }
                if (self.isFloat(ty0)) break :blk_z blk.builder.tirValue(.ConstFloat, blk, ty0, loc, .{ .value = 0.0 });
                if (self.isType(ty0, .Simd)) {
                    const simd_info = self.context.type_store.get(.Simd, ty0);
                    const e_kind = self.context.type_store.getKind(simd_info.elem);
                    const scalar = if (e_kind == .F32 or e_kind == .F64)
                        blk.builder.tirValue(.ConstFloat, blk, simd_info.elem, loc, .{ .value = 0.0 })
                    else
                        blk.builder.tirValue(.ConstInt, blk, simd_info.elem, loc, .{ .value = 0 });
                    break :blk_z blk.builder.tirValue(.Broadcast, blk, ty0, loc, .{ .value = scalar });
                }
                break :blk_z blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = 0 });
            };
            break :blk_neg blk.builder.bin(blk, .Sub, ty0, zero, v0, loc);
        },
        .logical_not => blk_not: {
            const bty = self.context.type_store.tBool();
            v0 = self.emitCoerce(blk, v0, self.getExprType(ctx, a, row.expr), bty, optLoc(a, row.expr));
            break :blk_not blk.builder.un1(blk, .LogicalNot, bty, v0, loc);
        },
        .address_of => unreachable,
    };

    return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
}

fn lowerRange(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    if (self.isSpreadRangeExpr(ctx, a, env, id)) {
        return self.lowerExpr(ctx, a, env, f, blk, a.exprs.get(.Range, id).end.unwrap(), expected_ty, .rvalue);
    }
    const row = a.exprs.get(.Range, id);
    const ty0 = self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const usize_ty = self.context.type_store.tUsize();

    const start_v = if (!row.start.isNone()) try self.lowerExpr(ctx, a, env, f, blk, row.start.unwrap(), usize_ty, .rvalue) else blk.builder.tirValue(.ConstUndef, blk, usize_ty, loc, .{});
    const end_v = if (!row.end.isNone()) try self.lowerExpr(ctx, a, env, f, blk, row.end.unwrap(), usize_ty, .rvalue) else blk.builder.tirValue(.ConstUndef, blk, usize_ty, loc, .{});

    const v = blk.builder.rangeMake(blk, ty0, start_v, end_v, blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = row.inclusive_right }), loc);
    return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
}

fn lowerDeref(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) !tir.ValueId {
    const row = a.exprs.get(.Deref, id);
    if (mode == .lvalue_addr) return self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);

    const ty0 = self.getExprType(ctx, a, id);
    const ptr = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    const loc = optLoc(a, id);
    const v = blk.builder.tirValue(.Load, blk, ty0, loc, .{ .ptr = ptr, .@"align" = 0 });

    return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
}

fn lowerArrayLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.ArrayLit, id);
    const ty0 = expected_ty orelse self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const vk = self.context.type_store.getKind(ty0);

    const ids = a.exprs.expr_pool.slice(row.elems);

    const v = switch (vk) {
        .Array, .Simd => blk_arr: {
            const elem_ty = if (vk == .Array) self.context.type_store.get(.Array, ty0).elem else self.context.type_store.get(.Simd, ty0).elem;

            var vals_buf: [32]tir.ValueId = undefined;
            var vals: []tir.ValueId = if (ids.len <= 32) vals_buf[0..ids.len] else try self.gpa.alloc(tir.ValueId, ids.len);
            defer if (ids.len > 32) self.gpa.free(vals);

            for (ids, 0..) |eid, i| {
                vals[i] = try self.lowerExpr(ctx, a, env, f, blk, eid, elem_ty, .rvalue);
            }
            break :blk_arr blk.builder.arrayMake(blk, ty0, vals, loc);
        },
        .Slice, .DynArray => blk_dyn: {
            const is_slice = vk == .Slice;
            const elem_ty = if (is_slice) self.context.type_store.get(.Slice, ty0).elem else self.context.type_store.get(.DynArray, ty0).elem;
            const ptr_ty = self.context.type_store.mkPtr(elem_ty, false);
            const usize_ty = self.context.type_store.tUsize();

            if (ids.len == 0) {
                const null_ptr = blk.builder.constNull(blk, ptr_ty, loc);
                const zero = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = 0 });
                if (is_slice) {
                    break :blk_dyn blk.builder.structMake(blk, ty0, &[_]tir.Rows.StructFieldInit{
                        .{ .index = 0, .name = .none(), .value = null_ptr },
                        .{ .index = 1, .name = .none(), .value = zero },
                    }, loc);
                } else {
                    break :blk_dyn blk.builder.structMake(blk, ty0, &[_]tir.Rows.StructFieldInit{
                        .{ .index = 0, .name = .none(), .value = null_ptr },
                        .{ .index = 1, .name = .none(), .value = zero },
                        .{ .index = 2, .name = .none(), .value = zero },
                    }, loc);
                }
            }

            var elem_buf: [32]tir.ValueId = undefined;
            var elems: []tir.ValueId = if (ids.len <= 32) elem_buf[0..ids.len] else try self.gpa.alloc(tir.ValueId, ids.len);
            defer if (ids.len > 32) self.gpa.free(elems);

            for (ids, 0..) |eid, i| {
                elems[i] = try self.lowerExpr(ctx, a, env, f, blk, eid, elem_ty, .rvalue);
            }

            const elem_size = check_types.typeSize(self.context, elem_ty);
            const total_bytes = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = @as(u64, @intCast(elem_size * ids.len)) });
            const raw_ptr = self.callRuntimeAllocPtr(blk, total_bytes, loc);
            const data_ptr = blk.builder.tirValue(.CastBit, blk, ptr_ty, loc, .{ .value = raw_ptr });

            for (elems, 0..) |ev, idx| {
                const off = blk.builder.gepConst(@intCast(idx));
                const ep = blk.builder.gep(blk, ptr_ty, data_ptr, &.{off}, loc);
                _ = blk.builder.tirValue(.Store, blk, elem_ty, loc, .{ .ptr = ep, .value = ev, .@"align" = 0 });
            }

            const len_v = blk.builder.tirValue(.ConstInt, blk, usize_ty, loc, .{ .value = @as(u64, @intCast(ids.len)) });

            if (is_slice) {
                break :blk_dyn blk.builder.structMake(blk, ty0, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = data_ptr },
                    .{ .index = 1, .name = .none(), .value = len_v },
                }, loc);
            } else {
                break :blk_dyn blk.builder.structMake(blk, ty0, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = data_ptr },
                    .{ .index = 1, .name = .none(), .value = len_v },
                    .{ .index = 2, .name = .none(), .value = len_v },
                }, loc);
            }
        },
        .Tensor => try self.lowerTensorArrayLiteral(ctx, a, env, f, blk, id, ty0, loc),
        else => unreachable,
    };

    return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
}

/// Lower tensor-style array literals by flattening nested arrays into element sequences.
fn lowerTensorArrayLiteral(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    tensor_ty: types.TypeId,
    loc: tir.OptLocId,
) !tir.ValueId {
    if (self.context.type_store.get(.Tensor, tensor_ty).rank == 0) unreachable;

    var values: List(tir.ValueId) = .empty;
    defer values.deinit(self.gpa);

    try self.collectTensorLiteralValues(ctx, a, env, f, blk, id, tensor_ty, &values);

    const slice = try values.toOwnedSlice(self.gpa);
    defer self.gpa.free(slice);

    return blk.builder.arrayMake(blk, tensor_ty, slice, loc);
}

/// Recursively collect element values for multi-dimensional tensor literals.
fn collectTensorLiteralValues(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    expr_id: ast.ExprId,
    current_ty: types.TypeId,
    out: *List(tir.ValueId),
) !void {
    if (self.context.type_store.getKind(current_ty) == .Tensor) {
        if (a.kind(expr_id) != .ArrayLit) unreachable;

        const row = a.exprs.get(.ArrayLit, expr_id);
        const ids = a.exprs.expr_pool.slice(row.elems);
        const tensor_info = self.context.type_store.get(.Tensor, current_ty);

        std.debug.assert(tensor_info.rank > 0);
        std.debug.assert(ids.len == @as(usize, @intCast(tensor_info.dims[0])));

        var next_ty: types.TypeId = undefined;
        if (tensor_info.rank == 1) {
            next_ty = tensor_info.elem;
        } else {
            var dims_buf: [types.max_tensor_rank]usize = undefined;
            var i: usize = 0;
            while (i + 1 < tensor_info.rank) : (i += 1) {
                dims_buf[i] = tensor_info.dims[i + 1];
            }
            next_ty = self.context.type_store.mkTensor(tensor_info.elem, dims_buf[0 .. tensor_info.rank - 1]);
        }

        for (ids) |child_id| {
            try self.collectTensorLiteralValues(ctx, a, env, f, blk, child_id, next_ty, out);
        }
        return;
    }

    try out.append(self.gpa, try self.lowerExpr(ctx, a, env, f, blk, expr_id, current_ty, .rvalue));
}

/// Lower tuple literals by constructing a struct-like aggregate with ordered fields.
fn lowerTupleLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.TupleLit, id);
    var ty0 = self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const ids = a.exprs.expr_pool.slice(row.elems);

    if (self.context.type_store.getKind(ty0) == .TypeType) {
        const inner = self.context.type_store.get(.TypeType, ty0).of;
        return blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = @as(u64, @intCast(inner.toRaw())) });
    }

    var vals_buf: [32]tir.ValueId = undefined;
    var vals: []tir.ValueId = if (ids.len <= 32) vals_buf[0..ids.len] else try self.gpa.alloc(tir.ValueId, ids.len);
    defer if (ids.len > 32) self.gpa.free(vals);

    if (self.context.type_store.getKind(ty0) == .Any) {
        var elem_tys = try self.gpa.alloc(types.TypeId, ids.len);
        defer self.gpa.free(elem_tys);

        for (ids, 0..) |eid, i| {
            vals[i] = try self.lowerExpr(ctx, a, env, f, blk, eid, null, .rvalue);
            elem_tys[i] = self.getExprType(ctx, a, eid);
        }
        ty0 = self.context.type_store.mkTuple(elem_tys);
    } else {
        const is_tuple = self.context.type_store.getKind(ty0) == .Tuple;
        const elems = if (is_tuple) self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, ty0).elems) else &.{};

        for (ids, 0..) |eid, i| {
            const expect_elem = if (is_tuple and i < elems.len) elems[i] else null;
            vals[i] = try self.lowerExpr(ctx, a, env, f, blk, eid, expect_elem, .rvalue);
        }
    }

    var fields_buf: [32]tir.Rows.StructFieldInit = undefined;
    var fields: []tir.Rows.StructFieldInit = if (vals.len <= 32) fields_buf[0..vals.len] else try self.gpa.alloc(tir.Rows.StructFieldInit, vals.len);
    defer if (vals.len > 32) self.gpa.free(fields);

    for (vals, 0..) |val, j| {
        fields[j] = .{ .index = @intCast(j), .name = .none(), .value = val };
    }

    const v = blk.builder.structMake(blk, ty0, fields, loc);
    return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
}

/// Lower struct literals by computing each field init and applying defaults when needed.
fn lowerStructLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.StructLit, id);
    var ty0 = expected_ty orelse self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);

    if (self.context.type_store.getKind(ty0) == .Optional) {
        const opt = self.context.type_store.get(.Optional, ty0);
        if (self.context.type_store.getKind(opt.elem) == .Struct) ty0 = opt.elem;
    }

    const ty0_kind = self.context.type_store.getKind(ty0);
    const fids = a.exprs.sfv_pool.slice(row.fields);
    var spread_expr: ?ast.ExprId = null;
    for (fids) |fid_idx| {
        if (ast.structFieldSpreadExpr(a, fid_idx)) |payload| {
            spread_expr = payload;
            break;
        }
    }

    if ((ty0_kind == .Variant or ty0_kind == .Error) and !row.ty.isNone() and a.kind(row.ty.unwrap()) == .FieldAccess) {
        const fr = a.exprs.get(.FieldAccess, row.ty.unwrap());
        if (self.tagIndexForCase(ty0, fr.field)) |tag_idx| {
            const fields = if (ty0_kind == .Variant)
                self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, ty0).variants)
            else
                self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, ty0).variants);
            const payload_ty = self.context.type_store.Field.get(fields[tag_idx]).ty;
            if (self.context.type_store.getKind(payload_ty) == .Struct) {
                const payload_val = try self.lowerStructLit(ctx, a, env, f, blk, id, payload_ty);
                const union_ty = self.getUnionTypeFromVariant(ty0) orelse return error.LoweringBug;
                const union_val = blk.builder.tirValue(.UnionMake, blk, union_ty, loc, .{ .field_index = tag_idx, .value = payload_val });
                const tag_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), loc, .{ .value = tag_idx });
                const v = blk.builder.structMake(blk, ty0, &[_]tir.Rows.StructFieldInit{
                    .{ .index = 0, .name = .none(), .value = tag_val },
                    .{ .index = 1, .name = .none(), .value = union_val },
                }, loc);
                return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
            }
        }
    }

    if (spread_expr != null) {
        if (ty0_kind != .Struct) return error.LoweringBug;

        const type_fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, ty0).fields);
        const base_val = try self.lowerExpr(ctx, a, env, f, blk, spread_expr.?, ty0, .rvalue);
        var field_inits = try self.gpa.alloc(tir.Rows.StructFieldInit, type_fields.len);
        defer self.gpa.free(field_inits);

        for (type_fields, 0..) |fid, j| {
            const fdef = self.context.type_store.Field.get(fid);
            field_inits[j] = .{
                .index = @intCast(j),
                .name = .some(fdef.name),
                .value = blk.builder.extractField(blk, fdef.ty, base_val, @intCast(j), loc),
            };
        }

        for (fids) |fid_idx| {
            const sfv = a.exprs.StructFieldValue.get(fid_idx);
            if (sfv.name.isNone()) continue;
            var field_idx: ?usize = null;
            var want: types.TypeId = self.context.type_store.tAny();
            const name_id = sfv.name.unwrap();
            for (type_fields, 0..) |fid, j| {
                const fdef = self.context.type_store.Field.get(fid);
                if (fdef.name.eq(name_id)) {
                    field_idx = j;
                    want = fdef.ty;
                    break;
                }
            }
            const idx = field_idx orelse return error.LoweringBug;
            field_inits[idx].value = try self.lowerExpr(ctx, a, env, f, blk, sfv.value, want, .rvalue);
        }

        const v = blk.builder.structMake(blk, ty0, field_inits, loc);
        return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
    }

    var field_inits = List(tir.Rows.StructFieldInit){};
    defer field_inits.deinit(self.gpa);
    try field_inits.ensureTotalCapacity(self.gpa, fids.len); // Optimization: Pre-allocate known minimum

    const type_fields = switch (ty0_kind) {
        .Struct => self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, ty0).fields),
        .Union => self.context.type_store.field_pool.slice(self.context.type_store.get(.Union, ty0).fields),
        else => &[_]types.FieldId{},
    };

    var provided_mask: ?[]bool = null;
    if (ty0_kind == .Struct and !row.ty.isNone()) {
        provided_mask = try self.gpa.alloc(bool, type_fields.len);
        @memset(provided_mask.?, false);
    }
    defer if (provided_mask) |mask| self.gpa.free(mask);

    for (fids, 0..) |fid_idx, i| {
        const sfv = a.exprs.StructFieldValue.get(fid_idx);
        var field_idx: ?usize = null;
        var want: types.TypeId = self.context.type_store.tAny();

        if (!sfv.name.isNone()) {
            const name_id = sfv.name.unwrap();
            for (type_fields, 0..) |fid, j| {
                const fdef = self.context.type_store.Field.get(fid);
                if (fdef.name.eq(name_id)) {
                    field_idx = j;
                    want = fdef.ty;
                    break;
                }
            }
        } else if (i < type_fields.len) {
            field_idx = i;
            want = self.context.type_store.Field.get(type_fields[i]).ty;
        }

        const v_val = try self.lowerExpr(ctx, a, env, f, blk, sfv.value, want, .rvalue);
        const final_idx = field_idx orelse i;
        if (provided_mask) |mask| {
            if (field_idx) |idx| mask[idx] = true;
        }
        field_inits.appendAssumeCapacity(.{ .index = @intCast(final_idx), .name = sfv.name, .value = v_val });
    }

    if (provided_mask) |mask| {
        const type_expr = row.ty.unwrap();
        var j: usize = 0;
        while (j < mask.len) : (j += 1) {
            if (mask[j]) continue;
            const fid = type_fields[j];
            const field_def = self.context.type_store.Field.get(fid);
            if (self.structFieldDefaultExpr(a, type_expr, field_def.name)) |default_expr| {
                const default_val = try self.lowerExpr(ctx, a, env, f, blk, default_expr, field_def.ty, .rvalue);
                try field_inits.append(self.gpa, .{
                    .index = @intCast(j),
                    .name = .some(field_def.name),
                    .value = default_val,
                });
            }
        }
    }

    const field_slice = try field_inits.toOwnedSlice(self.gpa);
    defer self.gpa.free(field_slice);

    const v = if (ty0_kind == .Union) blk_u: {
        std.debug.assert(field_slice.len == 1);
        break :blk_u blk.builder.tirValue(.UnionMake, blk, ty0, loc, .{
            .field_index = field_slice[0].index,
            .value = field_slice[0].value,
        });
    } else blk.builder.structMake(blk, ty0, field_slice, loc);

    return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
}

/// Lower map literals by emitting a runtime call that constructs the map from key/value pairs.
fn lowerMapLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.MapLit, id);
    var ty0 = expected_ty orelse self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const kv_ids = a.exprs.kv_pool.slice(row.entries);

    var key_ty = self.context.type_store.tAny();
    var val_ty = self.context.type_store.tAny();

    if (self.context.type_store.getKind(ty0) == .Map) {
        const mr = self.context.type_store.get(.Map, ty0);
        key_ty = mr.key;
        val_ty = mr.value;
    } else if (kv_ids.len > 0) {
        const first = a.exprs.KeyValue.get(kv_ids[0]);
        key_ty = self.getExprType(ctx, a, first.key);
        val_ty = self.getExprType(ctx, a, first.value);
        ty0 = self.context.type_store.mkMap(key_ty, val_ty);
    }

    const entry_ty = self.context.type_store.mkStruct(&.{
        .{ .name = self.context.type_store.strs.intern("key"), .ty = key_ty },
        .{ .name = self.context.type_store.strs.intern("value"), .ty = val_ty },
    }, 0);

    const entry_size = check_types.typeSize(self.context, entry_ty);
    const key_size = check_types.typeSize(self.context, key_ty);
    const value_offset = std.mem.alignForward(usize, key_size, check_types.typeAlign(self.context, val_ty));

    const map_ptr_ty = self.context.type_store.mkPtr(ty0, false);
    const map_slot = blk.builder.tirValue(.Alloca, blk, map_ptr_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });

    const empty_map = blk.builder.call(blk, ty0, blk.builder.intern("builtin_map_empty"), &.{}, loc);
    _ = blk.builder.tirValue(.Store, blk, ty0, loc, .{ .ptr = map_slot, .value = empty_map, .@"align" = 0 });

    const ptr_u8_ty = self.context.type_store.mkPtr(self.context.type_store.tU8(), false);
    const key_size_v = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = key_size });
    const entry_size_v = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = entry_size });
    const value_off_v = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = value_offset });
    const val_ptr_ty = self.context.type_store.mkPtr(val_ty, false);
    const insert_fn = blk.builder.intern("builtin_map_get_or_insert");

    const key_ptr_ty = self.context.type_store.mkPtr(key_ty, false);
    const key_buf = blk.builder.tirValue(.Alloca, blk, key_ptr_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });
    const key_u8 = blk.builder.tirValue(.CastBit, blk, ptr_u8_ty, loc, .{ .value = key_buf });

    for (kv_ids) |kv_id| {
        const kv = a.exprs.KeyValue.get(kv_id);
        const key_v = try self.lowerExpr(ctx, a, env, f, blk, kv.key, key_ty, .rvalue);
        const val_v = try self.lowerExpr(ctx, a, env, f, blk, kv.value, val_ty, .rvalue);

        _ = blk.builder.tirValue(.Store, blk, key_ty, loc, .{ .ptr = key_buf, .value = key_v, .@"align" = 0 });
        const raw_ptr = blk.builder.call(blk, ptr_u8_ty, insert_fn, &.{ map_slot, key_u8, key_size_v, entry_size_v, value_off_v }, loc);
        const val_ptr = blk.builder.tirValue(.CastBit, blk, val_ptr_ty, loc, .{ .value = raw_ptr });
        _ = blk.builder.tirValue(.Store, blk, val_ty, loc, .{ .ptr = val_ptr, .value = val_v, .@"align" = 0 });
    }

    const final_map = blk.builder.tirValue(.Load, blk, ty0, loc, .{ .ptr = map_slot, .@"align" = 0 });
    return if (expected_ty) |want| self.emitCoerce(blk, final_map, ty0, want, loc) else final_map;
}

/// Map index access (get or insert) lowered via runtime helper.
fn lowerMapIndex(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    map_ty: types.TypeId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const loc = optLoc(a, id);
    const mr = self.context.type_store.get(.Map, map_ty);
    const row = a.exprs.get(.IndexAccess, id);

    const map_ptr = try self.lowerExpr(ctx, a, env, f, blk, row.collection, self.context.type_store.mkPtr(map_ty, false), .lvalue_addr);
    const key_val = try self.lowerExpr(ctx, a, env, f, blk, row.index, mr.key, .rvalue);

    const key_ptr_ty = self.context.type_store.mkPtr(mr.key, false);
    const key_buf = blk.builder.tirValue(.Alloca, blk, key_ptr_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });
    _ = blk.builder.tirValue(.Store, blk, mr.key, loc, .{ .ptr = key_buf, .value = key_val, .@"align" = 0 });

    const key_size = check_types.typeSize(self.context, mr.key);
    const value_offset = std.mem.alignForward(usize, key_size, check_types.typeAlign(self.context, mr.value));
    const entry_ty = self.context.type_store.mkStruct(&.{
        .{ .name = self.context.type_store.strs.intern("key"), .ty = mr.key },
        .{ .name = self.context.type_store.strs.intern("value"), .ty = mr.value },
    }, 0);
    const entry_size = check_types.typeSize(self.context, entry_ty);

    const ptr_u8_ty = self.context.type_store.mkPtr(self.context.type_store.tU8(), false);
    const make = blk.builder.intern("builtin_map_get_or_insert");
    const raw_ptr = blk.builder.call(blk, ptr_u8_ty, make, &.{
        map_ptr,
        blk.builder.tirValue(.CastBit, blk, ptr_u8_ty, loc, .{ .value = key_buf }),
        blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = key_size }),
        blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = entry_size }),
        blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = value_offset }),
    }, loc);

    const val_ptr = blk.builder.tirValue(.CastBit, blk, self.context.type_store.mkPtr(mr.value, false), loc, .{ .value = raw_ptr });

    if (mode == .lvalue_addr) return val_ptr;
    const loaded = blk.builder.tirValue(.Load, blk, mr.value, loc, .{ .ptr = val_ptr, .@"align" = 0 });
    return if (expected_ty) |want| self.emitCoerce(blk, loaded, mr.value, want, loc) else loaded;
}

/// Lower index access expressions to the appropriate GEP/load or optional indexing form.
fn lowerIndexAccess(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.IndexAccess, id);
    const base_ty = self.getExprType(ctx, a, row.collection);
    if (self.context.type_store.getKind(base_ty) == .Map) {
        return try self.lowerMapIndex(ctx, a, env, f, blk, id, base_ty, expected_ty, mode);
    }
    const loc = optLoc(a, id);

    if (mode == .lvalue_addr) {
        const idx_v = blk_idx: {
            if (a.kind(row.index) == .Literal) {
                const lit = a.exprs.get(.Literal, row.index);
                if (lit.kind == .int and lit.data == .int and lit.data.int.valid) {
                    break :blk_idx blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = @as(u64, @intCast(lit.data.int.value)) });
                }
            }
            break :blk_idx try self.lowerExpr(ctx, a, env, f, blk, row.index, self.context.type_store.tUsize(), .rvalue);
        };
        const idx = blk.builder.gepValue(idx_v);
        const elem_ty = self.getExprType(ctx, a, id);
        const ptr_elem_ty = self.context.type_store.mkPtr(elem_ty, false);
        const base_kind = self.context.type_store.getKind(base_ty);

        if (base_kind == .Slice or base_kind == .DynArray or base_kind == .String) {
            const base_val = try self.lowerExpr(ctx, a, env, f, blk, row.collection, null, .rvalue);
            const data_ptr = blk.builder.tirValue(.ExtractField, blk, ptr_elem_ty, loc, .{ .agg = base_val, .index = 0, .name = OptStrId.none() });
            return blk.builder.gep(blk, ptr_elem_ty, data_ptr, &.{idx}, loc);
        }

        const base_ptr = if (base_kind == .Ptr)
            try self.lowerExpr(ctx, a, env, f, blk, row.collection, null, .rvalue)
        else
            try self.lowerExpr(ctx, a, env, f, blk, row.collection, null, .lvalue_addr);

        const is_array = base_kind == .Array or (base_kind == .Ptr and self.context.type_store.getKind(self.context.type_store.get(.Ptr, base_ty).elem) == .Array);
        return if (is_array)
            blk.builder.gep(blk, ptr_elem_ty, base_ptr, &.{ blk.builder.gepConst(0), idx }, loc)
        else
            blk.builder.gep(blk, ptr_elem_ty, base_ptr, &.{idx}, loc);
    } else {
        const ty0 = self.getExprType(ctx, a, id);
        const is_addressable = switch (a.kind(row.collection)) {
            .Ident, .FieldAccess, .IndexAccess, .Deref => true,
            else => false,
        };
        const prefer_addr = is_addressable and self.context.type_store.getKind(base_ty) == .Array;

        const base = if (prefer_addr)
            try self.lowerExpr(ctx, a, env, f, blk, row.collection, null, .lvalue_addr)
        else
            try self.lowerExpr(ctx, a, env, f, blk, row.collection, null, .rvalue);

        const idx = blk_idx: {
            if (self.context.type_store.getKind(self.getExprType(ctx, a, row.index)) == .Slice) {
                break :blk_idx try self.lowerExpr(ctx, a, env, f, blk, row.index, self.context.type_store.mkSlice(self.context.type_store.tUsize(), false), .rvalue);
            }
            if (a.kind(row.index) == .Literal) {
                const lit = a.exprs.get(.Literal, row.index);
                if (lit.kind == .int and lit.data == .int and lit.data.int.valid) {
                    break :blk_idx blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tUsize(), loc, .{ .value = @as(u64, @intCast(lit.data.int.value)) });
                }
            }
            break :blk_idx try self.lowerExpr(ctx, a, env, f, blk, row.index, self.context.type_store.tUsize(), .rvalue);
        };

        const v = blk.builder.indexOp(blk, ty0, base, idx, loc);
        return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
    }
}

/// Lower an enum member reference to its integer discriminant constant.
fn lowerEnumMember(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    parent_expr: ast.ExprId,
    expected_ty: ?types.TypeId,
) !?tir.ValueId {
    const parent_ty = self.getExprType(ctx, a, parent_expr);
    const enum_ty: types.TypeId = switch (self.context.type_store.getKind(parent_ty)) {
        .Enum => parent_ty,
        .TypeType => blk: {
            const of = self.context.type_store.get(.TypeType, parent_ty).of;
            if (self.context.type_store.getKind(of) != .Enum) return null;
            break :blk of;
        },
        else => return null,
    };

    const ty0 = self.getExprType(ctx, a, id);
    const loc = optLoc(a, id);
    const value = self.enumMemberValue(enum_ty, a.exprs.get(.FieldAccess, id).field) orelse return null;

    const ev = blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = value });
    return if (expected_ty) |want| self.emitCoerce(blk, ev, ty0, want, loc) else ev;
}

/// Lower a literal variant tag (`T::Case`) when its payload is void.
fn lowerVariantTagLiteral(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    parent_expr: ast.ExprId,
    expected_ty: ?types.TypeId,
) !?tir.ValueId {
    const ty = self.getExprType(parent_expr) orelse return null;
    if (self.context.type_store.getKind(ty) != .TypeType) return null;

    const of = self.context.type_store.get(.TypeType, ty).of;
    const of_kind = self.context.type_store.getKind(of);
    if (of_kind != .Variant and of_kind != .Error) return null;

    const fields = if (of_kind == .Variant)
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, of).variants)
    else
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, of).variants);

    const tag_idx = self.type_info.getFieldIndex(id) orelse return null;
    const payload_ty = self.context.type_store.Field.get(fields[tag_idx]).ty;

    if (self.context.type_store.getKind(payload_ty) != .Void) return null;

    const ty0 = self.getExprType(ctx, a, id) orelse (expected_ty orelse self.context.type_store.tAny());
    const loc = optLoc(a, id);
    const tag_val = blk.builder.extractField(blk, self.context.type_store.tI32(), self.safeUndef(blk, ty, loc), 0, loc);

    return if (expected_ty) |want| self.emitCoerce(blk, tag_val, ty0, want, loc) else tag_val;
}

/// Lookup the position of `field_name` inside `parent_ty`, recursing through pointers.
fn getFieldIndex(self: *LowerTir, parent_ty: types.TypeId, field_name: ast.StrId) ?u32 {
    const ty_kind = self.context.type_store.getKind(parent_ty);
    switch (ty_kind) {
        .Struct => {
            const fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, parent_ty).fields);
            for (fields, 0..) |fid, i| {
                if (self.context.type_store.Field.get(fid).name.eq(field_name)) return @intCast(i);
            }
        },
        .Union => {
            const fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Union, parent_ty).fields);
            for (fields, 0..) |fid, i| {
                if (self.context.type_store.Field.get(fid).name.eq(field_name)) return @intCast(i);
            }
        },
        .Error => {
            const fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, parent_ty).variants);
            for (fields, 0..) |fid, i| {
                if (self.context.type_store.Field.get(fid).name.eq(field_name)) return @intCast(i);
            }
        },
        .Variant => {
            const fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, parent_ty).variants);
            for (fields, 0..) |fid, i| {
                if (self.context.type_store.Field.get(fid).name.eq(field_name)) return @intCast(i);
            }
        },
        .TypeType => return self.getFieldIndex(self.context.type_store.get(.TypeType, parent_ty).of, field_name),
        .Ptr => return self.getFieldIndex(self.context.type_store.get(.Ptr, parent_ty).elem, field_name),
        else => {},
    }
    return null;
}

/// Lower field access expressions, covering len/ptr/capacity, module members, variants, and structs.
fn lowerFieldAccess(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.FieldAccess, id);
    const loc = optLoc(a, id);
    const parent_ty = self.getExprType(ctx, a, row.parent);
    const parent_kind = self.context.type_store.getKind(parent_ty);
    const field_name = a.exprs.strs.get(row.field);

    // Special fields: len, ptr, capacity
    if (std.mem.eql(u8, field_name, "len")) {
        if (parent_kind == .Array) {
            const len = self.context.type_store.get(.Array, parent_ty).len;
            const ty0 = self.context.type_store.tUsize();
            const v = blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = @as(u64, @intCast(len)) });
            return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
        }
        if (parent_kind == .Tuple) {
            const len = self.context.type_store.get(.Tuple, parent_ty).elems.len;
            const ty0 = self.context.type_store.tUsize();
            const v = blk.builder.tirValue(.ConstInt, blk, ty0, loc, .{ .value = @as(u64, @intCast(len)) });
            return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
        }
        if (parent_kind == .Slice or parent_kind == .DynArray or parent_kind == .String) {
            const base = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, .rvalue);
            const ty0 = self.context.type_store.tUsize();
            const v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
            return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
        }
    } else if (std.mem.eql(u8, field_name, "ptr")) {
        const ptr_ty: ?types.TypeId = switch (parent_kind) {
            .Slice => self.context.type_store.mkPtr(self.context.type_store.get(.Slice, parent_ty).elem, false),
            .DynArray => self.context.type_store.mkPtr(self.context.type_store.get(.DynArray, parent_ty).elem, false),
            .String => self.context.type_store.mkPtr(self.context.type_store.tU8(), true),
            else => null,
        };
        if (ptr_ty) |ty0| {
            const base = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, .rvalue);
            const v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
            return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
        }
    } else if (std.mem.eql(u8, field_name, "capacity") and parent_kind == .DynArray) {
        const base = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, .rvalue);
        const ty0 = self.context.type_store.tUsize();
        const v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
        return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
    }

    // Imported module member
    if (mode == .rvalue) {
        const pk = a.kind(row.parent);
        if (pk == .Ident or pk == .Import) {
            if (try self.tryLowerImportedModuleMember(a, blk, row.parent, row.field, expected_ty, loc)) |v| return v;
        }
    }

    const idx_maybe = a.type_info.getFieldIndex(id) orelse self.getFieldIndex(parent_ty, row.field);

    // Enum constant
    if (mode == .rvalue) {
        if (try self.lowerEnumMember(ctx, a, blk, id, row.parent, expected_ty)) |v| return v;
    }

    // Address path (LValue)
    if (mode == .lvalue_addr) {
        const parent_lower_mode: LowerMode = if (parent_kind == .Ptr) .rvalue else .lvalue_addr;
        const parent_ptr = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, parent_lower_mode);
        const idx = idx_maybe orelse return self.throwErr(a.exprs.locs.get(row.loc));
        const rptr_ty = self.context.type_store.mkPtr(self.getExprType(ctx, a, id), false);

        if (parent_kind == .Union) {
            return blk.builder.tirValue(.UnionFieldPtr, blk, rptr_ty, loc, .{ .base = parent_ptr, .field_index = idx });
        }
        return blk.builder.gep(blk, rptr_ty, parent_ptr, &.{ blk.builder.gepConst(0), blk.builder.gepConst(@intCast(idx)) }, loc);
    }

    // RValue extraction
    const ty0 = self.getExprType(ctx, a, id);
    const base = try self.lowerExpr(ctx, a, env, f, blk, row.parent, null, .rvalue);

    if (idx_maybe) |resolved_idx| {
        if (parent_kind == .Variant) {
            if (row.is_tuple) return blk.builder.extractField(blk, ty0, base, resolved_idx, loc);

            const variants = self.context.type_store.get(.Variant, parent_ty).variants;
            const fields = self.context.type_store.field_pool.slice(variants);

            // Stack allocate small variants
            var stack_args: [16]types.TypeStore.StructFieldArg = undefined;
            var heap_args: []types.TypeStore.StructFieldArg = &.{};
            defer if (heap_args.len > 0) self.gpa.free(heap_args);

            const union_fields_args = if (fields.len <= 16) stack_args[0..fields.len] else blk_alloc: {
                heap_args = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                break :blk_alloc heap_args;
            };

            for (fields, 0..) |fld_id, i| {
                const fld = self.context.type_store.Field.get(fld_id);
                union_fields_args[i] = .{ .name = fld.name, .ty = fld.ty };
            }
            const union_ty = self.context.type_store.mkUnion(union_fields_args);
            const union_val = blk.builder.extractField(blk, union_ty, base, 1, loc);
            return blk.builder.tirValue(.UnionField, blk, ty0, loc, .{ .base = union_val, .field_index = resolved_idx });
        } else if (parent_kind == .Ptr) {
            const field_ptr = try self.lowerExpr(ctx, a, env, f, blk, id, null, .lvalue_addr);
            return blk.builder.tirValue(.Load, blk, ty0, loc, .{ .ptr = field_ptr, .@"align" = 0 });
        } else if (parent_kind == .TypeType) {
            const of_ty = self.context.type_store.get(.TypeType, parent_ty).of;
            const of_kind = self.context.type_store.getKind(of_ty);
            std.debug.assert(of_kind == .Variant or of_kind == .Error);

            const fields = if (of_kind == .Variant)
                self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, of_ty).variants)
            else
                self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, of_ty).variants);

            const payload_ty = self.context.type_store.Field.get(fields[resolved_idx]).ty;
            const tag_val = blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), loc, .{ .value = resolved_idx });

            // Re-use allocation logic or use stack for construction
            var stack_args: [16]types.TypeStore.StructFieldArg = undefined;
            var heap_args: []types.TypeStore.StructFieldArg = &.{};
            defer if (heap_args.len > 0) self.gpa.free(heap_args);

            const union_fields_args = if (fields.len <= 16) stack_args[0..fields.len] else blk_alloc: {
                heap_args = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                break :blk_alloc heap_args;
            };

            for (fields, 0..) |fld_id, i| {
                const fld = self.context.type_store.Field.get(fld_id);
                union_fields_args[i] = .{ .name = fld.name, .ty = fld.ty };
            }
            const union_ty = self.context.type_store.mkUnion(union_fields_args);
            const union_val = if (self.context.type_store.getKind(payload_ty) == .Void)
                blk.builder.tirValue(.ConstUndef, blk, union_ty, loc, .{})
            else
                blk.builder.tirValue(.UnionMake, blk, union_ty, loc, .{ .field_index = resolved_idx, .value = self.safeUndef(blk, payload_ty, loc) });

            const v_res = blk.builder.structMake(blk, of_ty, &[_]tir.Rows.StructFieldInit{
                .{ .index = 0, .name = .none(), .value = tag_val },
                .{ .index = 1, .name = .none(), .value = union_val },
            }, loc);

            return if (expected_ty) |want| self.emitCoerce(blk, v_res, of_ty, want, loc) else v_res;
        } else if (self.context.type_store.getKind(parent_ty) == .Tuple) {
            return blk.builder.extractElem(blk, ty0, base, resolved_idx, loc);
        } else if (parent_kind == .Union) {
            return blk.builder.tirValue(.UnionField, blk, ty0, loc, .{ .base = base, .field_index = resolved_idx });
        } else {
            const res_ty = if (self.context.type_store.getKind(ty0) == .Any) self.context.type_store.tUsize() else ty0;
            return blk.builder.extractField(blk, res_ty, base, resolved_idx, loc);
        }
    }

    const v = blk.builder.extractFieldNamed(blk, ty0, base, row.field, loc);
    return if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
}

/// Try to lower `parent.field` where parent is an imported module.
fn tryLowerImportedModuleMember(
    self: *LowerTir,
    caller_ast: *ast.Ast,
    blk: *Builder.BlockFrame,
    parent_expr: ast.ExprId,
    field_name: ast.StrId,
    expected_ty: ?types.TypeId,
    loc: ast.OptLocId,
) !?tir.ValueId {
    const parent_kind = caller_ast.kind(parent_expr);
    var target_ast: ?*ast.Ast = null;

    // Resolve module AST
    const path_sid: ?ast.StrId = if (parent_kind == .Import)
        caller_ast.exprs.get(.Import, parent_expr).path
    else if (parent_kind == .Ident) blk: {
        const name = caller_ast.exprs.get(.Ident, parent_expr).name;
        const did = call_resolution.findDeclId(caller_ast, name) orelse break :blk null;
        const decl = caller_ast.exprs.Decl.get(did);
        if (caller_ast.kind(decl.value) != .Import) break :blk null;
        break :blk caller_ast.exprs.get(.Import, decl.value).path;
    } else null;

    if (path_sid) |pid| {
        const path = caller_ast.exprs.strs.get(pid);
        var it = self.context.compilation_unit.packages.iterator();
        while (it.next()) |pkg| {
            if (pkg.value_ptr.sources.get(path)) |unit_ref| {
                target_ast = unit_ref.ast;
                break;
            }
        }
    }

    const ta = target_ast orelse return null;
    const ex = ta.type_info.getExport(field_name) orelse return null;

    if (self.context.type_store.getKind(ex.ty) == .Function) return null;

    const name = try self.qualifySymbolName(ta, field_name);
    const ptr_ty = self.context.type_store.mkPtr(ex.ty, false);
    const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = name });
    const val = blk.builder.tirValue(.Load, blk, ex.ty, loc, .{ .ptr = addr, .@"align" = 0 });

    return if (expected_ty) |want| self.emitCoerce(blk, val, ex.ty, want, loc) else val;
}

/// Lower identifier expressions, resolving globals/locals/types/slots and emitting loads.
fn lowerIdentAddrByName(
    self: *LowerTir,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    name: ast.StrId,
    expr_ty: types.TypeId,
    want_elem: types.TypeId,
    loc: tir.OptLocId,
) anyerror!tir.ValueId {
    if (env.lookup(name)) |bnd| {
        if (bnd.is_slot) return bnd.value;
        if (self.context.type_store.getKind(bnd.ty) == .Ptr) return bnd.value;
    }

    const did_opt = call_resolution.findDeclId(a, name);
    if (did_opt) |did| {
        const d = a.exprs.Decl.get(did);
        const gty = getDeclType(a, did) orelse unreachable;
        if (self.context.type_store.getKind(gty) != .TypeType) {
            const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
            const sym = (try self.symbolNameForDecl(a, did)) orelse name;
            return blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = sym });
        }
    }

    if (env.lookup(name)) |bnd| {
        const slot_ty = self.context.type_store.mkPtr(want_elem, false);
        const slot = f.builder.tirValue(.Alloca, blk, slot_ty, loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });
        const src_ty = if (!self.isType(expr_ty, .Any)) expr_ty else bnd.ty;
        const to_store = self.emitCoerce(blk, bnd.value, src_ty, want_elem, loc);
        _ = f.builder.tirValue(.Store, blk, want_elem, loc, .{ .ptr = slot, .value = to_store, .@"align" = 0 });
        try env.bind(self.gpa, name, .{ .value = slot, .ty = want_elem, .is_slot = true }, f.builder, blk, loc);
        return slot;
    }

    try self.context.diags.addError(a.exprs.locs.get(loc.unwrap()), .undefined_identifier, .{});
    return error.LoweringBug;
}

fn lowerIdent(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Ident, id);
    const name = row.name;
    const loc = optLoc(a, id);
    var expr_ty = self.getExprType(ctx, a, id);
    const did_opt = call_resolution.findDeclId(a, name);

    if (self.lookupComptimeAliasType(a, name)) |bound_ty| {
        expr_ty = self.context.type_store.mkTypeType(bound_ty);
    }

    const want_elem = if (expected_ty) |want|
        if (self.context.type_store.getKind(want) == .Ptr) self.context.type_store.get(.Ptr, want).elem else expr_ty
    else
        expr_ty;

    if (mode == .lvalue_addr) {
        return try self.lowerIdentAddrByName(a, env, f, blk, name, expr_ty, want_elem, loc);
    }

    // RValue Path
    const bnd = env.lookup(name) orelse blk_b: {
        if (did_opt) |did| {
            const d = a.exprs.Decl.get(did);
            const gty = getDeclType(a, did) orelse unreachable;
            if (self.context.type_store.getKind(gty) != .TypeType) {
                const ptr_ty = self.context.type_store.mkPtr(gty, !d.flags.is_const);
                const sym = (try self.symbolNameForDecl(a, did)) orelse name;
                const addr = blk.builder.tirValue(.GlobalAddr, blk, ptr_ty, loc, .{ .name = sym });
                const is_fn = self.context.type_store.getKind(gty) == .Function;
                break :blk_b ValueBinding{ .value = addr, .ty = gty, .is_slot = !is_fn };
            }
        }
        const placeholder = self.safeUndef(blk, expr_ty, loc);
        try env.bind(self.gpa, name, .{ .value = placeholder, .ty = expr_ty, .is_slot = false }, f.builder, blk, loc);
        break :blk_b env.lookup(name).?;
    };

    if (bnd.is_slot) {
        const load_ty = if (!self.isType(expr_ty, .Any)) expr_ty else bnd.ty;
        var loaded = blk.builder.tirValue(.Load, blk, load_ty, loc, .{ .ptr = bnd.value, .@"align" = 0 });
        if (expected_ty) |want| loaded = self.emitCoerce(blk, loaded, load_ty, want, loc);
        return loaded;
    }

    const got_ty = if (!self.isType(expr_ty, .Any)) expr_ty else bnd.ty;
    return if (expected_ty) |want| self.emitCoerce(blk, bnd.value, got_ty, want, loc) else bnd.value;
}

fn isScalarNumeric(kind: types.TypeKind) bool {
    return switch (kind) {
        .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64, .Usize, .F32, .F64 => true,
        else => false,
    };
}

/// Lower binary expressions, including comparisons, arithmetic, and short-circuit helpers.
fn lowerBinary(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Binary, id);
    const loc = optLoc(a, id);

    // Variant/Error equality fast-path
    if (row.op == .eq or row.op == .neq) {
        const l_ty = self.getExprType(ctx, a, row.left);
        const r_ty = self.getExprType(ctx, a, row.right);

        const check_tag = struct {
            fn run(s: *LowerTir, c: *LowerContext, ast_: *ast.Ast, e: *cf.Env, fr: *Builder.FunctionFrame, b: *Builder.BlockFrame, val_expr: ast.ExprId, val_ty: types.TypeId, tag_path: ast.ExprId, op: ast.BinaryOp, l: tir.OptLocId) !?tir.ValueId {
                if (!s.isVariantLike(val_ty)) return null;
                const info = s.tagConstFromTypePath(c, ast_, tag_path) orelse return null;
                if (!info.of_ty.eq(val_ty)) return null;

                const val = try s.lowerExpr(c, ast_, e, fr, b, val_expr, val_ty, .rvalue);
                const tag = b.builder.extractField(b, s.context.type_store.tI32(), val, 0, l);
                const want = b.builder.tirValue(.ConstInt, b, s.context.type_store.tI32(), l, .{ .value = info.tag_idx });
                return if (op == .eq) b.builder.binBool(b, .CmpEq, tag, want, l) else b.builder.binBool(b, .CmpNe, tag, want, l);
            }
        };

        if (try check_tag.run(self, ctx, a, env, f, blk, row.left, l_ty, row.right, row.op, loc)) |res| return res;
        if (try check_tag.run(self, ctx, a, env, f, blk, row.right, r_ty, row.left, row.op, loc)) |res| return res;
    }

    const lhs_stamped = self.getExprType(ctx, a, row.left);
    const rhs_stamped = self.getExprType(ctx, a, row.right);
    const lhs_hint = try self.refineExprType(ctx, a, env, row.left, lhs_stamped);
    const rhs_hint = try self.refineExprType(ctx, a, env, row.right, rhs_stamped);

    var lhs_expect: ?types.TypeId = null;
    var rhs_expect: ?types.TypeId = null;
    var op_ty: ?types.TypeId = self.getExprType(ctx, a, id);

    // Type Election Logic
    switch (row.op) {
        .add, .sub, .mul, .div, .mod, .shl, .shr, .bit_and, .bit_or, .bit_xor => {
            const chosen = blk_ty: {
                const lk = self.context.type_store.getKind(lhs_hint orelse lhs_stamped);
                const rk = self.context.type_store.getKind(rhs_hint orelse rhs_stamped);
                const l_ptr = lk == .Ptr or lk == .MlirType;
                const r_ptr = rk == .Ptr or rk == .MlirType;

                // Tensor arithmetic
                if ((row.op == .add or row.op == .sub) and ((l_ptr and rk == .Tensor) or (r_ptr and lk == .Tensor))) {
                    if (op_ty) |t| if (!self.isVoid(t) and !self.isType(t, .Any)) break :blk_ty t;
                    break :blk_ty if (l_ptr) lhs_hint orelse lhs_stamped else rhs_hint orelse rhs_stamped;
                }
                if (op_ty) |t| if (!self.isVoid(t) and !self.isType(t, .Any)) break :blk_ty t;
                break :blk_ty (self.commonNumeric(lhs_hint, rhs_hint) orelse (expected_ty orelse self.context.type_store.tI64()));
            };

            const ck = self.context.type_store.getKind(chosen);
            const is_ptr_tensor = (row.op == .add or row.op == .sub) and ck == .Tensor and blk_pt: {
                const ek = self.context.type_store.getKind(self.context.type_store.get(.Tensor, chosen).elem);
                break :blk_pt ek == .Ptr or ek == .MlirType;
            };

            op_ty = chosen;
            if (is_ptr_tensor) {
                const lh = lhs_hint orelse lhs_stamped;
                const rh = rhs_hint orelse rhs_stamped;
                const l_ptr = self.context.type_store.getKind(lh) == .Ptr or self.context.type_store.getKind(lh) == .MlirType;
                lhs_expect = if (l_ptr) lh else null;
                rhs_expect = if (self.context.type_store.getKind(rh) == .Ptr or self.context.type_store.getKind(rh) == .MlirType) rh else if (!l_ptr) rh else null;
            } else if (ck == .Tensor or ck == .Ptr or ck == .MlirType) {
                lhs_expect = if (self.context.type_store.getKind(lhs_hint orelse lhs_stamped) == ck) chosen else null;
                rhs_expect = if (self.context.type_store.getKind(rhs_hint orelse rhs_stamped) == ck) chosen else null;
            } else if (ck == .Complex) {
                lhs_expect = chosen;
                rhs_expect = chosen;
            } else {
                lhs_expect = chosen;
                rhs_expect = chosen;
                // SIMD Scalar broadcast hints
                if (ck == .Simd) {
                    if (isScalarNumeric(self.context.type_store.getKind(rhs_hint orelse rhs_stamped))) rhs_expect = null;
                    if (isScalarNumeric(self.context.type_store.getKind(lhs_hint orelse lhs_stamped))) lhs_expect = null;
                }
            }
        },
        .eq, .neq, .lt, .lte, .gt, .gte => {
            var tensor_cmp = false;
            if (op_ty) |t| if (self.context.type_store.getKind(t) == .Tensor) {
                lhs_expect = if (self.context.type_store.getKind(lhs_hint orelse lhs_stamped) == .Tensor) lhs_hint orelse lhs_stamped else null;
                rhs_expect = if (self.context.type_store.getKind(rhs_hint orelse rhs_stamped) == .Tensor) rhs_hint orelse rhs_stamped else null;
                tensor_cmp = true;
            };
            if (!tensor_cmp) {
                const want = self.commonNumeric(lhs_hint, rhs_hint) orelse lhs_hint orelse rhs_hint;
                lhs_expect = want;
                rhs_expect = want;
                op_ty = self.context.type_store.tBool();

                // Handle Optional comparisons
                if (row.op == .eq or row.op == .neq) {
                    const l_opt = self.context.type_store.getKind(lhs_hint orelse lhs_stamped) == .Optional;
                    const r_opt = self.context.type_store.getKind(rhs_hint orelse rhs_stamped) == .Optional;
                    if (l_opt and !r_opt) {
                        lhs_expect = lhs_hint orelse lhs_stamped;
                        rhs_expect = self.context.type_store.get(.Optional, lhs_hint orelse lhs_stamped).elem;
                    }
                    if (r_opt and !l_opt) {
                        rhs_expect = rhs_hint orelse rhs_stamped;
                        lhs_expect = self.context.type_store.get(.Optional, rhs_hint orelse rhs_stamped).elem;
                    }
                }
            }
        },
        .logical_and, .logical_or => {
            lhs_expect = self.context.type_store.tBool();
            rhs_expect = lhs_expect;
            op_ty = lhs_expect;
        },
        .@"orelse" => return self.lowerOrelse(ctx, a, env, f, blk, id, expected_ty),
        .contains => {
            try self.context.diags.addError(a.exprs.locs.get(row.loc), .in_operator_not_supported, .{});
            return error.LoweringBug;
        },
    }

    var l = try self.lowerExpr(ctx, a, env, f, blk, row.left, lhs_expect, .rvalue);
    var r = try self.lowerExpr(ctx, a, env, f, blk, row.right, rhs_expect, .rvalue);

    // Explicit Coercions
    if (lhs_expect) |want| {
        const got = self.getExprType(ctx, a, row.left);
        if (!got.eq(want)) l = self.emitCoerce(blk, l, got, want, optLoc(a, row.left));
    }
    if (rhs_expect) |want| {
        const got = self.getExprType(ctx, a, row.right);
        if (!got.eq(want)) r = self.emitCoerce(blk, r, got, want, optLoc(a, row.right));
    }

    // SIMD/Tensor Scalar Broadcasts
    const l_ty_promo = self.getExprType(ctx, a, row.left);
    const r_ty_promo = self.getExprType(ctx, a, row.right);

    if (self.context.type_store.getKind(l_ty_promo) == .Simd and isScalarNumeric(self.context.type_store.getKind(r_ty_promo))) {
        const elem = self.context.type_store.get(.Simd, l_ty_promo).elem;
        r = blk.builder.tirValue(.Broadcast, blk, l_ty_promo, loc, .{ .value = self.emitCoerce(blk, r, r_ty_promo, elem, loc) });
    } else if (self.context.type_store.getKind(r_ty_promo) == .Simd and isScalarNumeric(self.context.type_store.getKind(l_ty_promo))) {
        const elem = self.context.type_store.get(.Simd, r_ty_promo).elem;
        l = blk.builder.tirValue(.Broadcast, blk, r_ty_promo, loc, .{ .value = self.emitCoerce(blk, l, l_ty_promo, elem, loc) });
    }

    // Optional Equality
    const l_opt = self.context.type_store.getKind(l_ty_promo) == .Optional;
    const r_opt = self.context.type_store.getKind(r_ty_promo) == .Optional;

    if ((row.op == .eq or row.op == .neq) and (l_opt or r_opt)) {
        if (l_opt and r_opt) {
            // Compare flags, then payload if present
            const flag_l = self.optionalFlag(blk, l_ty_promo, l, loc);
            const flag_r = self.optionalFlag(blk, r_ty_promo, r, loc);
            const flags_eq = blk.builder.binBool(blk, .CmpEq, flag_l, flag_r, loc);

            // Check if payload comparison needed (non-scalar) or simple scalar
            const elem_ty = self.context.type_store.get(.Optional, l_ty_promo).elem;
            const elem_kind = self.context.type_store.getKind(elem_ty);
            const is_scalar = isScalarNumeric(elem_kind) or elem_kind == .Bool or elem_kind == .Ptr or elem_kind == .MlirType or elem_kind == .Enum or elem_kind == .Error;

            if (is_scalar) {
                var then_blk = try f.builder.beginBlock(f);
                var join_blk = try f.builder.beginBlock(f);
                const res_param = try f.builder.addBlockParam(&join_blk, null, self.context.type_store.tBool());

                try f.builder.condBr(blk, blk.builder.binBool(blk, .LogicalAnd, flag_l, flag_r, loc), then_blk.id, &.{}, join_blk.id, &.{flags_eq}, loc);
                try f.builder.endBlock(f, blk.*);

                const pl = self.optionalPayload(&then_blk, l_ty_promo, l, loc);
                const pr = self.optionalPayload(&then_blk, r_ty_promo, r, loc);
                const peq = then_blk.builder.binBool(&then_blk, .CmpEq, pl, pr, loc);
                try f.builder.br(&then_blk, join_blk.id, &.{peq}, loc);
                try f.builder.endBlock(f, then_blk);

                blk.* = join_blk;
                return if (row.op == .neq)
                    blk.builder.binBool(blk, .CmpEq, res_param, blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false }), loc)
                else
                    res_param;
            }
            return if (row.op == .neq)
                blk.builder.binBool(blk, .CmpEq, flags_eq, blk.builder.tirValue(.ConstBool, blk, self.context.type_store.tBool(), loc, .{ .value = false }), loc)
            else
                flags_eq;
        } else {
            // Mixed Optional/Value equality
            const opt_val = if (l_opt) l else r;
            const opt_ty = if (l_opt) l_ty_promo else r_ty_promo;
            const raw_val = if (l_opt) r else l;
            const raw_ty = if (l_opt) r_ty_promo else l_ty_promo;
            const elem_ty = self.context.type_store.get(.Optional, opt_ty).elem;

            const coerced_raw = if (raw_ty.eq(elem_ty)) raw_val else self.emitCoerce(blk, raw_val, raw_ty, elem_ty, loc);
            const flag = self.optionalFlag(blk, opt_ty, opt_val, loc);
            const payload = self.optionalPayload(blk, opt_ty, opt_val, loc);

            var then_blk = try f.builder.beginBlock(f);
            var else_blk = try f.builder.beginBlock(f);
            var join_blk = try f.builder.beginBlock(f);
            const res_param = try f.builder.addBlockParam(&join_blk, null, self.context.type_store.tBool());

            try f.builder.condBr(blk, flag, then_blk.id, &.{}, else_blk.id, &.{}, loc);
            try f.builder.endBlock(f, blk.*);

            const cmp = if (row.op == .eq) then_blk.builder.binBool(&then_blk, .CmpEq, payload, coerced_raw, loc) else then_blk.builder.binBool(&then_blk, .CmpNe, payload, coerced_raw, loc);
            try f.builder.br(&then_blk, join_blk.id, &.{cmp}, loc);
            try f.builder.endBlock(f, then_blk);

            const else_val = else_blk.builder.tirValue(.ConstBool, &else_blk, self.context.type_store.tBool(), loc, .{ .value = (row.op == .neq) });
            try f.builder.br(&else_blk, join_blk.id, &.{else_val}, loc);
            try f.builder.endBlock(f, else_blk);

            blk.* = join_blk;
            return res_param;
        }
    }

    // Final binary emission
    const t = op_ty orelse self.commonNumeric(l_ty_promo, r_ty_promo) orelse self.context.type_store.tI64();
    try self.noteExprType(ctx, id, t);
    const is_tensor = self.context.type_store.getKind(t) == .Tensor;

    const v = switch (row.op) {
        .add => if (row.saturate) blk.builder.bin(blk, .BinSatAdd, t, l, r, loc) else if (row.wrap) blk.builder.bin(blk, .BinWrapAdd, t, l, r, loc) else blk.builder.bin(blk, .Add, t, l, r, loc),
        .sub => if (row.saturate) blk.builder.bin(blk, .BinSatSub, t, l, r, loc) else if (row.wrap) blk.builder.bin(blk, .BinWrapSub, t, l, r, loc) else blk.builder.bin(blk, .Sub, t, l, r, loc),
        .mul => if (row.saturate) blk.builder.bin(blk, .BinSatMul, t, l, r, loc) else if (row.wrap) blk.builder.bin(blk, .BinWrapMul, t, l, r, loc) else blk.builder.bin(blk, .Mul, t, l, r, loc),
        .div => blk.builder.bin(blk, .Div, t, l, r, loc),
        .mod => blk.builder.bin(blk, .Mod, t, l, r, loc),
        .shl => if (row.saturate) blk.builder.bin(blk, .BinSatShl, t, l, r, loc) else blk.builder.bin(blk, .Shl, t, l, r, loc),
        .shr => blk.builder.bin(blk, .Shr, t, l, r, loc),
        .bit_and => blk.builder.bin(blk, .BitAnd, t, l, r, loc),
        .bit_or => blk.builder.bin(blk, .BitOr, t, l, r, loc),
        .bit_xor => blk.builder.bin(blk, .BitXor, t, l, r, loc),
        .eq => if (is_tensor) blk.builder.bin(blk, .CmpEq, t, l, r, loc) else blk.builder.binBool(blk, .CmpEq, l, r, loc),
        .neq => if (is_tensor) blk.builder.bin(blk, .CmpNe, t, l, r, loc) else blk.builder.binBool(blk, .CmpNe, l, r, loc),
        .lt => if (is_tensor) blk.builder.bin(blk, .CmpLt, t, l, r, loc) else blk.builder.binBool(blk, .CmpLt, l, r, loc),
        .lte => if (is_tensor) blk.builder.bin(blk, .CmpLe, t, l, r, loc) else blk.builder.binBool(blk, .CmpLe, l, r, loc),
        .gt => if (is_tensor) blk.builder.bin(blk, .CmpGt, t, l, r, loc) else blk.builder.binBool(blk, .CmpGt, l, r, loc),
        .gte => if (is_tensor) blk.builder.bin(blk, .CmpGe, t, l, r, loc) else blk.builder.binBool(blk, .CmpGe, l, r, loc),
        .logical_and => blk.builder.binBool(blk, .LogicalAnd, l, r, loc),
        .logical_or => blk.builder.binBool(blk, .LogicalOr, l, r, loc),
        .contains => {
            try self.context.diags.addError(a.exprs.locs.get(row.loc), .in_operator_not_supported, .{});
            return error.LoweringBug;
        },
        else => unreachable,
    };
    return if (expected_ty) |want| if (!self.isVoid(t)) self.emitCoerce(blk, v, t, want, loc) else v else v;
}

/// Lower the `catch` expression by wiring error/result handlers and running defers.
fn lowerCatch(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Catch, id);
    const loc = optLoc(a, id);
    const stamped_ty = self.getExprType(ctx, a, id);
    const out_ty_guess = stamped_ty;
    const produce_value = !self.isVoid(out_ty_guess);

    const lhs_val = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    const lhs_ty0 = self.getExprType(ctx, a, row.expr);
    const lhs_kind = self.context.type_store.getKind(lhs_ty0);

    var es_ty = lhs_ty0;
    var is_optional_es = false;
    if (lhs_kind == .Optional) {
        es_ty = self.context.type_store.get(.Optional, lhs_ty0).elem;
        is_optional_es = true;
    }
    const es = self.context.type_store.get(.ErrorSet, es_ty);
    const expr_loc = optLoc(a, row.expr);

    if (is_optional_es) {
        const some_flag = self.optionalFlag(blk, lhs_ty0, lhs_val, expr_loc);
        const es_payload = self.optionalPayload(blk, lhs_ty0, lhs_val, expr_loc);

        var some_blk = try f.builder.beginBlock(f);
        var none_blk = try f.builder.beginBlock(f);
        var join_blk = try f.builder.beginBlock(f);

        const res_opt_ty = self.context.type_store.mkOptional(es.value_ty);
        try self.noteExprType(ctx, id, res_opt_ty);
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_opt_ty);

        try f.builder.condBr(blk, self.forceLocalCond(blk, some_flag, expr_loc), some_blk.id, &.{}, none_blk.id, &.{}, loc);
        try f.builder.endBlock(f, blk.*);

        const tag = some_blk.builder.extractField(&some_blk, self.context.type_store.tI32(), es_payload, 0, expr_loc);
        const zero = some_blk.builder.tirValue(.ConstInt, &some_blk, self.context.type_store.tI32(), expr_loc, .{ .value = 0 });
        const is_ok_inner = some_blk.builder.binBool(&some_blk, .CmpEq, tag, zero, expr_loc);

        var ok_blk = try f.builder.beginBlock(f);
        var err_blk = try f.builder.beginBlock(f);
        try f.builder.condBr(&some_blk, is_ok_inner, ok_blk.id, &.{}, err_blk.id, &.{}, loc);
        try f.builder.endBlock(f, some_blk);

        const one = self.context.type_store.tBool();
        const true_v = ok_blk.builder.tirValue(.ConstBool, &ok_blk, one, loc, .{ .value = true });

        const ok_union = self.context.type_store.mkUnion(&.{ .{ .name = f.builder.intern("Ok"), .ty = es.value_ty }, .{ .name = f.builder.intern("Err"), .ty = es.error_ty } });
        const payload_union_ok = ok_blk.builder.extractField(&ok_blk, ok_union, es_payload, 1, expr_loc);
        const ok_v = ok_blk.builder.tirValue(.UnionField, &ok_blk, es.value_ty, loc, .{ .base = payload_union_ok, .field_index = 0 });

        const ok_fields = [_]tir.Rows.StructFieldInit{ .{ .index = 0, .name = .none(), .value = true_v }, .{ .index = 1, .name = .none(), .value = ok_v } };
        try f.builder.br(&ok_blk, join_blk.id, &.{ok_blk.builder.structMake(&ok_blk, res_opt_ty, &ok_fields, loc)}, loc);
        try f.builder.endBlock(f, ok_blk);

        const payload_union_err = err_blk.builder.extractField(&err_blk, ok_union, es_payload, 1, expr_loc);
        const err_val = err_blk.builder.tirValue(.UnionField, &err_blk, es.error_ty, loc, .{ .base = payload_union_err, .field_index = 1 });
        if (!row.binding_name.isNone()) {
            try env.bind(self.gpa, row.binding_name.unwrap(), .{ .value = err_val, .ty = es.error_ty, .is_slot = false }, f.builder, &err_blk, loc);
        }

        if (err_blk.term.isNone()) {
            const hv = try self.lowerBlockExprValue(ctx, a, env, f, &err_blk, row.handler, es.value_ty);
            if (err_blk.term.isNone()) {
                const true_v_err = err_blk.builder.tirValue(.ConstBool, &err_blk, one, loc, .{ .value = true });
                const err_fields = [_]tir.Rows.StructFieldInit{ .{ .index = 0, .name = .none(), .value = true_v_err }, .{ .index = 1, .name = .none(), .value = hv } };
                try f.builder.br(&err_blk, join_blk.id, &.{err_blk.builder.structMake(&err_blk, res_opt_ty, &err_fields, loc)}, loc);
            }
        }
        try f.builder.endBlock(f, err_blk);

        const false_v = none_blk.builder.tirValue(.ConstBool, &none_blk, one, loc, .{ .value = false });
        const nfields = [_]tir.Rows.StructFieldInit{ .{ .index = 0, .name = .none(), .value = false_v }, .{ .index = 1, .name = .none(), .value = self.safeUndef(&none_blk, es.value_ty, loc) } };
        try f.builder.br(&none_blk, join_blk.id, &.{none_blk.builder.structMake(&none_blk, res_opt_ty, &nfields, loc)}, loc);
        try f.builder.endBlock(f, none_blk);

        blk.* = join_blk;
        return if (expected_ty) |want| if (!self.isVoid(res_opt_ty)) self.emitCoerce(blk, res_param, res_opt_ty, want, loc) else res_param else res_param;
    }

    const lhs = lhs_val;
    const tag = blk.builder.extractField(blk, self.context.type_store.tI32(), lhs, 0, expr_loc);
    const is_ok = blk.builder.binBool(blk, .CmpEq, tag, blk.builder.tirValue(.ConstInt, blk, self.context.type_store.tI32(), expr_loc, .{ .value = 0 }), expr_loc);

    var then_blk = try f.builder.beginBlock(f);
    var else_blk = try f.builder.beginBlock(f);
    const payload_union_ty = self.context.type_store.mkUnion(&.{ .{ .name = f.builder.intern("Ok"), .ty = es.value_ty }, .{ .name = f.builder.intern("Err"), .ty = es.error_ty } });

    if (produce_value) {
        var join_blk = try f.builder.beginBlock(f);
        const res_ty = out_ty_guess;
        try self.noteExprType(ctx, id, res_ty);
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

        try f.builder.condBr(blk, self.forceLocalCond(blk, is_ok, expr_loc), then_blk.id, &.{}, else_blk.id, &.{}, loc);
        try f.builder.endBlock(f, blk.*);

        const payload_union_ok = then_blk.builder.extractField(&then_blk, payload_union_ty, lhs, 1, expr_loc);
        try f.builder.br(&then_blk, join_blk.id, &.{then_blk.builder.tirValue(.UnionField, &then_blk, es.value_ty, loc, .{ .base = payload_union_ok, .field_index = 0 })}, loc);

        try env.pushScope(self.gpa);
        const payload_union_err = else_blk.builder.extractField(&else_blk, payload_union_ty, lhs, 1, expr_loc);
        const err_val = else_blk.builder.tirValue(.UnionField, &else_blk, es.error_ty, loc, .{ .base = payload_union_err, .field_index = 1 });
        if (!row.binding_name.isNone()) {
            try env.bind(self.gpa, row.binding_name.unwrap(), .{ .value = err_val, .ty = es.error_ty, .is_slot = false }, f.builder, &else_blk, loc);
        }

        if (else_blk.term.isNone()) {
            const hv = try self.lowerBlockExprValue(ctx, a, env, f, &else_blk, row.handler, res_ty);
            if (else_blk.term.isNone()) try f.builder.br(&else_blk, join_blk.id, &.{hv}, loc);
        }
        _ = env.popScope(self.gpa);

        try f.builder.endBlock(f, then_blk);
        try f.builder.endBlock(f, else_blk);
        blk.* = join_blk;

        return if (expected_ty) |want| if (!self.isVoid(res_ty)) self.emitCoerce(blk, res_param, res_ty, want, loc) else res_param else res_param;
    } else {
        const exit_blk = try f.builder.beginBlock(f);
        try f.builder.condBr(blk, self.forceLocalCond(blk, is_ok, expr_loc), then_blk.id, &.{}, else_blk.id, &.{}, loc);
        try f.builder.endBlock(f, blk.*);

        if (then_blk.term.isNone()) try f.builder.br(&then_blk, exit_blk.id, &.{}, loc);
        try f.builder.endBlock(f, then_blk);

        try env.pushScope(self.gpa);
        const payload_union_err = else_blk.builder.extractField(&else_blk, payload_union_ty, lhs, 1, expr_loc);
        const err_val = else_blk.builder.tirValue(.UnionField, &else_blk, es.error_ty, loc, .{ .base = payload_union_err, .field_index = 1 });
        if (!row.binding_name.isNone()) {
            try env.bind(self.gpa, row.binding_name.unwrap(), .{ .value = err_val, .ty = es.error_ty, .is_slot = false }, f.builder, &else_blk, loc);
        }
        try self.lowerExprAsStmtList(ctx, a, env, f, &else_blk, row.handler);
        _ = env.popScope(self.gpa);

        if (else_blk.term.isNone()) try f.builder.br(&else_blk, exit_blk.id, &.{}, loc);
        try f.builder.endBlock(f, else_blk);

        blk.* = exit_blk;
        return self.safeUndef(blk, self.context.type_store.tAny(), loc);
    }
}

/// Lower the `orelse` expression by evaluating the left side and branching on errors.
fn lowerOrelse(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Binary, id);
    const loc = optLoc(a, id);
    const lhs_ty = self.getExprType(ctx, a, row.left);
    if (self.context.type_store.getKind(lhs_ty) != .Optional) return error.LoweringBug;

    const lhs_val = try self.lowerExpr(ctx, a, env, f, blk, row.left, lhs_ty, .rvalue);
    const opt_info = self.context.type_store.get(.Optional, lhs_ty);
    const flag = self.optionalFlag(blk, lhs_ty, lhs_val, loc);
    const payload = self.optionalPayload(blk, lhs_ty, lhs_val, loc);

    var then_blk = try f.builder.beginBlock(f);
    var else_blk = try f.builder.beginBlock(f);
    var join_blk = try f.builder.beginBlock(f);

    const elem_kind = self.context.type_store.getKind(opt_info.elem);

    if (elem_kind != .ErrorSet) {
        const res_ty = expected_ty orelse opt_info.elem;
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_ty);

        try f.builder.condBr(blk, flag, then_blk.id, &.{payload}, else_blk.id, &.{}, loc);
        try f.builder.endBlock(f, blk.*);

        const then_param = try f.builder.addBlockParam(&then_blk, null, opt_info.elem);
        const unwrapped = if (expected_ty) |want| self.emitCoerce(&then_blk, then_param, opt_info.elem, want, loc) else then_param;
        try f.builder.br(&then_blk, join_blk.id, &.{unwrapped}, loc);
        try f.builder.endBlock(f, then_blk);

        if (else_blk.term.isNone()) {
            const rhs_val = try self.lowerExpr(ctx, a, env, f, &else_blk, row.right, res_ty, .rvalue);
            const rk = self.context.type_store.getKind(self.getExprType(ctx, a, row.right));

            if (else_blk.term.isNone()) {
                if (rk == .Void) try f.builder.setReturnVoid(&else_blk, loc) else if (rk != .Noreturn) try f.builder.br(&else_blk, join_blk.id, &.{self.emitCoerce(&else_blk, rhs_val, self.getExprType(ctx, a, row.right), res_ty, loc)}, loc);
            }
            try f.builder.endBlock(f, else_blk);
        }

        blk.* = join_blk;
        try self.noteExprType(ctx, id, res_ty);
        return res_param;
    } else {
        const es = self.context.type_store.get(.ErrorSet, opt_info.elem);
        const res_es_ty = self.context.type_store.mkErrorSet(es.value_ty, es.error_ty);
        const res_param = try f.builder.addBlockParam(&join_blk, null, res_es_ty);

        try f.builder.condBr(blk, flag, then_blk.id, &.{payload}, else_blk.id, &.{}, loc);
        try f.builder.endBlock(f, blk.*);

        const then_param = try f.builder.addBlockParam(&then_blk, null, res_es_ty);
        try f.builder.br(&then_blk, join_blk.id, &.{then_param}, loc);
        try f.builder.endBlock(f, then_blk);

        if (else_blk.term.isNone()) {
            var rhs_val = try self.lowerExpr(ctx, a, env, f, &else_blk, row.right, es.value_ty, .rvalue);
            const rhs_ty = self.getExprType(ctx, a, row.right);
            if (!rhs_ty.eq(es.value_ty)) rhs_val = self.emitCoerce(&else_blk, rhs_val, rhs_ty, es.value_ty, loc);

            const union_ty = self.context.type_store.mkUnion(&.{ .{ .name = f.builder.intern("Ok"), .ty = es.value_ty }, .{ .name = f.builder.intern("Err"), .ty = es.error_ty } });
            const union_val = else_blk.builder.tirValue(.UnionMake, &else_blk, union_ty, loc, .{ .field_index = 0, .value = rhs_val });
            const tag0 = else_blk.builder.tirValue(.ConstInt, &else_blk, self.context.type_store.tI32(), loc, .{ .value = 0 });

            const fields = [_]tir.Rows.StructFieldInit{ .{ .index = 0, .name = .none(), .value = tag0 }, .{ .index = 1, .name = .none(), .value = union_val } };
            try f.builder.br(&else_blk, join_blk.id, &.{else_blk.builder.structMake(&else_blk, res_es_ty, &fields, loc)}, loc);
            try f.builder.endBlock(f, else_blk);
        }

        blk.* = join_blk;
        try self.noteExprType(ctx, id, res_es_ty);
        return res_param;
    }
}

/// Lower cast expressions by delegating to TypeKind-specific builders (normal/bitcast/etc.).
fn lowerCast(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
) anyerror!tir.ValueId {
    const row = a.exprs.get(.Cast, id);
    const ty0 = self.getExprType(ctx, a, id);
    const v = try self.lowerExpr(ctx, a, env, f, blk, row.expr, null, .rvalue);
    const loc = optLoc(a, id);
    const out = switch (row.kind) {
        .normal => blk.builder.tirValue(.CastNormal, blk, ty0, loc, .{ .value = v }),
        .bitcast => blk.builder.tirValue(.CastBit, blk, ty0, loc, .{ .value = v }),
        .saturate => blk.builder.tirValue(.CastSaturate, blk, ty0, loc, .{ .value = v }),
        .wrap => blk.builder.tirValue(.CastWrap, blk, ty0, loc, .{ .value = v }),
        .checked => blk.builder.tirValue(.CastChecked, blk, ty0, loc, .{ .value = v }),
    };
    return if (expected_ty) |want| self.emitCoerce(blk, out, ty0, want, loc) else out;
}

/// Lower expression `id` into TIR, targeting `expected_ty`/`mode` and respecting the current env.
pub fn lowerExpr(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    id: ast.ExprId,
    expected_ty: ?types.TypeId,
    mode: LowerMode,
) anyerror!tir.ValueId {
    const kind = a.kind(id);
    if (isTypeExprKind(kind)) {
        return self.lowerTypeExprOpaque(ctx, a, blk, id, expected_ty);
    }
    if (kind == .CodeBlock) {
        const idx = id.toRaw();
        const has_type = idx < a.type_info.expr_types.items.len and a.type_info.expr_types.items[idx] != null;
        const ty = if (has_type) self.getExprType(ctx, a, id) else self.context.type_store.tCode();
        return self.safeUndef(blk, expected_ty orelse ty, optLoc(a, id));
    }
    try self.ensureExprTypeStamped(ctx, a, id);
    _ = try self.refineExprType(ctx, a, env, id, self.getExprType(ctx, a, id));
    try self.ensureExprTypeNotError(ctx, a, id);

    return switch (kind) {
        .Literal => self.lowerLiteral(ctx, a, blk, id, expected_ty),
        .NullLit => blk_null: {
            const loc = optLoc(a, id);
            if (expected_ty) |want| if (self.context.type_store.getKind(want) == .Optional) break :blk_null blk.builder.constNull(blk, want, loc);
            const ty0 = self.getExprType(ctx, a, id);
            const v = blk.builder.constNull(blk, ty0, loc);
            break :blk_null if (expected_ty) |want| self.emitCoerce(blk, v, ty0, want, loc) else v;
        },
        .UndefLit => blk_undef: {
            const loc = optLoc(a, id);
            break :blk_undef if (expected_ty) |want_raw| blk.builder.constNull(blk, want_raw, loc) else self.safeUndef(blk, self.context.type_store.tAny(), loc);
        },
        .Unary => self.lowerUnary(ctx, a, env, f, blk, id, expected_ty, mode),
        .Range => self.lowerRange(ctx, a, env, f, blk, id, expected_ty),
        .Deref => self.lowerDeref(ctx, a, env, f, blk, id, expected_ty, mode),
        .TupleLit => self.lowerTupleLit(ctx, a, env, f, blk, id, expected_ty),
        .ArrayLit => self.lowerArrayLit(ctx, a, env, f, blk, id, expected_ty),
        .StructLit => self.lowerStructLit(ctx, a, env, f, blk, id, expected_ty),
        .MapLit => self.lowerMapLit(ctx, a, env, f, blk, id, expected_ty),
        .IndexAccess => self.lowerIndexAccess(ctx, a, env, f, blk, id, expected_ty, mode),
        .FieldAccess => self.lowerFieldAccess(ctx, a, env, f, blk, id, expected_ty, mode),
        .Block => try self.lowerBlockExprValue(ctx, a, env, f, blk, id, expected_ty orelse self.getExprType(ctx, a, id)),
        .Splice => blk_splice: {
            var cval = try self.getCachedComptimeValue(a, id);
            if (cval) |*comptime_val| {
                defer comptime_val.destroy(self.gpa);
                if (comptime_val.* == .Code) {
                    if (comp.codeExprFromCodeValue(a, comptime_val.Code)) |expr_id| {
                        break :blk_splice try self.lowerExpr(ctx, a, env, f, blk, expr_id, expected_ty, mode);
                    }
                    return error.LoweringBug;
                }
                break :blk_splice try comp.constValueFromComptime(self, blk, expected_ty orelse self.getExprType(ctx, a, id), comptime_val.*);
            }
            return error.LoweringBug;
        },
        .Ident => self.lowerIdent(ctx, a, env, f, blk, id, expected_ty, mode),
        .Binary => self.lowerBinary(ctx, a, env, f, blk, id, expected_ty),
        .Catch => self.lowerCatch(ctx, a, env, f, blk, id, expected_ty),
        .Return => blk_ret: {
            const row = a.exprs.get(.Return, id);
            const loc = optLoc(a, id);
            const poison = self.safeUndef(blk, self.getExprType(ctx, a, id), loc);
            try self.lowerReturnCommon(ctx, a, env, f, blk, row.value, loc);
            break :blk_ret poison;
        },
        .Break => blk_br: {
            const row = a.exprs.get(.Break, id);
            const loc = optLoc(a, id);
            const poison = self.safeUndef(blk, expected_ty orelse self.getExprType(ctx, a, id), loc);
            try cf.lowerBreakCommon(self, ctx, a, env, f, blk, row.label, row.value, loc);
            break :blk_br poison;
        },
        .Continue => blk_cont: {
            const row = a.exprs.get(.Continue, id);
            const loc = optLoc(a, id);
            const poison = self.safeUndef(blk, expected_ty orelse self.getExprType(ctx, a, id), loc);
            try cf.lowerContinueCommon(self, ctx, a, env, f, blk, row.label, loc);
            break :blk_cont poison;
        },
        .If => cf.lowerIf(self, ctx, a, env, f, blk, id, expected_ty),
        .Call => self.lowerCall(ctx, a, env, f, blk, id, expected_ty, mode),
        .Cast => self.lowerCast(ctx, a, env, f, blk, id, expected_ty),
        .OptionalUnwrap => cf.lowerOptionalUnwrap(self, ctx, a, env, f, blk, id, expected_ty),
        .Await => blk_await: {
            const aw = a.exprs.get(.Await, id);
            const loc = optLoc(a, id);
            const res_ty = self.getExprType(ctx, a, id);
            const val = blk.builder.tirValue(.Await, blk, res_ty, loc, .{ .operand = try self.lowerExpr(ctx, a, env, f, blk, aw.expr, null, .rvalue) });
            break :blk_await if (expected_ty) |want| if (!res_ty.eq(want)) self.emitCoerce(blk, val, res_ty, want, loc) else val else val;
        },
        .ErrUnwrap => cf.lowerErrUnwrap(self, ctx, a, env, f, blk, id, expected_ty),
        .TypeOf => self.lowerTypeOf(ctx, a, blk, id),
        .Match => cf.lowerMatch(self, ctx, a, env, f, blk, id, expected_ty),
        .While => cf.lowerWhile(self, ctx, a, env, f, blk, id, expected_ty),
        .For => cf.lowerFor(self, ctx, a, env, f, blk, id, expected_ty),
        .MlirBlock => if (mode == .lvalue_addr) error.LoweringBug else try self.lowerMlirBlock(ctx, a, env, f, blk, id, expected_ty, optLoc(a, id)),
        .Import => blk.builder.tirValue(.ConstUndef, blk, self.getExprType(ctx, a, id), optLoc(a, id), .{}),
        .CodeBlock => self.safeUndef(blk, self.getExprType(ctx, a, id), optLoc(a, id)),
        .ComptimeBlock => blk_comp: {
            const cb = a.exprs.get(.ComptimeBlock, id);
            var cval = try self.getCachedComptimeValue(a, cb.block);
            if (cval) |*comptime_val| {
                defer comptime_val.destroy(self.gpa);
                break :blk_comp try comp.constValueFromComptime(self, blk, self.getExprType(ctx, a, cb.block), comptime_val.*);
            }
            return error.LoweringBug;
        },
        else => {
            std.debug.print("lowerExpr: unhandled expr kind {}\n", .{a.kind(id)});
            return error.LoweringBug;
        },
    };
}

fn isTypeExprKind(kind: ast.ExprKind) bool {
    return switch (kind) {
        .TupleType,
        .ArrayType,
        .DynArrayType,
        .SliceType,
        .MapType,
        .OptionalType,
        .ErrorSetType,
        .ErrorType,
        .StructType,
        .EnumType,
        .VariantType,
        .UnionType,
        .PointerType,
        .SimdType,
        .ComplexType,
        .TensorType,
        .TypeType,
        .AnyType,
        .NoreturnType,
        => true,
        else => false,
    };
}

/// Evaluate the block expression `block_expr` and return its resulting TIR value.
pub fn lowerBlockExprValue(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    block_expr: ast.ExprId,
    expected_ty: types.TypeId,
) anyerror!tir.ValueId {
    if (a.kind(block_expr) != .Block) return self.lowerExpr(ctx, a, env, f, blk, block_expr, expected_ty, .rvalue);

    const b = a.exprs.get(.Block, block_expr);
    const stmts = a.stmts.stmt_pool.slice(b.items);
    const loc = optLoc(a, block_expr);

    if (stmts.len == 0) {
        try self.noteExprType(ctx, block_expr, expected_ty);
        return self.safeUndef(blk, expected_ty, loc);
    }

    try env.pushScope(self.gpa);
    defer _ = env.popScope(self.gpa);

    const mark: u32 = @intCast(env.defers.items.len);
    var i: usize = 0;
    while (i + 1 < stmts.len) : (i += 1) {
        try self.lowerStmt(ctx, a, env, f, blk, stmts[i]);
    }

    const last = stmts[stmts.len - 1];
    if (a.kind(last) == .Expr) {
        const v = try self.lowerExpr(ctx, a, env, f, blk, a.stmts.get(.Expr, last).expr, expected_ty, .rvalue);
        try self.noteExprType(ctx, block_expr, expected_ty);
        try cf.runNormalDefersFrom(self, ctx, a, env, f, blk, mark);
        return v;
    } else {
        try self.lowerStmt(ctx, a, env, f, blk, last);
        try cf.runNormalDefersFrom(self, ctx, a, env, f, blk, mark);
        try self.noteExprType(ctx, block_expr, expected_ty);
        return self.safeUndef(blk, expected_ty, loc);
    }
}

/// Compute the symbol name representing `did` if it introduces a runtime value.
fn symbolNameForDecl(self: *LowerTir, decl_ast: *ast.Ast, did: ast.DeclId) !?StrId {
    const decl = decl_ast.exprs.Decl.get(did);
    const is_extern_fn = switch (decl_ast.kind(decl.value)) {
        .FunctionLit => decl_ast.exprs.get(.FunctionLit, decl.value).flags.is_extern,
        else => false,
    };
    if (!decl.pattern.isNone()) {
        const name = bindingNameOfPattern(decl_ast, decl.pattern.unwrap()) orelse return null;
        return if (is_extern_fn) name else try self.qualifySymbolName(decl_ast, name);
    }
    if (!decl.method_path.isNone()) {
        const base = try methodSymbolShortName(self, decl_ast, did);
        return if (is_extern_fn) base else try self.qualifySymbolName(decl_ast, base);
    }
    return null;
}

/// Return the declared default expression for `field_name` in `type_expr`, if present.
fn structFieldDefaultExpr(self: *LowerTir, a: *ast.Ast, type_expr: ast.ExprId, field_name: ast.StrId) ?ast.ExprId {
    const struct_expr = self.structTypeExprFromTypeRef(a, type_expr) orelse return null;
    return structFieldDefaultInStructExpr(a, struct_expr, field_name);
}

/// Resolve a struct literal expression pointer from a type reference, if it names a struct.
fn structTypeExprFromTypeRef(_: *LowerTir, a: *ast.Ast, type_expr: ast.ExprId) ?ast.ExprId {
    return switch (a.kind(type_expr)) {
        .StructType => type_expr,
        .Ident => blk: {
            const decl_id = call_resolution.findDeclId(a, a.exprs.get(.Ident, type_expr).name) orelse break :blk null;
            const decl = a.exprs.Decl.get(decl_id);
            break :blk if (a.kind(decl.value) == .StructType) decl.value else null;
        },
        else => null,
    };
}

/// Look for a default initializer for `field_name` inside `struct_expr`.
fn structFieldDefaultInStructExpr(a: *ast.Ast, struct_expr: ast.ExprId, field_name: ast.StrId) ?ast.ExprId {
    const sfields = a.exprs.sfield_pool.slice(a.exprs.get(.StructType, struct_expr).fields);
    for (sfields) |fid| {
        const sf = a.exprs.StructField.get(fid);
        if (sf.name.eq(field_name) and !sf.value.isNone()) return sf.value.unwrap();
    }
    return null;
}

/// True if `ty` is a numeric scalar type.
fn isNumeric(self: *const LowerTir, ty: types.TypeId) bool {
    if (self.isVoid(ty)) return false;
    return switch (self.context.type_store.getKind(ty)) {
        .U8, .U16, .U32, .U64, .I8, .I16, .I32, .I64, .Usize, .F32, .F64, .Simd, .Tensor => true,
        else => false,
    };
}

/// Return true when `ty` is either `f32` or `f64`.
fn isFloat(self: *const LowerTir, ty: types.TypeId) bool {
    const k = self.context.type_store.getKind(ty);
    return k == .F32 or k == .F64;
}

/// Test whether `ty` currently maps to `kind` in the type store index.
pub fn isType(self: *const LowerTir, ty: types.TypeId, kind: types.TypeKind) bool {
    return self.context.type_store.getKind(ty) == kind;
}

/// Choose a common numeric type for binary ops when the checker didn't provide one.
fn commonNumeric(self: *const LowerTir, l: ?types.TypeId, r: ?types.TypeId) ?types.TypeId {
    const ts = self.context.type_store;
    if (l) |lt| if (self.isNumeric(lt)) {
        if (r) |rt| {
            if (self.isNumeric(rt)) {
                const kL = ts.getKind(lt);
                const kR = ts.getKind(rt);
                if (kL == .Simd or kL == .Tensor) return lt;
                if (kR == .Simd or kR == .Tensor) return rt;
                if (kL == .F64 or kR == .F64) return ts.tF64();
                if (kL == .F32 or kR == .F32) return ts.tF32();

                const signedPref = [_]types.TypeId{ ts.tI64(), ts.tI32(), ts.tI16(), ts.tI8() };
                for (signedPref) |cand| if (lt.eq(cand) or rt.eq(cand)) return cand;

                const unsignedPref = [_]types.TypeId{ ts.tU64(), ts.tU32(), ts.tU16(), ts.tU8() };
                for (unsignedPref) |cand| if (lt.eq(cand) or rt.eq(cand)) return cand;

                return lt;
            }
            return lt;
        }
        return lt;
    } else if (r) |rt| if (self.isNumeric(rt)) return rt;
    return null;
}

fn lookupComptimeAliasType(self: *LowerTir, a: *ast.Ast, name: ast.StrId) ?types.TypeId {
    const ty = a.type_info.lookupComptimeBindingType(name) orelse return null;
    return if (self.context.type_store.getKind(ty) == .TypeType) ty else null;
}

fn cloneComptimeAliasValue(self: *LowerTir, a: *ast.Ast, name: ast.StrId) !?comp.ComptimeValue {
    return try a.type_info.cloneComptimeBindingValue(self.gpa, name);
}

/// Optionally adjust the type recorded for `expr` by considering surrounding bindings.
fn refineExprType(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    expr: ast.ExprId,
    stamped: types.TypeId,
) !?types.TypeId {
    switch (a.kind(expr)) {
        .Ident => {
            const name = a.exprs.get(.Ident, expr).name;
            if (env.lookup(name)) |bnd| {
                try self.noteExprType(ctx, expr, bnd.ty);
                return bnd.ty;
            }
            if (self.lookupComptimeAliasType(a, name)) |ty| {
                const type_ty = self.context.type_store.mkTypeType(ty);
                try self.noteExprType(ctx, expr, type_ty);
                return type_ty;
            }
        },
        .Range => {
            if (self.isSpreadRangeExpr(ctx, a, env, expr)) {
                const row = a.exprs.get(.Range, expr);
                if (!row.end.isNone()) {
                    const inner = row.end.unwrap();
                    const inner_stamped = self.getExprType(ctx, a, inner);
                    if (try self.refineExprType(ctx, a, env, inner, inner_stamped)) |inner_refined| {
                        try self.noteExprType(ctx, expr, inner_refined);
                        return inner_refined;
                    }
                    try self.noteExprType(ctx, expr, inner_stamped);
                    return inner_stamped;
                }
            }
        },
        else => {},
    }
    return stamped;
}

/// Compute the effective type for `expr` by combining stamped type and any local refinements.
fn exprTypeWithEnv(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    expr: ast.ExprId,
) types.TypeId {
    const stamped = self.getExprType(ctx, a, expr);
    return (self.refineExprType(ctx, a, env, expr, stamped) catch null) orelse stamped;
}

// ============================
// Misc helpers
// ============================

/// Return the recorded type for expression `id`, honoring any override entries in `ctx`.
pub fn getExprType(self: *const LowerTir, ctx: *LowerContext, a: *ast.Ast, id: ast.ExprId) types.TypeId {
    if (self.lookupExprTypeOverride(ctx, id)) |override| return override;
    const i = id.toRaw();
    std.debug.assert(i < a.type_info.expr_types.items.len);
    return a.type_info.expr_types.items[i] orelse unreachable;
}

/// Return the recorded type for declaration `did`, if the checker produced one.
fn getDeclType(a: *ast.Ast, did: ast.DeclId) ?types.TypeId {
    const i = did.toRaw();
    std.debug.assert(i < a.type_info.decl_types.items.len);
    return a.type_info.decl_types.items[i];
}

/// Construct the anonymous union that represents the payload fields of `vty` (variant/error).
pub fn getUnionTypeFromVariant(self: *const LowerTir, vty: types.TypeId) ?types.TypeId {
    const ts = self.context.type_store;
    const k = ts.getKind(vty);

    if (k == .Variant or k == .Error) {
        const fields = if (k == .Variant) ts.field_pool.slice(ts.get(.Variant, vty).variants) else ts.field_pool.slice(ts.get(.Error, vty).variants);

        var stack_args: [16]types.TypeStore.StructFieldArg = undefined;
        var heap_args: []types.TypeStore.StructFieldArg = &.{};
        defer if (heap_args.len > 0) self.gpa.free(heap_args);

        const args = if (fields.len <= 16) stack_args[0..fields.len] else blk: {
            heap_args = self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len) catch return null;
            break :blk heap_args;
        };

        for (fields, 0..) |fid, i| {
            const f = ts.Field.get(fid);
            args[i] = .{ .name = f.name, .ty = f.ty };
        }
        return ts.mkUnion(args);
    }

    if (k == .Struct) {
        const sfields = ts.field_pool.slice(ts.get(.Struct, vty).fields);
        if (sfields.len != 2) return null;
        return ts.Field.get(sfields[1]).ty;
    }

    return null;
}

/// Walk `pid` and bind every leaf to `value`, optionally storing into slots for mut bindings.
fn destructureDeclPattern(self: *LowerTir, a: *ast.Ast, env: *cf.Env, f: *Builder.FunctionFrame, blk: *Builder.BlockFrame, pid: ast.PatternId, value: tir.ValueId, vty: types.TypeId, to_slots: bool) !void {
    const loc = optLoc(a, pid);
    switch (a.kind(pid)) {
        .Binding => {
            const nm = a.pats.get(.Binding, pid).name;
            if (self.isVoid(vty)) return;
            if (to_slots) {
                const slot = f.builder.tirValue(.Alloca, blk, self.context.type_store.mkPtr(vty, false), loc, .{ .count = tir.OptValueId.none(), .@"align" = 0 });
                _ = f.builder.tirValue(.Store, blk, vty, loc, .{ .ptr = slot, .value = value, .@"align" = 0 });
                try env.bind(self.gpa, nm, .{ .value = slot, .ty = vty, .is_slot = true }, f.builder, blk, loc);
            } else {
                try env.bind(self.gpa, nm, .{ .value = value, .ty = vty, .is_slot = false }, f.builder, blk, loc);
            }
        },
        .Tuple => {
            const elems = a.pats.pat_pool.slice(a.pats.get(.Tuple, pid).elems);
            const etys = if (self.context.type_store.getKind(vty) == .Tuple) self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, vty).elems) else &[_]types.TypeId{};
            for (elems, 0..) |elem, i| {
                const ety = if (i < etys.len) etys[i] else self.context.type_store.tAny();
                try self.destructureDeclPattern(a, env, f, blk, elem, blk.builder.extractElem(blk, ety, value, @intCast(i), loc), ety, to_slots);
            }
        },
        .Struct => {
            const fields = a.pats.field_pool.slice(a.pats.get(.Struct, pid).fields);
            const idx_by_name = if (self.context.type_store.getKind(vty) == .Struct) self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, vty).fields) else null;

            for (fields) |fid| {
                const pf = a.pats.StructField.get(fid);
                var fty = self.context.type_store.tAny();
                var extracted: tir.ValueId = undefined;

                if (idx_by_name) |field_ids| {
                    var found = false;
                    for (field_ids, 0..) |f_id, j| {
                        const stf = self.context.type_store.Field.get(f_id);
                        if (stf.name.eq(pf.name)) {
                            fty = stf.ty;
                            extracted = blk.builder.extractField(blk, fty, value, @intCast(j), loc);
                            found = true;
                            break;
                        }
                    }
                    if (!found) extracted = self.safeUndef(blk, fty, loc);
                } else {
                    extracted = blk.builder.extractFieldNamed(blk, fty, value, pf.name, loc);
                }
                try self.destructureDeclPattern(a, env, f, blk, pf.pattern, extracted, fty, to_slots);
            }
        },
        else => {},
    }
}

/// When the RHS is a tuple literal, destructure its elements directly into the pattern.
fn destructureDeclFromTupleLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    pid: ast.PatternId,
    src_expr: ast.ExprId,
    vty: types.TypeId,
    to_slots: bool,
) anyerror!void {
    const elems_pat = a.pats.pat_pool.slice(a.pats.get(.Tuple, pid).elems);
    const elems_expr = a.exprs.expr_pool.slice(a.exprs.get(.TupleLit, src_expr).elems);
    const etys = if (self.context.type_store.getKind(vty) == .Tuple) self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, vty).elems) else &[_]types.TypeId{};

    var i: usize = 0;
    const n = @min(elems_pat.len, elems_expr.len);
    while (i < n) : (i += 1) {
        const ety = if (i < etys.len) etys[i] else self.context.type_store.tAny();
        try self.destructureDeclFromExpr(ctx, a, env, f, blk, elems_pat[i], elems_expr[i], ety, to_slots);
    }
    while (i < elems_pat.len) : (i += 1) {
        const ety = if (i < etys.len) etys[i] else self.context.type_store.tAny();
        try self.destructureDeclPattern(a, env, f, blk, elems_pat[i], self.safeUndef(blk, ety, optLoc(a, elems_pat[i])), ety, to_slots);
    }
}

/// When the RHS is a struct literal, match named fields against the pattern to bind them.
fn destructureDeclFromStructLit(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    pid: ast.PatternId,
    src_expr: ast.ExprId,
    vty: types.TypeId,
    to_slots: bool,
) !void {
    const pfields = a.pats.field_pool.slice(a.pats.get(.Struct, pid).fields);
    const sfields = a.exprs.sfv_pool.slice(a.exprs.get(.StructLit, src_expr).fields);
    const type_fields = if (self.context.type_store.getKind(vty) == .Struct) self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, vty).fields) else &[_]types.FieldId{};

    for (pfields) |pfid| {
        const pf = a.pats.StructField.get(pfid);
        var val_expr: ?ast.ExprId = null;
        for (sfields) |sfid| {
            const sf = a.exprs.StructFieldValue.get(sfid);
            if (sf.name.eq(pf.name)) {
                val_expr = sf.value;
                break;
            }
        }

        var fty = self.context.type_store.tAny();
        for (type_fields) |tfid| {
            const tf = self.context.type_store.Field.get(tfid);
            if (tf.name.eq(pf.name)) {
                fty = tf.ty;
                break;
            }
        }

        if (val_expr) |ve| try self.destructureDeclFromExpr(ctx, a, env, f, blk, pf.pattern, ve, fty, to_slots) else try self.destructureDeclPattern(a, env, f, blk, pf.pattern, self.safeUndef(blk, fty, optLoc(a, pf.pattern)), fty, to_slots);
    }
}

/// Destructure an arbitrary expression `src_expr` according to `pid`, emitting stores and binds.
fn destructureDeclFromExpr(
    self: *LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    env: *cf.Env,
    f: *Builder.FunctionFrame,
    blk: *Builder.BlockFrame,
    pid: ast.PatternId,
    src_expr: ast.ExprId,
    target_ty: types.TypeId,
    to_slots: bool,
) anyerror!void {
    const target_kind = self.context.type_store.getKind(target_ty);
    const src_ty = self.getExprType(ctx, a, src_expr);
    const vty = if (target_kind == .Any) src_ty else target_ty;
    const expr_loc = optLoc(a, src_expr);

    if (target_kind == .TypeType) {
        const resolved_ty = blk_res: {
            if (self.context.type_store.getKind(src_ty) == .TypeType) {
                const tt = self.context.type_store.get(.TypeType, src_ty);
                if (!self.isType(tt.of, .Any)) break :blk_res tt.of;
            }
            var cval = try self.getCachedComptimeValue(a, src_expr);
            if (cval) |*computed| {
                defer computed.destroy(self.gpa);
                if (computed.* == .Type) break :blk_res computed.Type;
            }
            return error.UnsupportedComptimeType;
        };
        const type_ty = self.context.type_store.mkTypeType(resolved_ty);
        try self.noteExprType(ctx, src_expr, type_ty);
        return try self.destructureDeclPattern(a, env, f, blk, pid, self.safeUndef(blk, type_ty, expr_loc), type_ty, to_slots);
    }

    switch (a.kind(pid)) {
        .Binding => {
            try self.ensureExprTypeStamped(ctx, a, src_expr);
            var raw = try self.lowerExpr(ctx, a, env, f, blk, src_expr, if (target_kind == .Any) src_ty else target_ty, .rvalue);
            const refined = (try self.refineExprType(ctx, a, env, src_expr, self.getExprType(ctx, a, src_expr))) orelse unreachable;
            const eff_ty = if (target_kind == .Any and !self.isType(refined, .Any)) refined else target_ty;
            if (!refined.eq(eff_ty)) raw = self.emitCoerce(blk, raw, refined, eff_ty, expr_loc);
            return try self.destructureDeclPattern(a, env, f, blk, pid, raw, eff_ty, to_slots);
        },
        .Tuple => {
            if (a.kind(src_expr) == .TupleLit) return try self.destructureDeclFromTupleLit(ctx, a, env, f, blk, pid, src_expr, if (target_kind == .Any) src_ty else target_ty, to_slots);
            const eff_ty = if (target_kind == .Any) src_ty else target_ty;
            const raw = try self.lowerExpr(ctx, a, env, f, blk, src_expr, eff_ty, .rvalue);
            const val = if (!src_ty.eq(eff_ty)) self.emitCoerce(blk, raw, src_ty, eff_ty, expr_loc) else raw;
            return try self.destructureDeclPattern(a, env, f, blk, pid, val, eff_ty, to_slots);
        },
        .Struct => {
            if (a.kind(src_expr) == .StructLit) return try self.destructureDeclFromStructLit(ctx, a, env, f, blk, pid, src_expr, if (target_kind == .Any) src_ty else target_ty, to_slots);
            const eff_ty = if (target_kind == .Any) src_ty else target_ty;
            const raw = try self.lowerExpr(ctx, a, env, f, blk, src_expr, eff_ty, .rvalue);
            const val = if (!src_ty.eq(eff_ty)) self.emitCoerce(blk, raw, src_ty, eff_ty, expr_loc) else raw;
            return try self.destructureDeclPattern(a, env, f, blk, pid, val, eff_ty, to_slots);
        },
        .VariantTuple => {
            const pr = a.pats.get(.VariantTuple, pid);
            const p_segs = a.pats.seg_pool.slice(pr.path);
            const case_name = a.pats.PathSeg.get(p_segs[p_segs.len - 1]).name;

            if (a.kind(src_expr) == .Call) {
                const call = a.exprs.get(.Call, src_expr);
                var cur = call.callee;
                var callee_last: ?ast.StrId = null;
                while (a.kind(cur) == .FieldAccess) {
                    const fr = a.exprs.get(.FieldAccess, cur);
                    callee_last = fr.field;
                    cur = fr.parent;
                }

                if (callee_last != null and callee_last.?.eq(case_name)) {
                    const args = a.exprs.expr_pool.slice(call.args);
                    var elem_tys: []const types.TypeId = &[_]types.TypeId{};

                    if (self.context.type_store.getKind(vty) == .Variant) {
                        const fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, vty).variants);
                        for (fields) |fid| {
                            const fld = self.context.type_store.Field.get(fid);
                            if (fld.name.eq(case_name) and self.context.type_store.getKind(fld.ty) == .Tuple) {
                                elem_tys = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, fld.ty).elems);
                                break;
                            }
                        }
                    }

                    const pelems = a.pats.pat_pool.slice(pr.elems);
                    var i: usize = 0;
                    const n = @min(pelems.len, args.len);
                    while (i < n) : (i += 1) {
                        try self.destructureDeclFromExpr(ctx, a, env, f, blk, pelems[i], args[i], if (i < elem_tys.len) elem_tys[i] else self.context.type_store.tAny(), to_slots);
                    }
                    while (i < pelems.len) : (i += 1) {
                        const ety = if (i < elem_tys.len) elem_tys[i] else self.context.type_store.tAny();
                        try self.destructureDeclPattern(a, env, f, blk, pelems[i], self.safeUndef(blk, ety, optLoc(a, pelems[i])), ety, to_slots);
                    }
                    return;
                }
            }

            const pelems = a.pats.pat_pool.slice(pr.elems);
            var elem_tys: []const types.TypeId = &[_]types.TypeId{};
            if (self.context.type_store.getKind(vty) == .Variant) {
                const fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, vty).variants);
                for (fields) |fid| {
                    const fld = self.context.type_store.Field.get(fid);
                    if (fld.name.eq(case_name) and self.context.type_store.getKind(fld.ty) == .Tuple) {
                        elem_tys = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, fld.ty).elems);
                        break;
                    }
                }
            }
            for (pelems, 0..) |pelem, i| {
                const ety = if (i < elem_tys.len) elem_tys[i] else self.context.type_store.tAny();
                try self.destructureDeclPattern(a, env, f, blk, pelem, self.safeUndef(blk, ety, optLoc(a, pelem)), ety, to_slots);
            }
        },
        .VariantStruct => {
            const pr = a.pats.get(.VariantStruct, pid);
            const segs = a.pats.seg_pool.slice(pr.path);
            const case_name = a.pats.PathSeg.get(segs[segs.len - 1]).name;

            if (a.kind(src_expr) == .StructLit) {
                const sl = a.exprs.get(.StructLit, src_expr);
                if (!sl.ty.isNone()) {
                    var cur = sl.ty.unwrap();
                    var last_seg: ?ast.StrId = null;
                    while (a.kind(cur) == .FieldAccess) {
                        const fr = a.exprs.get(.FieldAccess, cur);
                        last_seg = fr.field;
                        cur = fr.parent;
                    }
                    if (last_seg != null and last_seg.?.eq(case_name)) {
                        var field_tys: []const types.FieldId = &[_]types.FieldId{};
                        if (self.context.type_store.getKind(vty) == .Variant) {
                            const variants = self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, vty).variants);
                            for (variants) |fid| {
                                const vf = self.context.type_store.Field.get(fid);
                                if (vf.name.eq(case_name) and self.context.type_store.getKind(vf.ty) == .Struct) {
                                    field_tys = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, vf.ty).fields);
                                    break;
                                }
                            }
                        }

                        const pfields = a.pats.field_pool.slice(pr.fields);
                        const sfields = a.exprs.sfv_pool.slice(sl.fields);
                        for (pfields) |pfid| {
                            const pf = a.pats.StructField.get(pfid);
                            var val_expr: ?ast.ExprId = null;
                            for (sfields) |sfid| {
                                const sf = a.exprs.StructFieldValue.get(sfid);
                                if (sf.name.eq(pf.name)) {
                                    val_expr = sf.value;
                                    break;
                                }
                            }
                            var fty = self.context.type_store.tAny();
                            for (field_tys) |tfid| {
                                const tf = self.context.type_store.Field.get(tfid);
                                if (tf.name.eq(pf.name)) {
                                    fty = tf.ty;
                                    break;
                                }
                            }
                            if (val_expr) |ve| try self.destructureDeclFromExpr(ctx, a, env, f, blk, pf.pattern, ve, fty, to_slots) else try self.destructureDeclPattern(a, env, f, blk, pf.pattern, self.safeUndef(blk, fty, optLoc(a, pf.pattern)), fty, to_slots);
                        }
                        return;
                    }
                }
            }
            const pfields = a.pats.field_pool.slice(pr.fields);
            for (pfields) |pfid| {
                const pf = a.pats.StructField.get(pfid);
                try self.destructureDeclPattern(a, env, f, blk, pf.pattern, self.safeUndef(blk, self.context.type_store.tAny(), optLoc(a, pf.pattern)), self.context.type_store.tAny(), to_slots);
            }
        },
        else => {
            const val = try self.lowerExpr(ctx, a, env, f, blk, src_expr, vty, .rvalue);
            return try self.destructureDeclPattern(a, env, f, blk, pid, val, vty, to_slots);
        },
    }
}

/// Look up the tag index for `name` within the variant/error `case_ty`, if it exists.
pub fn tagIndexForCase(self: *const LowerTir, case_ty: types.TypeId, name: StrId) ?u32 {
    const k = self.context.type_store.getKind(case_ty);
    if (k != .Variant and k != .Error) return null;
    const fields = if (k == .Variant) self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, case_ty).variants) else self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, case_ty).variants);
    for (fields, 0..) |fid, i| {
        if (self.context.type_store.Field.get(fid).name.eq(name)) return @intCast(i);
    }
    return null;
}

/// Return the numeric value assigned to enum member `name`, or null if missing.
pub fn enumMemberValue(self: *const LowerTir, enum_ty: types.TypeId, name: StrId) ?i64 {
    if (self.context.type_store.getKind(enum_ty) != .Enum) return null;
    const members = self.context.type_store.enum_member_pool.slice(self.context.type_store.get(.Enum, enum_ty).members);
    for (members) |mid| {
        const m = self.context.type_store.EnumMember.get(mid);
        if (m.name.eq(name)) return @intCast(m.value);
    }
    return null;
}

/// Ensure `cond` is defined in `blk` and is i1.
pub fn forceLocalCond(self: *LowerTir, blk: *Builder.BlockFrame, cond: tir.ValueId, loc: tir.OptLocId) tir.ValueId {
    return blk.builder.tirValue(.CastBit, blk, self.context.type_store.tBool(), loc, .{ .value = cond });
}

/// Return true when `ty` represents either a variant or error type.
fn isVariantLike(self: *const LowerTir, ty: types.TypeId) bool {
    const k = self.context.type_store.getKind(ty);
    return k == .Variant or k == .Error;
}

/// If `expr` is a tag literal like `MyErr.NotFound` return the variant/error type and resolved tag index.
fn tagConstFromTypePath(
    self: *const LowerTir,
    ctx: *LowerContext,
    a: *ast.Ast,
    expr: ast.ExprId,
) ?struct { of_ty: types.TypeId, tag_idx: u32 } {
    if (a.kind(expr) != .FieldAccess) return null;
    const fr = a.exprs.get(.FieldAccess, expr);
    const pty = self.getExprType(ctx, a, fr.parent);
    if (self.context.type_store.getKind(pty) != .TypeType) return null;

    const of_ty = self.context.type_store.get(.TypeType, pty).of;
    const of_kind = self.context.type_store.getKind(of_ty);
    if (of_kind != .Variant and of_kind != .Error) return null;

    const idx = a.type_info.getFieldIndex(expr) orelse return null;
    const fields = if (of_kind == .Variant) self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, of_ty).variants) else self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, of_ty).variants);

    if (idx >= fields.len) return null;
    if (self.context.type_store.getKind(self.context.type_store.Field.get(fields[idx]).ty) != .Void) return null;

    return .{ .of_ty = of_ty, .tag_idx = @intCast(idx) };
}

/// Reapply a snapshot of symbol bindings (e.g., after destructuring) in reverse order.
pub fn restoreBindings(self: *LowerTir, env: *cf.Env, saved: []const EnvBindingSnapshot) !void {
    var i: usize = saved.len;
    while (i > 0) : (i -= 1) try env.restoreBinding(self.gpa, saved[i - 1].name, saved[i - 1].prev);
}

/// Restore the binding environment to the snapshot in `saved`, dropping new names.
pub fn restoreEnvSnapshot(
    self: *LowerTir,
    env: *cf.Env,
    saved: []const EnvBindingSnapshot,
    scratch_names: *std.ArrayList(ast.StrId),
) !void {
    scratch_names.clearRetainingCapacity();
    var it = env.map.iterator();
    while (it.next()) |entry| {
        var found = false;
        for (saved) |snap| if (snap.name.toRaw() == entry.key_ptr.toRaw()) {
            found = true;
            break;
        };
        if (!found) try scratch_names.append(self.gpa, entry.key_ptr.*);
    }
    for (scratch_names.items) |name| _ = env.map.swapRemove(name);
    try self.restoreBindings(env, saved);
}
