const Checker = @import("checker.zig").Checker;
const types = @import("types.zig");
const ast = @import("ast.zig");
const std = @import("std");
const compile = @import("compile.zig");

const comp = @import("comptime.zig");
const ComptimeBinding = @import("pipeline.zig").Pipeline.ComptimeBinding;
const Loc = @import("lexer.zig").Token.Loc;
const interpreter = @import("interpreter.zig");
const symbols = @import("symbols.zig");

const List = std.ArrayList;

/// Describes compile-time bindings introduced during type resolution (type/value).
pub const Binding = union(enum) {
    Type: struct {
        name: ast.StrId,
        ty: types.TypeId,
    },
    Value: struct {
        name: ast.StrId,
        value: comp.ValueId,
        ty: types.TypeId,
    },
};

const ComptimeBindingSlice = struct {
    items: []ComptimeBinding,
    owns: bool,
};

/// Return true when `func_ty` is a non-extern function whose final parameter is `any`.
pub fn isInternalVariadic(store: *types.TypeStore, func_ty: types.TypeId) bool {
    if (store.getKind(func_ty) != .Function) return false;
    const fn_row = store.get(.Function, func_ty);
    if (fn_row.is_extern) return false;
    const params = store.type_pool.slice(fn_row.params);
    if (params.len == 0) return false;
    const last = params[params.len - 1];
    return store.getKind(last) == .Any;
}

/// Recursively collect all expression IDs reachable from `expr_id`.
fn collectExprIds(
    gpa: std.mem.Allocator,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    out: *List(ast.ExprId),
) !void {
    try out.append(gpa, expr_id);
    const expr_store = &ast_unit.exprs;
    switch (ast_unit.kind(expr_id)) {
        .Literal, .Ident, .Splice, .NullLit, .UndefLit, .AnyType, .TypeType, .NoreturnType, .Continue => {},
        .Binary => {
            const row = expr_store.get(.Binary, expr_id);
            try collectExprIds(gpa, ast_unit, row.left, out);
            try collectExprIds(gpa, ast_unit, row.right, out);
        },
        .Range => {
            const row = expr_store.get(.Range, expr_id);
            if (!row.start.isNone()) try collectExprIds(gpa, ast_unit, row.start.unwrap(), out);
            if (!row.end.isNone()) try collectExprIds(gpa, ast_unit, row.end.unwrap(), out);
        },
        inline .ArrayLit, .TupleLit => |k| {
            const row = expr_store.get(k, expr_id);
            const elems = expr_store.expr_pool.slice(row.elems);
            for (elems) |elem| try collectExprIds(gpa, ast_unit, elem, out);
        },
        .MapLit => {
            const row = expr_store.get(.MapLit, expr_id);
            const entries = expr_store.kv_pool.slice(row.entries);
            for (entries) |entry_id| {
                const entry = expr_store.KeyValue.get(entry_id);
                try collectExprIds(gpa, ast_unit, entry.key, out);
                try collectExprIds(gpa, ast_unit, entry.value, out);
            }
        },
        .Call => {
            const row = expr_store.get(.Call, expr_id);
            try collectExprIds(gpa, ast_unit, row.callee, out);
            const args = expr_store.expr_pool.slice(row.args);
            for (args) |arg| try collectExprIds(gpa, ast_unit, arg, out);
        },
        .IndexAccess => {
            const row = expr_store.get(.IndexAccess, expr_id);
            try collectExprIds(gpa, ast_unit, row.collection, out);
            try collectExprIds(gpa, ast_unit, row.index, out);
        },
        .FieldAccess => try collectExprIds(gpa, ast_unit, expr_store.get(.FieldAccess, expr_id).parent, out),
        .StructLit => {
            const row = expr_store.get(.StructLit, expr_id);
            if (!row.ty.isNone()) try collectExprIds(gpa, ast_unit, row.ty.unwrap(), out);
            const fields = expr_store.sfv_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.StructFieldValue.get(fid);
                try collectExprIds(gpa, ast_unit, field.value, out);
            }
        },
        .FunctionLit => {
            const row = expr_store.get(.FunctionLit, expr_id);
            const params = expr_store.param_pool.slice(row.params);
            for (params) |pid| {
                const param = expr_store.Param.get(pid);
                if (!param.ty.isNone()) try collectExprIds(gpa, ast_unit, param.ty.unwrap(), out);
                if (!param.value.isNone()) try collectExprIds(gpa, ast_unit, param.value.unwrap(), out);
                if (!param.pat.isNone()) try collectPatternExprs(gpa, ast_unit, param.pat.unwrap(), out);
            }
            if (!row.result_ty.isNone()) try collectExprIds(gpa, ast_unit, row.result_ty.unwrap(), out);
            if (!row.body.isNone()) try collectExprIds(gpa, ast_unit, row.body.unwrap(), out);
        },
        .Block => {
            const row = expr_store.get(.Block, expr_id);
            const stmts = ast_unit.stmts.stmt_pool.slice(row.items);
            for (stmts) |sid| try collectStmtExprs(gpa, ast_unit, sid, out);
        },
        .ComptimeBlock => try collectExprIds(gpa, ast_unit, expr_store.get(.ComptimeBlock, expr_id).block, out),
        .CodeBlock => try collectExprIds(gpa, ast_unit, expr_store.get(.CodeBlock, expr_id).block, out),
        .AsyncBlock => try collectExprIds(gpa, ast_unit, expr_store.get(.AsyncBlock, expr_id).body, out),
        .MlirBlock => {
            const row = expr_store.get(.MlirBlock, expr_id);
            const args = expr_store.expr_pool.slice(row.args);
            for (args) |arg| try collectExprIds(gpa, ast_unit, arg, out);
        },
        .Return => {
            const row = expr_store.get(.Return, expr_id);
            if (!row.value.isNone()) try collectExprIds(gpa, ast_unit, row.value.unwrap(), out);
        },
        .If => {
            const row = expr_store.get(.If, expr_id);
            try collectExprIds(gpa, ast_unit, row.cond, out);
            try collectExprIds(gpa, ast_unit, row.then_block, out);
            if (!row.else_block.isNone()) try collectExprIds(gpa, ast_unit, row.else_block.unwrap(), out);
        },
        .While => {
            const row = expr_store.get(.While, expr_id);
            if (!row.cond.isNone()) try collectExprIds(gpa, ast_unit, row.cond.unwrap(), out);
            if (!row.pattern.isNone()) try collectPatternExprs(gpa, ast_unit, row.pattern.unwrap(), out);
            try collectExprIds(gpa, ast_unit, row.body, out);
        },
        .For => {
            const row = expr_store.get(.For, expr_id);
            try collectPatternExprs(gpa, ast_unit, row.pattern, out);
            try collectExprIds(gpa, ast_unit, row.iterable, out);
            try collectExprIds(gpa, ast_unit, row.body, out);
        },
        .Match => {
            const row = expr_store.get(.Match, expr_id);
            try collectExprIds(gpa, ast_unit, row.expr, out);
            const arms = expr_store.arm_pool.slice(row.arms);
            for (arms) |arm_id| {
                const arm = expr_store.MatchArm.get(arm_id);
                try collectPatternExprs(gpa, ast_unit, arm.pattern, out);
                if (!arm.guard.isNone()) try collectExprIds(gpa, ast_unit, arm.guard.unwrap(), out);
                try collectExprIds(gpa, ast_unit, arm.body, out);
            }
        },
        .Break => {
            const row = expr_store.get(.Break, expr_id);
            if (!row.value.isNone()) try collectExprIds(gpa, ast_unit, row.value.unwrap(), out);
        },
        .Closure => {
            const row = expr_store.get(.Closure, expr_id);
            const params = expr_store.param_pool.slice(row.params);
            for (params) |pid| {
                const param = expr_store.Param.get(pid);
                if (!param.ty.isNone()) try collectExprIds(gpa, ast_unit, param.ty.unwrap(), out);
                if (!param.value.isNone()) try collectExprIds(gpa, ast_unit, param.value.unwrap(), out);
                if (!param.pat.isNone()) try collectPatternExprs(gpa, ast_unit, param.pat.unwrap(), out);
            }
            if (!row.result_ty.isNone()) try collectExprIds(gpa, ast_unit, row.result_ty.unwrap(), out);
            try collectExprIds(gpa, ast_unit, row.body, out);
        },
        .Cast => {
            const row = expr_store.get(.Cast, expr_id);
            try collectExprIds(gpa, ast_unit, row.expr, out);
            try collectExprIds(gpa, ast_unit, row.ty, out);
        },
        .Catch => {
            const row = expr_store.get(.Catch, expr_id);
            try collectExprIds(gpa, ast_unit, row.expr, out);
            try collectExprIds(gpa, ast_unit, row.handler, out);
        },
        inline .Unary, .Insert, .Await, .TypeOf, .Deref, .Defer, .ErrDefer, .ErrUnwrap, .OptionalUnwrap => |k| try collectExprIds(gpa, ast_unit, expr_store.get(k, expr_id).expr, out),
        .TupleType => {
            const row = expr_store.get(.TupleType, expr_id);
            const elems = expr_store.expr_pool.slice(row.elems);
            for (elems) |elem| try collectExprIds(gpa, ast_unit, elem, out);
        },
        .ArrayType => {
            const row = expr_store.get(.ArrayType, expr_id);
            try collectExprIds(gpa, ast_unit, row.elem, out);
            try collectExprIds(gpa, ast_unit, row.size, out);
        },
        .DynArrayType => try collectExprIds(gpa, ast_unit, expr_store.get(.DynArrayType, expr_id).elem, out),
        .MapType => {
            const row = expr_store.get(.MapType, expr_id);
            try collectExprIds(gpa, ast_unit, row.key, out);
            try collectExprIds(gpa, ast_unit, row.value, out);
        },
        .ErrorSetType => {
            const row = expr_store.get(.ErrorSetType, expr_id);
            try collectExprIds(gpa, ast_unit, row.err, out);
            try collectExprIds(gpa, ast_unit, row.value, out);
        },
        .StructType => {
            const row = expr_store.get(.StructType, expr_id);
            const fields = expr_store.sfield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.StructField.get(fid);
                try collectExprIds(gpa, ast_unit, field.ty, out);
                if (!field.value.isNone()) try collectExprIds(gpa, ast_unit, field.value.unwrap(), out);
            }
        },
        .EnumType => {
            const row = expr_store.get(.EnumType, expr_id);
            if (!row.discriminant.isNone()) try collectExprIds(gpa, ast_unit, row.discriminant.unwrap(), out);
            const fields = expr_store.efield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.EnumField.get(fid);
                if (!field.value.isNone()) try collectExprIds(gpa, ast_unit, field.value.unwrap(), out);
            }
        },
        inline .ErrorType, .VariantType => |k| {
            const row = expr_store.get(k, expr_id);
            const fields = expr_store.vfield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.VariantField.get(fid);
                if (!field.value.isNone()) try collectExprIds(gpa, ast_unit, field.value.unwrap(), out);
            }
        },
        .UnionType => {
            const row = expr_store.get(.UnionType, expr_id);
            const fields = expr_store.sfield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.StructField.get(fid);
                try collectExprIds(gpa, ast_unit, field.ty, out);
                if (!field.value.isNone()) try collectExprIds(gpa, ast_unit, field.value.unwrap(), out);
            }
        },
        inline .PointerType, .ComplexType, .SliceType, .OptionalType => |k| try collectExprIds(gpa, ast_unit, expr_store.get(k, expr_id).elem, out),
        .SimdType => {
            const row = expr_store.get(.SimdType, expr_id);
            try collectExprIds(gpa, ast_unit, row.elem, out);
            try collectExprIds(gpa, ast_unit, row.lanes, out);
        },
        .TensorType => {
            const row = expr_store.get(.TensorType, expr_id);
            try collectExprIds(gpa, ast_unit, row.elem, out);
            const shape = expr_store.expr_pool.slice(row.shape);
            for (shape) |dim| try collectExprIds(gpa, ast_unit, dim, out);
        },
        else => unreachable,
    }
}

pub fn exprMentionsAnyNameBitset(
    gpa: std.mem.Allocator,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    names: *const std.DynamicBitSetUnmanaged,
) !bool {
    if (names.count() == 0) return false;
    if (ast_unit.kind(expr_id) == .Ident) {
        const name = ast_unit.exprs.get(.Ident, expr_id).name;
        const raw = name.toRaw();
        return raw < names.capacity() and names.isSet(raw);
    }
    var ids = List(ast.ExprId){};
    defer ids.deinit(gpa);
    try collectExprIds(gpa, ast_unit, expr_id, &ids);
    for (ids.items) |eid| {
        if (ast_unit.kind(eid) != .Ident) continue;
        const name = ast_unit.exprs.get(.Ident, eid).name;
        const raw = name.toRaw();
        if (raw < names.capacity() and names.isSet(raw)) return true;
    }
    return false;
}

pub fn findAnyTypeExpr(gpa: std.mem.Allocator, ast_unit: *ast.Ast, expr_id: ast.ExprId) !?ast.ExprId {
    var ids = List(ast.ExprId){};
    defer ids.deinit(gpa);
    try collectExprIds(gpa, ast_unit, expr_id, &ids);
    for (ids.items) |eid| {
        if (ast_unit.kind(eid) == .AnyType) return eid;
    }
    return null;
}

pub const PatternChildDesc = union(enum) {
    TupleElem: usize,
    StructField: ast.StrId,
    VariantTupleElem: struct { case_name: ast.StrId, index: usize },
    VariantStructField: struct { case_name: ast.StrId, field_name: ast.StrId },
    SliceElem: usize,
    SliceRest: void,
    OrAlt: usize,
    AtPattern: void,
};

pub const PatternWalkerContext = struct {
    ctx: *void,
    onExpr: ?*const fn (*void, *ast.Ast, ast.ExprId) anyerror!void,
    onBinding: ?*const fn (*void, *ast.Ast, ast.PatternId, ast.StrId, ?types.TypeId) anyerror!void,
    onChildType: ?*const fn (*void, *ast.Ast, ast.PatternId, ?types.TypeId, ast.PatternId, PatternChildDesc) ?types.TypeId,
};

fn callOnExpr(ctx: *PatternWalkerContext, ast_unit: *ast.Ast, expr: ast.ExprId) anyerror!void {
    if (ctx.onExpr) |hook| try hook(ctx.ctx, ast_unit, expr);
    return;
}

fn callOnBinding(ctx: *PatternWalkerContext, ast_unit: *ast.Ast, pid: ast.PatternId, name: ast.StrId, value_ty: ?types.TypeId) anyerror!void {
    if (ctx.onBinding) |hook| try hook(ctx.ctx, ast_unit, pid, name, value_ty);
    return;
}

fn patternCaseName(ast_unit: *ast.Ast, path: ast.RangePathSeg) ?ast.StrId {
    const segs = ast_unit.pats.seg_pool.slice(path);
    if (segs.len == 0) return null;
    return ast_unit.pats.PathSeg.get(segs[segs.len - 1]).name;
}

fn walkChild(
    ctx: *PatternWalkerContext,
    ast_unit: *ast.Ast,
    parent_pid: ast.PatternId,
    parent_ty: ?types.TypeId,
    child_pid: ast.PatternId,
    desc: PatternChildDesc,
) anyerror!void {
    const child_ty = if (ctx.onChildType) |hook| hook(ctx.ctx, ast_unit, parent_pid, parent_ty, child_pid, desc) else null;
    const next_ty = if (child_ty) |ty| ty else parent_ty;
    try walkPattern(ctx, ast_unit, child_pid, next_ty);
}

pub fn walkPattern(ctx: *PatternWalkerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: ?types.TypeId) anyerror!void {
    const pats = &ast_unit.pats;
    switch (ast_unit.kind(pid)) {
        .Wildcard, .Path => {},
        .Literal => try callOnExpr(ctx, ast_unit, pats.get(.Literal, pid).expr),
        .Binding => try callOnBinding(ctx, ast_unit, pid, pats.get(.Binding, pid).name, value_ty),
        .Tuple => {
            const row = pats.get(.Tuple, pid);
            const elems = pats.pat_pool.slice(row.elems);
            for (elems, 0..) |elem, index|
                try walkChild(ctx, ast_unit, pid, value_ty, elem, .{ .TupleElem = index });
        },
        .Slice => {
            const row = pats.get(.Slice, pid);
            const elems = pats.pat_pool.slice(row.elems);
            for (elems, 0..) |elem, index|
                try walkChild(ctx, ast_unit, pid, value_ty, elem, .{ .SliceElem = index });
            if (!row.rest_binding.isNone())
                try walkChild(ctx, ast_unit, pid, value_ty, row.rest_binding.unwrap(), .SliceRest);
        },
        .Struct => {
            const row = pats.get(.Struct, pid);
            const fields = pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const field = pats.StructField.get(fid);
                try walkChild(ctx, ast_unit, pid, value_ty, field.pattern, .{
                    .StructField = field.name,
                });
            }
        },
        .VariantTuple => {
            const row = pats.get(.VariantTuple, pid);
            const elems = pats.pat_pool.slice(row.elems);
            const case_name = patternCaseName(ast_unit, row.path) orelse ast.StrId.fromRaw(0);
            for (elems, 0..) |elem, index|
                try walkChild(ctx, ast_unit, pid, value_ty, elem, .{
                    .VariantTupleElem = .{ .case_name = case_name, .index = index },
                });
        },
        .VariantStruct => {
            const row = pats.get(.VariantStruct, pid);
            const fields = pats.field_pool.slice(row.fields);
            const case_name = patternCaseName(ast_unit, row.path) orelse ast.StrId.fromRaw(0);
            for (fields) |fid| {
                const field = pats.StructField.get(fid);
                try walkChild(ctx, ast_unit, pid, value_ty, field.pattern, .{
                    .VariantStructField = .{ .case_name = case_name, .field_name = field.name },
                });
            }
        },
        .Range => {
            const row = pats.get(.Range, pid);
            if (!row.start.isNone()) try callOnExpr(ctx, ast_unit, row.start.unwrap());
            if (!row.end.isNone()) try callOnExpr(ctx, ast_unit, row.end.unwrap());
        },
        .Or => {
            const alts = pats.pat_pool.slice(pats.get(.Or, pid).alts);
            for (alts, 0..) |alt, index|
                try walkChild(ctx, ast_unit, pid, value_ty, alt, .{ .OrAlt = index });
        },
        .At => {
            const row = pats.get(.At, pid);
            try callOnBinding(ctx, ast_unit, pid, row.binder, value_ty);
            try walkChild(ctx, ast_unit, pid, value_ty, row.pattern, .AtPattern);
        },
    }
}

/// Recursively collect expression ids referenced from pattern `pat_id`.
fn collectPatternExprs(
    gpa: std.mem.Allocator,
    ast_unit: *ast.Ast,
    pat_id: ast.PatternId,
    out: *List(ast.ExprId),
) anyerror!void {
    var visitor = PatternExprCollector{
        .gpa = gpa,
        .out = out,
    };
    var ctx = PatternWalkerContext{
        .ctx = @ptrCast(@alignCast(&visitor)),
        .onExpr = patternExprOnExpr,
        .onBinding = null,
        .onChildType = null,
    };
    try walkPattern(&ctx, ast_unit, pat_id, null);
}

const PatternExprCollector = struct {
    gpa: std.mem.Allocator,
    out: *List(ast.ExprId),
};

fn patternExprOnExpr(ctx: *void, _: *ast.Ast, expr: ast.ExprId) anyerror!void {
    const collector: *PatternExprCollector = @ptrCast(@alignCast(ctx));
    try collector.out.append(collector.gpa, expr);
}

/// Collect expression ids touched by statement `stmt_id`.
fn collectStmtExprs(
    gpa: std.mem.Allocator,
    ast_unit: *ast.Ast,
    stmt_id: ast.StmtId,
    out: *List(ast.ExprId),
) anyerror!void {
    const stmt_store = &ast_unit.stmts;
    switch (ast_unit.kind(stmt_id)) {
        inline .Expr, .Defer, .ErrDefer, .Insert => |k| try collectExprIds(gpa, ast_unit, stmt_store.get(k, stmt_id).expr, out),
        .Decl => try collectDeclExprs(gpa, ast_unit, stmt_store.get(.Decl, stmt_id).decl, out),
        .Assign => {
            const row = stmt_store.get(.Assign, stmt_id);
            switch (row.left) {
                .expr => |e| try collectExprIds(gpa, ast_unit, e, out),
                .pattern => |p| try collectPatternExprs(gpa, ast_unit, p, out),
            }
            try collectExprIds(gpa, ast_unit, row.right, out);
        },
        .Return => {
            const row = stmt_store.get(.Return, stmt_id);
            if (!row.value.isNone()) try collectExprIds(gpa, ast_unit, row.value.unwrap(), out);
        },
        .Break => {
            const row = stmt_store.get(.Break, stmt_id);
            if (!row.value.isNone()) try collectExprIds(gpa, ast_unit, row.value.unwrap(), out);
        },
        .Continue, .Unreachable => {},
    }
}

/// Collect expressions from declaration `decl_id`, including patterns, annotations, and initializer.
pub fn collectDeclExprs(
    gpa: std.mem.Allocator,
    ast_unit: *ast.Ast,
    decl_id: ast.DeclId,
    out: *List(ast.ExprId),
) !void {
    const decl = ast_unit.exprs.Decl.get(decl_id);
    if (!decl.pattern.isNone()) try collectPatternExprs(gpa, ast_unit, decl.pattern.unwrap(), out);
    if (!decl.ty.isNone()) try collectExprIds(gpa, ast_unit, decl.ty.unwrap(), out);
    try collectExprIds(gpa, ast_unit, decl.value, out);
}

/// Snapshot the expression types for `fn_expr` so later specializations can reuse them.
pub fn storeMethodExprTypes(
    self: *Checker,
    ast_unit: *ast.Ast,
    owner_ty: types.TypeId,
    method_name: ast.StrId,
    fn_expr: ast.ExprId,
) !void {
    const mark = self.expr_id_scratch.items.len;
    try self.acquireExprIdsScratch();
    defer self.releaseExprIdsScratch();
    try collectExprIds(self.gpa, ast_unit, fn_expr, &self.expr_id_scratch);
    const expr_ids_slice = self.expr_id_scratch.items[mark..];
    if (expr_ids_slice.len == 0) return;

    const expr_types = ast_unit.type_info.expr_types.items;
    var needed: usize = 0;
    for (expr_ids_slice) |eid| {
        const raw = eid.toRaw();
        if (raw >= expr_types.len) continue;
        if (expr_types[raw]) |_| needed += 1;
    }
    if (needed == 0) return;

    var raw_ids = try self.gpa.alloc(u32, needed);
    defer self.gpa.free(raw_ids);
    var type_buf = try self.gpa.alloc(types.TypeId, needed);
    defer self.gpa.free(type_buf);

    var filled: usize = 0;
    for (expr_ids_slice) |eid| {
        const raw = eid.toRaw();
        if (raw >= expr_types.len) continue;
        if (expr_types[raw]) |ty| {
            raw_ids[filled] = raw;
            type_buf[filled] = ty;
            filled += 1;
        }
    }
    std.debug.assert(filled == needed);
    try ast_unit.type_info.storeMethodExprSnapshot(owner_ty, method_name, raw_ids[0..filled], type_buf[0..filled]);
}

/// Snapshot expr types and comptime values for a specialized clone.
pub fn storeSpecializationSnapshots(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_ids: []const ast.ExprId,
    specialization_decl_id: ast.DeclId,
) !void {
    if (expr_ids.len == 0) return;

    var type_ids = std.ArrayListUnmanaged(u32){};
    var type_vals = std.ArrayListUnmanaged(types.TypeId){};
    var cv_ids = std.ArrayListUnmanaged(u32){};
    var cv_vals = std.ArrayListUnmanaged(comp.ValueId){};
    defer {
        type_ids.deinit(self.gpa);
        type_vals.deinit(self.gpa);
        cv_ids.deinit(self.gpa);
        cv_vals.deinit(self.gpa);
    }

    const expr_types = ast_unit.type_info.expr_types.items;
    for (expr_ids) |eid| {
        const raw = eid.toRaw();
        if (raw < expr_types.len) {
            if (expr_types[raw]) |ty| {
                try type_ids.append(self.gpa, raw);
                try type_vals.append(self.gpa, ty);
            }
        }
        if (ast_unit.type_info.getComptimeValue(eid)) |val| {
            try cv_ids.append(self.gpa, raw);
            try cv_vals.append(self.gpa, val.*);
        }
    }

    if (type_ids.items.len > 0) {
        try ast_unit.type_info.storeSpecializationExprSnapshot(specialization_decl_id, type_ids.items, type_vals.items);
    }
    if (cv_ids.items.len > 0) {
        try ast_unit.type_info.storeSpecializationComptimeExprSnapshot(specialization_decl_id, cv_ids.items, cv_vals.items);
    }
}

/// Convert `bindings` into a pipeline binding slice suitable for `evalComptimeExpr`.
fn comptimeBindingsFor(self: *Checker, ast_unit: *ast.Ast, bindings: []const Binding) !ComptimeBindingSlice {
    if (bindings.len == 0) return .{ .items = &.{}, .owns = false };

    var out = try self.gpa.alloc(ComptimeBinding, bindings.len);
    var i: usize = 0;
    while (i < bindings.len) : (i += 1) {
        out[i] = switch (bindings[i]) {
            .Type => |t| .{ .type_param = .{ .name = t.name, .ty = t.ty } },
            .Value => |v| .{ .value_param = .{ .name = v.name, .ty = v.ty, .value = v.value, .store = &ast_unit.type_info.val_store } },
        };
    }

    return .{ .items = out, .owns = true };
}

/// Evaluate `expr` at comptime, applying additional `bindings` to the interpreter.
fn evalComptimeValueWithBindings(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    expr: ast.ExprId,
    bindings: []const Binding,
) !comp.ValueId {
    const pb = try comptimeBindingsFor(self, ast_unit, bindings);
    defer if (pb.owns) self.gpa.free(pb.items);
    return self.evalComptimeExpr(ctx, ast_unit, expr, pb.items);
}

/// Search `bindings` for a type binding named `name`.
fn lookupTypeBinding(bindings: []const Binding, name: ast.StrId) ?types.TypeId {
    for (bindings) |binding| {
        switch (binding) {
            .Type => |t| if (t.name.eq(name)) return t.ty,
            else => {},
        }
    }
    return null;
}

/// Search `bindings` for a value binding named `name`.
fn lookupValueBinding(bindings: []const Binding, name: ast.StrId) ?comp.ValueId {
    for (bindings) |binding| {
        switch (binding) {
            .Value => |v| if (v.name.eq(name)) return v.value,
            else => {},
        }
    }
    return null;
}

/// Reset cached type info for the pattern subtree rooted at `pat_id`.
fn clearPatternTypes(ast_unit: *ast.Ast, pat_id: ast.PatternId) void {
    const pats = &ast_unit.pats;
    switch (ast_unit.kind(pat_id)) {
        .Literal => clearExprTypes(ast_unit, pats.get(.Literal, pat_id).expr),
        .Range => {
            const row = pats.get(.Range, pat_id);
            if (!row.start.isNone()) clearExprTypes(ast_unit, row.start.unwrap());
            if (!row.end.isNone()) clearExprTypes(ast_unit, row.end.unwrap());
        },
        .Tuple => {
            const elems = pats.pat_pool.slice(pats.get(.Tuple, pat_id).elems);
            for (elems) |elem| clearPatternTypes(ast_unit, elem);
        },
        .Slice => {
            const row = pats.get(.Slice, pat_id);
            const elems = pats.pat_pool.slice(row.elems);
            for (elems) |elem| clearPatternTypes(ast_unit, elem);
            if (!row.rest_binding.isNone()) clearPatternTypes(ast_unit, row.rest_binding.unwrap());
        },
        inline .Struct, .VariantStruct => |k| {
            const row = pats.get(k, pat_id);
            const fields = pats.field_pool.slice(row.fields);
            for (fields) |fid| clearPatternTypes(ast_unit, pats.StructField.get(fid).pattern);
        },
        .VariantTuple => {
            const elems = pats.pat_pool.slice(pats.get(.VariantTuple, pat_id).elems);
            for (elems) |elem| clearPatternTypes(ast_unit, elem);
        },
        .Or => {
            const alts = pats.pat_pool.slice(pats.get(.Or, pat_id).alts);
            for (alts) |alt| clearPatternTypes(ast_unit, alt);
        },
        .At => clearPatternTypes(ast_unit, pats.get(.At, pat_id).pattern),
        else => {},
    }
}

/// Clear cached expression types and related metadata for `expr_id`.
fn clearExprTypes(ast_unit: *ast.Ast, expr_id: ast.ExprId) void {
    const ti = &ast_unit.type_info;
    if (expr_id.toRaw() < ti.expr_types.items.len) {
        ti.expr_types.items[expr_id.toRaw()] = null;
    }
    _ = ti.method_bindings.swapRemove(expr_id.toRaw());
    ti.clearFieldIndex(expr_id) catch {};

    const expr_store = &ast_unit.exprs;
    switch (ast_unit.kind(expr_id)) {
        .Literal, .Ident, .Splice, .NullLit, .UndefLit, .AnyType, .TypeType, .NoreturnType, .Continue => {},
        inline .Unary, .Deref, .Defer, .ErrDefer, .ErrUnwrap, .OptionalUnwrap, .Await, .Insert, .TypeOf => |k| clearExprTypes(ast_unit, expr_store.get(k, expr_id).expr),
        .Binary => {
            const row = expr_store.get(.Binary, expr_id);
            clearExprTypes(ast_unit, row.left);
            clearExprTypes(ast_unit, row.right);
        },
        .Range => {
            const row = expr_store.get(.Range, expr_id);
            if (!row.start.isNone()) clearExprTypes(ast_unit, row.start.unwrap());
            if (!row.end.isNone()) clearExprTypes(ast_unit, row.end.unwrap());
        },
        inline .ArrayLit, .TupleLit => |k| {
            const elems = expr_store.expr_pool.slice(expr_store.get(k, expr_id).elems);
            for (elems) |elem| clearExprTypes(ast_unit, elem);
        },
        .MapLit => {
            const entries = expr_store.kv_pool.slice(expr_store.get(.MapLit, expr_id).entries);
            for (entries) |entry_id| {
                const entry = expr_store.KeyValue.get(entry_id);
                clearExprTypes(ast_unit, entry.key);
                clearExprTypes(ast_unit, entry.value);
            }
        },
        .Call => {
            const row = expr_store.get(.Call, expr_id);
            clearExprTypes(ast_unit, row.callee);
            const args = expr_store.expr_pool.slice(row.args);
            for (args) |arg| clearExprTypes(ast_unit, arg);
        },
        .IndexAccess => {
            const row = expr_store.get(.IndexAccess, expr_id);
            clearExprTypes(ast_unit, row.collection);
            clearExprTypes(ast_unit, row.index);
        },
        .FieldAccess => clearExprTypes(ast_unit, expr_store.get(.FieldAccess, expr_id).parent),
        .StructLit => {
            const row = expr_store.get(.StructLit, expr_id);
            if (!row.ty.isNone()) clearExprTypes(ast_unit, row.ty.unwrap());
            const fields = expr_store.sfv_pool.slice(row.fields);
            for (fields) |fid|
                clearExprTypes(ast_unit, expr_store.StructFieldValue.get(fid).value);
        },
        .FunctionLit => {
            const row = expr_store.get(.FunctionLit, expr_id);
            const params = expr_store.param_pool.slice(row.params);
            for (params) |pid| {
                const param = expr_store.Param.get(pid);
                if (!param.ty.isNone()) clearExprTypes(ast_unit, param.ty.unwrap());
                if (!param.value.isNone()) clearExprTypes(ast_unit, param.value.unwrap());
                if (!param.pat.isNone()) clearPatternTypes(ast_unit, param.pat.unwrap());
            }
            if (!row.result_ty.isNone()) clearExprTypes(ast_unit, row.result_ty.unwrap());
            if (!row.body.isNone()) clearExprTypes(ast_unit, row.body.unwrap());
        },
        .Block => {
            const stmts = ast_unit.stmts.stmt_pool.slice(expr_store.get(.Block, expr_id).items);
            for (stmts) |sid| clearStmtTypes(ast_unit, sid);
        },
        .ComptimeBlock => clearExprTypes(ast_unit, expr_store.get(.ComptimeBlock, expr_id).block),
        .CodeBlock => clearExprTypes(ast_unit, expr_store.get(.CodeBlock, expr_id).block),
        .AsyncBlock => clearExprTypes(ast_unit, expr_store.get(.AsyncBlock, expr_id).body),
        .MlirBlock => {
            const row = expr_store.get(.MlirBlock, expr_id);
            const args = expr_store.expr_pool.slice(row.args);
            for (args) |arg| clearExprTypes(ast_unit, arg);
        },
        .Return => {
            const row = expr_store.get(.Return, expr_id);
            if (!row.value.isNone()) clearExprTypes(ast_unit, row.value.unwrap());
        },
        .If => {
            const row = expr_store.get(.If, expr_id);
            clearExprTypes(ast_unit, row.cond);
            clearExprTypes(ast_unit, row.then_block);
            if (!row.else_block.isNone()) clearExprTypes(ast_unit, row.else_block.unwrap());
        },
        .While => {
            const row = expr_store.get(.While, expr_id);
            if (!row.cond.isNone()) clearExprTypes(ast_unit, row.cond.unwrap());
            if (!row.pattern.isNone()) clearPatternTypes(ast_unit, row.pattern.unwrap());
            clearExprTypes(ast_unit, row.body);
        },
        .For => {
            const row = expr_store.get(.For, expr_id);
            clearPatternTypes(ast_unit, row.pattern);
            clearExprTypes(ast_unit, row.iterable);
            clearExprTypes(ast_unit, row.body);
        },
        .Match => {
            const row = expr_store.get(.Match, expr_id);
            clearExprTypes(ast_unit, row.expr);
            const arms = expr_store.arm_pool.slice(row.arms);
            for (arms) |arm_id| {
                const arm = expr_store.MatchArm.get(arm_id);
                clearPatternTypes(ast_unit, arm.pattern);
                if (!arm.guard.isNone()) clearExprTypes(ast_unit, arm.guard.unwrap());
                clearExprTypes(ast_unit, arm.body);
            }
        },
        .Break => {
            const row = expr_store.get(.Break, expr_id);
            if (!row.value.isNone()) clearExprTypes(ast_unit, row.value.unwrap());
        },
        .Closure => {
            const row = expr_store.get(.Closure, expr_id);
            const params = expr_store.param_pool.slice(row.params);
            for (params) |pid| {
                const param = expr_store.Param.get(pid);
                if (!param.ty.isNone()) clearExprTypes(ast_unit, param.ty.unwrap());
                if (!param.value.isNone()) clearExprTypes(ast_unit, param.value.unwrap());
                if (!param.pat.isNone()) clearPatternTypes(ast_unit, param.pat.unwrap());
            }
            if (!row.result_ty.isNone()) clearExprTypes(ast_unit, row.result_ty.unwrap());
            clearExprTypes(ast_unit, row.body);
        },
        .Cast => {
            const row = expr_store.get(.Cast, expr_id);
            clearExprTypes(ast_unit, row.expr);
            clearExprTypes(ast_unit, row.ty);
        },
        .Catch => {
            const row = expr_store.get(.Catch, expr_id);
            clearExprTypes(ast_unit, row.expr);
            clearExprTypes(ast_unit, row.handler);
        },
        .TupleType => {
            const row = expr_store.get(.TupleType, expr_id);
            const elems = expr_store.expr_pool.slice(row.elems);
            for (elems) |elem| clearExprTypes(ast_unit, elem);
        },
        .ArrayType => {
            const row = expr_store.get(.ArrayType, expr_id);
            clearExprTypes(ast_unit, row.elem);
            clearExprTypes(ast_unit, row.size);
        },
        .MapType => {
            const row = expr_store.get(.MapType, expr_id);
            clearExprTypes(ast_unit, row.key);
            clearExprTypes(ast_unit, row.value);
        },
        inline .SliceType, .ComplexType, .PointerType, .OptionalType, .DynArrayType => |k| clearExprTypes(ast_unit, expr_store.get(k, expr_id).elem),
        .ErrorSetType => {
            const row = expr_store.get(.ErrorSetType, expr_id);
            clearExprTypes(ast_unit, row.err);
            clearExprTypes(ast_unit, row.value);
        },
        inline .StructType, .UnionType => |k| {
            const row = expr_store.get(k, expr_id);
            const fields = expr_store.sfield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.StructField.get(fid);
                clearExprTypes(ast_unit, field.ty);
                if (!field.value.isNone()) clearExprTypes(ast_unit, field.value.unwrap());
            }
        },
        .EnumType => {
            const row = expr_store.get(.EnumType, expr_id);
            if (!row.discriminant.isNone()) clearExprTypes(ast_unit, row.discriminant.unwrap());
            const fields = expr_store.efield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.EnumField.get(fid);
                if (!field.value.isNone()) clearExprTypes(ast_unit, field.value.unwrap());
            }
        },
        inline .VariantType, .ErrorType => |k| {
            const row = expr_store.get(k, expr_id);
            const fields = expr_store.vfield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.VariantField.get(fid);
                if (!field.value.isNone()) clearExprTypes(ast_unit, field.value.unwrap());
            }
        },
        .SimdType => {
            const row = expr_store.get(.SimdType, expr_id);
            clearExprTypes(ast_unit, row.elem);
            clearExprTypes(ast_unit, row.lanes);
        },
        .TensorType => {
            const row = expr_store.get(.TensorType, expr_id);
            clearExprTypes(ast_unit, row.elem);
            const shape = expr_store.expr_pool.slice(row.shape);
            for (shape) |dim| clearExprTypes(ast_unit, dim);
        },
        else => unreachable,
    }
}

/// Reset expression type caches referenced by statement `stmt_id`.
fn clearStmtTypes(ast_unit: *ast.Ast, stmt_id: ast.StmtId) void {
    const stmt_store = &ast_unit.stmts;
    switch (ast_unit.kind(stmt_id)) {
        inline .Expr, .Insert, .Defer, .ErrDefer => clearExprTypes(ast_unit, stmt_store.get(.Expr, stmt_id).expr),
        .Decl => clearDeclTypes(ast_unit, stmt_store.get(.Decl, stmt_id).decl),
        .Assign => {
            const row = stmt_store.get(.Assign, stmt_id);
            switch (row.left) {
                .expr => |e| clearExprTypes(ast_unit, e),
                .pattern => |p| clearPatternTypes(ast_unit, p),
            }
            clearExprTypes(ast_unit, row.right);
        },
        inline .Return, .Break => |k| {
            const row = stmt_store.get(k, stmt_id);
            if (!row.value.isNone()) clearExprTypes(ast_unit, row.value.unwrap());
        },
        .Continue, .Unreachable => {},
    }
}

/// Clear type caches tied to declaration `decl_id`, including patterns and value.
fn clearDeclTypes(ast_unit: *ast.Ast, decl_id: ast.DeclId) void {
    if (decl_id.toRaw() < ast_unit.type_info.decl_types.items.len) {
        ast_unit.type_info.decl_types.items[decl_id.toRaw()] = null;
    }
    const decl = ast_unit.exprs.Decl.get(decl_id);
    if (!decl.pattern.isNone()) clearPatternTypes(ast_unit, decl.pattern.unwrap());
    if (!decl.ty.isNone()) clearExprTypes(ast_unit, decl.ty.unwrap());
    clearExprTypes(ast_unit, decl.value);
}

// --------- type helpers
/// Return true when `k` represents a numeric type (including tensors/complex).
pub fn isNumericKind(_: *const Checker, k: types.TypeKind) bool {
    return switch (k) {
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize, .Tensor, .Simd, .Complex => true,
        else => false,
    };
}
/// Return true when `k` is an integer kind (signed or unsigned).
pub fn isIntegerKind(_: *const Checker, k: types.TypeKind) bool {
    return switch (k) {
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => true,
        else => false,
    };
}

/// Return true when `k` is an unsigned integer kind.
pub fn isUnsignedInt(k: types.TypeKind) bool {
    return switch (k) {
        .U8, .U16, .U32, .U64, .Usize => true,
        else => false,
    };
}

/// Estimate alignment requirements for `ty_id` based on structural layout rules.
pub fn typeAlign(ctx: *const compile.Context, ty_id: types.TypeId) usize {
    return switch (ctx.type_store.getKind(ty_id)) {
        .Bool, .I8, .U8 => 1,
        .I16, .U16 => 2,
        .I32, .U32, .F32 => 4,
        .I64, .U64, .Usize, .F64, .Ptr, .MlirModule, .MlirAttribute, .MlirType, .Function, .Closure, .Code => 8,
        .Simd => blk: { // Assume natural vector alignment (at least 16) on 64-bit targets
            const elem_align = typeAlign(ctx, ctx.type_store.get(.Simd, ty_id).elem);
            break :blk if (elem_align < 16) 16 else elem_align;
        },
        .String, .Slice, .DynArray => 8, // Conservative defaults for aggregates (will be refined by element alignment)
        .Array => typeAlign(ctx, ctx.type_store.get(.Array, ty_id).elem),
        .Struct => blk: {
            const st = ctx.type_store.get(.Struct, ty_id);
            const fields = ctx.type_store.field_pool.slice(st.fields);
            var max_a: usize = 1;
            for (fields) |fid|
                max_a = @max(max_a, typeAlign(ctx, ctx.type_store.Field.get(fid).ty));
            break :blk max_a;
        },
        .Tuple => blk: {
            const tp = ctx.type_store.get(.Tuple, ty_id);
            const elems = ctx.type_store.type_pool.slice(tp.elems);
            var max_a: usize = 1;
            for (elems) |eid|
                max_a = @max(max_a, typeAlign(ctx, eid));
            break :blk max_a;
        },
        inline .Variant, .Error => |k| {
            const fields = ctx.type_store.field_pool.slice(ctx.type_store.get(k, ty_id).variants);
            var max_a: usize = 1;
            for (fields) |fid|
                max_a = @max(max_a, typeAlign(ctx, ctx.type_store.Field.get(fid).ty));
            // Struct layout: i32 tag (align 4), then payload (align max_a)
            return if (max_a > 4) max_a else 4;
        },
        .Union => blk: {
            const u = ctx.type_store.get(.Union, ty_id);
            const fields = ctx.type_store.field_pool.slice(u.fields);
            var max_a: usize = 1;
            for (fields) |fid|
                max_a = @max(max_a, typeAlign(ctx, ctx.type_store.Field.get(fid).ty));
            break :blk max_a;
        },
        .Optional => {
            const a = typeAlign(ctx, ctx.type_store.get(.Optional, ty_id).elem);
            return if (a > 1) a else 1;
        },
        else => 1,
    };
}

/// Return the size in bytes of `ty_id` using the target type store.
pub fn typeSize(ctx: *const compile.Context, ty_id: types.TypeId) usize {
    return switch (ctx.type_store.getKind(ty_id)) {
        .I8, .U8, .Bool => 1,
        .I16, .U16 => 2,
        .I32, .U32, .F32 => 4,
        .I64, .U64, .F64, .Usize => 8, // best-effort default for 64-bit targets
        .Ptr, .Code => 8, // best-effort default for 64-bit targets
        .MlirModule, .MlirAttribute, .MlirType => 8,
        .Closure => 16, // fn ptr + env ptr
        .Enum => typeSize(ctx, ctx.type_store.get(.Enum, ty_id).tag_type),
        .Simd => blk: {
            const simd = ctx.type_store.get(.Simd, ty_id);
            break :blk simd.lanes * typeSize(ctx, simd.elem);
        },
        .Void => 0,
        .Any => 0, // Size is not known
        .String => 16, // ptr + len on 64-bit targets
        .Slice => 16, // best-effort: ptr + len on 64-bit
        .DynArray => 24, // ptr + len + cap (3 * usize) on 64-bit
        .Array => ctx.type_store.get(.Array, ty_id).len * typeSize(ctx, ctx.type_store.get(.Array, ty_id).elem),
        .Struct => blk: {
            const st = ctx.type_store.get(.Struct, ty_id);
            const fields = ctx.type_store.field_pool.slice(st.fields);
            var offset: usize = 0;
            var max_a: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const sz = typeSize(ctx, f.ty);
                const a = typeAlign(ctx, f.ty);
                if (a > max_a) max_a = a;
                offset = std.mem.alignForward(usize, offset, a);
                offset += sz;
            }
            break :blk std.mem.alignForward(usize, offset, max_a);
        },
        .Tuple => blk: {
            const tp = ctx.type_store.get(.Tuple, ty_id);
            const elems = ctx.type_store.type_pool.slice(tp.elems);
            var total: usize = 0;
            for (elems) |eid| total += typeSize(ctx, eid);
            break :blk total;
        },
        inline .Variant, .Error => |k| blk: {
            // Runtime shape: struct { tag: i32, payload: union {...} }
            const fields = ctx.type_store.field_pool.slice(ctx.type_store.get(k, ty_id).variants);
            var max_payload: usize = 0;
            var max_align: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                max_payload = @max(max_payload, typeSize(ctx, f.ty));
                max_align = @max(max_align, typeAlign(ctx, f.ty));
            }
            const payload_sz = std.mem.alignForward(usize, max_payload, max_align);
            // tag is 4 bytes (i32). We pack payload immediately after tag.
            break :blk (4 + payload_sz);
        },
        .ErrorSet => blk: {
            const es = ctx.type_store.get(.ErrorSet, ty_id);
            const max_payload = @max(typeSize(ctx, es.error_ty), typeSize(ctx, es.value_ty));
            break :blk (4 + max_payload);
        },
        .Union => blk: {
            const u = ctx.type_store.get(.Union, ty_id);
            const fields = ctx.type_store.field_pool.slice(u.fields);
            var max_sz: usize = 0;
            var max_align: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                max_sz = @max(max_sz, typeSize(ctx, f.ty));
                max_align = @max(max_align, typeAlign(ctx, f.ty));
            }
            break :blk std.mem.alignForward(usize, max_sz, max_align);
        },
        .Optional => blk: {
            const o = ctx.type_store.get(.Optional, ty_id);
            const elem_sz = typeSize(ctx, o.elem);
            const elem_align = typeAlign(ctx, o.elem);
            // Runtime shape: struct { is_some: bool, payload } with natural alignment
            const after_flag = std.mem.alignForward(usize, 1, elem_align);
            const total = std.mem.alignForward(usize, after_flag + elem_sz, if (elem_align > 1) elem_align else 1);
            break :blk total;
        },
        .Function => 8,
        .TypeType => typeSize(ctx, ctx.type_store.get(.TypeType, ty_id).of),
        // Optional/Struct/Tuple/Union/Map/Error/Variant/ErrorSet/Simd/Tensor:
        // ABI/padding/representation are not modeled here yet.
        else => {
            std.debug.print("typeSize: unhandled kind {}\n", .{ctx.type_store.getKind(ty_id)});
            unreachable;
        },
    };
}

/// If `id` is an optional type, return its element type, else `null`.
pub fn isOptional(self: *Checker, id: types.TypeId) ?types.TypeId {
    if (self.context.type_store.getKind(id) != .Optional) return null;
    return self.context.type_store.get(.Optional, id).elem;
}

/// Resolve `typeof(expr)` expressions via the checker.
pub fn checkTypeOf(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const tr = ast_unit.exprs.get(.TypeOf, id);
    // typeof should accept value expressions; get their type directly.
    const et = try self.checkExpr(ctx, ast_unit, tr.expr);
    if (self.typeKind(et) != .TypeError)
        return self.context.type_store.mkTypeType(et);
    // As a fallback, allow typeof on a type expression (yielding that type).
    const res = try typeFromTypeExpr(self, ctx, ast_unit, tr.expr);
    if (res[0])
        return self.context.type_store.mkTypeType(res[1]);
    try self.context.diags.addError(ast_unit.exprs.locs.get(tr.loc), .could_not_resolve_type, .{});
    return self.context.type_store.tTypeError();
}

// =========================================================
// Type expressions
// =========================================================
/// Return the payload type for `tag` within variant type `variant_ty`.
fn variantPayloadType(self: *Checker, variant_ty: types.TypeId, tag: ast.StrId) ?types.TypeId {
    const vt = self.context.type_store.get(.Variant, variant_ty);
    const cases = self.context.type_store.field_pool.slice(vt.variants);
    var i: usize = 0;
    while (i < cases.len) : (i += 1) {
        const vc = self.context.type_store.Field.get(cases[i]);
        if (vc.name.eq(tag)) return vc.ty;
    }
    return null;
}

/// Evaluate literal expression `id` to a comptime integer value when possible.
fn evalLiteralToComptime(ast_unit: *ast.Ast, id: ast.ExprId) !?comp.ValueId {
    if (ast_unit.kind(id) != .Literal) return null;
    const lit = ast_unit.exprs.get(.Literal, id);
    const s = &ast_unit.type_info.val_store;
    return switch (lit.kind) {
        .int => blk: {
            const info = switch (lit.data) {
                .int => |i| i,
                else => return null,
            };
            if (!info.valid) return null;
            break :blk s.add(.Int, .{ .value = @as(i128, @intCast(info.value)) });
        },
        else => null,
    };
}

fn resolveTensorType(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    row: ast.Rows.TensorType,
    bindings: []const Binding,
) anyerror!struct { bool, types.TypeId } {
    const ts = self.context.type_store;
    var status = true;

    // Validate shape dimensions
    const dims = ast_unit.exprs.expr_pool.slice(row.shape);
    var dim_values = [_]usize{0} ** types.max_tensor_rank;
    var current_rank: usize = 0;

    for (dims) |dim_expr| {
        // Handle Range sugar (e.g. 0..N -> N)
        const expr_to_eval = if (ast_unit.kind(dim_expr) == .Range)
            ast_unit.exprs.get(.Range, dim_expr).end.unwrap()
        else
            dim_expr;

        // Optimization: Fast path for integer literals
        if (ast_unit.kind(expr_to_eval) == .Literal) {
            const lit = ast_unit.exprs.get(.Literal, expr_to_eval);
            if (lit.kind == .int and lit.data.int.valid) {
                if (current_rank < types.max_tensor_rank) {
                    dim_values[current_rank] = std.math.cast(usize, lit.data.int.value) orelse 0;
                    current_rank += 1;
                    continue;
                } else {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_rank_exceeds_limit, .{});
                    status = false;
                    continue;
                }
            }
        }

        // Optimization: Fast path for known bindings
        var value_resolved = false;
        var resolved_int: usize = 0;
        const s = &ast_unit.type_info.val_store;

        if (ast_unit.kind(expr_to_eval) == .Ident) {
            const name = ast_unit.exprs.get(.Ident, expr_to_eval).name;
            if (lookupValueBinding(bindings, name)) |val| {
                if (s.kind(val) == .Int) {
                    resolved_int = std.math.cast(usize, s.get(.Int, val).value) orelse 0;
                    value_resolved = true;
                }
            } else if (lookupTypeBinding(bindings, name)) |ty| {
                // Placeholder for generic params
                if (isIntegerKind(self, self.typeKind(ty))) {
                    resolved_int = 1;
                    value_resolved = true;
                }
            }
        }

        if (!value_resolved) {
            if (evalComptimeValueWithBindings(self, ctx, ast_unit, expr_to_eval, bindings)) |cv| {
                switch (s.kind(cv)) {
                    .Int => {
                        const v = s.get(.Int, cv).value;
                        resolved_int = std.math.cast(usize, v) orelse 0;
                        value_resolved = true;
                    },
                    .Sequence => {
                        const seq = s.get(.Sequence, cv);
                        // Handle tuple expansion for shapes
                        for (s.val_pool.slice(seq.elems)) |item| {
                            const item_val = if (s.kind(item) == .Int) std.math.cast(usize, s.get(.Int, item).value) orelse 0 else 0;
                            if (item_val == 0) {
                                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                                status = false;
                            }
                            if (current_rank < types.max_tensor_rank) {
                                dim_values[current_rank] = item_val;
                                current_rank += 1;
                            } else {
                                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_rank_exceeds_limit, .{});
                                status = false;
                            }
                        }
                        continue; // Skip standard insertion
                    },
                    else => {},
                }
            } else |_| {}
        }

        if (value_resolved) {
            if (current_rank < types.max_tensor_rank) {
                dim_values[current_rank] = resolved_int;
                current_rank += 1;
            } else {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_rank_exceeds_limit, .{});
                status = false;
            }
        } else {
            try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
            status = false;
        }
    }

    // Resolve element type
    const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.elem, bindings);
    if (self.typeKind(res[1]) == .TypeError) {
        try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_missing_element_type, .{});
    }

    return .{ status and res[0], ts.mkTensor(res[1], dim_values[0..current_rank]) };
}

/// When a call expression refers to a type-level function, try resolving its return type.
fn resolveTypeFunctionCall(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    call_id: ast.ExprId,
    existing_bindings: []const Binding,
) anyerror!?struct { bool, types.TypeId } {
    const call = ast_unit.exprs.get(.Call, call_id);
    if (ast_unit.kind(call.callee) != .Ident) return null;

    const callee_ident = ast_unit.exprs.get(.Ident, call.callee);
    const sym_id = self.lookup(ctx, callee_ident.name) orelse return null;
    const sym = ctx.symtab.syms.get(sym_id);
    if (sym.origin_decl.isNone()) return null;

    const decl_id = sym.origin_decl.unwrap();
    const decl = ast_unit.exprs.Decl.get(decl_id);
    if (ast_unit.kind(decl.value) != .FunctionLit) return null;

    const fn_lit = ast_unit.exprs.get(.FunctionLit, decl.value);
    if (fn_lit.body.isNone()) return null;

    const params = ast_unit.exprs.param_pool.slice(fn_lit.params);
    const args = ast_unit.exprs.expr_pool.slice(call.args);
    if (params.len != args.len) return null;

    // Determine Context
    var callee_ctx = ctx;
    if (ast_unit.file_id < self.checker_ctx.items.len) {
        if (self.checker_ctx.items[ast_unit.file_id]) |c| callee_ctx = c;
    }

    // Pre-allocate Bindings
    const total_cap = existing_bindings.len + params.len;
    var bindings_builder = try List(Binding).initCapacity(self.gpa, total_cap);
    defer bindings_builder.deinit(self.gpa);
    bindings_builder.appendSliceAssumeCapacity(existing_bindings);

    var interp_param_bindings = try List(interpreter.Binding).initCapacity(self.gpa, total_cap);
    defer {
        // value is ValueId, no destroy
        interp_param_bindings.deinit(self.gpa);
    }

    // Capture specialization state before modification
    const base_param_specs = callee_ctx.param_specializations.items.len;
    defer callee_ctx.param_specializations.items.len = base_param_specs;

    try self.ensureInterpreter(ast_unit, callee_ctx);
    var interp = &callee_ctx.interp.?;

    // Load existing bindings into interpreter and specializations
    for (existing_bindings) |b| {
        switch (b) {
            .Type => |t| {
                try callee_ctx.param_specializations.append(self.gpa, .{ .name = t.name, .ty = t.ty });
                try interp_param_bindings.append(self.gpa, .{ .name = t.name, .value = interp.store().add(.Type, .{ .ty = t.ty }), .store = interp.store() });
            },
            .Value => |v| {
                const cloned = try interp.store().cloneValue(&ast_unit.type_info.val_store, v.value);
                try interp_param_bindings.append(self.gpa, .{ .name = v.name, .value = cloned, .store = interp.store() });
            },
        }
    }

    var status = true;
    for (params, args) |pid, arg_expr| {
        const param = ast_unit.exprs.Param.get(pid);
        if (!param.is_comptime or param.pat.isNone() or param.ty.isNone()) return null;

        const pat_id = param.pat.unwrap();
        if (ast_unit.kind(pat_id) != .Binding) return null;
        const pname = ast_unit.pats.get(.Binding, pat_id).name;

        const res = try typeFromTypeExpr(self, callee_ctx, ast_unit, param.ty.unwrap());
        status = status and res[0];
        const annotated = res[1];

        // Dependent typing: slice of currently resolved bindings
        const current_bindings = bindings_builder.items;

        if (self.typeKind(annotated) == .TypeType) {
            const arg_res = try typeFromTypeExprWithBindings(self, callee_ctx, ast_unit, arg_expr, current_bindings);
            status = status and arg_res[0];

            bindings_builder.appendAssumeCapacity(.{ .Type = .{ .name = pname, .ty = arg_res[1] } });
            try callee_ctx.param_specializations.append(self.gpa, .{ .name = pname, .ty = arg_res[1] });
            try interp_param_bindings.append(self.gpa, .{ .name = pname, .value = interp.store().add(.Type, .{ .ty = arg_res[1] }), .store = interp.store() });
        } else {
            var value: comp.ValueId = undefined;
            var have_value = false;

            // Fast path: Ident lookup
            if (ast_unit.kind(arg_expr) == .Ident) {
                const ident_name = ast_unit.exprs.get(.Ident, arg_expr).name;
                if (lookupValueBinding(current_bindings, ident_name)) |existing| {
                    value = existing;
                    have_value = true;
                }
            }

            // Slow path: Eval
            if (!have_value) {
                if (evalComptimeValueWithBindings(self, ctx, ast_unit, arg_expr, current_bindings)) |v| {
                    value = v;
                    have_value = true;
                } else |_| {
                    if (ast_unit.kind(arg_expr) == .Literal) {
                        if (try evalLiteralToComptime(ast_unit, arg_expr)) |lv| {
                            value = lv;
                            have_value = true;
                        }
                    }
                }
            }

            if (!have_value) return null;

            bindings_builder.appendAssumeCapacity(.{ .Value = .{ .name = pname, .value = value, .ty = annotated } });
            try interp_param_bindings.append(self.gpa, .{ .name = pname, .value = try interp.store().cloneValue(&ast_unit.type_info.val_store, value), .store = interp.store() });
        }
    }

    // Setup Execution Scope
    const body_id = fn_lit.body.unwrap();
    if (ast_unit.kind(body_id) != .Block) return null;
    const stmts = ast_unit.stmts.stmt_pool.slice(ast_unit.exprs.get(.Block, body_id).items);

    _ = try callee_ctx.symtab.push(callee_ctx.symtab.currentId());
    defer callee_ctx.symtab.pop();

    for (params) |pid| {
        const p = ast_unit.exprs.Param.get(pid);
        const pname = ast_unit.pats.get(.Binding, p.pat.unwrap()).name;
        _ = try callee_ctx.symtab.declare(.{
            .name = pname,
            .kind = .Param,
            .is_comptime = true,
            .loc = p.loc,
            .origin_decl = .none(),
            .origin_param = .some(pid),
        });
    }

    var scope = try interp.pushBindings(&interp_param_bindings);
    defer scope.deinit();

    // Execute Body
    for (stmts) |sid| {
        switch (ast_unit.kind(sid)) {
            .Decl => {
                const row = ast_unit.stmts.get(.Decl, sid);
                clearDeclTypes(ast_unit, row.decl);
                try self.checkDecl(callee_ctx, ast_unit, row.decl);
            },
            .Return => {
                const ret = ast_unit.stmts.get(.Return, sid);
                if (ret.value.isNone()) return null;
                clearExprTypes(ast_unit, ret.value.unwrap());
                const res = try typeFromTypeExprWithBindings(self, callee_ctx, ast_unit, ret.value.unwrap(), bindings_builder.items);
                status = status and res[0];

                try ast_unit.type_info.ensureExpr(self.gpa, call_id);
                ast_unit.type_info.expr_types.items[call_id.toRaw()] = self.context.type_store.mkTypeType(res[1]);
                return .{ status, res[1] };
            },
            else => continue,
        }
    }

    return null;
}

/// Evaluate a type expression. This is a wrapper around `typeFromTypeExprWithBindings` with empty bindings.
pub fn typeFromTypeExpr(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) anyerror!struct { bool, types.TypeId } {
    return typeFromTypeExprWithBindings(self, ctx, ast_unit, id, &.{});
}

/// Resolve a type expression while providing `param_bindings` that shadow names during evaluation.
pub fn typeFromTypeExprWithBindings(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    id: ast.ExprId,
    bindings: []const Binding,
) anyerror!struct { bool, types.TypeId } {
    const ts = self.context.type_store;
    var status = true;

    // Ensure symbol table stack is initialized
    if (ctx.symtab.stack.items.len == 0) {
        _ = ctx.symtab.push(null) catch return .{ false, ts.tTypeError() };
    }

    return switch (ast_unit.kind(id)) {
        .Ident => blk_ident: {
            const ident = ast_unit.exprs.get(.Ident, id);
            const name = ident.name;

            // 1. Check Binding Shadowing
            if (lookupTypeBinding(bindings, name)) |ty| break :blk_ident .{ true, ty };

            // 2. Check Primitives (Optimized Lookup)
            const ident_name = ast_unit.exprs.strs.get(name);
            const PrimitiveTag = enum { bool, i8, i16, i32, i64, u8, u16, u32, u64, f32, f64, usize, char, string, void, any, err, type_type, code };
            const map = std.StaticStringMap(PrimitiveTag).initComptime(.{
                .{ "bool", .bool }, .{ "i8", .i8 },         .{ "i16", .i16 },
                .{ "i32", .i32 },   .{ "i64", .i64 },       .{ "u8", .u8 },
                .{ "u16", .u16 },   .{ "u32", .u32 },       .{ "u64", .u64 },
                .{ "f32", .f32 },   .{ "f64", .f64 },       .{ "usize", .usize },
                .{ "char", .char }, .{ "string", .string }, .{ "void", .void },
                .{ "any", .any },   .{ "Error", .err },     .{ "type", .type_type },
                .{ "Code", .code },
            });

            if (map.get(ident_name)) |tag| {
                const ty = switch (tag) {
                    .bool => ts.tBool(),
                    .i8 => ts.tI8(),
                    .i16 => ts.tI16(),
                    .i32 => ts.tI32(),
                    .i64 => ts.tI64(),
                    .u8 => ts.tU8(),
                    .u16 => ts.tU16(),
                    .u32 => ts.tU32(),
                    .u64 => ts.tU64(),
                    .f32 => ts.tF32(),
                    .f64 => ts.tF64(),
                    .usize => ts.tUsize(),
                    .char => ts.tU32(),
                    .string => ts.tString(),
                    .void => ts.tVoid(),
                    .any => ts.tAny(),
                    .err => ts.tTestError(),
                    .type_type => ts.mkTypeType(ts.tAny()),
                    .code => ts.tCode(),
                };
                break :blk_ident .{ true, ty };
            }

            // 3. Check Param Specialization
            if (self.lookupParamSpecialization(ctx, name)) |ty| {
                if (self.typeKind(ty) == .TypeType) return .{ status, ts.get(.TypeType, ty).of };
                return .{ status, ty };
            }

            // 4. Symbol Table Lookup
            if (self.lookup(ctx, name)) |sid| {
                const sym = ctx.symtab.syms.get(sid);

                // Handle Declaration
                if (!sym.origin_decl.isNone()) {
                    const did = sym.origin_decl.unwrap();
                    const raw_did = did.toRaw();

                    // Check if already resolved
                    if (ast_unit.type_info.decl_types.items[raw_did]) |ty| {
                        return .{ true, if (self.typeKind(ty) == .TypeType) ts.get(.TypeType, ty).of else ty };
                    }

                    // Recursion guard / Lazy resolution
                    if (ctx.resolving_type_decls.capacity() > raw_did and ctx.resolving_type_decls.isSet(raw_did)) {
                        return .{ true, ts.tAny() };
                    }
                    if (raw_did >= ctx.resolving_type_decls.capacity()) {
                        try ctx.resolving_type_decls.resize(self.gpa, raw_did + 1, false);
                    }
                    ctx.resolving_type_decls.set(raw_did);
                    defer ctx.resolving_type_decls.unset(raw_did);

                    const drow = ast_unit.exprs.Decl.get(did);
                    const rhs_res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, drow.value, bindings);
                    status = status and rhs_res[0];
                    const rhs_ty = rhs_res[1];

                    if (self.typeKind(rhs_ty) != .TypeError) {
                        const tt = ts.mkTypeType(rhs_ty);
                        ast_unit.type_info.decl_types.items[raw_did] = tt;
                        try ast_unit.type_info.ensureExpr(self.gpa, drow.value);
                        ast_unit.type_info.expr_types.items[drow.value.toRaw()] = tt;
                        return .{ status, rhs_ty };
                    } else {
                        if (status) try self.context.diags.addError(ast_unit.exprs.locs.get(ident.loc), .identifier_not_type, .{ident_name});
                        return .{ status, ts.tTypeError() };
                    }
                }

                // Handle Param
                if (!sym.origin_param.isNone()) {
                    const pid = sym.origin_param.unwrap();
                    const param_row = ast_unit.exprs.Param.get(pid);
                    if (!param_row.ty.isNone()) {
                        const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, param_row.ty.unwrap(), bindings);
                        const annotated = res[1];
                        if (param_row.is_comptime and self.typeKind(annotated) == .TypeType) {
                            return .{ status and res[0], ts.get(.TypeType, annotated).of };
                        }
                        return .{ status and res[0], annotated };
                    }
                    return .{ status, ts.tAny() };
                }
            }

            try self.context.diags.addError(ast_unit.exprs.locs.get(ident.loc), .undefined_identifier, .{ident_name});
            break :blk_ident .{ false, ts.tTypeError() };
        },
        .Splice => blk_splice: {
            const s = &ast_unit.type_info.val_store;
            if (ast_unit.type_info.getComptimeValue(id)) |cached| {
                if (s.kind(cached.*) == .Type) break :blk_splice .{ true, s.get(.Type, cached.*).ty };
            }
            const name = ast_unit.exprs.get(.Splice, id).name;
            if (ast_unit.type_info.comptime_bindings.get(name)) |e| {
                const val = e.value;
                try ast_unit.type_info.setComptimeValue(id, val);
                if (s.kind(val) == .Type) break :blk_splice .{ true, s.get(.Type, val).ty };
            }
            const row = ast_unit.exprs.get(.Splice, id);
            const name_str = ast_unit.exprs.strs.get(row.name);
            try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .code_splice_requires_type, .{name_str});
            break :blk_splice .{ false, ts.tTypeError() };
        },
        .TypeOf => blk_typeof: {
            const tr = ast_unit.exprs.get(.TypeOf, id);
            if (ast_unit.kind(tr.expr) == .Ident) {
                const name = ast_unit.exprs.get(.Ident, tr.expr).name;
                if (lookupTypeBinding(bindings, name)) |bound_ty| break :blk_typeof .{ status, bound_ty };
            }
            const typeof_ty = try checkTypeOf(self, ctx, ast_unit, id);
            const tk = self.typeKind(typeof_ty);
            if (tk == .TypeError) break :blk_typeof .{ false, typeof_ty };
            if (tk == .TypeType) break :blk_typeof .{ status, ts.get(.TypeType, typeof_ty).of };
            break :blk_typeof .{ status, typeof_ty };
        },
        .StructType => blk_struct: {
            const row = ast_unit.exprs.get(.StructType, id);
            const sfs = ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer ts.gpa.free(buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);

            for (sfs, 0..) |sf_idx, i| {
                const f = ast_unit.exprs.StructField.get(sf_idx);
                const gop = try seen.getOrPut(self.gpa, f.name.toRaw());
                if (gop.found_existing) {
                    const field_name = ast_unit.exprs.strs.get(f.name);
                    const first_loc = ast_unit.exprs.locs.get(gop.value_ptr.*);
                    const diag_idx = self.context.diags.count();
                    try self.context.diags.addError(ast_unit.exprs.locs.get(f.loc), .duplicate_field, .{field_name});
                    try self.context.diags.attachNote(diag_idx, first_loc, .first_defined_here);
                    status = false;
                } else {
                    gop.value_ptr.* = f.loc;
                }

                const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, f.ty, bindings);
                status = status and res[0];

                // Check default value assignment compatibility if present
                if (!f.value.isNone()) {
                    const val_ty = try self.checkExpr(ctx, ast_unit, f.value.unwrap());
                    if (self.typeKind(val_ty) != .TypeError and res[0]) {
                        if (self.assignable(val_ty, res[1]) != .success) {
                            try self.context.diags.addError(ast_unit.exprs.locs.get(f.loc), .type_annotation_mismatch, .{ res[1], val_ty });
                            status = false;
                        }
                    }
                }
                buf[i] = .{ .name = f.name, .ty = res[1] };
            }
            break :blk_struct .{ status, ts.mkStruct(buf, @as(u64, ast_unit.file_id) << 32 | id.toRaw()) };
        },
        .ArrayType => blk_at: {
            const row = ast_unit.exprs.get(.ArrayType, id);
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.elem, bindings);
            status = status and res[0];
            const elem = res[1];

            var size: usize = 0;
            const size_loc = ast_unit.exprs.locs.get(row.loc);

            if (evalComptimeValueWithBindings(self, ctx, ast_unit, row.size, bindings)) |v| {
                const s = &ast_unit.type_info.val_store;
                if (s.kind(v) == .Int) {
                    if (std.math.cast(usize, s.get(.Int, v).value)) |concrete| {
                        size = concrete;
                    } else {
                        try self.context.diags.addError(size_loc, .array_size_not_integer_literal, .{});
                        status = false;
                    }
                } else {
                    try self.context.diags.addError(size_loc, .array_size_not_integer_literal, .{});
                    status = false;
                }
            } else |_| {
                try self.context.diags.addError(size_loc, .array_size_not_integer_literal, .{});
                status = false;
            }
            break :blk_at .{ status, ts.mkArray(elem, size) };
        },
        .TensorType => blk_tensor: {
            const row = ast_unit.exprs.get(.TensorType, id);
            const res = try resolveTensorType(self, ctx, ast_unit, row, bindings);
            break :blk_tensor .{ status and res[0], res[1] };
        },
        .Call => blk_call: {
            const call_row = ast_unit.exprs.get(.Call, id);
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, call_row.callee, bindings);
            status = status and res[0];

            if (try resolveTypeFunctionCall(self, ctx, ast_unit, id, bindings)) |ty_res| {
                break :blk_call .{ status and ty_res[0], ty_res[1] };
            }

            const callee_kind = ast_unit.kind(call_row.callee);
            if (callee_kind == .FieldAccess or callee_kind == .Ident) {
                const value = evalComptimeValueWithBindings(self, ctx, ast_unit, id, bindings) catch |err| {
                    if (status) {
                        const msg = std.fmt.allocPrint(self.gpa, "comptime evaluation of type function failed: {s}", .{@errorName(err)}) catch "comptime evaluation failed";
                        try self.context.diags.addError(ast_unit.exprs.locs.get(call_row.loc), .could_not_resolve_type, .{@as([]const u8, msg)});
                    }
                    break :blk_call .{ false, ts.tTypeError() };
                };
                const s = &ast_unit.type_info.val_store;
                if (s.kind(value) == .Type) {
                    const wrapped = self.context.type_store.mkTypeType(s.get(.Type, value).ty);
                    try ast_unit.type_info.ensureExpr(self.gpa, id);
                    ast_unit.type_info.expr_types.items[id.toRaw()] = wrapped;
                    break :blk_call .{ status, s.get(.Type, value).ty };
                } else if (status) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(call_row.loc), .could_not_resolve_type, .{@as([]const u8, "expression evaluated to a value, but a type was expected")});
                    status = false;
                }
            } else if (status) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(call_row.loc), .could_not_resolve_type, .{@as([]const u8, "invalid type expression")});
            }
            break :blk_call .{ false, ts.tTypeError() };
        },
        .MlirBlock => blk_mlir: {
            const row = ast_unit.exprs.get(.MlirBlock, id);
            break :blk_mlir switch (row.kind) {
                .Type => .{ true, ts.mkTypeType(ts.mkMlirType(row.text)) },
                .Attribute => .{ true, ts.mkMlirAttribute(row.text) },
                .Module => .{ true, ts.tMlirModule() },
                .Operation => {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .mlir_block_not_a_type, .{});
                    return .{ false, ts.tTypeError() };
                },
            };
        },
        inline .TupleType, .TupleLit => |tag| blk_tuple: {
            const row = ast_unit.exprs.get(tag, id);
            const ids = ast_unit.exprs.expr_pool.slice(row.elems);
            var buf = try ts.gpa.alloc(types.TypeId, ids.len);
            defer ts.gpa.free(buf);
            for (ids, 0..) |eid, i| {
                const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, eid, bindings);
                status = status and res[0];
                buf[i] = res[1];
            }
            break :blk_tuple .{ status, ts.mkTuple(buf) };
        },
        .MapType => blk_mt: {
            const row = ast_unit.exprs.get(.MapType, id);
            const key_res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.key, bindings);
            const val_res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.value, bindings);
            break :blk_mt .{ status and key_res[0] and val_res[0], ts.mkMap(key_res[1], val_res[1]) };
        },
        .DynArrayType => blk_dt: {
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, ast_unit.exprs.get(.DynArrayType, id).elem, bindings);
            break :blk_dt .{ status and res[0], ts.mkDynArray(res[1]) };
        },
        .SliceType => blk_st: {
            const row = ast_unit.exprs.get(.SliceType, id);
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.elem, bindings);
            break :blk_st .{ status and res[0], ts.mkSlice(res[1], row.is_const) };
        },
        .OptionalType => blk_ot: {
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, ast_unit.exprs.get(.OptionalType, id).elem, bindings);
            break :blk_ot .{ status and res[0], ts.mkOptional(res[1]) };
        },
        .PointerType => blk_pt: {
            const row = ast_unit.exprs.get(.PointerType, id);
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.elem, bindings);
            break :blk_pt .{ status and res[0], ts.mkPtr(res[1], row.is_const) };
        },
        .ComplexType => blk_complex: {
            const row = ast_unit.exprs.get(.ComplexType, id);
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.elem, bindings);
            break :blk_complex .{ status and res[0], ts.mkComplex(res[1]) };
        },
        .SimdType => blk_simd: {
            const row = ast_unit.exprs.get(.SimdType, id);
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.elem, bindings);
            status = status and res[0];
            const elem_ty = res[1];

            if (!isNumericKind(self, self.typeKind(elem_ty))) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_invalid_element_type, .{});
                status = false;
            }

            var lanes_val: usize = 0;
            if (ast_unit.kind(row.lanes) == .Literal) {
                const lit = ast_unit.exprs.get(.Literal, row.lanes);
                if (lit.kind == .int and lit.data.int.valid) {
                    lanes_val = std.math.cast(usize, lit.data.int.value) orelse 0;
                }
            }
            if (lanes_val == 0 or lanes_val > std.math.maxInt(u16)) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                status = false;
            }
            break :blk_simd .{ status, ts.mkSimd(elem_ty, @intCast(lanes_val)) };
        },
        .UnionType => blk_un: {
            const row = ast_unit.exprs.get(.UnionType, id);
            const sfs = ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer ts.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);

            for (sfs, 0..) |sf_idx, i| {
                const sf = ast_unit.exprs.StructField.get(sf_idx);
                const gop = try seen.getOrPut(self.gpa, sf.name.toRaw());
                if (gop.found_existing) {
                    const field_name = ast_unit.exprs.strs.get(sf.name);
                    const diag_idx = self.context.diags.count();
                    try self.context.diags.addError(ast_unit.exprs.locs.get(sf.loc), .duplicate_field, .{field_name});
                    try self.context.diags.attachNote(diag_idx, ast_unit.exprs.locs.get(gop.value_ptr.*), .first_defined_here);
                    status = false;
                } else {
                    gop.value_ptr.* = sf.loc;
                }
                const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, sf.ty, bindings);
                status = status and res[0];
                if (!sf.value.isNone()) {
                    const val_ty = try self.checkExpr(ctx, ast_unit, sf.value.unwrap());
                    if (self.typeKind(val_ty) != .TypeError and res[0] and self.assignable(val_ty, res[1]) != .success) {
                        try self.context.diags.addError(ast_unit.exprs.locs.get(sf.loc), .type_annotation_mismatch, .{ res[1], val_ty });
                        status = false;
                    }
                }
                buf[i] = .{ .name = sf.name, .ty = res[1] };
            }
            break :blk_un .{ status, ts.mkUnion(buf) };
        },
        .EnumType => blk_en: {
            const row = ast_unit.exprs.get(.EnumType, id);
            const tag_res = if (row.discriminant.isNone()) .{ true, ts.tI32() } else try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.discriminant.unwrap(), bindings);
            status = status and tag_res[0];
            const tag_ty = tag_res[1];
            if (!isIntegerKind(self, self.typeKind(tag_ty))) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .enum_discriminant_not_integer, .{});
                status = false;
            }

            const efs = ast_unit.exprs.efield_pool.slice(row.fields);
            var member_buf = try self.gpa.alloc(types.TypeStore.EnumMemberArg, efs.len);
            defer self.gpa.free(member_buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);
            var enum_value_bindings: List(Binding) = .empty;
            defer enum_value_bindings.deinit(self.gpa);

            var next_value: i128 = 0;
            for (efs, 0..) |ef_idx, i| {
                const enum_field = ast_unit.exprs.EnumField.get(ef_idx);
                const gop = try seen.getOrPut(self.gpa, enum_field.name.toRaw());
                if (gop.found_existing) {
                    const tag_name = ast_unit.exprs.strs.get(enum_field.name);
                    const diag_idx = self.context.diags.count();
                    try self.context.diags.addError(ast_unit.exprs.locs.get(enum_field.loc), .duplicate_enum_field, .{tag_name});
                    try self.context.diags.attachNote(diag_idx, ast_unit.exprs.locs.get(gop.value_ptr.*), .first_defined_here);
                    status = false;
                } else {
                    gop.value_ptr.* = enum_field.loc;
                }

                var current_value: i128 = next_value;
                if (!enum_field.value.isNone()) {
                    const val_id = enum_field.value.unwrap();
                    var resolved = false;
                    const b_slice = enum_value_bindings.items;
                    const s = &ast_unit.type_info.val_store;
                    var val_result: ?comp.ValueId = null;

                    if (ast_unit.kind(val_id) == .Ident) {
                        const ident = ast_unit.exprs.get(.Ident, val_id);
                        if (lookupValueBinding(b_slice, ident.name)) |bv| val_result = bv;
                    }

                    if (val_result == null) {
                        val_result = evalComptimeValueWithBindings(self, ctx, ast_unit, val_id, b_slice) catch null;
                    }

                    if (val_result) |v| {
                        if (s.kind(v) == .Int) {
                            current_value = s.get(.Int, v).value;
                            resolved = true;
                        }
                    }

                    if (!resolved) {
                        try self.context.diags.addError(ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                        status = false;
                    }
                }
                member_buf[i] = .{ .name = enum_field.name, .value = @intCast(current_value) };
                const int_val = ast_unit.type_info.val_store.add(.Int, .{ .value = current_value });
                try enum_value_bindings.append(self.gpa, .{ .Value = .{ .name = enum_field.name, .value = int_val, .ty = tag_ty } });
                next_value = current_value + 1;
            }
            break :blk_en .{ status, ts.mkEnum(member_buf, tag_ty) };
        },
        .ErrorType => blk_err: {
            const row = ast_unit.exprs.get(.ErrorType, id);
            const vfs = ast_unit.exprs.vfield_pool.slice(row.fields);
            var case_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
            defer self.gpa.free(case_buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);

            for (vfs, 0..) |vf_idx, i| {
                const vf = ast_unit.exprs.VariantField.get(vf_idx);
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    const tag_name = ast_unit.exprs.strs.get(vf.name);
                    const diag_idx = self.context.diags.count();
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vf.loc), .duplicate_error_variant, .{tag_name});
                    try self.context.diags.attachNote(diag_idx, ast_unit.exprs.locs.get(gop.value_ptr.*), .first_defined_here);
                } else {
                    gop.value_ptr.* = vf.loc;
                }
                const payload_ty = switch (vf.payload_kind) {
                    .none => ts.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) break :blk_tuple ts.tVoid();
                        const elems = ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        for (elems, 0..) |e, j| {
                            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, e, bindings);
                            status = status and res[0];
                            elem_buf[j] = res[1];
                        }
                        break :blk_tuple ts.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) break :blk_struct ts.tVoid();
                        const fields = ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        for (fields, 0..) |f_idx, j| {
                            const sf = ast_unit.exprs.StructField.get(f_idx);
                            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, sf.ty, bindings);
                            status = status and res[0];
                            field_buf[j] = .{ .name = sf.name, .ty = res[1] };
                        }
                        break :blk_struct ts.mkStruct(field_buf, 0);
                    },
                };
                case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
            }
            break :blk_err .{ status, ts.mkError(case_buf) };
        },
        .ErrorSetType => blk_est: {
            const row = ast_unit.exprs.get(.ErrorSetType, id);
            const val_res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.value, bindings);
            const err_res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, row.err, bindings);
            break :blk_est .{ status and val_res[0] and err_res[0], ts.mkErrorSet(val_res[1], err_res[1]) };
        },
        .VariantType => blk_var: {
            const row = ast_unit.exprs.get(.VariantType, id);
            const vfs = ast_unit.exprs.vfield_pool.slice(row.fields);
            var case_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
            defer self.gpa.free(case_buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);

            for (vfs, 0..) |vf_idx, i| {
                const vf = ast_unit.exprs.VariantField.get(vf_idx);
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    const tag_name = ast_unit.exprs.strs.get(vf.name);
                    const diag_idx = self.context.diags.count();
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vf.loc), .duplicate_variant, .{tag_name});
                    try self.context.diags.attachNote(diag_idx, ast_unit.exprs.locs.get(gop.value_ptr.*), .first_defined_here);
                    status = false;
                } else {
                    gop.value_ptr.* = vf.loc;
                }
                const payload_ty = switch (vf.payload_kind) {
                    .none => ts.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) break :blk_tuple ts.tVoid();
                        const elems = ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        for (elems, 0..) |e, j| {
                            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, e, bindings);
                            status = status and res[0];
                            elem_buf[j] = res[1];
                        }
                        break :blk_tuple ts.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) break :blk_struct ts.tVoid();
                        const fields = ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        for (fields, 0..) |f_idx, j| {
                            const sf = ast_unit.exprs.StructField.get(f_idx);
                            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, sf.ty, bindings);
                            status = status and res[0];
                            field_buf[j] = .{ .name = sf.name, .ty = res[1] };
                        }
                        break :blk_struct ts.mkStruct(field_buf, 0);
                    },
                };
                case_buf[i] = .{ .name = vf.name, .ty = payload_ty };
            }
            break :blk_var .{ status, ts.mkVariant(case_buf) };
        },
        .FunctionLit => blk_fn: {
            const fnr = ast_unit.exprs.get(.FunctionLit, id);
            const params = ast_unit.exprs.param_pool.slice(fnr.params);
            var pbuf = try self.gpa.alloc(types.TypeId, params.len);
            defer self.gpa.free(pbuf);
            for (params, 0..) |pid, i| {
                const p = ast_unit.exprs.Param.get(pid);
                if (p.ty.isNone()) break :blk_fn .{ false, ts.tTypeError() };
                const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, p.ty.unwrap(), bindings);
                status = status and res[0];
                if (self.typeKind(res[1]) == .TypeError) return .{ false, ts.tTypeError() };
                pbuf[i] = res[1];
            }
            const res_res = if (!fnr.result_ty.isNone()) (try typeFromTypeExprWithBindings(self, ctx, ast_unit, fnr.result_ty.unwrap(), bindings)) else .{ true, ts.tVoid() };
            break :blk_fn .{ status and res_res[0], ts.mkFunction(pbuf, res_res[1], fnr.flags.is_variadic, !fnr.flags.is_proc, fnr.flags.is_extern) };
        },
        .FieldAccess => blk_fa: {
            const raw_id = id.toRaw();
            if (ctx.resolving_type_exprs.capacity() > raw_id and ctx.resolving_type_exprs.isSet(raw_id)) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(ast_unit.exprs.get(.FieldAccess, id).loc), .field_access_on_non_aggregate, .{});
                break :blk_fa .{ false, ts.tTypeError() };
            }
            if (raw_id >= ctx.resolving_type_exprs.capacity()) try ctx.resolving_type_exprs.resize(self.gpa, raw_id + 1, false);
            ctx.resolving_type_exprs.set(raw_id);
            defer ctx.resolving_type_exprs.unset(raw_id);

            const fr = ast_unit.exprs.get(.FieldAccess, id);
            const parent_res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, fr.parent, bindings);
            status = status and parent_res[0];
            const parent_ty = parent_res[1];

            break :blk_fa switch (self.typeKind(parent_ty)) {
                .Ast => blk_ast: {
                    const ast_ty = ts.get(.Ast, parent_ty);
                    const parent_unit = self.context.compilation_unit.findFileUnit(
                        self.context.interner.get(ast_ty.pkg_name),
                        self.context.interner.get(ast_ty.filepath),
                    ) orelse {
                        try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .import_not_found, .{});
                        break :blk_ast .{ false, ts.tTypeError() };
                    };
                    if (parent_unit.ast) |a| {
                        const target_sid = a.exprs.strs.intern(ast_unit.exprs.strs.get(fr.field));
                        if (if (self.checker_ctx.items[a.file_id]) |c| c.symtab.lookup(.fromRaw(0), target_sid) else null) |ex| {
                            const sym = self.checker_ctx.items[a.file_id].?.symtab.syms.get(ex);
                            const decl = sym.origin_decl.unwrap();
                            if (a.type_info.decl_types.items[decl.toRaw()] == null) {
                                try self.checkDecl(self.checker_ctx.items[a.file_id].?, a, decl);
                            }
                            if (a.type_info.decl_types.items[decl.toRaw()]) |resolved| {
                                const ty = if (self.typeKind(resolved) == .TypeType) ts.get(.TypeType, resolved).of else resolved;
                                break :blk_ast .{ status, ty };
                            }
                            break :blk_ast .{ false, ts.tTypeError() };
                        }
                    }
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_module_field, .{ast_unit.exprs.strs.get(fr.field)});
                    break :blk_ast .{ false, ts.tTypeError() };
                },
                .Struct => {
                    const st = ts.get(.Struct, parent_ty);
                    const fields = ts.field_pool.slice(st.fields);
                    for (fields) |f| if (ts.Field.get(f).name.eq(fr.field)) return .{ status, ts.Field.get(f).ty };
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
                .Variant => {
                    if (variantPayloadType(self, parent_ty, fr.field)) |pt| return .{ status, pt };
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_variant_tag, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
                .Enum => {
                    const et = ts.get(.Enum, parent_ty);
                    const members = ts.enum_member_pool.slice(et.members);
                    for (members) |m| if (ts.EnumMember.get(m).name.eq(fr.field)) return .{ status, parent_ty };
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
                else => {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .field_access_on_non_aggregate, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
            };
        },
        .Import => blk_import: {
            const ir = ast_unit.exprs.get(.Import, id);
            const filepath = ast_unit.exprs.strs.get(ir.path);
            for (self.context.compilation_unit.packages.values()) |pkg| {
                if (pkg.sources.get(filepath)) |_| {
                    break :blk_import .{ true, ts.mkAst(self.context.interner.intern(pkg.name), ir.path) };
                }
            }
            try self.context.diags.addError(ast_unit.exprs.locs.get(ir.loc), .import_not_found, .{});
            break :blk_import .{ false, ts.tTypeError() };
        },
        .AnyType => .{ true, ts.tAny() },
        .TypeType => .{ true, ts.tType() },
        .NoreturnType => .{ true, ts.tNoReturn() },
        else => .{ false, ts.tTypeError() },
    };
}
