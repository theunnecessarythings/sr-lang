const Checker = @import("checker.zig").Checker;
const types = @import("types.zig");
const ast = @import("ast.zig");
const std = @import("std");
const compile = @import("compile.zig");

const comp = @import("comptime.zig");
const PipelineBinding = @import("pipeline.zig").Pipeline.ComptimeBinding;
const Loc = @import("lexer.zig").Token.Loc;
const interpreter = @import("interpreter.zig");
const symbols = @import("symbols.zig");

/// Describes compile-time bindings introduced during type resolution (type/value).
pub const Binding = union(enum) {
    /// Type binding (name -> type id).
    Type: struct {
        /// Identifier bound to a type.
        name: ast.StrId,
        /// Assigned type for the identifier.
        ty: types.TypeId,
    },
    /// Value binding (name -> constant value + type).
    Value: struct {
        /// Identifier bound to a value.
        name: ast.StrId,
        /// Constant value assigned to the identifier.
        value: comp.ComptimeValue,
        /// Type describing the stored value.
        ty: types.TypeId,
    },
};

/// View into pipeline source bindings optionally owning the buffer.
const PipelineBindingSlice = struct {
    /// Array of pipeline bindings used to populate the interpreter.
    items: []PipelineBinding,
    /// Whether this slice owns the memory (needs freeing).
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
fn collectExprIds(gpa: std.mem.Allocator, ast_unit: *ast.Ast, expr_id: ast.ExprId, out: *std.ArrayList(ast.ExprId)) !void {
    try out.append(gpa, expr_id);
    const expr_store = &ast_unit.exprs;
    switch (ast_unit.kind(expr_id)) {
        .Literal, .Ident, .NullLit, .UndefLit, .AnyType, .TypeType, .NoreturnType => {},
        .Unary => try collectExprIds(gpa, ast_unit, expr_store.get(.Unary, expr_id).expr, out),
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
        .Deref => try collectExprIds(gpa, ast_unit, expr_store.get(.Deref, expr_id).expr, out),
        .ArrayLit => {
            const row = expr_store.get(.ArrayLit, expr_id);
            const elems = expr_store.expr_pool.slice(row.elems);
            for (elems) |elem| try collectExprIds(gpa, ast_unit, elem, out);
        },
        .TupleLit => {
            const row = expr_store.get(.TupleLit, expr_id);
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
        .Insert => try collectExprIds(gpa, ast_unit, expr_store.get(.Insert, expr_id).expr, out),
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
        .Continue => {},
        .Defer => try collectExprIds(gpa, ast_unit, expr_store.get(.Defer, expr_id).expr, out),
        .ErrDefer => try collectExprIds(gpa, ast_unit, expr_store.get(.ErrDefer, expr_id).expr, out),
        .ErrUnwrap => try collectExprIds(gpa, ast_unit, expr_store.get(.ErrUnwrap, expr_id).expr, out),
        .OptionalUnwrap => try collectExprIds(gpa, ast_unit, expr_store.get(.OptionalUnwrap, expr_id).expr, out),
        .Await => try collectExprIds(gpa, ast_unit, expr_store.get(.Await, expr_id).expr, out),
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
        .TypeOf => try collectExprIds(gpa, ast_unit, expr_store.get(.TypeOf, expr_id).expr, out),
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
        .SliceType => try collectExprIds(gpa, ast_unit, expr_store.get(.SliceType, expr_id).elem, out),
        .OptionalType => try collectExprIds(gpa, ast_unit, expr_store.get(.OptionalType, expr_id).elem, out),
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
        .VariantType => {
            const row = expr_store.get(.VariantType, expr_id);
            const fields = expr_store.vfield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.VariantField.get(fid);
                if (!field.value.isNone()) try collectExprIds(gpa, ast_unit, field.value.unwrap(), out);
            }
        },
        .ErrorType => {
            const row = expr_store.get(.ErrorType, expr_id);
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
        .PointerType => try collectExprIds(gpa, ast_unit, expr_store.get(.PointerType, expr_id).elem, out),
        .SimdType => {
            const row = expr_store.get(.SimdType, expr_id);
            try collectExprIds(gpa, ast_unit, row.elem, out);
            try collectExprIds(gpa, ast_unit, row.lanes, out);
        },
        .ComplexType => try collectExprIds(gpa, ast_unit, expr_store.get(.ComplexType, expr_id).elem, out),
        .TensorType => {
            const row = expr_store.get(.TensorType, expr_id);
            try collectExprIds(gpa, ast_unit, row.elem, out);
            const shape = expr_store.expr_pool.slice(row.shape);
            for (shape) |dim| try collectExprIds(gpa, ast_unit, dim, out);
        },
        else => {},
    }
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
        .Literal => {
            const row = pats.get(.Literal, pid);
            try callOnExpr(ctx, ast_unit, row.expr);
        },
        .Binding => {
            const row = pats.get(.Binding, pid);
            try callOnBinding(ctx, ast_unit, pid, row.name, value_ty);
        },
        .Tuple => {
            const row = pats.get(.Tuple, pid);
            const elems = pats.pat_pool.slice(row.elems);
            for (elems, 0..) |elem, index| {
                try walkChild(ctx, ast_unit, pid, value_ty, elem, .{ .TupleElem = index });
            }
        },
        .Slice => {
            const row = pats.get(.Slice, pid);
            const elems = pats.pat_pool.slice(row.elems);
            for (elems, 0..) |elem, index| {
                try walkChild(ctx, ast_unit, pid, value_ty, elem, .{ .SliceElem = index });
            }
            if (!row.rest_binding.isNone()) {
                try walkChild(
                    ctx,
                    ast_unit,
                    pid,
                    value_ty,
                    row.rest_binding.unwrap(),
                    .SliceRest,
                );
            }
        },
        .Struct => {
            const row = pats.get(.Struct, pid);
            const fields = pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const field = pats.StructField.get(fid);
                try walkChild(ctx, ast_unit, pid, value_ty, field.pattern, .{ .StructField = field.name });
            }
        },
        .VariantTuple => {
            const row = pats.get(.VariantTuple, pid);
            const elems = pats.pat_pool.slice(row.elems);
            const case_name = patternCaseName(ast_unit, row.path) orelse ast.StrId.fromRaw(0);
            for (elems, 0..) |elem, index| {
                try walkChild(
                    ctx,
                    ast_unit,
                    pid,
                    value_ty,
                    elem,
                    .{ .VariantTupleElem = .{ .case_name = case_name, .index = index } },
                );
            }
        },
        .VariantStruct => {
            const row = pats.get(.VariantStruct, pid);
            const fields = pats.field_pool.slice(row.fields);
            const case_name = patternCaseName(ast_unit, row.path) orelse ast.StrId.fromRaw(0);
            for (fields) |fid| {
                const field = pats.StructField.get(fid);
                try walkChild(
                    ctx,
                    ast_unit,
                    pid,
                    value_ty,
                    field.pattern,
                    .{ .VariantStructField = .{ .case_name = case_name, .field_name = field.name } },
                );
            }
        },
        .Range => {
            const row = pats.get(.Range, pid);
            if (!row.start.isNone()) try callOnExpr(ctx, ast_unit, row.start.unwrap());
            if (!row.end.isNone()) try callOnExpr(ctx, ast_unit, row.end.unwrap());
        },
        .Or => {
            const row = pats.get(.Or, pid);
            const alts = pats.pat_pool.slice(row.alts);
            for (alts, 0..) |alt, index| {
                try walkChild(ctx, ast_unit, pid, value_ty, alt, .{ .OrAlt = index });
            }
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
    out: *std.ArrayList(ast.ExprId),
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
    out: *std.ArrayList(ast.ExprId),
};

fn patternExprOnExpr(ctx: *void, ast_unit: *ast.Ast, expr: ast.ExprId) anyerror!void {
    _ = ast_unit;
    const collector: *PatternExprCollector = @ptrCast(@alignCast(ctx));
    try collector.out.append(collector.gpa, expr);
    return;
}

/// Collect expression ids touched by statement `stmt_id`.
fn collectStmtExprs(
    gpa: std.mem.Allocator,
    ast_unit: *ast.Ast,
    stmt_id: ast.StmtId,
    out: *std.ArrayList(ast.ExprId),
) anyerror!void {
    const stmt_store = &ast_unit.stmts;
    switch (ast_unit.kind(stmt_id)) {
        .Expr => try collectExprIds(gpa, ast_unit, stmt_store.get(.Expr, stmt_id).expr, out),
        .Decl => {
            const row = stmt_store.get(.Decl, stmt_id);
            try collectDeclExprs(gpa, ast_unit, row.decl, out);
        },
        .Assign => {
            const row = stmt_store.get(.Assign, stmt_id);
            try collectExprIds(gpa, ast_unit, row.left, out);
            try collectExprIds(gpa, ast_unit, row.right, out);
        },
        .Insert => try collectExprIds(gpa, ast_unit, stmt_store.get(.Insert, stmt_id).expr, out),
        .Return => {
            const row = stmt_store.get(.Return, stmt_id);
            if (!row.value.isNone()) try collectExprIds(gpa, ast_unit, row.value.unwrap(), out);
        },
        .Break => {
            const row = stmt_store.get(.Break, stmt_id);
            if (!row.value.isNone()) try collectExprIds(gpa, ast_unit, row.value.unwrap(), out);
        },
        .Continue => {},
        .Unreachable => {},
        .Defer => try collectExprIds(gpa, ast_unit, stmt_store.get(.Defer, stmt_id).expr, out),
        .ErrDefer => try collectExprIds(gpa, ast_unit, stmt_store.get(.ErrDefer, stmt_id).expr, out),
    }
}

/// Collect expressions from declaration `decl_id`, including patterns, annotations, and initializer.
pub fn collectDeclExprs(gpa: std.mem.Allocator, ast_unit: *ast.Ast, decl_id: ast.DeclId, out: *std.ArrayList(ast.ExprId)) !void {
    const decl = ast_unit.exprs.Decl.get(decl_id);
    if (!decl.pattern.isNone()) try collectPatternExprs(gpa, ast_unit, decl.pattern.unwrap(), out);
    if (!decl.ty.isNone()) try collectExprIds(gpa, ast_unit, decl.ty.unwrap(), out);
    try collectExprIds(gpa, ast_unit, decl.value, out);
}

/// Snapshot the expression types for `fn_expr` so later specializations can reuse them.
/// Record the expression types for a method so future lookups can reuse them.
pub fn storeMethodExprTypes(
    self: *Checker,
    ast_unit: *ast.Ast,
    owner_ty: types.TypeId,
    method_name: ast.StrId,
    fn_expr: ast.ExprId,
) !void {
    var expr_ids = try self.acquireExprIdsScratch();
    defer self.releaseExprIdsScratch();
    try collectExprIds(self.gpa, ast_unit, fn_expr, expr_ids);
    if (expr_ids.items.len == 0) return;

    const expr_types = ast_unit.type_info.expr_types.items;
    var needed: usize = 0;
    for (expr_ids.items[0..expr_ids.items.len]) |eid| {
        const raw = eid.toRaw();
        if (raw >= expr_types.len) continue;
        if (expr_types[raw]) |_| {
            needed += 1;
        }
    }
    if (needed == 0) return;

    var raw_ids = try self.gpa.alloc(u32, needed);
    defer self.gpa.free(raw_ids);
    var type_buf = try self.gpa.alloc(types.TypeId, needed);
    defer self.gpa.free(type_buf);

    var filled: usize = 0;
    for (expr_ids.items[0..expr_ids.items.len]) |eid| {
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

/// Snapshot the expression types for `decl_id` when emitting a specialized clone.
pub fn storeSpecializationExprTypes(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_ids: []const ast.ExprId,
    specialization_decl_id: ast.DeclId,
) !void {
    if (expr_ids.len == 0) return;

    const expr_types = ast_unit.type_info.expr_types.items;
    var needed: usize = 0;
    for (expr_ids) |eid| {
        const raw = eid.toRaw();
        if (raw >= expr_types.len) continue;
        if (expr_types[raw]) |_| {
            needed += 1;
        }
    }
    if (needed == 0) return;

    var raw_ids = try self.gpa.alloc(u32, needed);
    defer self.gpa.free(raw_ids);
    var type_buf = try self.gpa.alloc(types.TypeId, needed);
    defer self.gpa.free(type_buf);

    var filled: usize = 0;
    for (expr_ids) |eid| {
        const raw = eid.toRaw();
        if (raw >= expr_types.len) continue;
        if (expr_types[raw]) |ty| {
            raw_ids[filled] = raw;
            type_buf[filled] = ty;
            filled += 1;
        }
    }
    std.debug.assert(filled == needed);
    try ast_unit.type_info.storeSpecializationExprSnapshot(specialization_decl_id, raw_ids[0..filled], type_buf[0..filled]);
}

/// Convert `bindings` into a pipeline binding slice suitable for `evalComptimeExpr`.
fn pipelineBindingsFor(self: *Checker, bindings: []const Binding) !PipelineBindingSlice {
    if (bindings.len == 0) return .{ .items = &[_]PipelineBinding{}, .owns = false };

    var out = try self.gpa.alloc(PipelineBinding, bindings.len);
    var i: usize = 0;
    while (i < bindings.len) : (i += 1) {
        const b = bindings[i];
        out[i] = switch (b) {
            .Type => |t| .{ .type_param = .{ .name = t.name, .ty = t.ty } },
            .Value => |v| .{ .value_param = .{ .name = v.name, .ty = v.ty, .value = v.value } },
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
) !comp.ComptimeValue {
    const pb = try pipelineBindingsFor(self, bindings);
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
fn lookupValueBinding(bindings: []const Binding, name: ast.StrId) ?comp.ComptimeValue {
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
        .Literal => {
            const row = pats.get(.Literal, pat_id);
            clearExprTypes(ast_unit, row.expr);
        },
        .Range => {
            const row = pats.get(.Range, pat_id);
            if (!row.start.isNone()) clearExprTypes(ast_unit, row.start.unwrap());
            if (!row.end.isNone()) clearExprTypes(ast_unit, row.end.unwrap());
        },
        .Tuple => {
            const row = pats.get(.Tuple, pat_id);
            const elems = pats.pat_pool.slice(row.elems);
            for (elems) |elem| clearPatternTypes(ast_unit, elem);
        },
        .Slice => {
            const row = pats.get(.Slice, pat_id);
            const elems = pats.pat_pool.slice(row.elems);
            for (elems) |elem| clearPatternTypes(ast_unit, elem);
            if (!row.rest_binding.isNone()) clearPatternTypes(ast_unit, row.rest_binding.unwrap());
        },
        .Struct => {
            const row = pats.get(.Struct, pat_id);
            const fields = pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const field = pats.StructField.get(fid);
                clearPatternTypes(ast_unit, field.pattern);
            }
        },
        .VariantStruct => {
            const row = pats.get(.VariantStruct, pat_id);
            const fields = pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const field = pats.StructField.get(fid);
                clearPatternTypes(ast_unit, field.pattern);
            }
        },
        .VariantTuple => {
            const row = pats.get(.VariantTuple, pat_id);
            const elems = pats.pat_pool.slice(row.elems);
            for (elems) |elem| clearPatternTypes(ast_unit, elem);
        },
        .Or => {
            const row = pats.get(.Or, pat_id);
            const alts = pats.pat_pool.slice(row.alts);
            for (alts) |alt| clearPatternTypes(ast_unit, alt);
        },
        .At => {
            const row = pats.get(.At, pat_id);
            clearPatternTypes(ast_unit, row.pattern);
        },
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
        .Literal, .Ident, .NullLit, .UndefLit, .AnyType, .TypeType, .NoreturnType => {},
        .Unary => {
            const row = expr_store.get(.Unary, expr_id);
            clearExprTypes(ast_unit, row.expr);
        },
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
        .Deref => clearExprTypes(ast_unit, expr_store.get(.Deref, expr_id).expr),
        .ArrayLit => {
            const row = expr_store.get(.ArrayLit, expr_id);
            const elems = expr_store.expr_pool.slice(row.elems);
            for (elems) |elem| clearExprTypes(ast_unit, elem);
        },
        .TupleLit => {
            const row = expr_store.get(.TupleLit, expr_id);
            const elems = expr_store.expr_pool.slice(row.elems);
            for (elems) |elem| clearExprTypes(ast_unit, elem);
        },
        .MapLit => {
            const row = expr_store.get(.MapLit, expr_id);
            const entries = expr_store.kv_pool.slice(row.entries);
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
            for (fields) |fid| {
                const field = expr_store.StructFieldValue.get(fid);
                clearExprTypes(ast_unit, field.value);
            }
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
            const row = expr_store.get(.Block, expr_id);
            const stmts = ast_unit.stmts.stmt_pool.slice(row.items);
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
        .Insert => clearExprTypes(ast_unit, expr_store.get(.Insert, expr_id).expr),
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
        .Continue => {},
        .Defer => clearExprTypes(ast_unit, expr_store.get(.Defer, expr_id).expr),
        .ErrDefer => clearExprTypes(ast_unit, expr_store.get(.ErrDefer, expr_id).expr),
        .ErrUnwrap => clearExprTypes(ast_unit, expr_store.get(.ErrUnwrap, expr_id).expr),
        .OptionalUnwrap => clearExprTypes(ast_unit, expr_store.get(.OptionalUnwrap, expr_id).expr),
        .Await => clearExprTypes(ast_unit, expr_store.get(.Await, expr_id).expr),
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
        .TypeOf => clearExprTypes(ast_unit, expr_store.get(.TypeOf, expr_id).expr),
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
        .DynArrayType => clearExprTypes(ast_unit, expr_store.get(.DynArrayType, expr_id).elem),
        .MapType => {
            const row = expr_store.get(.MapType, expr_id);
            clearExprTypes(ast_unit, row.key);
            clearExprTypes(ast_unit, row.value);
        },
        .SliceType => clearExprTypes(ast_unit, expr_store.get(.SliceType, expr_id).elem),
        .OptionalType => clearExprTypes(ast_unit, expr_store.get(.OptionalType, expr_id).elem),
        .ErrorSetType => {
            const row = expr_store.get(.ErrorSetType, expr_id);
            clearExprTypes(ast_unit, row.err);
            clearExprTypes(ast_unit, row.value);
        },
        .StructType => {
            const row = expr_store.get(.StructType, expr_id);
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
        .VariantType => {
            const row = expr_store.get(.VariantType, expr_id);
            const fields = expr_store.vfield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.VariantField.get(fid);
                if (!field.value.isNone()) clearExprTypes(ast_unit, field.value.unwrap());
            }
        },
        .ErrorType => {
            const row = expr_store.get(.ErrorType, expr_id);
            const fields = expr_store.vfield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.VariantField.get(fid);
                if (!field.value.isNone()) clearExprTypes(ast_unit, field.value.unwrap());
            }
        },
        .UnionType => {
            const row = expr_store.get(.UnionType, expr_id);
            const fields = expr_store.sfield_pool.slice(row.fields);
            for (fields) |fid| {
                const field = expr_store.StructField.get(fid);
                clearExprTypes(ast_unit, field.ty);
                if (!field.value.isNone()) clearExprTypes(ast_unit, field.value.unwrap());
            }
        },
        .PointerType => clearExprTypes(ast_unit, expr_store.get(.PointerType, expr_id).elem),
        .SimdType => {
            const row = expr_store.get(.SimdType, expr_id);
            clearExprTypes(ast_unit, row.elem);
            clearExprTypes(ast_unit, row.lanes);
        },
        .ComplexType => clearExprTypes(ast_unit, expr_store.get(.ComplexType, expr_id).elem),
        .TensorType => {
            const row = expr_store.get(.TensorType, expr_id);
            clearExprTypes(ast_unit, row.elem);
            const shape = expr_store.expr_pool.slice(row.shape);
            for (shape) |dim| clearExprTypes(ast_unit, dim);
        },
        else => {},
    }
}

/// Reset expression type caches referenced by statement `stmt_id`.
fn clearStmtTypes(ast_unit: *ast.Ast, stmt_id: ast.StmtId) void {
    const stmt_store = &ast_unit.stmts;
    switch (ast_unit.kind(stmt_id)) {
        .Expr => clearExprTypes(ast_unit, stmt_store.get(.Expr, stmt_id).expr),
        .Decl => clearDeclTypes(ast_unit, stmt_store.get(.Decl, stmt_id).decl),
        .Assign => {
            const row = stmt_store.get(.Assign, stmt_id);
            clearExprTypes(ast_unit, row.left);
            clearExprTypes(ast_unit, row.right);
        },
        .Insert => clearExprTypes(ast_unit, stmt_store.get(.Insert, stmt_id).expr),
        .Return => {
            const row = stmt_store.get(.Return, stmt_id);
            if (!row.value.isNone()) clearExprTypes(ast_unit, row.value.unwrap());
        },
        .Break => {
            const row = stmt_store.get(.Break, stmt_id);
            if (!row.value.isNone()) clearExprTypes(ast_unit, row.value.unwrap());
        },
        .Continue => {},
        .Unreachable => {},
        .Defer => clearExprTypes(ast_unit, stmt_store.get(.Defer, stmt_id).expr),
        .ErrDefer => clearExprTypes(ast_unit, stmt_store.get(.ErrDefer, stmt_id).expr),
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

/// Estimate alignment requirements for `ty_id` based on structural layout rules.
pub fn typeAlign(ctx: *const compile.Context, ty_id: types.TypeId) usize {
    return switch (ctx.type_store.getKind(ty_id)) {
        .Bool, .I8, .U8 => 1,
        .I16, .U16 => 2,
        .I32, .U32, .F32 => 4,
        .I64, .U64, .Usize, .F64, .Ptr, .MlirModule, .MlirAttribute, .MlirType, .Function => 8,
        .Simd => blk: {
            // Assume natural vector alignment (at least 16) on 64-bit targets
            const elem_align = typeAlign(ctx, ctx.type_store.get(.Simd, ty_id).elem);
            break :blk if (elem_align < 16) 16 else elem_align;
        },
        // Conservative defaults for aggregates (will be refined by element alignment)
        .String, .Slice, .DynArray => 8,
        .Array => typeAlign(ctx, ctx.type_store.get(.Array, ty_id).elem),
        .Struct => blk_s: {
            const st = ctx.type_store.get(.Struct, ty_id);
            const fields = ctx.type_store.field_pool.slice(st.fields);
            var max_a: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const a = typeAlign(ctx, f.ty);
                if (a > max_a) max_a = a;
            }
            break :blk_s max_a;
        },
        .Tuple => blk_t: {
            const tp = ctx.type_store.get(.Tuple, ty_id);
            const elems = ctx.type_store.type_pool.slice(tp.elems);
            var max_a: usize = 1;
            for (elems) |eid| {
                const a = typeAlign(ctx, eid);
                if (a > max_a) max_a = a;
            }
            break :blk_t max_a;
        },
        .Variant, .Error => {
            const fields = if (ctx.type_store.getKind(ty_id) == .Variant)
                ctx.type_store.field_pool.slice(ctx.type_store.get(.Variant, ty_id).variants)
            else
                ctx.type_store.field_pool.slice(ctx.type_store.get(.Error, ty_id).variants);
            var max_a: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const a = typeAlign(ctx, f.ty);
                if (a > max_a) max_a = a;
            }
            // Struct layout: i32 tag (align 4), then payload (align max_a)
            return if (max_a > 4) max_a else 4;
        },
        .Union => blk_u: {
            const u = ctx.type_store.get(.Union, ty_id);
            const fields = ctx.type_store.field_pool.slice(u.fields);
            var max_a: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const a = typeAlign(ctx, f.ty);
                if (a > max_a) max_a = a;
            }
            break :blk_u max_a;
        },
        .Optional => {
            const o = ctx.type_store.get(.Optional, ty_id);
            const a = typeAlign(ctx, o.elem);
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
        .Ptr => 8, // best-effort default for 64-bit targets
        .MlirModule, .MlirAttribute, .MlirType => 8,
        // Enums lower to their tag type; assume 32-bit by default via tag_type
        .Enum => blk_enum: {
            const en = ctx.type_store.get(.Enum, ty_id);
            break :blk_enum typeSize(ctx, en.tag_type);
        },
        .Simd => blk_simd: {
            const simd = ctx.type_store.get(.Simd, ty_id);
            const elem_size = typeSize(ctx, simd.elem);
            break :blk_simd std.math.mul(usize, elem_size, @as(usize, simd.lanes)) catch unreachable;
        },
        .Void => 0,
        .Any => 0, // Size is not known
        .String => 16, // ptr + len on 64-bit targets
        .Slice => 16, // best-effort: ptr + len on 64-bit
        .DynArray => 24, // ptr + len + cap (3 * usize) on 64-bit
        .Array => blk: {
            const arr = ctx.type_store.get(.Array, ty_id);
            const elem_size = typeSize(ctx, arr.elem);
            break :blk std.math.mul(usize, elem_size, arr.len) catch unreachable;
        },
        .Struct => blk: {
            const st = ctx.type_store.get(.Struct, ty_id);
            const fields = ctx.type_store.field_pool.slice(st.fields);
            var offset: usize = 0;
            var max_a: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const a = typeAlign(ctx, f.ty);
                const sz = typeSize(ctx, f.ty);
                if (a > max_a) max_a = a;
                offset = std.mem.alignForward(usize, offset, a);
                offset = std.math.add(usize, offset, sz) catch unreachable;
            }
            const total = std.mem.alignForward(usize, offset, max_a);
            break :blk total;
        },
        .Tuple => blk_tup: {
            const tp = ctx.type_store.get(.Tuple, ty_id);
            const elems = ctx.type_store.type_pool.slice(tp.elems);
            var total: usize = 0;
            for (elems) |eid| {
                const esz = typeSize(ctx, eid);
                total = std.math.add(usize, total, esz) catch unreachable;
            }
            break :blk_tup total;
        },
        .Variant, .Error => blk_var: {
            // Runtime shape: struct { tag: i32, payload: union {...} }
            const fields = if (ctx.type_store.getKind(ty_id) == .Variant)
                ctx.type_store.field_pool.slice(ctx.type_store.get(.Variant, ty_id).variants)
            else
                ctx.type_store.field_pool.slice(ctx.type_store.get(.Error, ty_id).variants);
            var max_payload: usize = 0;
            var max_align: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const sz = typeSize(ctx, f.ty);
                if (sz > max_payload) max_payload = sz;
                const a = typeAlign(ctx, f.ty);
                if (a > max_align) max_align = a;
            }
            const payload_sz = std.mem.alignForward(usize, max_payload, max_align);
            // tag is 4 bytes (i32). We pack payload immediately after tag.
            break :blk_var (4 + payload_sz);
        },
        .ErrorSet => blk_es: {
            const es = ctx.type_store.get(.ErrorSet, ty_id);
            const v_sz = typeSize(ctx, es.value_ty);
            const e_sz = typeSize(ctx, es.error_ty);
            const max_payload = if (v_sz > e_sz) v_sz else e_sz;
            break :blk_es (4 + max_payload);
        },
        .Union => blk_union: {
            const u = ctx.type_store.get(.Union, ty_id);
            const fields = ctx.type_store.field_pool.slice(u.fields);
            var max_sz: usize = 0;
            var max_align: usize = 1;
            for (fields) |fid| {
                const f = ctx.type_store.Field.get(fid);
                const sz = typeSize(ctx, f.ty);
                if (sz > max_sz) max_sz = sz;
                const a = typeAlign(ctx, f.ty);
                if (a > max_align) max_align = a;
            }
            break :blk_union std.mem.alignForward(usize, max_sz, max_align);
        },
        .Optional => blk_opt: {
            const o = ctx.type_store.get(.Optional, ty_id);
            const elem_sz = typeSize(ctx, o.elem);
            const elem_align = typeAlign(ctx, o.elem);
            // Runtime shape: struct { is_some: bool, payload } with natural alignment
            const after_flag = std.mem.alignForward(usize, 1, elem_align);
            const total = std.mem.alignForward(usize, after_flag + elem_sz, if (elem_align > 1) elem_align else 1);
            break :blk_opt total;
        },
        .Function => 8,
        .TypeType => blk: {
            const tt = ctx.type_store.get(.TypeType, ty_id);
            break :blk typeSize(ctx, tt.of);
        },
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
    if (self.typeKind(et) != .TypeError) {
        return self.context.type_store.mkTypeType(et);
    }
    // As a fallback, allow typeof on a type expression (yielding that type).
    const res = try typeFromTypeExpr(self, ctx, ast_unit, tr.expr);
    if (res[0]) {
        return self.context.type_store.mkTypeType(res[1]);
    }
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
fn evalLiteralToComptime(ast_unit: *ast.Ast, id: ast.ExprId) !?comp.ComptimeValue {
    if (ast_unit.kind(id) != .Literal) return null;
    const lit = ast_unit.exprs.get(.Literal, id);
    return switch (lit.kind) {
        .int => blk: {
            const info = switch (lit.data) {
                .int => |i| i,
                else => return null,
            };
            if (!info.valid) return null;
            break :blk comp.ComptimeValue{ .Int = @as(i128, @intCast(info.value)) };
        },
        else => null,
    };
}

/// Resolve a type expression while providing `bindings` that shadow names during evaluation.
pub fn typeFromTypeExprWithBindings(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    id: ast.ExprId,
    bindings: []const Binding,
) anyerror!struct { bool, types.TypeId } {
    const ts = self.context.type_store;
    var status = true;
    return switch (ast_unit.kind(id)) {
        .Ident => blk_ident: {
            const name = ast_unit.exprs.get(.Ident, id).name;
            if (lookupTypeBinding(bindings, name)) |ty|
                break :blk_ident .{ status, ty };
            break :blk_ident try typeFromTypeExpr(self, ctx, ast_unit, id);
        },
        .StructType => blk_struct: {
            const row = ast_unit.exprs.get(.StructType, id);
            const sfs = ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer ts.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const f = ast_unit.exprs.StructField.get(sfs[i]);
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
            var size_eval = evalComptimeValueWithBindings(self, ctx, ast_unit, row.size, bindings) catch {
                // If interpreter is unavailable (e.g. synthetic specialization), fall back to TypeError and surface a diagnostic.
                try self.context.diags.addError(size_loc, .array_size_not_integer_literal, .{});
                status = false;
                break :blk_at .{ status, ts.mkArray(elem, size) };
            };
            defer size_eval.destroy(self.gpa);

            switch (size_eval) {
                .Int => |len| {
                    const concrete = std.math.cast(usize, len) orelse {
                        try self.context.diags.addError(size_loc, .array_size_not_integer_literal, .{});
                        status = false;
                        break :blk_at .{ status, ts.mkArray(elem, size) };
                    };
                    size = concrete;
                },
                else => {
                    try self.context.diags.addError(size_loc, .array_size_not_integer_literal, .{});
                    status = false;
                },
            }

            break :blk_at .{ status, ts.mkArray(elem, size) };
        },
        .Call => blk_call: {
            const res = try typeFromTypeExpr(self, ctx, ast_unit, ast_unit.exprs.get(.Call, id).callee);
            status = status and res[0];
            if (try resolveTypeFunctionCall(self, ctx, ast_unit, id, bindings)) |ty_res| {
                status = status and ty_res[0];
                break :blk_call .{ status, ty_res[1] };
            }
            const call_row = ast_unit.exprs.get(.Call, id);
            const callee_kind = ast_unit.kind(call_row.callee);
            if (callee_kind == .FieldAccess or callee_kind == .Ident) {
                var value = evalComptimeValueWithBindings(self, ctx, ast_unit, id, bindings) catch {
                    break :blk_call .{ false, ts.tTypeError() };
                };
                defer value.destroy(self.gpa);
                switch (value) {
                    .Type => |resolved| {
                        const wrapped = self.context.type_store.mkTypeType(resolved);
                        try ast_unit.type_info.ensureExpr(self.gpa, id);
                        ast_unit.type_info.expr_types.items[id.toRaw()] = wrapped;
                        break :blk_call .{ status, resolved };
                    },
                    else => {
                        std.debug.print("evalComptimeValueWithBindings returned non-Type for call {}\n", .{id});
                    },
                }
            }
            break :blk_call .{ false, ts.tTypeError() };
        },
        else => try typeFromTypeExpr(self, ctx, ast_unit, id),
    };
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
    const params = ast_unit.exprs.param_pool.slice(fn_lit.params);
    const args = ast_unit.exprs.expr_pool.slice(call.args);
    if (params.len != args.len) return null;

    var bindings_builder: std.ArrayList(Binding) = .empty;
    defer bindings_builder.deinit(self.gpa);
    if (existing_bindings.len > 0) {
        try bindings_builder.appendSlice(self.gpa, existing_bindings);
    }
    var callee_ctx = ctx;
    if (ast_unit.file_id < self.checker_ctx.items.len) {
        callee_ctx = &self.checker_ctx.items[ast_unit.file_id];
    }

    var i: usize = 0;
    var status = true;
    while (i < params.len) : (i += 1) {
        const param = ast_unit.exprs.Param.get(params[i]);
        if (!param.is_comptime or param.pat.isNone() or param.ty.isNone()) return null;

        const pat_id = param.pat.unwrap();
        if (ast_unit.kind(pat_id) != .Binding) return null;
        const pname = ast_unit.pats.get(.Binding, pat_id).name;

        const res = try typeFromTypeExpr(self, callee_ctx, ast_unit, param.ty.unwrap());
        status = status and res[0];
        const annotated = res[1];
        if (self.typeKind(annotated) == .TypeType) {
            const current_bindings = bindings_builder.items[0..bindings_builder.items.len];
            const arg_res = try typeFromTypeExprWithBindings(self, callee_ctx, ast_unit, args[i], current_bindings);
            status = status and arg_res[0];
            try bindings_builder.append(self.gpa, .{ .Type = .{ .name = pname, .ty = arg_res[1] } });
        } else {
            const current_bindings = bindings_builder.items[0..bindings_builder.items.len];
            const arg_expr = args[i];
            const arg_kind = ast_unit.kind(arg_expr);

            var have_value = false;
            var value: comp.ComptimeValue = undefined;

            if (arg_kind == .Ident) {
                const ident_name = ast_unit.exprs.get(.Ident, arg_expr).name;
                if (lookupValueBinding(current_bindings, ident_name)) |existing| {
                    value = existing;
                    have_value = true;
                }
            }

            if (!have_value) {
                value = blk: {
                    const computed = evalComptimeValueWithBindings(self, ctx, ast_unit, arg_expr, current_bindings) catch {
                        if (arg_kind == .Literal) {
                            const literal_val = (try evalLiteralToComptime(ast_unit, arg_expr)) orelse return null;
                            break :blk literal_val;
                        }
                        return null;
                    };
                    break :blk computed;
                };
                have_value = true;
            }

            if (!have_value) return null;
            try bindings_builder.append(self.gpa, .{ .Value = .{ .name = pname, .value = value, .ty = annotated } });
        }
    }

    if (fn_lit.body.isNone()) return null;
    const body_id = fn_lit.body.unwrap();
    if (ast_unit.kind(body_id) != .Block) return null;
    const block = ast_unit.exprs.get(.Block, body_id);
    const stmts = ast_unit.stmts.stmt_pool.slice(block.items);
    _ = try callee_ctx.symtab.push(callee_ctx.symtab.currentId());
    defer callee_ctx.symtab.pop();

    for (params) |pid| {
        const p = ast_unit.exprs.Param.get(pid);
        if (p.pat.isNone()) continue;
        const pat_id = p.pat.unwrap();
        if (ast_unit.kind(pat_id) != .Binding) continue;
        const pname = ast_unit.pats.get(.Binding, pat_id).name;

        _ = try callee_ctx.symtab.declare(.{
            .name = pname,
            .kind = .Param,
            .is_comptime = p.is_comptime,
            .loc = p.loc,
            .origin_decl = .none(),
            .origin_param = .some(pid),
        });
    }

    const base_param_specs = callee_ctx.param_specializations.items.len;
    defer callee_ctx.param_specializations.items.len = base_param_specs;
    try self.ensureInterpreter(ast_unit, callee_ctx);
    const interp = callee_ctx.interp.?;

    var interp_bindings = std.ArrayList(interpreter.Binding){};
    defer {
        for (interp_bindings.items) |*b| b.value.destroy(self.gpa);
        interp_bindings.deinit(self.gpa);
    }

    for (bindings_builder.items) |binding| {
        switch (binding) {
            .Type => |t| {
                try callee_ctx.param_specializations.append(self.gpa, .{ .name = t.name, .ty = t.ty });
                // Also bind types in the interpreter so typeof() or type expressions using them work
                const val = comp.ComptimeValue{ .Type = t.ty };
                try interp_bindings.append(self.gpa, .{ .name = t.name, .value = val });
            },
            .Value => |v| {
                const cloned = try comp.cloneComptimeValue(self.gpa, v.value);
                try interp_bindings.append(self.gpa, .{ .name = v.name, .value = cloned });
            },
        }
    }

    var scope = try interp.pushBindings(&interp_bindings);
    defer scope.deinit();

    for (stmts) |sid| {
        if (ast_unit.kind(sid) == .Decl) {
            const row = ast_unit.stmts.get(.Decl, sid);
            clearDeclTypes(ast_unit, row.decl);
            try self.checkDecl(callee_ctx, ast_unit, row.decl);
            continue;
        }
        if (ast_unit.kind(sid) != .Return) continue;
        const ret = ast_unit.stmts.get(.Return, sid);
        if (ret.value.isNone()) return null;
        clearExprTypes(ast_unit, ret.value.unwrap());
        const res = try typeFromTypeExprWithBindings(self, callee_ctx, ast_unit, ret.value.unwrap(), bindings_builder.items);
        status = status and res[0];
        const resolved = res[1];
        try ast_unit.type_info.ensureExpr(self.gpa, call_id);
        const type_ty = self.context.type_store.mkTypeType(resolved);
        ast_unit.type_info.expr_types.items[call_id.toRaw()] = type_ty;
        return .{ status, resolved };
    }
    return null;
}

/// Evaluate a type expression, reporting whether it is a nominal type and its ID.
pub fn typeFromTypeExpr(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) anyerror!struct { bool, types.TypeId } {
    const ts = self.context.type_store;
    var status = true;
    if (ctx.symtab.stack.items.len == 0) {
        _ = ctx.symtab.push(null) catch return .{ false, ts.tTypeError() };
    }
    return switch (ast_unit.kind(id)) {
        .Ident => blk: {
            const ident = ast_unit.exprs.get(.Ident, id);
            const name = ident.name;
            const ident_name = ast_unit.exprs.strs.get(name);
            const s = ident_name;
            if (std.mem.eql(u8, s, "bool")) break :blk .{ true, ts.tBool() };
            if (std.mem.eql(u8, s, "i8")) break :blk .{ true, ts.tI8() };
            if (std.mem.eql(u8, s, "i16")) break :blk .{ true, ts.tI16() };
            if (std.mem.eql(u8, s, "i32")) break :blk .{ true, ts.tI32() };
            if (std.mem.eql(u8, s, "i64")) break :blk .{ true, ts.tI64() };
            if (std.mem.eql(u8, s, "u8")) break :blk .{ true, ts.tU8() };
            if (std.mem.eql(u8, s, "u16")) break :blk .{ true, ts.tU16() };
            if (std.mem.eql(u8, s, "u32")) break :blk .{ true, ts.tU32() };
            if (std.mem.eql(u8, s, "u64")) break :blk .{ true, ts.tU64() };
            if (std.mem.eql(u8, s, "f32")) break :blk .{ true, ts.tF32() };
            if (std.mem.eql(u8, s, "f64")) break :blk .{ true, ts.tF64() };
            if (std.mem.eql(u8, s, "usize")) break :blk .{ true, ts.tUsize() };
            if (std.mem.eql(u8, s, "char")) break :blk .{ true, ts.tU32() };
            if (std.mem.eql(u8, s, "string")) break :blk .{ true, ts.tString() };
            if (std.mem.eql(u8, s, "void")) break :blk .{ true, ts.tVoid() };
            if (std.mem.eql(u8, s, "any")) break :blk .{ true, ts.tAny() };
            if (std.mem.eql(u8, s, "Error")) break :blk .{ true, ts.tTestError() };
            if (std.mem.eql(u8, s, "type"))
                break :blk .{ true, ts.mkTypeType(ts.tAny()) };

            if (self.lookupParamSpecialization(ctx, name)) |ty| {
                const k = self.typeKind(ty);
                if (k == .TypeType) {
                    return .{ status, ts.get(.TypeType, ty).of };
                }
                return .{ status, ty };
            }

            if (self.lookup(ctx, name)) |sid| {
                const sym = ctx.symtab.syms.get(sid);
                if (!sym.origin_decl.isNone()) {
                    const did = sym.origin_decl.unwrap();
                    if (ast_unit.type_info.decl_types.items[did.toRaw()]) |ty| {
                        const kind = self.typeKind(ty);
                        if (kind == .TypeType) {
                            const tt = ts.get(.TypeType, ty);
                            if (self.typeKind(tt.of) != .Any) {
                                return .{ true, tt.of };
                            }
                        } else {
                            return .{ true, ty };
                        }
                    }

                    // Recursion guard for lazy type resolution.
                    if (ctx.resolving_type_decls.get(did)) |_| {
                        return .{ true, ts.tAny() };
                    }
                    try ctx.resolving_type_decls.put(self.gpa, did, {});
                    defer _ = ctx.resolving_type_decls.swapRemove(did);

                    // Lazy resolve: if the declaration's RHS is a type expression, resolve it now.
                    const drow = ast_unit.exprs.Decl.get(did);
                    const rhs_res = try typeFromTypeExpr(self, ctx, ast_unit, drow.value);
                    status = status and rhs_res[0];
                    const rhs_ty = rhs_res[1];
                    if (self.typeKind(rhs_ty) != .TypeError) {
                        // Record as a type constant for future queries
                        const tt = ts.mkTypeType(rhs_ty);
                        ast_unit.type_info.decl_types.items[did.toRaw()] = tt;
                        try ast_unit.type_info.ensureExpr(self.gpa, drow.value);
                        ast_unit.type_info.expr_types.items[drow.value.toRaw()] = tt;
                        return .{ status, rhs_ty };
                    } else {
                        if (status) {
                            try self.context.diags.addError(
                                ast_unit.exprs.locs.get(ident.loc),
                                .identifier_not_type,
                                .{ident_name},
                            );
                        }
                        return .{ status, ts.tTypeError() };
                    }
                }
                if (!sym.origin_param.isNone()) {
                    const pid = sym.origin_param.unwrap();
                    const param_row = ast_unit.exprs.Param.get(pid);
                    if (!param_row.ty.isNone()) {
                        const res = try typeFromTypeExpr(self, ctx, ast_unit, param_row.ty.unwrap());
                        status = status and res[0];
                        const annotated = res[1];
                        if (param_row.is_comptime) {
                            if (self.typeKind(annotated) == .TypeType) {
                                return .{ status, ts.get(.TypeType, annotated).of };
                            }
                            return .{ status, annotated };
                        }
                        return .{ status, annotated };
                    }
                    return .{ status, ts.tAny() };
                }
            }

            try self.context.diags.addError(ast_unit.exprs.locs.get(ident.loc), .undefined_identifier, .{ident_name});
            break :blk .{ false, ts.tTypeError() };
        },
        .MlirBlock => blk: {
            const row = ast_unit.exprs.get(.MlirBlock, id);
            break :blk switch (row.kind) {
                .Type => .{ true, ts.tMlirType() },
                .Attribute => .{ true, ts.tMlirAttribute() },
                .Module => .{ true, ts.tMlirModule() },
                .Operation => blk_inner: {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .mlir_block_not_a_type, .{});
                    break :blk_inner .{ false, ts.tTypeError() };
                },
            };
        },
        .TupleType => blk_tt: {
            const row = ast_unit.exprs.get(.TupleType, id);
            const ids = ast_unit.exprs.expr_pool.slice(row.elems);
            var buf = try ts.gpa.alloc(types.TypeId, ids.len);
            defer ts.gpa.free(buf);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) {
                const res = try typeFromTypeExpr(self, ctx, ast_unit, ids[i]);
                status = status and res[0];
                buf[i] = res[1];
            }

            break :blk_tt .{ status, ts.mkTuple(buf) };
        },
        .TupleLit => blk_ttl: {
            const row = ast_unit.exprs.get(.TupleLit, id);
            const ids = ast_unit.exprs.expr_pool.slice(row.elems);
            var buf = try ts.gpa.alloc(types.TypeId, ids.len);
            defer ts.gpa.free(buf);
            var i: usize = 0;
            while (i < ids.len) : (i += 1) {
                const res = try typeFromTypeExpr(self, ctx, ast_unit, ids[i]);
                status = status and res[0];
                buf[i] = res[1];
            }
            break :blk_ttl .{ status, ts.mkTuple(buf) };
        },
        .MapType => blk_mt: {
            const row = ast_unit.exprs.get(.MapType, id);
            const key_res = try typeFromTypeExpr(self, ctx, ast_unit, row.key);
            const val_res = try typeFromTypeExpr(self, ctx, ast_unit, row.value);
            status = status and key_res[0] and val_res[0];
            break :blk_mt .{ status, ts.mkMap(key_res[1], val_res[1]) };
        },
        .ArrayType => blk_at: {
            const res = try typeFromTypeExprWithBindings(self, ctx, ast_unit, id, &[_]Binding{});
            break :blk_at res;
        },
        .DynArrayType => blk_dt: {
            const row = ast_unit.exprs.get(.DynArrayType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            break :blk_dt .{ status, ts.mkDynArray(res[1]) };
        },
        .SliceType => blk_st: {
            const row = ast_unit.exprs.get(.SliceType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            break :blk_st .{ status, ts.mkSlice(res[1], row.is_const) };
        },
        .OptionalType => blk_ot: {
            const row = ast_unit.exprs.get(.OptionalType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            break :blk_ot .{ status, ts.mkOptional(res[1]) };
        },
        .PointerType => blk_pt: {
            const row = ast_unit.exprs.get(.PointerType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            break :blk_pt .{ status, ts.mkPtr(res[1], row.is_const) };
        },
        .SimdType => blk_simd: {
            const row = ast_unit.exprs.get(.SimdType, id);
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            const elem_ty = res[1];
            const ek = self.typeKind(elem_ty);
            if (!isNumericKind(self, ek)) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_invalid_element_type, .{});
                status = false;
            }
            if (ast_unit.kind(row.lanes) != .Literal) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                status = false;
            }
            const lit = ast_unit.exprs.get(.Literal, row.lanes);
            if (lit.kind != .int) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                status = false;
            }
            const lanes_val = switch (lit.data) {
                .int => |int_info| blk: {
                    if (!int_info.valid) break :blk 0;
                    break :blk std.math.cast(usize, int_info.value) orelse 0;
                },
                else => 0,
            };
            if (lanes_val == 0 or lanes_val > std.math.maxInt(u16)) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .simd_lanes_not_integer_literal, .{});
                status = false;
            }
            const simd_ty = ts.mkSimd(elem_ty, @intCast(lanes_val));
            break :blk_simd .{ status, simd_ty };
        },
        .TensorType => blk_tensor: {
            const row = ast_unit.exprs.get(.TensorType, id);
            // Validate shape dimensions are integer literals
            const dims = ast_unit.exprs.expr_pool.slice(row.shape);
            if (dims.len > types.max_tensor_rank) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_rank_exceeds_limit, .{});
                status = false;
            }
            var dim_values = [_]usize{0} ** types.max_tensor_rank;
            var i: usize = 0;
            while (i < dims.len) : (i += 1) {
                if (ast_unit.kind(dims[i]) != .Literal) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    status = false;
                    continue;
                }
                const dl = ast_unit.exprs.get(.Literal, dims[i]);
                if (dl.kind != .int) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    status = false;
                    continue;
                }
                const info = switch (dl.data) {
                    .int => |int_info| int_info,
                    else => ast.LiteralInt{ .text = .{ .index = 0 }, .value = 0, .base = 0, .valid = false },
                };
                if (!info.valid) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    status = false;
                }
                const dim_val = std.math.cast(usize, info.value) orelse val: {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_dimension_not_integer_literal, .{});
                    status = false;
                    break :val 0;
                };
                dim_values[i] = dim_val;
            }
            // Validate element type present and resolvable
            const res = try typeFromTypeExpr(self, ctx, ast_unit, row.elem);
            status = status and res[0];
            const ety = res[1];
            if (self.typeKind(ety) == .TypeError) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .tensor_missing_element_type, .{});
            }
            const rank = dims.len;
            const tensor_ty = ts.mkTensor(ety, dim_values[0..rank]);
            break :blk_tensor .{ status, tensor_ty };
        },
        .StructType => blk_sty: {
            const row = ast_unit.exprs.get(.StructType, id);
            const sfs = ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer ts.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const f = ast_unit.exprs.StructField.get(sfs[i]);
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
                const res = try typeFromTypeExpr(self, ctx, ast_unit, f.ty);
                status = status and res[0];
                if (!f.value.isNone()) {
                    const val_ty = try self.checkExpr(ctx, ast_unit, f.value.unwrap());
                    if (self.typeKind(val_ty) != .TypeError and res[0]) {
                        const field_ty = res[1];
                        if (self.assignable(val_ty, field_ty) != .success) {
                            try self.context.diags.addError(
                                ast_unit.exprs.locs.get(f.loc),
                                .type_annotation_mismatch,
                                .{ field_ty, val_ty },
                            );
                            status = false;
                        }
                    }
                }
                buf[i] = .{ .name = f.name, .ty = res[1] };
            }
            break :blk_sty .{ status, ts.mkStruct(buf, @as(u64, ast_unit.file_id) << 32 | id.toRaw()) };
        },
        .UnionType => blk_un: {
            const row = ast_unit.exprs.get(.UnionType, id);
            const sfs = ast_unit.exprs.sfield_pool.slice(row.fields);
            var buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
            defer ts.gpa.free(buf);
            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);
            var i: usize = 0;
            while (i < sfs.len) : (i += 1) {
                const sf = ast_unit.exprs.StructField.get(sfs[i]);
                const gop = try seen.getOrPut(self.gpa, sf.name.toRaw());
                if (gop.found_existing) {
                    const field_name = ast_unit.exprs.strs.get(sf.name);
                    const first_loc = ast_unit.exprs.locs.get(gop.value_ptr.*);
                    const diag_idx = self.context.diags.count();
                    try self.context.diags.addError(ast_unit.exprs.locs.get(sf.loc), .duplicate_field, .{field_name});
                    try self.context.diags.attachNote(diag_idx, first_loc, .first_defined_here);
                    status = false;
                } else {
                    gop.value_ptr.* = sf.loc;
                }
                const res = try typeFromTypeExpr(self, ctx, ast_unit, sf.ty);
                status = status and res[0];
                if (!sf.value.isNone()) {
                    const val_ty = try self.checkExpr(ctx, ast_unit, sf.value.unwrap());
                    if (self.typeKind(val_ty) != .TypeError and res[0]) {
                        const field_ty = res[1];
                        if (self.assignable(val_ty, field_ty) != .success) {
                            try self.context.diags.addError(
                                ast_unit.exprs.locs.get(sf.loc),
                                .type_annotation_mismatch,
                                .{ field_ty, val_ty },
                            );
                            status = false;
                        }
                    }
                }
                buf[i] = .{ .name = sf.name, .ty = res[1] };
            }
            break :blk_un .{ status, ts.mkUnion(buf) };
        },
        .EnumType => blk_en: {
            const row = ast_unit.exprs.get(.EnumType, id);
            const efs = ast_unit.exprs.efield_pool.slice(row.fields);

            const tag_res = if (row.discriminant.isNone())
                .{ true, ts.tI32() }
            else
                (try typeFromTypeExpr(self, ctx, ast_unit, row.discriminant.unwrap()));
            status = status and tag_res[0];
            const tag_ty = tag_res[1];

            // Ensure the tag type is an integer.
            const tk = self.typeKind(tag_ty);
            if (!isIntegerKind(self, tk)) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(row.loc), .enum_discriminant_not_integer, .{});
                status = false;
            }

            var member_buf = try self.gpa.alloc(types.TypeStore.EnumMemberArg, efs.len);
            defer self.gpa.free(member_buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);
            var enum_value_bindings: std.ArrayList(Binding) = .empty;
            defer enum_value_bindings.deinit(self.gpa);

            var next_value: i128 = 0;
            var i: usize = 0;
            while (i < efs.len) : (i += 1) {
                const enum_field = ast_unit.exprs.EnumField.get(efs[i]);

                const gop = try seen.getOrPut(self.gpa, enum_field.name.toRaw());
                if (gop.found_existing) {
                    const tag_name = ast_unit.exprs.strs.get(enum_field.name);
                    const first_loc = ast_unit.exprs.locs.get(gop.value_ptr.*);
                    const diag_idx = self.context.diags.count();
                    try self.context.diags.addError(ast_unit.exprs.locs.get(enum_field.loc), .duplicate_enum_field, .{tag_name});
                    try self.context.diags.attachNote(diag_idx, first_loc, .first_defined_here);
                    status = false;
                } else {
                    gop.value_ptr.* = enum_field.loc;
                }

                var current_value: i128 = next_value;
                const binding_slice = enum_value_bindings.items[0..enum_value_bindings.items.len];
                if (!enum_field.value.isNone()) {
                    const val_id = enum_field.value.unwrap();
                    var resolved_from_binding = false;
                    if (ast_unit.kind(val_id) == .Ident) {
                        const ident = ast_unit.exprs.get(.Ident, val_id);
                        if (lookupValueBinding(binding_slice, ident.name)) |binding_val| {
                            switch (binding_val) {
                                .Int => |v| {
                                    current_value = v;
                                    resolved_from_binding = true;
                                },
                                else => {},
                            }
                        }
                    }

                    if (!resolved_from_binding) {
                        const comptime_eval_ok = comptime_block: {
                            var comptime_val = evalComptimeValueWithBindings(self, ctx, ast_unit, val_id, binding_slice) catch {
                                break :comptime_block false;
                            };
                            defer comptime_val.destroy(self.gpa);

                            switch (comptime_val) {
                                .Int => |v| current_value = v,
                                else => break :comptime_block false,
                            }
                            break :comptime_block true;
                        };

                        if (!comptime_eval_ok) {
                            try self.context.diags.addError(ast_unit.exprs.locs.get(enum_field.loc), .enum_discriminant_not_integer, .{});
                            status = false;
                        }
                    }
                }

                member_buf[i] = .{ .name = enum_field.name, .value = @intCast(current_value) };
                try enum_value_bindings.append(self.gpa, .{
                    .Value = .{ .name = enum_field.name, .value = comp.ComptimeValue{ .Int = current_value }, .ty = tag_ty },
                });
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

            var i: usize = 0;
            while (i < vfs.len) : (i += 1) {
                const vf = ast_unit.exprs.VariantField.get(vfs[i]);
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    const tag_name = ast_unit.exprs.strs.get(vf.name);
                    const first_loc = ast_unit.exprs.locs.get(gop.value_ptr.*);
                    const diag_idx = self.context.diags.count();
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vf.loc), .duplicate_error_variant, .{tag_name});
                    try self.context.diags.attachNote(diag_idx, first_loc, .first_defined_here);
                } else {
                    gop.value_ptr.* = vf.loc;
                }

                const payload_ty = switch (vf.payload_kind) {
                    .none => ts.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) {
                            break :blk_tuple ts.tVoid();
                        }
                        const elems = ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        var j: usize = 0;
                        while (j < elems.len) : (j += 1) {
                            const res = try typeFromTypeExpr(self, ctx, ast_unit, elems[j]);
                            status = status and res[0];
                            elem_buf[j] = res[1];
                        }

                        break :blk_tuple ts.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) {
                            break :blk_struct ts.tVoid();
                        }
                        const fields = ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        var j: usize = 0;
                        while (j < fields.len) : (j += 1) {
                            const sf = ast_unit.exprs.StructField.get(fields[j]);
                            const res = try typeFromTypeExpr(self, ctx, ast_unit, sf.ty);
                            status = status and res[0];
                            field_buf[j] = .{
                                .name = sf.name,
                                .ty = res[1],
                            };
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
            const val_res = try typeFromTypeExpr(self, ctx, ast_unit, row.value);
            const err_res = try typeFromTypeExpr(self, ctx, ast_unit, row.err);
            status = status and val_res[0] and err_res[0];
            break :blk_est .{ status, ts.mkErrorSet(val_res[1], err_res[1]) };
        },
        .VariantType => blk_var: {
            const row = ast_unit.exprs.get(.VariantType, id);
            const vfs = ast_unit.exprs.vfield_pool.slice(row.fields);
            var case_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, vfs.len);
            defer self.gpa.free(case_buf);

            var seen = std.AutoArrayHashMapUnmanaged(u32, ast.LocId){};
            defer seen.deinit(self.gpa);

            var i: usize = 0;
            while (i < vfs.len) : (i += 1) {
                const vf = ast_unit.exprs.VariantField.get(vfs[i]);
                const gop = try seen.getOrPut(self.gpa, vf.name.toRaw());
                if (gop.found_existing) {
                    const tag_name = ast_unit.exprs.strs.get(vf.name);
                    const first_loc = ast_unit.exprs.locs.get(gop.value_ptr.*);
                    const diag_idx = self.context.diags.count();
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vf.loc), .duplicate_variant, .{tag_name});
                    try self.context.diags.attachNote(diag_idx, first_loc, .first_defined_here);
                    status = false;
                } else {
                    gop.value_ptr.* = vf.loc;
                }

                const payload_ty = switch (vf.payload_kind) {
                    .none => ts.tVoid(),
                    .tuple => blk_tuple: {
                        if (vf.payload_elems.isNone()) {
                            break :blk_tuple ts.tVoid();
                        }
                        const elems = ast_unit.exprs.expr_pool.slice(vf.payload_elems.asRange());
                        var elem_buf = try self.gpa.alloc(types.TypeId, elems.len);
                        defer self.gpa.free(elem_buf);
                        var j: usize = 0;
                        while (j < elems.len) : (j += 1) {
                            const res = try typeFromTypeExpr(self, ctx, ast_unit, elems[j]);
                            status = status and res[0];
                            elem_buf[j] = res[1];
                        }
                        break :blk_tuple ts.mkTuple(elem_buf);
                    },
                    .@"struct" => blk_struct: {
                        if (vf.payload_fields.isNone()) {
                            break :blk_struct ts.tVoid();
                        }
                        const fields = ast_unit.exprs.sfield_pool.slice(vf.payload_fields.asRange());
                        var field_buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, fields.len);
                        defer self.gpa.free(field_buf);
                        var j: usize = 0;
                        while (j < fields.len) : (j += 1) {
                            const sf = ast_unit.exprs.StructField.get(fields[j]);
                            const res = try typeFromTypeExpr(self, ctx, ast_unit, sf.ty);
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
            // function type in type position
            const fnr = ast_unit.exprs.get(.FunctionLit, id);
            const params = ast_unit.exprs.param_pool.slice(fnr.params);
            var pbuf = try self.gpa.alloc(types.TypeId, params.len);
            defer self.gpa.free(pbuf);
            var i: usize = 0;
            while (i < params.len) : (i += 1) {
                const p = ast_unit.exprs.Param.get(params[i]);
                if (p.ty.isNone()) break :blk_fn .{ false, ts.tTypeError() };
                const res = try typeFromTypeExpr(self, ctx, ast_unit, p.ty.unwrap());
                status = status and res[0];
                const pt = res[1];
                if (self.typeKind(pt) == .TypeError) return .{ false, ts.tTypeError() };
                pbuf[i] = pt;
            }
            const res_res = if (!fnr.result_ty.isNone()) (try typeFromTypeExpr(self, ctx, ast_unit, fnr.result_ty.unwrap())) else .{ true, ts.tVoid() };
            status = status and res_res[0];
            const res = res_res[1];
            const is_pure = !fnr.flags.is_proc;
            break :blk_fn .{ status, ts.mkFunction(pbuf, res, fnr.flags.is_variadic, is_pure, fnr.flags.is_extern) };
        },
        .FieldAccess => blk_fa: {
            // Recursion guard: check if we're already resolving this expression
            if (ctx.resolving_type_exprs.get(id)) |_| {
                // Circular type expression detected. Return type error to avoid stack overflow.
                try self.context.diags.addError(ast_unit.exprs.locs.get(ast_unit.exprs.get(.FieldAccess, id).loc), .field_access_on_non_aggregate, .{});
                break :blk_fa .{ false, ts.tTypeError() };
            }
            try ctx.resolving_type_exprs.put(self.gpa, id, void{});
            defer _ = ctx.resolving_type_exprs.swapRemove(id);

            const fr = ast_unit.exprs.get(.FieldAccess, id);
            const parent_res = try typeFromTypeExpr(self, ctx, ast_unit, fr.parent);
            status = status and parent_res[0];
            const parent_ty = parent_res[1];
            const parent_kind = self.typeKind(parent_ty);
            switch (parent_kind) {
                .Ast => {
                    // Accessing a member from an imported module in type position
                    const ast_ty = ts.get(.Ast, parent_ty);
                    const pkg_name = self.context.interner.get(ast_ty.pkg_name);
                    const filepath = self.context.interner.get(ast_ty.filepath);
                    const pkg = self.context.compilation_unit.packages.getPtr(pkg_name) orelse {
                        try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .import_not_found, .{});
                        break :blk_fa .{ false, ts.tTypeError() };
                    };
                    const parent_unit = pkg.sources.getPtr(filepath) orelse {
                        try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .import_not_found, .{});
                        break :blk_fa .{ false, ts.tTypeError() };
                    };
                    if (parent_unit.ast) |a| {
                        // Re-intern field name in the imported unit's interner for lookup
                        const name_bytes = ast_unit.exprs.strs.get(fr.field);
                        const target_sid = a.exprs.strs.intern(name_bytes);
                        const sym_row = self.checker_ctx.items[a.file_id].symtab.lookup(.fromRaw(0), target_sid);
                        if (sym_row) |ex| {
                            const sym = self.checker_ctx.items[a.file_id].symtab.syms.get(ex);
                            const decl = sym.origin_decl.unwrap();

                            if (a.type_info.decl_types.items[decl.toRaw()] == null) {
                                const other_ctx = &self.checker_ctx.items[a.file_id];
                                try self.checkDecl(other_ctx, a, decl);
                            }

                            if (a.type_info.decl_types.items[decl.toRaw()]) |resolved| {
                                var ty = resolved;
                                if (self.typeKind(ty) == .TypeType)
                                    ty = ts.get(.TypeType, ty).of;
                                break :blk_fa .{ status, ty };
                            }
                            break :blk_fa .{ false, ts.tTypeError() };
                        }
                    }
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_module_field, .{ast_unit.exprs.strs.get(fr.field)});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
                .Struct => {
                    const st = ts.get(.Struct, parent_ty);
                    const fields = ts.field_pool.slice(st.fields);
                    var i: usize = 0;
                    while (i < fields.len) : (i += 1) {
                        const f = fields[i];
                        const field = ts.Field.get(f);
                        if (field.name.eq(fr.field)) return .{ status, field.ty };
                    }
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
                    var i: usize = 0;
                    while (i < members.len) : (i += 1) {
                        const member = ts.EnumMember.get(members[i]);
                        if (member.name.eq(fr.field)) {
                            return .{ status, parent_ty };
                        }
                    }
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .unknown_struct_field, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
                else => {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(fr.loc), .field_access_on_non_aggregate, .{});
                    break :blk_fa .{ false, ts.tTypeError() };
                },
            }
        },
        .Import => blk_import: {
            const ir = ast_unit.exprs.get(.Import, id);
            const filepath = ast_unit.exprs.strs.get(ir.path);
            var found = false;
            for (self.context.compilation_unit.packages.values()) |pkg| {
                if (pkg.sources.get(filepath) == null) continue;
                const pkg_name = self.context.interner.intern(pkg.name);
                const ast_ty = ts.mkAst(pkg_name, ir.path);
                // Note: record type directly; no need to stamp expr_types here in type position
                found = true;
                break :blk_import .{ true, ast_ty };
            }
            if (!found) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(ir.loc), .import_not_found, .{});
                break :blk_import .{ false, ts.tTypeError() };
            }
            // Defensive: if control reaches here, return a type error instead of panicking
            break :blk_import .{ false, ts.tTypeError() };
        },
        .Call => blk_call: {
            const res = try typeFromTypeExpr(self, ctx, ast_unit, ast_unit.exprs.get(.Call, id).callee);
            status = status and res[0];
            if (try resolveTypeFunctionCall(self, ctx, ast_unit, id, &[_]Binding{})) |ty_res| {
                status = status and ty_res[0];
                break :blk_call .{ status, ty_res[1] };
            }
            const call_row = ast_unit.exprs.get(.Call, id);
            const callee_kind = ast_unit.kind(call_row.callee);
            if (callee_kind == .FieldAccess or callee_kind == .Ident) {
                var value = evalComptimeValueWithBindings(self, ctx, ast_unit, id, &[_]Binding{}) catch break :blk_call .{ false, ts.tTypeError() };
                defer value.destroy(self.gpa);
                switch (value) {
                    .Type => |resolved| {
                        const wrapped = ts.mkTypeType(resolved);
                        try ast_unit.type_info.ensureExpr(self.gpa, id);
                        ast_unit.type_info.expr_types.items[id.toRaw()] = wrapped;
                        break :blk_call .{ status, resolved };
                    },
                    else => {},
                }
            }
            break :blk_call .{ false, ts.tTypeError() };
        },
        .AnyType => .{ true, ts.tAny() },
        .TypeType => .{ true, ts.tType() },
        .NoreturnType => .{ true, ts.tNoReturn() },
        else => .{ false, ts.tTypeError() },
    };
}
