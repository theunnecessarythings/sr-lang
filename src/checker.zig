const std = @import("std");

const ast = @import("ast.zig");
const check_types = @import("check_types.zig");
const compile = @import("compile.zig");
const Context = compile.Context;
const diag = @import("diagnostics.zig");
const Diagnostics = diag.Diagnostics;
const Loc = @import("lexer.zig").Token.Loc;
const pattern_matching = @import("check_pattern_matching.zig");
const Pipeline = @import("pipeline.zig").Pipeline;
const comp = @import("comptime.zig");
const symbols = @import("symbols.zig");
const types = @import("types.zig");
const TypeInfo = types.TypeInfo;
const MethodBinding = types.MethodBinding;
const MethodEntry = types.MethodEntry;
const mlir = @import("mlir_bindings.zig");

const List = std.ArrayList;

pub const Checker = @This();

gpa: std.mem.Allocator,
context: *Context,
pipeline: *Pipeline,
checker_ctx: List(*CheckerContext),

pub const CheckerContext = struct {
    symtab: symbols.SymbolStore,

    func_stack: List(FunctionCtx) = .{},
    loop_stack: List(LoopCtx) = .{},
    value_ctx: List(bool) = .{},
    warned_meta: bool = false,
    warned_comptime: bool = false,
    warned_code: bool = false,

    loop_binding_stack: List(LoopBindingCtx) = .{},
    catch_binding_stack: List(CatchBindingCtx) = .{},
    match_binding_stack: List(MatchBindingCtx) = .{},
    param_specializations: List(ParamSpecialization) = .{},

    pub fn deinit(self: *CheckerContext, gpa: std.mem.Allocator) void {
        self.symtab.deinit();
        self.func_stack.deinit(gpa);
        self.loop_stack.deinit(gpa);
        self.value_ctx.deinit(gpa);
        self.loop_binding_stack.deinit(gpa);
        self.catch_binding_stack.deinit(gpa);
        self.match_binding_stack.deinit(gpa);
        self.param_specializations.deinit(gpa);
    }
};

const LoopBindingCtx = struct {
    pat: ast.OptPatternId,
    subject_ty: types.TypeId,
};
const MatchBindingCtx = struct {
    pat: ast.PatternId,
    subject_ty: types.TypeId,
};
const CatchBindingCtx = struct {
    name: ast.StrId,
    ty: types.TypeId,
};

pub const ParamSpecialization = struct {
    name: ast.StrId,
    ty: types.TypeId,
};

// --------- tiny helpers (readability & consistency) ----------
pub inline fn typeKind(self: *const Checker, t: types.TypeId) types.TypeKind {
    return self.context.type_store.index.kinds.items[t.toRaw()];
}
inline fn exprKind(ast_unit: *const ast.Ast, eid: ast.ExprId) ast.ExprKind {
    return ast_unit.exprs.index.kinds.items[eid.toRaw()];
}
inline fn exprLocFromId(ast_unit: *ast.Ast, eid: ast.ExprId) Loc {
    const k = exprKind(ast_unit, eid);
    return switch (k) {
        inline else => |x| exprLoc(ast_unit, getExpr(ast_unit, x, eid)),
    };
}
inline fn exprLoc(ast_unit: *ast.Ast, expr: anytype) Loc {
    return ast_unit.exprs.locs.get(expr.loc);
}
inline fn getStmt(ast_unit: *ast.Ast, comptime K: ast.StmtKind, id: ast.StmtId) ast.StmtRowT(K) {
    return ast_unit.stmts.get(K, id);
}
pub inline fn getStr(ast_unit: *const ast.Ast, sid: ast.StrId) []const u8 {
    return ast_unit.exprs.strs.get(sid);
}
inline fn getExpr(ast_unit: *const ast.Ast, comptime K: ast.ExprKind, id: ast.ExprId) ast.RowT(K) {
    return ast_unit.exprs.get(K, id);
}

pub fn init(
    gpa: std.mem.Allocator,
    context: *Context,
    pipeline: *Pipeline,
) Checker {
    return .{
        .gpa = gpa,
        .context = context,
        .pipeline = pipeline,
        .checker_ctx = .{},
    };
}

pub fn deinit(self: *Checker) void {
    self.checker_ctx.deinit(self.gpa);
}

pub fn run(self: *Checker, levels: *const compile.DependencyLevels) !void {
    var ast_by_file = std.AutoHashMap(u32, *ast.Ast).init(self.gpa);
    defer ast_by_file.deinit();

    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var source_iter = pkg.value_ptr.sources.iterator();
        while (source_iter.next()) |unit| {
            if (unit.value_ptr.ast) |ast_unit| {
                try ast_by_file.put(unit.value_ptr.file_id, ast_unit);
            }
        }
    }

    // Size the per-file checker context table by max file_id + 1 to allow
    // direct indexing via ast_unit.file_id used during lowering.
    var max_file_id: usize = 0;
    {
        var it = ast_by_file.iterator();
        while (it.next()) |entry| {
            const fid: usize = entry.key_ptr.*;
            if (fid > max_file_id) max_file_id = fid;
        }
    }
    try self.checker_ctx.resize(self.gpa, max_file_id + 1);

    var threads = std.ArrayList(std.Thread){};
    defer threads.deinit(self.gpa);

    for (levels.levels.items) |level| {
        threads.clearRetainingCapacity();
        if (level.items.len == 0) continue;

        for (level.items) |file_id| {
            const ast_unit = ast_by_file.get(file_id) orelse continue;
            const checker_ctx = try self.gpa.create(CheckerContext);
            checker_ctx.* = CheckerContext{
                .symtab = symbols.SymbolStore.init(self.gpa),
            };
            // Expose this context by file id for TIR to use on-demand.
            if (file_id >= 0 and file_id < self.checker_ctx.items.len) {
                self.checker_ctx.items[file_id] = checker_ctx;
            }
            const thread = try std.Thread.spawn(.{}, runAst, .{ self, ast_unit, checker_ctx });
            try threads.append(self.gpa, thread);
        }

        for (threads.items) |thread| {
            thread.join();
        }
    }
}

pub fn runAst(self: *Checker, ast_unit: *ast.Ast, ctx: *CheckerContext) !void {
    // pre-allocate type slots
    const expr_len: usize = ast_unit.exprs.index.kinds.items.len;
    const decl_len: usize = ast_unit.exprs.Decl.list.len;
    try ast_unit.type_info.expr_types.appendNTimes(self.gpa, null, expr_len);
    try ast_unit.type_info.decl_types.appendNTimes(self.gpa, null, decl_len);

    // Add builtin symbols to the global scope
    _ = try ctx.symtab.push(null);

    const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);

    // (1) Bind all top-level names so forward refs resolve
    for (decl_ids) |did| {
        const d = ast_unit.exprs.Decl.get(did);
        try self.bindDeclPattern(ctx, ast_unit, did, d);
    }

    // (2) Predeclare signatures for all top-level functions
    for (decl_ids) |did| {
        const d = ast_unit.exprs.Decl.get(did);
        if (exprKind(ast_unit, d.value) == .FunctionLit) {
            try self.predeclareFunction(ctx, ast_unit, did);
        }
    }

    // (2b) Pre-register all methods using their predeclared signatures so that
    // method calls can resolve across declarations and ordering.
    for (decl_ids) |did| {
        const d = ast_unit.exprs.Decl.get(did);
        if (d.method_path.isNone()) continue;
        if (exprKind(ast_unit, d.value) != .FunctionLit) continue;
        const sig_ty = ast_unit.type_info.decl_types.items[did.toRaw()] orelse self.context.type_store.tAny();
        _ = try self.registerMethodDecl(ctx, ast_unit, did, d, sig_ty);
    }

    // (3) Now type-check declarations (walk bodies, defaults, patterns, methods, etc.)
    for (decl_ids) |did| {
        try self.checkDecl(ctx, ast_unit, did);
    }
}

// --------- context
const FunctionCtx = struct {
    result: types.TypeId,
    has_result: bool,
    pure: bool,
    require_pure: bool,
    locals: std.AutoArrayHashMapUnmanaged(u32, void) = .{},
};
const LoopCtx = struct {
    label: ast.OptStrId,
    result_ty: ?types.TypeId = null,
};

fn bindDeclPattern(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    did: ast.DeclId,
    d: ast.Rows.Decl,
) !void {
    if (d.pattern.isNone()) return;
    try pattern_matching.declareBindingsInPattern(self, ctx, ast_unit, d.pattern.unwrap(), d.loc, .{ .decl = did });
}

fn bindParamPattern(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, pid: ast.ParamId, p: ast.Rows.Param) !void {
    if (p.pat.isNone()) return;
    try pattern_matching.declareBindingsInPattern(self, ctx, ast_unit, p.pat.unwrap(), p.loc, .{ .param = pid });
}

fn pushFunc(
    self: *Checker,
    ctx: *CheckerContext,
    result_ty: types.TypeId,
    has_result: bool,
    require_pure: bool,
) !void {
    try ctx.func_stack.append(self.gpa, .{
        .result = result_ty,
        .has_result = has_result,
        .pure = true,
        .require_pure = require_pure,
    });
}
fn popFunc(self: *Checker, ctx: *CheckerContext) void {
    if (ctx.func_stack.items.len > 0) {
        var context = &ctx.func_stack.items[ctx.func_stack.items.len - 1];
        context.locals.deinit(self.gpa);
        _ = ctx.func_stack.pop();
    }
}
fn inFunction(_: *const Checker, ctx: *CheckerContext) bool {
    return ctx.func_stack.items.len > 0;
}
fn currentFunc(_: *const Checker, ctx: *CheckerContext) ?FunctionCtx {
    if (ctx.func_stack.items.len == 0) return null;
    return ctx.func_stack.items[ctx.func_stack.items.len - 1];
}

fn pushLoop(self: *Checker, ctx: *CheckerContext, label: ast.OptStrId) !void {
    try ctx.loop_stack.append(self.gpa, .{ .label = label, .result_ty = null });
}
fn popLoop(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.loop_stack.items.len > 0) _ = ctx.loop_stack.pop();
}
fn inLoop(_: *const Checker, ctx: *CheckerContext) bool {
    return ctx.loop_stack.items.len > 0;
}
inline fn pushLoopBinding(self: *Checker, ctx: *CheckerContext, pat: ast.OptPatternId, subj: types.TypeId) !void {
    try ctx.loop_binding_stack.append(self.gpa, .{ .pat = pat, .subject_ty = subj });
}
inline fn popLoopBinding(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.loop_binding_stack.items.len > 0) _ = ctx.loop_binding_stack.pop();
}

fn bindingNameOfPattern(ast_unit: *ast.Ast, pid: ast.PatternId) ?ast.StrId {
    const pkind = ast_unit.pats.index.kinds.items[pid.toRaw()];
    return switch (pkind) {
        .Binding => ast_unit.pats.get(.Binding, pid).name,
        else => null,
    };
}

fn predeclareFunction(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    did: ast.DeclId,
) !void {
    const d = ast_unit.exprs.Decl.get(did);
    if (exprKind(ast_unit, d.value) != .FunctionLit) return;

    const fid = d.value;
    const fnr = getExpr(ast_unit, .FunctionLit, fid);
    const params = ast_unit.exprs.param_pool.slice(fnr.params);

    var pbuf = try self.gpa.alloc(types.TypeId, params.len);
    defer self.gpa.free(pbuf);

    // Parameter types (no pattern checks, no default-value checks here)
    var i: usize = 0;
    while (i < params.len) : (i += 1) {
        const p = ast_unit.exprs.Param.get(params[i]);
        if (!p.ty.isNone()) {
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, p.ty.unwrap());
            const pt_or_err = res[1];
            pbuf[i] = if (self.typeKind(pt_or_err) == .TypeError) self.context.type_store.tAny() else pt_or_err;
        } else if (p.is_comptime) {
            pbuf[i] = self.context.type_store.mkTypeType(self.context.type_store.tAny());
        } else {
            // Unannotated runtime param – unknown until body checking
            pbuf[i] = self.context.type_store.tAny();
        }
    }

    const res_or_err = if (!fnr.result_ty.isNone())
        (try check_types.typeFromTypeExpr(self, ctx, ast_unit, fnr.result_ty.unwrap()))[1]
    else
        self.context.type_store.tVoid();
    if (self.typeKind(res_or_err) == .TypeError) return; // diagnostics already emitted
    const res = res_or_err;

    // Be optimistic about purity here; we’ll finalize after body checking.
    const sig_ty = self.context.type_store.mkFunction(pbuf, res, fnr.flags.is_variadic, true);

    // Stamp both the decl type and the function literal expr type.
    ast_unit.type_info.decl_types.items[did.toRaw()] = sig_ty;

    // If this is a top-level binding with a pattern, export its bindings now so imports
    // and same-file forward refs see the function in the module API.
    // if (!self.inFunction(ctx) and (!d.pattern.isNone())) {
    //     try self.recordExportsForDecl(ctx, ast_unit, did, sig_ty);
    // }
}

fn lookupParamSpecialization(_: *const Checker, ctx: *CheckerContext, name: ast.StrId) ?types.TypeId {
    var i: usize = ctx.param_specializations.items.len;
    while (i > 0) {
        i -= 1;
        const spec = ctx.param_specializations.items[i];
        if (spec.name.eq(name)) return spec.ty;
    }
    return null;
}

pub fn checkSpecializedFunction(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    id: ast.ExprId,
    specs: []const ParamSpecialization,
) !types.TypeId {
    const need_scope = ctx.symtab.stack.items.len == 0;
    if (need_scope) {
        _ = try ctx.symtab.push(null);
        const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
        for (decl_ids) |did| {
            const d = ast_unit.exprs.Decl.get(did);
            try self.bindDeclPattern(ctx, ast_unit, did, d);
        }
    }
    defer if (need_scope) ctx.symtab.pop();

    const base_len = ctx.param_specializations.items.len;
    defer ctx.param_specializations.items.len = base_len;
    if (specs.len > 0) try ctx.param_specializations.appendSlice(self.gpa, specs);

    const backup_len = ast_unit.type_info.expr_types.items.len;
    const backup = try self.gpa.alloc(?types.TypeId, backup_len);
    if (backup_len != 0) {
        const src = ast_unit.type_info.expr_types.items[0..backup_len];
        std.mem.copyForwards(?types.TypeId, backup, src);
    }
    defer {
        ast_unit.type_info.expr_types.items.len = backup_len;
        if (backup_len != 0) {
            const dest = ast_unit.type_info.expr_types.items[0..backup_len];
            std.mem.copyForwards(?types.TypeId, dest, backup);
        }
        self.gpa.free(backup);
    }

    return try self.checkFunctionLit(ctx, ast_unit, id);
}

pub inline fn pushMatchBinding(self: *Checker, ctx: *CheckerContext, pat: ast.PatternId, subj: types.TypeId) !void {
    try ctx.match_binding_stack.append(self.gpa, .{ .pat = pat, .subject_ty = subj });
}
pub inline fn popMatchBinding(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.match_binding_stack.items.len > 0) _ = ctx.match_binding_stack.pop();
}

inline fn pushCatchBinding(self: *Checker, ctx: *CheckerContext, name: ast.StrId, ty: types.TypeId) !void {
    try ctx.catch_binding_stack.append(self.gpa, .{ .name = name, .ty = ty });
}
inline fn popCatchBinding(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.catch_binding_stack.items.len > 0) _ = ctx.catch_binding_stack.pop();
}

inline fn bindingTypeFromActiveCatches(_: *Checker, ctx: *CheckerContext, name: ast.StrId) ?types.TypeId {
    var i: isize = @as(isize, @intCast(ctx.catch_binding_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const context = ctx.catch_binding_stack.items[@intCast(i)];
        if (context.name.eq(name)) return context.ty;
    }
    return null;
}

inline fn bindingTypeFromActiveMatches(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    name: ast.StrId,
) ?types.TypeId {
    var i: isize = @as(isize, @intCast(ctx.match_binding_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const context = ctx.match_binding_stack.items[@intCast(i)];
        if (pattern_matching.bindingTypeInPattern(self, ast_unit, context.pat, name, context.subject_ty)) |bt|
            return bt;
    }
    return null;
}

inline fn bindingTypeFromActiveLoops(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    name: ast.StrId,
) ?types.TypeId {
    var i: isize = @as(isize, @intCast(ctx.loop_binding_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const context = ctx.loop_binding_stack.items[@intCast(i)];
        if (!context.pat.isNone()) {
            if (pattern_matching.bindingTypeInPattern(self, ast_unit, context.pat.unwrap(), name, context.subject_ty)) |bt|
                return bt;
        }
    }
    return null;
}

fn pushValueReq(self: *Checker, ctx: *CheckerContext, v: bool) !void {
    try ctx.value_ctx.append(self.gpa, v);
}
fn popValueReq(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.value_ctx.items.len > 0) _ = ctx.value_ctx.pop();
}
pub fn isValueReq(_: *const Checker, ctx: *CheckerContext) bool {
    if (ctx.value_ctx.items.len == 0) return true; // default: value required
    return ctx.value_ctx.items[ctx.value_ctx.items.len - 1];
}

pub fn lookup(_: *Checker, ctx: *CheckerContext, name: ast.StrId) ?symbols.SymbolId {
    return ctx.symtab.lookup(ctx.symtab.currentId(), name);
}

fn loopCtxForLabel(_: *Checker, ctx: *CheckerContext, opt_label: ast.OptStrId) ?*LoopCtx {
    if (ctx.loop_stack.items.len == 0) return null;
    const want: ?u32 = if (!opt_label.isNone()) opt_label.unwrap().toRaw() else null;
    var i: isize = @as(isize, @intCast(ctx.loop_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const idx: usize = @intCast(i);
        const lc = &ctx.loop_stack.items[idx];
        if (want == null) return lc;
        if (!lc.label.isNone() and lc.label.unwrap().toRaw() == want.?) return lc;
    }
    return null;
}

// =========================================================
// Declarations & Statements
// =========================================================
fn checkDecl(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, decl_id: ast.DeclId) !void {
    // pattern : expect_ty = value
    const decl = ast_unit.exprs.Decl.get(decl_id);

    // Predeclare local bindings in the current scope so subsequent statements can reference them.
    if (!decl.pattern.isNone()) {
        try pattern_matching.declareBindingsInPattern(self, ctx, ast_unit, decl.pattern.unwrap(), decl.loc, .{ .decl = decl_id });
    }

    // Expected type from type annotation (if any)
    const expect_ty = if (decl.ty.isNone())
        null
    else
        (try check_types.typeFromTypeExpr(self, ctx, ast_unit, decl.ty.unwrap()))[1];

    // Method registration happens in runAst() pre-pass.

    // Initializers must be evaluated in value context even inside statement blocks
    try self.pushValueReq(ctx, true);
    const rhs_ty = try self.checkExpr(ctx, ast_unit, decl.value);
    self.popValueReq(ctx);

    if (self.typeKind(rhs_ty) == .TypeError) return;

    // Try to coerce value type to expected type (if any)
    try self.tryTypeCoercion(ctx, ast_unit, decl_id, rhs_ty, expect_ty);

    // If LHS is a pattern, ensure the RHS type matches the pattern's shape.
    if (!decl.pattern.isNone()) {
        const shape_ok = pattern_matching.checkPatternShapeForDecl(self, ast_unit, decl.pattern.unwrap(), rhs_ty);
        switch (shape_ok) {
            .ok => {},
            .tuple_arity_mismatch => {
                try self.context.diags.addError(exprLoc(ast_unit, decl), .tuple_arity_mismatch, .{});
                return;
            },
            .struct_pattern_field_mismatch => {
                try self.context.diags.addError(exprLoc(ast_unit, decl), .struct_pattern_field_mismatch, .{});
                return;
            },
            .pattern_shape_mismatch => {
                try self.context.diags.addError(exprLoc(ast_unit, decl), .pattern_shape_mismatch, .{});
                return;
            },
        }
    }

    // Record exports for top-level bindings only (not inside functions).
    if (!self.inFunction(ctx)) {
        // Prefer finalized decl type if present (post-coercion), otherwise use rhs type.
        const final_rhs_ty =
            if (ast_unit.type_info.decl_types.items[decl_id.toRaw()]) |t| t else rhs_ty;
        try self.recordExportsForDecl(ctx, ast_unit, decl_id, final_rhs_ty);
    }
}

fn recordExportsForDecl(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    decl_id: ast.DeclId,
    value_ty: types.TypeId,
) !void {
    const decl = ast_unit.exprs.Decl.get(decl_id);
    if (decl.pattern.isNone()) return;

    // Use already-declared bindings in the current scope to avoid re-walking the pattern.
    const scope_id = ctx.symtab.currentId();
    const scope_row = ctx.symtab.scopes.get(scope_id);

    // Gather candidates from finalized pool
    const pool_ids = ctx.symtab.sym_pool.slice(scope_row.symbols);
    for (pool_ids) |sid| {
        const srow = ctx.symtab.syms.get(sid);
        if (!srow.origin_decl.isNone() and srow.origin_decl.unwrap().eq(decl_id)) {
            const nm = srow.name;
            const bty = pattern_matching.bindingTypeInPattern(self, ast_unit, decl.pattern.unwrap(), nm, value_ty) orelse value_ty;
            // Export debug print silenced for cleaner checker output
            // const filename = self.context.source_manager.get(@intCast(ast_unit.file_id)) orelse "unknown";
            // std.debug.print("!!! EXPORTING {s} from {s}\n", .{ getStr(ast_unit, nm), filename });
            try ast_unit.type_info.addExport(nm, bty, decl_id);
        }
    }

    // Also include any not-yet-finalized symbols in the active frame for this scope (mirrors lookup).
    for (ctx.symtab.stack.items) |frame| {
        if (!frame.id.eq(scope_id)) continue;
        for (frame.list.items) |sid| {
            const srow = ctx.symtab.syms.get(sid);
            if (!srow.origin_decl.isNone() and srow.origin_decl.unwrap().eq(decl_id)) {
                const nm = srow.name;
                const bty = pattern_matching.bindingTypeInPattern(self, ast_unit, decl.pattern.unwrap(), nm, value_ty) orelse value_ty;
                // const filename = self.context.source_manager.get(@intCast(ast_unit.file_id)) orelse "unknown";
                // std.debug.print("!!! EXPORTING {s} from {s} (from active frame)\n", .{ getStr(ast_unit, nm), filename });
                try ast_unit.type_info.addExport(nm, bty, decl_id);
            }
        }
        break;
    }
}

fn registerMethodDecl(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    decl_id: ast.DeclId,
    decl: ast.Rows.Decl,
    fn_ty: types.TypeId,
) !bool {
    const seg_range = decl.method_path.asRange();
    const seg_ids = ast_unit.exprs.method_path_pool.slice(seg_range);
    if (seg_ids.len < 2) return false;

    const owner_seg = ast_unit.exprs.MethodPathSeg.get(seg_ids[0]);
    if (seg_ids.len != 2) {
        try self.context.diags.addError(ast_unit.exprs.locs.get(owner_seg.loc), .method_invalid_owner_path, .{});
        return false;
    }

    const method_seg = ast_unit.exprs.MethodPathSeg.get(seg_ids[seg_ids.len - 1]);

    const owner_sym_id = self.lookup(ctx, owner_seg.name) orelse {
        try self.context.diags.addError(ast_unit.exprs.locs.get(owner_seg.loc), .undefined_identifier, .{});
        return false;
    };
    const owner_sym = ctx.symtab.syms.get(owner_sym_id);
    if (owner_sym.origin_decl.isNone()) {
        try self.context.diags.addError(ast_unit.exprs.locs.get(owner_seg.loc), .method_owner_not_struct, .{});
        return false;
    }
    const owner_decl_id = owner_sym.origin_decl.unwrap();

    var owner_ty = if (ast_unit.type_info.decl_types.items[owner_decl_id.toRaw()]) |t| t else blk: {
        const owner_decl = ast_unit.exprs.Decl.get(owner_decl_id);
        const ty = try self.checkExpr(ctx, ast_unit, owner_decl.value);
        if (self.typeKind(ty) == .TypeError) return false;
        ast_unit.type_info.decl_types.items[owner_decl_id.toRaw()] = ty;
        break :blk ty;
    };
    if (self.typeKind(owner_ty) == .TypeType) {
        owner_ty = self.context.type_store.get(.TypeType, owner_ty).of;
    }
    const owner_kind = self.typeKind(owner_ty);
    switch (owner_kind) {
        .Struct, .Union, .Enum, .Variant, .Error => {},
        else => {
            try self.context.diags.addError(ast_unit.exprs.locs.get(owner_seg.loc), .method_owner_not_struct, .{});
            return false;
        },
    }

    if (self.typeKind(fn_ty) != .Function) {
        try self.context.diags.addError(exprLoc(ast_unit, decl), .method_requires_function_value, .{});
        return false;
    }
    if (exprKind(ast_unit, decl.value) != .FunctionLit) {
        try self.context.diags.addError(exprLoc(ast_unit, decl), .method_requires_function_value, .{});
        return false;
    }

    const fn_lit = getExpr(ast_unit, .FunctionLit, decl.value);
    const params = ast_unit.exprs.param_pool.slice(fn_lit.params);
    const fn_row = self.context.type_store.get(.Function, fn_ty);
    const fn_params = self.context.type_store.type_pool.slice(fn_row.params);

    var receiver_kind: types.MethodReceiverKind = .none;
    var self_param_type_opt: ?types.TypeId = null;

    if (params.len > 0 and fn_params.len > 0) {
        const first_param_id = params[0];
        const first_param = ast_unit.exprs.Param.get(first_param_id);
        const param_loc = ast_unit.exprs.locs.get(first_param.loc);
        var is_self_binding = false;
        if (!first_param.pat.isNone()) {
            const pat_id = first_param.pat.unwrap();
            if (ast_unit.pats.index.kinds.items[pat_id.toRaw()] == .Binding) {
                const binding = ast_unit.pats.get(.Binding, pat_id);
                if (std.mem.eql(u8, getStr(ast_unit, binding.name), "self")) {
                    is_self_binding = true;
                }
            }
        }

        if (is_self_binding) {
            if (first_param.ty.isNone()) {
                try self.context.diags.addError(param_loc, .method_self_requires_type, .{});
                return false;
            }

            const self_param_ty = fn_params[0];
            const self_param_kind = self.typeKind(self_param_ty);
            switch (self_param_kind) {
                .Ptr => {
                    const ptr_row = self.context.type_store.get(.Ptr, self_param_ty);
                    if (!ptr_row.elem.eq(owner_ty)) {
                        try self.context.diags.addError(param_loc, .method_self_type_mismatch, .{});
                        return false;
                    }
                    receiver_kind = if (ptr_row.is_const)
                        .pointer_const
                    else
                        .pointer;
                },
                else => {
                    if (!self_param_ty.eq(owner_ty)) {
                        try self.context.diags.addError(param_loc, .method_self_type_mismatch, .{});
                        return false;
                    }
                    receiver_kind = .value;
                },
            }

            self_param_type_opt = self_param_ty;
        }
    }

    const entry: types.MethodEntry = .{
        .owner_type = owner_ty,
        .method_name = method_seg.name,
        .decl_id = decl_id,
        .decl_ast = ast_unit,
        .func_expr = decl.value,
        .func_type = fn_ty,
        .self_param_type = self_param_type_opt,
        .receiver_kind = receiver_kind,
        .builtin = null,
    };
    if (!try self.context.type_store.addMethod(entry)) {
        try self.context.diags.addError(
            ast_unit.exprs.locs.get(method_seg.loc),
            .duplicate_method_on_type,
            .{getStr(ast_unit, method_seg.name)},
        );
        return false;
    }

    return true;
}

const AssignErrors = enum {
    array_length_mismatch,
    tuple_arity_mismatch,
    assign_null_to_non_optional,
    pointer_type_mismatch,
    pointer_constness_violation,
    expected_array_type,
    expected_tuple_type,
    expected_map_type,
    expected_pointer_type,
    expected_integer_type,
    expected_float_type,
    expected_enum_type,
    map_wrong_key_type,
    type_value_mismatch,
    noreturn_not_storable,
    expected_struct_type,
    struct_field_count_mismatch,
    unknown_struct_field,
    struct_field_name_mismatch,
    union_literal_multiple_fields,
    union_empty_literal,
    expected_tensor_type,
    tensor_rank_mismatch,
    tensor_dimension_mismatch,
    tensor_element_type_mismatch,
    failure,
    success,
};

pub fn assignable(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    if (got.eq(expect)) return .success;
    const got_kind = self.typeKind(got);
    const expected_kind = self.typeKind(expect);
    if (expected_kind == .Any or got_kind == .Any) return .success;

    if (got_kind == .Undef) {
        return switch (expected_kind) {
            .Noreturn => .noreturn_not_storable,
            else => .success,
        };
    }

    // Assigning `null` (modeled as Optional(Any)) to a non-optional target should error clearly.
    if (got_kind == .Optional and expected_kind != .Optional) {
        const got_opt = self.context.type_store.get(.Optional, got);
        const elem_kind = self.typeKind(got_opt.elem);
        if (elem_kind == .Any) return .assign_null_to_non_optional;
        // Implicit unwrap from Optional(T) -> T is not permitted.
        return .failure;
    }

    switch (expected_kind) {
        .Slice => {
            if (got_kind != .Slice) return .failure;
            const expected_ty = self.context.type_store.get(.Slice, expect);
            const got_ty = self.context.type_store.get(.Slice, got);
            return self.assignable(got_ty.elem, expected_ty.elem);
        },
        .Array => {
            if (got_kind != .Array) return .expected_array_type;
            const expected_ty = self.context.type_store.get(.Array, expect);
            const got_ty = self.context.type_store.get(.Array, got);
            const elem_ok = self.assignable(got_ty.elem, expected_ty.elem);
            const len_match = blk: {
                switch (expected_ty.len) {
                    .Concrete => |l1| switch (got_ty.len) {
                        .Concrete => |l2| break :blk l1 == l2,
                        .Unresolved => break :blk true, // compatible for now
                    },
                    .Unresolved => break :blk true, // compatible for now
                }
            };
            if (!len_match) return .array_length_mismatch;
            return elem_ok;
        },
        .DynArray => {
            // BUGFIX: allow assigning from DynArray itself AND from Array/Slice (element-compatible).
            const expected_ty = self.context.type_store.get(.DynArray, expect);
            switch (got_kind) {
                .DynArray => {
                    const got_ty = self.context.type_store.get(.DynArray, got);
                    return self.assignable(got_ty.elem, expected_ty.elem);
                },
                .Array => {
                    const got_ty = self.context.type_store.get(.Array, got);
                    return self.assignable(got_ty.elem, expected_ty.elem);
                },
                .Slice => {
                    const got_ty = self.context.type_store.get(.Slice, got);
                    return self.assignable(got_ty.elem, expected_ty.elem);
                },
                else => return .expected_array_type,
            }
        },
        .Tuple => {
            if (got_kind != .Tuple) return .expected_tuple_type;
            const expected_ty = self.context.type_store.get(.Tuple, expect);
            const got_ty = self.context.type_store.get(.Tuple, got);
            if (expected_ty.elems.len != got_ty.elems.len) return .tuple_arity_mismatch;
            const got_elems = self.context.type_store.type_pool.slice(got_ty.elems);
            const expected_elems = self.context.type_store.type_pool.slice(expected_ty.elems);
            for (expected_elems, 0..) |et, i| {
                const gt = got_elems[i];
                const res = self.assignable(gt, et);
                if (res != .success) return res;
            }
            return .success;
        },
        .Map => {
            // Allow "empty array" sugar to coerce to any map type.
            if (got_kind == .Array) {
                const got_ty = self.context.type_store.get(.Array, got);
                const is_zero = switch (got_ty.len) {
                    .Concrete => |l| l == 0,
                    .Unresolved => false,
                };
                if (!is_zero) return .expected_map_type;
                return .success;
            }
            if (got_kind != .Map) return .expected_map_type;
            const expected_ty = self.context.type_store.get(.Map, expect);
            const got_ty = self.context.type_store.get(.Map, got);
            const key_ok = self.assignable(got_ty.key, expected_ty.key);
            const value_ok = self.assignable(got_ty.value, expected_ty.value);
            if (key_ok != .success) return .map_wrong_key_type;
            if (value_ok != .success) return value_ok;
            return .success;
        },
        .Simd => {
            const expected_ty = self.context.type_store.get(.Simd, expect);
            switch (got_kind) {
                .Simd => {
                    const got_ty = self.context.type_store.get(.Simd, got);
                    if (got_ty.lanes != expected_ty.lanes) return .array_length_mismatch;
                    return self.assignable(got_ty.elem, expected_ty.elem);
                },
                .Array => {
                    const got_ty = self.context.type_store.get(.Array, got);
                    const len_ok = switch (got_ty.len) {
                        .Concrete => |l| l == expected_ty.lanes,
                        .Unresolved => false,
                    };
                    if (!len_ok) return .array_length_mismatch;
                    return self.assignable(got_ty.elem, expected_ty.elem);
                },
                else => return .failure,
            }
        },
        .Tensor => {
            const expected_ty = self.context.type_store.get(.Tensor, expect);
            const expected_rank: usize = @intCast(expected_ty.rank);
            switch (got_kind) {
                .Tensor => {
                    const got_ty = self.context.type_store.get(.Tensor, got);
                    if (got_ty.rank != expected_ty.rank) return .tensor_rank_mismatch;
                    var i: usize = 0;
                    while (i < expected_rank) : (i += 1) {
                        if (got_ty.dims[i] != expected_ty.dims[i]) return .tensor_dimension_mismatch;
                    }
                    return self.assignable(got_ty.elem, expected_ty.elem);
                },
                .Array => {
                    var dims_buf = [_]usize{0} ** types.max_tensor_rank;
                    var rank: usize = 0;
                    var current_ty = got;
                    var current_kind = got_kind;
                    var elem_ty = got;
                    while (current_kind == .Array) : (rank += 1) {
                        if (rank >= types.max_tensor_rank) return .tensor_rank_mismatch;
                        const arr = self.context.type_store.get(.Array, current_ty);
                        dims_buf[rank] = switch (arr.len) {
                            .Concrete => |l| l,
                            .Unresolved => return .failure,
                        };
                        elem_ty = arr.elem;
                        current_ty = arr.elem;
                        current_kind = self.typeKind(current_ty);
                    }
                    if (rank == 0) return .expected_tensor_type;
                    if (rank != expected_rank) return .tensor_rank_mismatch;
                    var j: usize = 0;
                    while (j < expected_rank) : (j += 1) {
                        if (dims_buf[j] != expected_ty.dims[j]) return .tensor_dimension_mismatch;
                    }
                    return self.assignable(elem_ty, expected_ty.elem);
                },
                else => return .expected_tensor_type,
            }
        },
        .Optional => {
            const expected_ty = self.context.type_store.get(.Optional, expect);
            if (got_kind == .Optional) {
                const got_ty = self.context.type_store.get(.Optional, got);
                return self.assignable(got_ty.elem, expected_ty.elem);
            }
            return self.assignable(got, expected_ty.elem);
        },
        .Ptr => {
            if (got_kind != .Ptr) return .expected_pointer_type;
            const expected_ty = self.context.type_store.get(.Ptr, expect);
            const got_ty = self.context.type_store.get(.Ptr, got);
            if (!expected_ty.is_const and got_ty.is_const) {
                return .pointer_constness_violation;
            }
            if (self.assignable(got_ty.elem, expected_ty.elem) != .success) {
                return .pointer_type_mismatch;
            }
            return .success;
        },
        .TypeType => {
            if (got_kind != .TypeType) return .type_value_mismatch;
            return .success;
        },
        .Noreturn => return .noreturn_not_storable,
        .Union => {
            if (got_kind != .Struct) return .expected_struct_type;
            const expected_ty = self.context.type_store.get(.Union, expect);
            const got_ty = self.context.type_store.get(.Struct, got);
            const expected_fields = self.context.type_store.field_pool.slice(expected_ty.fields);
            const got_fields = self.context.type_store.field_pool.slice(got_ty.fields);
            // Should only have one field set in union
            if (got_fields.len == 0) return .union_empty_literal;
            if (got_fields.len != 1) return .union_literal_multiple_fields;
            const gf = self.context.type_store.Field.get(got_fields[0]);
            var found = false;
            for (expected_fields) |efid| {
                const ef = self.context.type_store.Field.get(efid);
                if (ef.name.toRaw() == gf.name.toRaw()) {
                    found = true;
                    const res = self.assignable(gf.ty, ef.ty);
                    if (res != .success) return res;
                    break;
                }
            }
            if (!found) return .unknown_struct_field;
            return .success;
        },
        .Struct => {
            if (got_kind != .Struct) return .expected_struct_type;
            const expected_ty = self.context.type_store.get(.Struct, expect);
            const got_ty = self.context.type_store.get(.Struct, got);
            const expected_fields = self.context.type_store.field_pool.slice(expected_ty.fields);
            const got_fields = self.context.type_store.field_pool.slice(got_ty.fields);
            if (expected_fields.len < got_fields.len) return .unknown_struct_field;
            if (expected_fields.len > got_fields.len) return .struct_field_count_mismatch;

            // Check fields by name, not by order.
            for (expected_fields) |efid| {
                const ef = self.context.type_store.Field.get(efid);
                var found = false;
                for (got_fields) |gfid| {
                    const gf = self.context.type_store.Field.get(gfid);
                    if (ef.name.toRaw() == gf.name.toRaw()) {
                        found = true;
                        const res = self.assignable(gf.ty, ef.ty);
                        if (res != .success) return res;
                        break;
                    }
                }
                if (!found) return .struct_field_name_mismatch;
            }
            return .success;
        },
        .Enum => {
            if (got_kind != .Enum) return .expected_enum_type;
            if (!got.eq(expect)) return .failure;
            return .success;
        },
        .Function => {
            if (got_kind != .Function) return .failure;
            // const efn = self.context.type_store.get(.Function, expect);
            // const gfn = self.context.type_store.get(.Function, got);
            // if (efn.is_variadic != gfn.is_variadic) return .failure;
            // const eparams = self.context.type_store.type_pool.slice(efn.params);
            // const gparams = self.context.type_store.type_pool.slice(gfn.params);
            // if (eparams.len != gparams.len) return .failure;
            // var i: usize = 0;
            // while (i < eparams.len) : (i += 1) {
            //     if (!eparams[i].eq(gparams[i])) return .failure;
            // }
            // if (!efn.result.eq(gfn.result)) return .failure;
            // if (efn.is_pure and !gfn.is_pure) return .failure;
            return .success;
        },
        .ErrorSet => {
            const expected_ty = self.context.type_store.get(.ErrorSet, expect);
            if (got_kind == .Error) {
                return self.assignable(got, expected_ty.error_ty);
            } else {
                return self.assignable(got, expected_ty.value_ty);
            }
        },
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => {
            if (!check_types.isIntegerKind(self, got_kind)) return .expected_integer_type;
            return .success;
        },
        .F32, .F64 => {
            if (got_kind != .F32 and got_kind != .F64) return .expected_float_type;
            return .success;
        },
        else => {},
    }

    return .failure;
}

fn typeInferFromRHS(self: *Checker, ast_unit: *ast.Ast, decl_id: ast.DeclId, rhs_ty: types.TypeId) !void {
    const decl = ast_unit.exprs.Decl.get(decl_id);
    // Degenerate cases where we don't infer from RHS
    const rhs_kind = self.typeKind(rhs_ty);
    switch (rhs_kind) {
        .Array => {
            const arr = self.context.type_store.get(.Array, rhs_ty);
            const is_zero = switch (arr.len) {
                .Concrete => |l| l == 0,
                .Unresolved => false,
            };
            if (is_zero)
                try self.context.diags.addError(
                    exprLoc(ast_unit, ast_unit.exprs.Decl.get(decl_id)),
                    .cannot_infer_type_from_empty_array,
                    .{},
                );
        },
        else => {
            ast_unit.type_info.decl_types.items[decl_id.toRaw()] = rhs_ty;
            ast_unit.type_info.expr_types.items[decl.value.toRaw()] = rhs_ty;
        },
    }
}

fn updateCoercedLiteral(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    target_ty: types.TypeId,
    value_ty: *types.TypeId,
    kind: *types.TypeKind,
) !bool {
    if (!try self.coerceNumericLiteral(ast_unit, expr_id, target_ty)) return false;
    if (ast_unit.type_info.expr_types.items[expr_id.toRaw()]) |coerced| {
        value_ty.* = coerced;
    } else {
        value_ty.* = target_ty;
    }
    kind.* = self.typeKind(value_ty.*);
    return true;
}

// Determine if an expression is a comptime numeric expression (integer or float).
const ConstNumKind = enum { none, int, float };

fn constNumericKind(self: *Checker, ast_unit: *ast.Ast, expr_id: ast.ExprId) ConstNumKind {
    switch (exprKind(ast_unit, expr_id)) {
        .Literal => {
            const lit = getExpr(ast_unit, .Literal, expr_id);
            return switch (lit.kind) {
                .int => .int,
                .float => .float,
                else => .none,
            };
        },
        .Unary => {
            const u = getExpr(ast_unit, .Unary, expr_id);
            switch (u.op) {
                .pos, .neg => return self.constNumericKind(ast_unit, u.expr),
                else => return .none,
            }
        },
        .Binary => {
            const b = getExpr(ast_unit, .Binary, expr_id);
            const is_arith = b.op == .add or b.op == .sub or b.op == .mul or b.op == .div or b.op == .mod;
            if (!is_arith) return .none;
            const lk = self.constNumericKind(ast_unit, b.left);
            if (lk == .none) return .none;
            const rk = self.constNumericKind(ast_unit, b.right);
            if (rk == .none) return .none;
            if (b.op == .mod) {
                return if (lk == .int and rk == .int) .int else .none;
            }
            return if (lk == .float or rk == .float) .float else .int;
        },
        else => return .none,
    }
}

fn coerceComptimeNumericExpr(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    target_ty: types.TypeId,
) !bool {
    const kind = self.constNumericKind(ast_unit, expr_id);
    if (kind == .none) return false;
    const target_kind = self.typeKind(target_ty);
    // Allow coercion to float targets; avoid unsafe integer range assumptions for now.
    return switch (target_kind) {
        .F32, .F64 => blk: {
            ast_unit.type_info.setExprType(expr_id, target_ty);
            break :blk true;
        },
        else => false,
    };
}

fn updateCoercedConstNumeric(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    target_ty: types.TypeId,
    value_ty: *types.TypeId,
    kind: *types.TypeKind,
) !bool {
    if (!try self.coerceComptimeNumericExpr(ast_unit, expr_id, target_ty)) return false;
    if (ast_unit.type_info.expr_types.items[expr_id.toRaw()]) |coerced| {
        value_ty.* = coerced;
    } else {
        value_ty.* = target_ty;
    }
    kind.* = self.typeKind(value_ty.*);
    return true;
}

fn coerceNumericLiteral(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    target_ty: types.TypeId,
) !bool {
    if (exprKind(ast_unit, expr_id) != .Literal) return false;
    const lit = getExpr(ast_unit, .Literal, expr_id);
    const target_kind = self.typeKind(target_ty);
    return switch (lit.kind) {
        .int => coerceIntLiteral(ast_unit, expr_id, target_ty, target_kind, lit),
        .float => coerceFloatLiteral(ast_unit, expr_id, target_ty, target_kind, lit),
        .imaginary => self.coerceImaginaryLiteral(ast_unit, expr_id, target_ty, target_kind, lit),
        else => false,
    };
}

fn coerceIntLiteral(
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    target_ty: types.TypeId,
    target_kind: types.TypeKind,
    lit: ast.Rows.Literal,
) bool {
    const info = switch (lit.data) {
        .int => |i| i,
        else => return false,
    };
    if (!info.valid) return false;

    const value = info.value;
    const ok = switch (target_kind) {
        .I8 => value <= blk: {
            const max: u128 = @intCast(std.math.maxInt(i8));
            break :blk max;
        },
        .I16 => value <= blk: {
            const max: u128 = @intCast(std.math.maxInt(i16));
            break :blk max;
        },
        .I32 => value <= blk: {
            const max: u128 = @intCast(std.math.maxInt(i32));
            break :blk max;
        },
        .I64 => value <= blk: {
            const max: u128 = @intCast(std.math.maxInt(i64));
            break :blk max;
        },
        .U8 => value <= blk: {
            const max: u128 = @intCast(std.math.maxInt(u8));
            break :blk max;
        },
        .U16 => value <= blk: {
            const max: u128 = @intCast(std.math.maxInt(u16));
            break :blk max;
        },
        .U32 => value <= blk: {
            const max: u128 = @intCast(std.math.maxInt(u32));
            break :blk max;
        },
        .U64 => value <= blk: {
            const max: u128 = @intCast(std.math.maxInt(u64));
            break :blk max;
        },
        .Usize => value <= blk: {
            const max: u128 = @intCast(std.math.maxInt(usize));
            break :blk max;
        },
        .F32 => blk: {
            const limit: f128 = @floatCast(std.math.floatMax(f32));
            const as_float: f128 = @floatFromInt(value);
            break :blk as_float <= limit;
        },
        .F64 => true,
        else => false,
    };

    if (!ok) return false;
    ast_unit.type_info.setExprType(expr_id, target_ty);
    return true;
}

fn coerceFloatLiteral(
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    target_ty: types.TypeId,
    target_kind: types.TypeKind,
    lit: ast.Rows.Literal,
) bool {
    const info = switch (lit.data) {
        .float => |f| f,
        else => return false,
    };
    if (!info.valid) return false;

    const value = info.value;
    const ok = switch (target_kind) {
        .F32 => blk: {
            if (!std.math.isFinite(value)) break :blk false;
            const limit: f64 = @floatCast(std.math.floatMax(f32));
            break :blk @abs(value) <= limit;
        },
        .F64 => std.math.isFinite(value),
        else => false,
    };

    if (!ok) return false;
    ast_unit.type_info.setExprType(expr_id, target_ty);
    return true;
}

fn coerceImaginaryLiteral(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    target_ty: types.TypeId,
    target_kind: types.TypeKind,
    lit: ast.Rows.Literal,
) bool {
    if (target_kind != .Complex) return false;
    const info = switch (lit.data) {
        .imaginary => |imag| imag,
        else => return false,
    };
    if (!info.valid) return false;

    const target = self.context.type_store.get(.Complex, target_ty);
    const elem_ty = target.elem;
    const elem_kind = self.typeKind(elem_ty);
    const ok = switch (elem_kind) {
        .F32 => blk: {
            if (!std.math.isFinite(info.value)) break :blk false;
            const limit: f64 = @floatCast(std.math.floatMax(f32));
            break :blk @abs(info.value) <= limit;
        },
        .F64 => std.math.isFinite(info.value),
        else => false,
    };

    if (!ok) return false;
    ast_unit.type_info.setExprType(expr_id, target_ty);
    return true;
}

fn tryCoerceVariantOrErrorLiteral(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    expect_ty: types.TypeId,
) !bool {
    const value_kind = exprKind(ast_unit, expr_id);
    return switch (value_kind) {
        .Call => blk: { // Path 1: V.C(...) form
            const call = getExpr(ast_unit, .Call, expr_id);
            break :blk try self.tryCoerceCallLike(ctx, ast_unit, &call, expect_ty);
        },
        .StructLit => blk: { // Path 2: V.C{ ... } form
            const struct_lit = getExpr(ast_unit, .StructLit, expr_id);
            break :blk try self.tryCoerceStructLitLike(ctx, ast_unit, &struct_lit, expect_ty);
        },
        else => false,
    };
}

fn tryCoerceCallLike(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    call_like: *const ast.Rows.Call,
    expect_ty: types.TypeId,
) !bool {
    var cur = call_like.callee;
    var last: ?ast.StrId = null;
    while (exprKind(ast_unit, cur) == .FieldAccess) {
        const fr = getExpr(ast_unit, .FieldAccess, cur);
        last = fr.field;
        cur = fr.parent;
    }
    if (last) |lname| {
        if (self.getPayloadTypeForCase(expect_ty, lname)) |pay_ty| {
            return try self.checkCallArgsAgainstPayload(ctx, ast_unit, pay_ty, call_like);
        }
    }
    return false;
}

fn tryCoerceStructLitLike(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    sl: *const ast.Rows.StructLit,
    expect_ty: types.TypeId,
) !bool {
    if (sl.ty.isNone()) return false;

    var cur = sl.ty.unwrap();
    var last: ?ast.StrId = null;
    while (exprKind(ast_unit, cur) == .FieldAccess) {
        const fr = getExpr(ast_unit, .FieldAccess, cur);
        last = fr.field;
        cur = fr.parent;
    }
    if (last) |lname| {
        if (self.getPayloadTypeForCase(expect_ty, lname)) |pay_ty| {
            return try self.checkStructLitAgainstPayload(ctx, ast_unit, pay_ty, sl);
        }
    }
    return false;
}

fn getPayloadTypeForCase(
    self: *Checker,
    expect_ty: types.TypeId,
    lname: ast.StrId,
) ?types.TypeId {
    const ek = self.context.type_store.getKind(expect_ty);
    const cases = if (ek == .Variant)
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, expect_ty).variants)
    else
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, expect_ty).variants);

    for (cases) |fid| {
        const f = self.context.type_store.Field.get(fid);
        if (f.name.eq(lname)) return f.ty;
    }
    return null;
}

fn checkCallArgsAgainstPayload(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    pay_ty: types.TypeId,
    call: *const ast.Rows.Call,
) !bool {
    const k = self.context.type_store.getKind(pay_ty);

    if (k == .Tuple) {
        const tr = self.context.type_store.get(.Tuple, pay_ty);
        const tys = self.context.type_store.type_pool.slice(tr.elems);
        const args = ast_unit.exprs.expr_pool.slice(call.args);
        if (args.len != tys.len) return false;

        for (args, 0..) |aid, i| {
            // Arguments must be evaluated in value context
            try self.pushValueReq(ctx, true);
            var at = try self.checkExpr(ctx, ast_unit, aid);
            self.popValueReq(ctx);
            if (self.typeKind(at) == .TypeError) return false;
            if (self.assignable(at, tys[i]) != .success) {
                if (check_types.isNumericKind(self, self.typeKind(tys[i]))) {
                    var at_kind = self.typeKind(at);
                    if (try self.updateCoercedLiteral(ast_unit, aid, tys[i], &at, &at_kind) and
                        self.assignable(at, tys[i]) == .success)
                    {
                        continue;
                    }
                }
                return false;
            }
        }
        return true;
    }

    if (k == .Void) {
        return ast_unit.exprs.expr_pool.slice(call.args).len == 0;
    }

    // Single payload
    const args = ast_unit.exprs.expr_pool.slice(call.args);
    if (args.len != 1) return false;

    try self.pushValueReq(ctx, true);
    var at = try self.checkExpr(ctx, ast_unit, args[0]);
    self.popValueReq(ctx);
    if (self.typeKind(at) == .TypeError) return false;
    if (self.assignable(at, pay_ty) == .success) return true;
    if (check_types.isNumericKind(self, self.typeKind(pay_ty))) {
        var at_kind = self.typeKind(at);
        if (try self.updateCoercedLiteral(ast_unit, args[0], pay_ty, &at, &at_kind)) {
            return self.assignable(at, pay_ty) == .success;
        }
    }
    return false;
}

fn checkStructLitAgainstPayload(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    pay_ty: types.TypeId,
    sl: *const ast.Rows.StructLit,
) !bool {
    if (self.context.type_store.getKind(pay_ty) != .Struct) return false;

    const st = self.context.type_store.get(.Struct, pay_ty);
    const tfields = self.context.type_store.field_pool.slice(st.fields);
    const vfields = ast_unit.exprs.sfv_pool.slice(sl.fields);

    for (vfields) |sfid| {
        const sf = ast_unit.exprs.StructFieldValue.get(sfid);
        if (sf.name.isNone()) return false;

        const nm = sf.name.unwrap();
        var want: ?types.TypeId = null;

        // Find matching target field
        for (tfields) |tfid| {
            const tf = self.context.type_store.Field.get(tfid);
            if (tf.name.eq(nm)) {
                want = tf.ty;
                break;
            }
        }
        if (want == null) return false;

        // Type-check value against target field type
        var at = try self.checkExpr(ctx, ast_unit, sf.value);
        if (self.typeKind(at) == .TypeError) return false;
        if (self.assignable(at, want.?) != .success) {
            if (check_types.isNumericKind(self, self.typeKind(want.?))) {
                var at_kind = self.typeKind(at);
                if (try self.updateCoercedLiteral(ast_unit, sf.value, want.?, &at, &at_kind) and
                    self.assignable(at, want.?) == .success)
                {
                    continue;
                }
            }
            return false;
        }
    }

    return true;
}

fn tryTypeCoercion(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    decl_id: ast.DeclId,
    rhs_ty: types.TypeId,
    expect_ty: ?types.TypeId,
) !void {
    if (expect_ty == null) {
        try self.typeInferFromRHS(ast_unit, decl_id, rhs_ty);
        return;
    }

    // First, check direct assignability
    var current_rhs_ty = rhs_ty;
    var is_assignable = self.assignable(current_rhs_ty, expect_ty.?);

    const decl = ast_unit.exprs.Decl.get(decl_id);
    if (is_assignable != .success and
        check_types.isNumericKind(self, self.typeKind(expect_ty.?)))
    {
        var coerced = current_rhs_ty;
        var coerced_kind = self.typeKind(coerced);
        if (try self.updateCoercedLiteral(ast_unit, decl.value, expect_ty.?, &coerced, &coerced_kind)) {
            current_rhs_ty = coerced;
            is_assignable = self.assignable(current_rhs_ty, expect_ty.?);
        }
    }

    // If that failed, variant/error literals might be of the form V.C(...) or V.C{...}
    if (is_assignable == .failure) {
        const ek = self.context.type_store.getKind(expect_ty.?);
        if (ek == .Variant or ek == .Error) {
            if (try self.tryCoerceVariantOrErrorLiteral(ctx, ast_unit, decl.value, expect_ty.?)) {
                is_assignable = .success;
            }
        }
    }

    // Apply result (and corresponding diagnostics).
    switch (is_assignable) {
        .success => {
            // Use expected type and also update RHS expr type for consistency.
            ast_unit.type_info.decl_types.items[decl_id.toRaw()] = expect_ty.?;
            ast_unit.type_info.expr_types.items[decl.value.toRaw()] = expect_ty.?;
        },
        .failure => try self.context.diags.addError(exprLoc(ast_unit, decl), .type_annotation_mismatch, .{}),
        inline else => |x| {
            const diag_code = @field(diag.DiagnosticCode, @tagName(x));
            try self.context.diags.addError(exprLoc(ast_unit, decl), diag_code, .{});
        },
    }
}

fn checkAssign(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    stmt: *const ast.StmtRows.Assign,
) !void {
    // Handle `_ = rhs` as a special discard operation.
    if (exprKind(ast_unit, stmt.left) == .Ident) {
        const ident = getExpr(ast_unit, .Ident, stmt.left);
        const name = ast_unit.exprs.strs.get(ident.name);
        if (std.mem.eql(u8, name, "_")) {
            // Check the RHS for side effects, but discard the value.
            // The value of the expression is not required.
            try self.pushValueReq(ctx, false);
            _ = try self.checkExpr(ctx, ast_unit, stmt.right);
            self.popValueReq(ctx);
            return;
        }
    }

    // Pattern-shaped LHS support: tuple/struct/array destructuring
    const lkind = exprKind(ast_unit, stmt.left);
    if (lkind == .TupleLit or lkind == .StructLit or lkind == .ArrayLit) {
        // RHS of assignment should be checked in value context
        try self.pushValueReq(ctx, true);
        const rv_ty = try self.checkExpr(ctx, ast_unit, stmt.right);
        self.popValueReq(ctx);
        if (self.typeKind(rv_ty) != .TypeError) {
            const shape_ok = pattern_matching.checkPatternShapeForAssignExpr(self, ast_unit, stmt.left, rv_ty);
            switch (shape_ok) {
                .ok => {},
                inline else => |x| try self.context.diags.addError(exprLoc(ast_unit, stmt), @field(diag.DiagnosticCode, @tagName(x)), .{}),
            }
        }
    } else {
        const lt = try self.checkExpr(ctx, ast_unit, stmt.left);
        // RHS of assignment should be checked in value context
        try self.pushValueReq(ctx, true);
        const rt = try self.checkExpr(ctx, ast_unit, stmt.right);
        self.popValueReq(ctx);
        if (self.typeKind(lt) != .TypeError and self.typeKind(rt) != .TypeError) {
            const expected = lt;
            var value_ty = rt;
            if (self.assignable(value_ty, expected) != .success) {
                var coerced_ok = false;
                if (check_types.isNumericKind(self, self.typeKind(expected))) {
                    var value_kind = self.typeKind(value_ty);
                    if (try self.updateCoercedLiteral(ast_unit, stmt.right, expected, &value_ty, &value_kind) and
                        self.assignable(value_ty, expected) == .success)
                    {
                        coerced_ok = true;
                    }
                }
                if (!coerced_ok) {
                    try self.context.diags.addError(exprLoc(ast_unit, stmt), .type_annotation_mismatch, .{});
                }
            }
        }
    }
    // Purity: assignment writes inside pure functions are allowed only to locals
    if (self.inFunction(ctx) and self.currentFunc(ctx).?.require_pure) {
        switch (self.lvalueRootKind(ctx, ast_unit, stmt.left)) {
            .LocalDecl => {},
            .Param, .NonLocalDecl, .Unknown => {
                try self.context.diags.addError(exprLoc(ast_unit, stmt), .purity_violation, .{});
                ctx.func_stack.items[ctx.func_stack.items.len - 1].pure = false;
            },
        }
    }
}

fn checkStmt(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, sid: ast.StmtId) !types.TypeId {
    switch (ast_unit.stmts.index.kinds.items[sid.toRaw()]) {
        .Expr => {
            const expr = getStmt(ast_unit, .Expr, sid);
            // Statement expression: no value required
            try self.pushValueReq(ctx, false);
            defer self.popValueReq(ctx);
            _ = try self.checkExpr(ctx, ast_unit, expr.expr);
            return self.context.type_store.tVoid();
        },
        .Decl => {
            const stmt = getStmt(ast_unit, .Decl, sid);
            try self.checkDecl(ctx, ast_unit, stmt.decl);
            if (self.inFunction(ctx)) {
                // record local decl for purity tracking
                const idx = ctx.func_stack.items.len - 1;
                _ = ctx.func_stack.items[idx].locals.put(self.gpa, stmt.decl.toRaw(), {}) catch {};
            }
        },
        .Assign => try self.checkAssign(ctx, ast_unit, &getStmt(ast_unit, .Assign, sid)),
        .Insert => {
            const row = getStmt(ast_unit, .Insert, sid);
            if (!ctx.warned_meta) {
                try self.context.diags.addNote(exprLoc(ast_unit, row), .checker_insert_not_expanded, .{});
                ctx.warned_meta = true;
            }
            _ = try self.checkExpr(ctx, ast_unit, row.expr);
        },
        .Return => {
            const row = getStmt(ast_unit, .Return, sid);
            return try self.checkReturn(ctx, ast_unit, row);
        },
        .Break => return try self.checkBreak(ctx, ast_unit, getStmt(ast_unit, .Break, sid)),
        .Continue => {
            const row = getStmt(ast_unit, .Continue, sid);
            if (!self.inLoop(ctx))
                try self.context.diags.addError(exprLoc(ast_unit, row), .continue_outside_loop, .{});
        },
        .Unreachable => {},
        .Defer => _ = try self.checkDefer(ctx, ast_unit, getStmt(ast_unit, .Defer, sid)),
        .ErrDefer => _ = try self.checkErrDefer(ctx, ast_unit, getStmt(ast_unit, .ErrDefer, sid)),
    }
    return self.context.type_store.tVoid();
}

// =========================================================
// Expressions
// =========================================================
pub fn checkExpr(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) anyerror!types.TypeId {
    if (ast_unit.type_info.expr_types.items[id.toRaw()]) |cached| return cached;

    const k = exprKind(ast_unit, id);

    const tid: types.TypeId = switch (k) {
        .Literal => try self.checkLiteral(ast_unit, id),
        .Ident => try self.checkIdent(ctx, ast_unit, id),
        .Binary => try self.checkBinary(ctx, ast_unit, id),
        .Unary => try self.checkUnary(ctx, ast_unit, id),
        .FunctionLit => try self.checkFunctionLit(ctx, ast_unit, id),
        .ArrayLit => try self.checkArrayLit(ctx, ast_unit, id),
        .TupleLit => try self.checkTupleLit(ctx, ast_unit, id),
        .MapLit => try self.checkMapLit(ctx, ast_unit, id),
        .IndexAccess => try self.checkIndexAccess(ctx, ast_unit, id),
        .FieldAccess => try self.checkFieldAccess(ctx, ast_unit, id),
        .StructLit => try self.checkStructLit(ctx, ast_unit, id),
        .Range => try self.checkRange(ctx, ast_unit, id),
        .Deref => try self.checkDeref(ctx, ast_unit, id),
        .Call => try self.checkCall(ctx, ast_unit, id),
        .ComptimeBlock => {
            const cb = ast_unit.exprs.get(.ComptimeBlock, id);
            return try self.checkExpr(ctx, ast_unit, cb.block);
        },
        .CodeBlock => try self.checkCodeBlock(ctx, ast_unit, id),
        .AsyncBlock => try self.checkAsyncBlock(id),
        .MlirBlock => try self.checkMlirBlock(ctx, ast_unit, id),
        .Insert => try self.checkInsert(ctx, ast_unit, id),
        .Return => try self.checkReturn(ctx, ast_unit, getExpr(ast_unit, .Return, id)),
        .If => try self.checkIf(ctx, ast_unit, id),
        .While => try self.checkWhile(ctx, ast_unit, id),
        .For => try self.checkFor(ctx, ast_unit, id),
        .Match => try pattern_matching.checkMatch(self, ctx, ast_unit, id),
        .Break => try self.checkBreak(ctx, ast_unit, getExpr(ast_unit, .Break, id)),
        .Continue => try self.checkContinue(id),
        .Unreachable => try self.checkUnreachable(id),
        .UndefLit => self.context.type_store.tUndef(),

        .Block => try self.checkBlock(ctx, ast_unit, id),
        .Defer => try self.checkDefer(ctx, ast_unit, getExpr(ast_unit, .Defer, id)),
        .ErrDefer => try self.checkErrDefer(ctx, ast_unit, getExpr(ast_unit, .ErrDefer, id)),
        .ErrUnwrap => try self.checkErrUnwrap(ctx, ast_unit, id),
        .OptionalUnwrap => try self.checkOptionalUnwrap(ctx, ast_unit, id),
        .Await => try self.checkAwait(id),
        .Closure => try self.checkClosure(ctx, ast_unit, id),
        .Cast => try self.checkCast(ctx, ast_unit, id),
        .Catch => try self.checkCatch(ctx, ast_unit, id),
        .Import => try self.checkImport(ast_unit, id),
        .TypeOf => try check_types.checkTypeOf(self, ctx, ast_unit, id),
        .NullLit => self.context.type_store.mkOptional(self.context.type_store.tAny()),

        .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => blk: {
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, id);
            if (!res[0]) break :blk self.context.type_store.tTypeError();
            break :blk self.context.type_store.mkTypeType(res[1]);
        },
        .MapType => blk_mt_expr: {
            // Try to interpret as a type expression first
            const row = getExpr(ast_unit, .MapType, id);
            const key_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, row.key);
            const val_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, row.value);
            if (key_res[0] or val_res[0]) {
                break :blk_mt_expr self.context.type_store.mkTypeType(self.context.type_store.mkMap(key_res[1], val_res[1]));
            }
            // If not valid types, interpret operands as value expressions and produce a map value type
            const key_vt = try self.checkExpr(ctx, ast_unit, row.key);
            const val_vt = try self.checkExpr(ctx, ast_unit, row.value);
            if (self.typeKind(key_vt) == .TypeError or self.typeKind(val_vt) == .TypeError) {
                break :blk_mt_expr self.context.type_store.tTypeError();
            }
            break :blk_mt_expr self.context.type_store.mkMap(key_vt, val_vt);
        },
    };

    ast_unit.type_info.expr_types.items[id.toRaw()] = tid;
    return tid;
}

fn checkLiteral(self: *Checker, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const lit = getExpr(ast_unit, .Literal, id);
    return switch (lit.kind) {
        .int => blk: {
            const info = switch (lit.data) {
                .int => |int_info| int_info,
                else => return self.context.type_store.tTypeError(),
            };
            if (!info.valid) {
                try self.context.diags.addError(exprLoc(ast_unit, lit), .invalid_integer_literal, .{});
                return self.context.type_store.tTypeError();
            }
            const max_i64: u128 = @intCast(std.math.maxInt(i64));
            if (info.value > max_i64) {
                try self.context.diags.addError(exprLoc(ast_unit, lit), .invalid_integer_literal, .{});
                return self.context.type_store.tTypeError();
            }
            break :blk self.context.type_store.tI64();
        },
        .imaginary => blk: {
            const info = switch (lit.data) {
                .imaginary => |imag| imag,
                else => return self.context.type_store.tTypeError(),
            };
            if (!info.valid) {
                try self.context.diags.addError(exprLoc(ast_unit, lit), .invalid_imaginary_literal, .{});
                return self.context.type_store.tTypeError();
            }
            const text = getStr(ast_unit, info.text);
            const has_float_marker = std.mem.indexOfAny(u8, text, ".eEpP") != null;
            var is_int_literal = !has_float_marker;
            if (is_int_literal) {
                var acc: u128 = 0;
                for (text) |c| {
                    switch (c) {
                        '_' => continue,
                        '0'...'9' => {
                            acc = acc * 10 + @as(u128, c - '0');
                            if (acc > std.math.maxInt(i64)) {
                                is_int_literal = false;
                                break;
                            }
                        },
                        else => {
                            is_int_literal = false;
                            break;
                        },
                    }
                }
            }
            const elem_ty = if (is_int_literal)
                self.context.type_store.tI64()
            else
                self.context.type_store.tF64();
            break :blk self.context.type_store.add(.Complex, .{ .elem = elem_ty });
        },
        .float => blk: {
            const info = switch (lit.data) {
                .float => |float_info| float_info,
                else => return self.context.type_store.tTypeError(),
            };
            if (!info.valid) {
                try self.context.diags.addError(exprLoc(ast_unit, lit), .invalid_float_literal, .{});
                return self.context.type_store.tTypeError();
            }
            break :blk self.context.type_store.tF64();
        },
        .bool => self.context.type_store.tBool(),
        .string => self.context.type_store.tString(),
        .char => self.context.type_store.tU32(),
    };
}
fn checkIdent(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const row = getExpr(ast_unit, .Ident, id);
    // First try dynamic bindings from active loop/match contexts to support
    // pattern-introduced names even if they were not declared in the symtab.
    if (self.bindingTypeFromActiveCatches(ctx, row.name)) |btid_catch| return btid_catch;
    if (self.bindingTypeFromActiveLoops(ctx, ast_unit, row.name)) |btid_loop| return btid_loop;
    if (self.bindingTypeFromActiveMatches(ctx, ast_unit, row.name)) |btid_match| return btid_match;

    if (self.lookup(ctx, row.name)) |sid| {
        const srow = ctx.symtab.syms.get(sid);
        // Decl-originated symbol?
        if (!srow.origin_decl.isNone()) {
            const did = srow.origin_decl.unwrap();
            // If this decl had a pattern, compute binding type from pattern and RHS type
            const drow = ast_unit.exprs.Decl.get(did);
            if (!drow.pattern.isNone()) {
                const rhs_ty = blk: {
                    if (ast_unit.type_info.expr_types.items[drow.value.toRaw()]) |t| break :blk t;
                    if (ast_unit.type_info.decl_types.items[did.toRaw()]) |t| break :blk t;
                    // Fallback: check rhs now
                    break :blk try self.checkExpr(ctx, ast_unit, drow.value);
                };
                const p_kind = ast_unit.pats.index.kinds.items[drow.pattern.unwrap().toRaw()];
                if (p_kind == .Binding) {
                    return rhs_ty;
                }
                const bt = pattern_matching.bindingTypeInPattern(self, ast_unit, drow.pattern.unwrap(), row.name, rhs_ty);
                if (bt) |btid| return btid;
            }
            if (ast_unit.type_info.decl_types.items[did.toRaw()]) |dt| return dt;
        }
        // Param-originated symbol?
        if (!srow.origin_param.isNone()) {
            const pid = srow.origin_param.unwrap();
            const p = ast_unit.exprs.Param.get(pid);
            if (!p.ty.isNone()) {
                const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, p.ty.unwrap());
                if (!res[0]) {
                    return self.context.type_store.tTypeError();
                }
                const pt = res[1];
                if (self.typeKind(pt) == .TypeError) {
                    return self.context.type_store.tTypeError();
                }
                if (!p.pat.isNone()) {
                    // If this param had a pattern, compute binding type from pattern and param type
                    if (pattern_matching.bindingTypeInPattern(self, ast_unit, p.pat.unwrap(), row.name, pt)) |bt| return bt;
                }
                return pt;
            } else {
                if (self.lookupParamSpecialization(ctx, row.name)) |override_ty|
                    return override_ty;
                if (p.is_comptime) {
                    return self.context.type_store.mkTypeType(self.context.type_store.tAny());
                }
                // Unannotated param: if pattern, try infer from callee usage later; default any
                return self.context.type_store.tAny();
            }
        }

        // Fallback: plain binding introduced by pattern without origin info.
        // Try to infer its type from active loop/match binding contexts.
        if (self.bindingTypeFromActiveLoops(ctx, ast_unit, row.name)) |btid2| return btid2;
        if (self.bindingTypeFromActiveMatches(ctx, ast_unit, row.name)) |btid2| return btid2;
    }
    const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, id);
    if (res[0])
        return self.context.type_store.mkTypeType(res[1]);
    try self.context.diags.addError(exprLoc(ast_unit, row), .undefined_identifier, .{});
    return self.context.type_store.tTypeError();
}

fn checkBlock(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const br = getExpr(ast_unit, .Block, id);
    const stmts = ast_unit.stmts.stmt_pool.slice(br.items);
    _ = try ctx.symtab.push(ctx.symtab.currentId());
    defer ctx.symtab.pop();
    var i: usize = 0;

    if (stmts.len == 0) return self.context.type_store.tVoid();
    const value_required = self.isValueReq(ctx);
    var after_break: bool = false;
    if (!value_required) {
        // Statement context: just type-check children, no value produced
        while (i < stmts.len) : (i += 1) {
            if (after_break) {
                const loc = stmtLoc(ast_unit, stmts[i]);
                try self.context.diags.addError(loc, .unreachable_code_after_break, .{});
                return self.context.type_store.tTypeError();
            }
            _ = try self.checkStmt(ctx, ast_unit, stmts[i]);
            // Track unconditional break at top-level in this block
            const sk = ast_unit.stmts.index.kinds.items[stmts[i].toRaw()];
            if (sk == .Break) after_break = true else if (sk == .Expr) {
                const se = getStmt(ast_unit, .Expr, stmts[i]).expr;
                if (exprKind(ast_unit, se) == .Break) after_break = true;
            }
        }
        return self.context.type_store.tVoid();
    }
    // Value context: the last line must be an expression to produce a value
    while (i < stmts.len - 1) : (i += 1) {
        if (after_break) {
            const loc = stmtLoc(ast_unit, stmts[i]);
            try self.context.diags.addError(loc, .unreachable_code_after_break, .{});
            return self.context.type_store.tTypeError();
        }
        _ = try self.checkStmt(ctx, ast_unit, stmts[i]);
        const sk = ast_unit.stmts.index.kinds.items[stmts[i].toRaw()];
        if (sk == .Break) after_break = true else if (sk == .Expr) {
            const se = getStmt(ast_unit, .Expr, stmts[i]).expr;
            if (exprKind(ast_unit, se) == .Break) after_break = true;
        }
    }
    // If last is an expression, evaluate it in value context directly
    const last = stmts[stmts.len - 1];
    const last_kind = ast_unit.stmts.index.kinds.items[last.toRaw()];
    if (last_kind == .Expr) {
        if (after_break) {
            const loc = stmtLoc(ast_unit, last);
            try self.context.diags.addError(loc, .unreachable_code_after_break, .{});
            return self.context.type_store.tTypeError();
        }
        const row = getStmt(ast_unit, .Expr, last);
        return try self.checkExpr(ctx, ast_unit, row.expr);
    }
    // Otherwise, type-check the statement and treat as void
    if (after_break) {
        const loc = stmtLoc(ast_unit, last);
        try self.context.diags.addError(loc, .unreachable_code_after_break, .{});
        return self.context.type_store.tTypeError();
    }
    _ = try self.checkStmt(ctx, ast_unit, last);
    if (last_kind == .Break or last_kind == .Return) {
        return self.context.type_store.tNoreturn();
    }
    return self.context.type_store.tVoid();
}

fn stmtLoc(ast_unit: *ast.Ast, sid: ast.StmtId) Loc {
    return switch (ast_unit.stmts.index.kinds.items[sid.toRaw()]) {
        .Expr => exprLocFromId(ast_unit, getStmt(ast_unit, .Expr, sid).expr),
        .Decl => blk: {
            const row = getStmt(ast_unit, .Decl, sid);
            const d = ast_unit.exprs.Decl.get(row.decl);
            break :blk exprLoc(ast_unit, d);
        },
        inline else => |x| exprLoc(ast_unit, getStmt(ast_unit, x, sid)),
    };
}

fn checkBinary(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const bin: ast.Rows.Binary = getExpr(ast_unit, .Binary, id);
    var l = try self.checkExpr(ctx, ast_unit, bin.left);
    var r = try self.checkExpr(ctx, ast_unit, bin.right);
    var lhs_kind = self.typeKind(l);
    var rhs_kind = self.typeKind(r);

    if (lhs_kind == .TypeError or rhs_kind == .TypeError) return self.context.type_store.tTypeError();

    const left_expr_kind = exprKind(ast_unit, bin.left);
    const right_expr_kind = exprKind(ast_unit, bin.right);
    const left_is_literal = left_expr_kind == .Literal;
    const right_is_literal = right_expr_kind == .Literal;

    if (lhs_kind == .Undef or rhs_kind == .Undef) {
        try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
        return self.context.type_store.tTypeError();
    }

    switch (bin.op) {
        .add, .sub, .mul, .div, .mod, .bit_and, .bit_or, .bit_xor, .shl, .shr => {
            if (lhs_kind == .Simd or rhs_kind == .Simd) {
                switch (bin.op) {
                    .add, .sub, .mul, .div => {},
                    else => {
                        try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return self.context.type_store.tTypeError();
                    },
                }

                if (lhs_kind == .Simd and rhs_kind == .Simd) {
                    const ls = self.context.type_store.get(.Simd, l);
                    const rs = self.context.type_store.get(.Simd, r);
                    if (ls.lanes != rs.lanes or !ls.elem.eq(rs.elem)) {
                        try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return self.context.type_store.tTypeError();
                    }
                    return l;
                } else if (lhs_kind == .Simd and check_types.isNumericKind(self, rhs_kind)) {
                    const ls = self.context.type_store.get(.Simd, l);
                    if (self.assignable(r, ls.elem) != .success) {
                        if (right_is_literal) {
                            var r_copy = r;
                            var rk_copy = rhs_kind;
                            if (try self.updateCoercedLiteral(ast_unit, bin.right, ls.elem, &r_copy, &rk_copy)) {
                                if (self.assignable(r_copy, ls.elem) == .success) {
                                    return l;
                                }
                            }
                        }
                        try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return self.context.type_store.tTypeError();
                    }
                    return l;
                } else if (rhs_kind == .Simd and check_types.isNumericKind(self, lhs_kind)) {
                    const rs = self.context.type_store.get(.Simd, r);
                    if (self.assignable(l, rs.elem) != .success) {
                        if (left_is_literal) {
                            var l_copy = l;
                            var lk_copy = lhs_kind;
                            if (try self.updateCoercedLiteral(ast_unit, bin.left, rs.elem, &l_copy, &lk_copy)) {
                                if (self.assignable(l_copy, rs.elem) == .success) {
                                    return r;
                                }
                            }
                        }
                        try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return self.context.type_store.tTypeError();
                    }
                    return r;
                } else {
                    try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                    return self.context.type_store.tTypeError();
                }
            }
            if (bin.op == .div) try self.checkDivByZero(ast_unit, bin.right, exprLoc(ast_unit, bin));
            if (bin.op == .mod) {
                const left_is_float = switch (lhs_kind) {
                    .F32, .F64 => true,
                    else => false,
                };
                const right_is_float = switch (rhs_kind) {
                    .F32, .F64 => true,
                    else => false,
                };
                if (left_is_float or right_is_float) {
                    try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                    return self.context.type_store.tTypeError();
                }
                if (check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind))
                    try self.checkIntZeroLiteral(ast_unit, bin.right, exprLoc(ast_unit, bin));
            }
            // Complex arithmetic: allow + - * / with Complex and with scalar numeric (promote scalar)
            const lhs_is_complex = (lhs_kind == .Complex);
            const rhs_is_complex = (rhs_kind == .Complex);
            if (lhs_is_complex or rhs_is_complex) {
                // Only arithmetic ops allowed for Complex
                if (!(bin.op == .add or bin.op == .sub or bin.op == .mul or bin.op == .div)) {
                    try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                    return self.context.type_store.tTypeError();
                }
                if (lhs_is_complex and rhs_is_complex) {
                    // Require same element type for now
                    const lc = self.context.type_store.get(.Complex, l);
                    const rc = self.context.type_store.get(.Complex, r);
                    if (lc.elem.toRaw() == rc.elem.toRaw()) return l;
                    try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                    return self.context.type_store.tTypeError();
                }
                // One side complex, other side numeric scalar
                if (lhs_is_complex and check_types.isNumericKind(self, rhs_kind)) {
                    const lc = self.context.type_store.get(.Complex, l);
                    if (lc.elem.eq(r)) return l;
                    if (right_is_literal and try self.updateCoercedLiteral(ast_unit, bin.right, lc.elem, &r, &rhs_kind)) {
                        if (lc.elem.eq(r)) return l;
                    }
                }
                if (rhs_is_complex and check_types.isNumericKind(self, lhs_kind)) {
                    const rc = self.context.type_store.get(.Complex, r);
                    if (rc.elem.eq(l)) return r;
                    if (left_is_literal and try self.updateCoercedLiteral(ast_unit, bin.left, rc.elem, &l, &lhs_kind)) {
                        if (rc.elem.eq(l)) return r;
                    }
                }
                try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                return self.context.type_store.tTypeError();
            }
            if (!check_types.isNumericKind(self, lhs_kind) or !check_types.isNumericKind(self, rhs_kind)) {
                if (lhs_kind == .Any or rhs_kind == .Any) {
                    if (lhs_kind == .Any and rhs_kind == .Any) {
                        return self.context.type_store.tAny();
                    }
                    if (lhs_kind == .Any) {
                        return r;
                    }
                    return l;
                }
                try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                return self.context.type_store.tTypeError();
            }
            if (l.eq(r)) return l;

            const is_arith = bin.op == .add or bin.op == .sub or bin.op == .mul or bin.op == .div;

            if (is_arith) {
                if (left_is_literal and right_is_literal) {
                    const l_is_float = (lhs_kind == .F32 or lhs_kind == .F64);
                    const r_is_float = (rhs_kind == .F32 or rhs_kind == .F64);
                    if (l_is_float and !r_is_float and check_types.isIntegerKind(self, rhs_kind)) {
                        if (try self.updateCoercedLiteral(ast_unit, bin.right, l, &r, &rhs_kind)) return l;
                    } else if (r_is_float and !l_is_float and check_types.isIntegerKind(self, lhs_kind)) {
                        if (try self.updateCoercedLiteral(ast_unit, bin.left, r, &l, &lhs_kind)) return r;
                    }
                } else if (left_is_literal) {
                    if (try self.updateCoercedLiteral(ast_unit, bin.left, r, &l, &lhs_kind)) return r;
                } else if (right_is_literal) {
                    if (try self.updateCoercedLiteral(ast_unit, bin.right, l, &r, &rhs_kind)) return l;
                } else {
                    const left_const = self.constNumericKind(ast_unit, bin.left) != .none;
                    const right_const = self.constNumericKind(ast_unit, bin.right) != .none;
                    // Accept mixed float-int arithmetic when the int side is a comptime constant;
                    // return the float side's type without mutating child expression types.
                    if (left_const and (rhs_kind == .F32 or rhs_kind == .F64) and check_types.isIntegerKind(self, lhs_kind)) {
                        return r;
                    } else if (right_const and (lhs_kind == .F32 or lhs_kind == .F64) and check_types.isIntegerKind(self, rhs_kind)) {
                        return l;
                    } else if (left_const and right_const) {
                        const l_is_float = (lhs_kind == .F32 or lhs_kind == .F64);
                        const r_is_float = (rhs_kind == .F32 or rhs_kind == .F64);
                        if (l_is_float and !r_is_float and check_types.isIntegerKind(self, rhs_kind)) return l;
                        if (r_is_float and !l_is_float and check_types.isIntegerKind(self, lhs_kind)) return r;
                    }
                }
            }

            try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
            return self.context.type_store.tTypeError();
        },
        .eq, .neq, .lt, .lte, .gt, .gte => {
            if (lhs_kind == .Any or rhs_kind == .Any) {
                return self.context.type_store.tBool();
            }
            const is_equality = bin.op == .eq or bin.op == .neq;
            if (is_equality) {
                const lhs_is_optional = lhs_kind == .Optional;
                const rhs_is_optional = rhs_kind == .Optional;
                if (lhs_is_optional != rhs_is_optional) {
                    const opt_ty = if (lhs_is_optional) l else r;
                    const other_ty = if (lhs_is_optional) r else l;
                    const opt_elem_ty = self.context.type_store.get(.Optional, opt_ty).elem;
                    // Disallow comparing `null` with non-optional values.
                    if (self.typeKind(opt_elem_ty) == .Any) {
                        try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return self.context.type_store.tTypeError();
                    }
                    if (self.assignable(other_ty, opt_elem_ty) != .success) {
                        try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                        return self.context.type_store.tTypeError();
                    }
                    return self.context.type_store.tBool();
                }
            }
            var both_ints = check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind);
            var both_floats = (lhs_kind == .F32 or lhs_kind == .F64) and (rhs_kind == .F32 or rhs_kind == .F64);
            var both_bools = lhs_kind == .Bool and rhs_kind == .Bool;
            var both_complex = lhs_kind == .Complex and rhs_kind == .Complex;
            if (both_complex) {
                const lc = self.context.type_store.get(.Complex, l);
                const rc = self.context.type_store.get(.Complex, r);
                both_complex = (lc.elem.toRaw() == rc.elem.toRaw());
            }
            var both_same_enum = lhs_kind == .Enum and rhs_kind == .Enum and l.eq(r);
            var both_same_error = lhs_kind == .Error and rhs_kind == .Error and l.eq(r);

            // Handle Optional(T) == null or Optional(T) != null
            if ((bin.op == .eq or bin.op == .neq) and lhs_kind == .Optional and rhs_kind == .Optional) {
                const l_opt_elem_ty = self.context.type_store.get(.Optional, l).elem;
                const r_opt_elem_ty = self.context.type_store.get(.Optional, r).elem;

                if (self.typeKind(l_opt_elem_ty) == .Any or self.typeKind(r_opt_elem_ty) == .Any) {
                    return self.context.type_store.tBool();
                }
            }

            if ((bin.op == .eq or bin.op == .neq) and both_same_error) {
                return self.context.type_store.tBool();
            }

            // We avoid implicit *value* coercions. For comparisons, we accept same-class operands:
            //   - int ? int (any width/sign)
            //   - float ? float (F32/F64 mixed ok)
            //   - bool ? bool
            if (!(both_ints or both_floats or both_complex or both_bools or both_same_enum or both_same_error)) {
                if (left_is_literal and right_is_literal) {
                    const l_is_float = (lhs_kind == .F32 or lhs_kind == .F64);
                    const r_is_float = (rhs_kind == .F32 or rhs_kind == .F64);
                    var coerced = false;
                    if (l_is_float and !r_is_float and check_types.isIntegerKind(self, rhs_kind)) {
                        coerced = try self.updateCoercedLiteral(ast_unit, bin.right, l, &r, &rhs_kind);
                    } else if (r_is_float and !l_is_float and check_types.isIntegerKind(self, lhs_kind)) {
                        coerced = try self.updateCoercedLiteral(ast_unit, bin.left, r, &l, &lhs_kind);
                    }
                    if (coerced) {
                        both_ints = check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind);
                        both_floats = (lhs_kind == .F32 or lhs_kind == .F64) and (rhs_kind == .F32 or rhs_kind == .F64);
                        both_bools = lhs_kind == .Bool and rhs_kind == .Bool;
                        both_complex = lhs_kind == .Complex and rhs_kind == .Complex;
                        if (both_complex) {
                            const lc = self.context.type_store.get(.Complex, l);
                            const rc = self.context.type_store.get(.Complex, r);
                            both_complex = (lc.elem.toRaw() == rc.elem.toRaw());
                        }
                        both_same_enum = lhs_kind == .Enum and rhs_kind == .Enum and l.eq(r);
                        both_same_error = lhs_kind == .Error and rhs_kind == .Error and l.eq(r);
                    }
                } else if (left_is_literal and !right_is_literal and check_types.isNumericKind(self, rhs_kind)) {
                    if (try self.updateCoercedLiteral(ast_unit, bin.left, r, &l, &lhs_kind)) {
                        both_ints = check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind);
                        both_floats = (lhs_kind == .F32 or lhs_kind == .F64) and (rhs_kind == .F32 or rhs_kind == .F64);
                        both_bools = lhs_kind == .Bool and rhs_kind == .Bool;
                        both_complex = lhs_kind == .Complex and rhs_kind == .Complex;
                        if (both_complex) {
                            const lc = self.context.type_store.get(.Complex, l);
                            const rc = self.context.type_store.get(.Complex, r);
                            both_complex = (lc.elem.toRaw() == rc.elem.toRaw());
                        }
                        both_same_enum = lhs_kind == .Enum and rhs_kind == .Enum and l.eq(r);
                        both_same_error = lhs_kind == .Error and rhs_kind == .Error and l.eq(r);
                    }
                } else if (right_is_literal and !left_is_literal and check_types.isNumericKind(self, lhs_kind)) {
                    if (try self.updateCoercedLiteral(ast_unit, bin.right, l, &r, &rhs_kind)) {
                        both_ints = check_types.isIntegerKind(self, lhs_kind) and check_types.isIntegerKind(self, rhs_kind);
                        both_floats = (lhs_kind == .F32 or lhs_kind == .F64) and (rhs_kind == .F32 or rhs_kind == .F64);
                        both_bools = lhs_kind == .Bool and rhs_kind == .Bool;
                        both_complex = lhs_kind == .Complex and rhs_kind == .Complex;
                        if (both_complex) {
                            const lc = self.context.type_store.get(.Complex, l);
                            const rc = self.context.type_store.get(.Complex, r);
                            both_complex = (lc.elem.toRaw() == rc.elem.toRaw());
                        }
                        both_same_enum = lhs_kind == .Enum and rhs_kind == .Enum and l.eq(r);
                        both_same_error = lhs_kind == .Error and rhs_kind == .Error and l.eq(r);
                    }
                }
            }
            if (!(both_ints or both_floats or both_complex or both_bools or both_same_enum or both_same_error)) {
                try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                return self.context.type_store.tTypeError();
            }
            return self.context.type_store.tBool();
        },

        .logical_and, .logical_or => {
            if (l.toRaw() == self.context.type_store.tBool().toRaw() and
                r.toRaw() == self.context.type_store.tBool().toRaw())
                return self.context.type_store.tBool();
            try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
            return self.context.type_store.tTypeError();
        },
        .@"orelse" => {
            // Case A: Optional(T) orelse R -> T (R assignable to T)
            if (check_types.isOptional(self, l)) |elem| {
                const elem_kind = self.typeKind(elem);
                // Case B: Optional(ErrorSet(V,E)) orelse R -> ErrorSet(V,E)
                if (elem_kind == .ErrorSet) {
                    const es = self.context.type_store.get(.ErrorSet, elem);
                    if (self.assignable(es.value_ty, r) == .success) {
                        return self.context.type_store.mkErrorSet(es.value_ty, es.error_ty);
                    }
                    try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                    return self.context.type_store.tTypeError();
                }
                // Plain optional: require R assignable to T
                if (self.assignable(elem, r) == .success) return elem;
                try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                return self.context.type_store.tTypeError();
            }
            try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_use_of_orelse_on_non_optional, .{});
            return self.context.type_store.tTypeError();
        },
    }
    return self.context.type_store.tTypeError();
}

fn checkUnary(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const unary_expr = getExpr(ast_unit, .Unary, id);
    const expr_ty = try self.checkExpr(ctx, ast_unit, unary_expr.expr);
    const type_kind = self.typeKind(expr_ty);
    if (type_kind == .TypeError) return self.context.type_store.tTypeError();
    switch (unary_expr.op) {
        .pos, .neg => {
            if (!check_types.isNumericKind(self, type_kind)) {
                try self.context.diags.addError(exprLoc(ast_unit, unary_expr), .invalid_unary_op_operand, .{});
                return self.context.type_store.tTypeError();
            }
            return expr_ty;
        },
        .logical_not => {
            // Accept bool or any
            if (!expr_ty.eq(self.context.type_store.tBool()) and !expr_ty.eq(self.context.type_store.tAny())) {
                try self.context.diags.addError(exprLoc(ast_unit, unary_expr), .invalid_unary_op_operand, .{});
                return self.context.type_store.tTypeError();
            }
            return self.context.type_store.tBool();
        },
        .address_of => return self.context.type_store.mkPtr(expr_ty, false),
    }
}

fn checkFunctionLit(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    // Disallow nested function definitions (functions inside functions).
    if (self.inFunction(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, getExpr(ast_unit, .FunctionLit, id)), .nested_function_not_allowed, .{});
        return self.context.type_store.tTypeError();
    }
    const fnr = getExpr(ast_unit, .FunctionLit, id);
    const params = ast_unit.exprs.param_pool.slice(fnr.params);
    var pbuf = try self.gpa.alloc(types.TypeId, params.len);
    defer self.gpa.free(pbuf);
    _ = try ctx.symtab.push(ctx.symtab.currentId());
    defer ctx.symtab.pop();

    var i: usize = 0;
    while (i < params.len) : (i += 1) {
        const p = ast_unit.exprs.Param.get(params[i]);
        if (!p.ty.isNone()) {
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, p.ty.unwrap());
            if (!res[0]) return self.context.type_store.tTypeError();
            const pt = res[1];
            // If parameter uses a pattern, ensure its shape matches the annotated type
            if (!p.pat.isNone()) {
                const shape_ok = pattern_matching.checkPatternShapeForDecl(self, ast_unit, p.pat.unwrap(), pt);
                switch (shape_ok) {
                    .ok => {},
                    .tuple_arity_mismatch => {
                        try self.context.diags.addError(exprLoc(ast_unit, fnr), .tuple_arity_mismatch, .{});
                        return self.context.type_store.tTypeError();
                    },
                    .struct_pattern_field_mismatch => {
                        try self.context.diags.addError(exprLoc(ast_unit, fnr), .struct_pattern_field_mismatch, .{});
                        return self.context.type_store.tTypeError();
                    },
                    .pattern_shape_mismatch => {
                        try self.context.diags.addError(exprLoc(ast_unit, fnr), .pattern_shape_mismatch, .{});
                        return self.context.type_store.tTypeError();
                    },
                }
            }
            pbuf[i] = pt;
        } else {
            var override_ty: ?types.TypeId = null;
            if (!p.pat.isNone()) {
                if (bindingNameOfPattern(ast_unit, p.pat.unwrap())) |pname| {
                    override_ty = self.lookupParamSpecialization(ctx, pname);
                }
            }
            pbuf[i] = if (override_ty) |oty|
                oty
            else if (p.is_comptime)
                self.context.type_store.mkTypeType(self.context.type_store.tAny())
            else
                self.context.type_store.tAny();
        }
        // store in symbol table
        try self.bindParamPattern(ctx, ast_unit, params[i], p);

        // If parameter has a default value, type-check it now and ensure it
        // is assignable to the parameter type (when known).
        if (!p.value.isNone()) {
            const def_expr = p.value.unwrap();
            var def_ty = try self.checkExpr(ctx, ast_unit, def_expr);
            var def_kind = self.typeKind(def_ty);
            if (def_kind == .TypeError) return self.context.type_store.tTypeError();
            const pt = pbuf[i];
            if (!pt.eq(self.context.type_store.tAny())) {
                if (self.assignable(def_ty, pt) != .success) {
                    if (check_types.isNumericKind(self, self.typeKind(pt))) {
                        if (try self.updateCoercedLiteral(ast_unit, def_expr, pt, &def_ty, &def_kind) and
                            self.assignable(def_ty, pt) == .success)
                        {
                            // coerced OK
                        } else {
                            const expected_kind = self.typeKind(pt);
                            const actual_kind = def_kind;
                            try self.context.diags.addError(exprLocFromId(ast_unit, def_expr), .argument_type_mismatch, .{ expected_kind, actual_kind });
                            return self.context.type_store.tTypeError();
                        }
                    } else {
                        const expected_kind = self.typeKind(pt);
                        const actual_kind = def_kind;
                        try self.context.diags.addError(exprLocFromId(ast_unit, def_expr), .argument_type_mismatch, .{ expected_kind, actual_kind });
                        return self.context.type_store.tTypeError();
                    }
                }
            }
        }
    }

    const res_opt = if (!fnr.result_ty.isNone())
        (try check_types.typeFromTypeExpr(self, ctx, ast_unit, fnr.result_ty.unwrap()))
    else
        .{ true, self.context.type_store.tVoid() };
    if (!res_opt[0]) return self.context.type_store.tTypeError();
    const res = res_opt[1];

    // Temporarily record a function type (purity will be finalized after body analysis)
    const temp_ty = self.context.type_store.mkFunction(pbuf, res, fnr.flags.is_variadic, true);
    ast_unit.type_info.expr_types.items[id.toRaw()] = temp_ty;

    try self.pushFunc(ctx, res, !fnr.result_ty.isNone(), !fnr.flags.is_proc);
    defer self.popFunc(ctx);
    if (!fnr.body.isNone()) {
        // Function bodies are in statement context: no value required from the block
        try self.pushValueReq(ctx, false);
        defer self.popValueReq(ctx);
        _ = try self.checkExpr(ctx, ast_unit, fnr.body.unwrap());
    }
    // Extern procs are considered impure; otherwise proc purity comes from body analysis.
    const is_pure = if (fnr.flags.is_proc) false else true;
    const final_ty = self.context.type_store.mkFunction(pbuf, res, fnr.flags.is_variadic, is_pure);
    ast_unit.type_info.expr_types.items[id.toRaw()] = final_ty;
    return final_ty;
}

fn checkTupleLit(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    // Disambiguation: tuple literal vs tuple type share syntax.
    // We only interpret tuples as types when the checker is already in a type position
    // (handled via check_types.typeFromTypeExpr at use sites). Here, always treat as value.
    const tuple_lit = getExpr(ast_unit, .TupleLit, id);
    const elems = ast_unit.exprs.expr_pool.slice(tuple_lit.elems);

    var tbuf = try self.gpa.alloc(types.TypeId, elems.len);
    defer self.gpa.free(tbuf);
    var i: usize = 0;
    while (i < elems.len) : (i += 1) {
        const ety = try self.checkExpr(ctx, ast_unit, elems[i]);
        if (self.typeKind(ety) == .TypeError) return self.context.type_store.tTypeError();
        tbuf[i] = ety;
    }
    return self.context.type_store.mkTuple(tbuf);
}

fn checkArrayLit(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    id: ast.ExprId,
) !types.TypeId {
    const array_lit = getExpr(ast_unit, .ArrayLit, id);
    const elems = ast_unit.exprs.expr_pool.slice(array_lit.elems);

    // infer from first element, homogeneous requirement
    if (elems.len == 0) {
        return self.context.type_store.mkArray(self.context.type_store.tAny(), .{ .Concrete = 0 });
    }
    const first_ty = try self.checkExpr(ctx, ast_unit, elems[0]);
    if (self.typeKind(first_ty) == .TypeError) return self.context.type_store.tTypeError();
    var i: usize = 1;
    while (i < elems.len) : (i += 1) {
        const ety = try self.checkExpr(ctx, ast_unit, elems[i]);
        if (ety.toRaw() != first_ty.toRaw()) {
            try self.context.diags.addError(exprLoc(ast_unit, array_lit), .heterogeneous_array_elements, .{});
            return self.context.type_store.tTypeError();
        }
    }
    return self.context.type_store.mkArray(first_ty, .{ .Concrete = elems.len });
}

fn checkMapLit(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const row = getExpr(ast_unit, .MapLit, id);
    const kvs = ast_unit.exprs.kv_pool.slice(row.entries);

    if (kvs.len == 0) {
        return self.context.type_store.mkMap(self.context.type_store.tAny(), self.context.type_store.tAny());
    }
    const first = ast_unit.exprs.KeyValue.get(kvs[0]);
    const key_ty = try self.checkExpr(ctx, ast_unit, first.key);
    const val_ty = try self.checkExpr(ctx, ast_unit, first.value);
    if (self.typeKind(key_ty) == .TypeError or self.typeKind(val_ty) == .TypeError)
        return self.context.type_store.tTypeError();

    var i: usize = 1;
    while (i < kvs.len) : (i += 1) {
        const kv = ast_unit.exprs.KeyValue.get(kvs[i]);
        const kt = try self.checkExpr(ctx, ast_unit, kv.key);
        const vt = try self.checkExpr(ctx, ast_unit, kv.value);
        if (kt.toRaw() != key_ty.toRaw()) {
            try self.context.diags.addError(exprLoc(ast_unit, row), .map_mixed_key_types, .{});
            return self.context.type_store.tTypeError();
        }
        if (vt.toRaw() != val_ty.toRaw()) {
            try self.context.diags.addError(exprLoc(ast_unit, row), .map_mixed_value_types, .{});
            return self.context.type_store.tTypeError();
        }
    }
    return self.context.type_store.mkMap(key_ty, val_ty);
}

fn checkIndexAccess(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const index_expr = getExpr(ast_unit, .IndexAccess, id);
    const col_ty = try self.checkExpr(ctx, ast_unit, index_expr.collection);
    const col_kind = self.typeKind(col_ty);
    if (col_kind == .TypeError) return self.context.type_store.tTypeError();
    switch (col_kind) {
        .Array, .Slice, .DynArray => return self.indexElemTypeFromArrayLike(ctx, ast_unit, col_ty, index_expr.index, exprLoc(ast_unit, index_expr)),
        .Tensor => return self.indexElemTypeFromTensor(ctx, ast_unit, col_ty, index_expr.index, exprLoc(ast_unit, index_expr)),
        .Simd => {
            const idx_kind = exprKind(ast_unit, index_expr.index);
            if (idx_kind == .Range) {
                try self.context.diags.addError(exprLoc(ast_unit, index_expr), .non_integer_index, .{});
                return self.context.type_store.tTypeError();
            }
            const it = try self.checkExpr(ctx, ast_unit, index_expr.index);
            if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
            if (!check_types.isIntegerKind(self, self.typeKind(it))) {
                try self.context.diags.addError(exprLoc(ast_unit, index_expr), .non_integer_index, .{});
                return self.context.type_store.tTypeError();
            }
            const simd = self.context.type_store.get(.Simd, col_ty);
            return simd.elem;
        },
        .Map => {
            const m = self.context.type_store.get(.Map, col_ty);
            const it = try self.checkExpr(ctx, ast_unit, index_expr.index);
            if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
            if (it.toRaw() != m.key.toRaw()) {
                try self.context.diags.addError(exprLoc(ast_unit, index_expr), .map_wrong_key_type, .{});
                return self.context.type_store.tTypeError();
            }
            return m.value;
        },

        .String => {
            const it = try self.checkExpr(ctx, ast_unit, index_expr.index);
            if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
            if (!check_types.isIntegerKind(self, self.typeKind(it))) {
                try self.context.diags.addError(exprLoc(ast_unit, index_expr), .non_integer_index, .{});
                return self.context.type_store.tTypeError();
            }
            return self.context.type_store.tU8();
        },
        else => {
            try self.context.diags.addError(exprLoc(ast_unit, index_expr), .not_indexable, .{});
        },
    }
    return self.context.type_store.tTypeError();
}

fn indexElemTypeFromArrayLike(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, col_ty: types.TypeId, idx_expr: ast.ExprId, loc: Loc) !types.TypeId {
    const col_kind = self.typeKind(col_ty);
    if (!(col_kind == .Array or col_kind == .Slice or col_kind == .DynArray)) {
        // Defensive: caller promised an array-like, but was not. Avoid panic.
        try self.context.diags.addError(loc, .not_indexable, .{});
        return self.context.type_store.tTypeError();
    }
    const idx_kind = exprKind(ast_unit, idx_expr);
    if (idx_kind == .Range) {
        _ = self.checkExpr(ctx, ast_unit, idx_expr) catch return self.context.type_store.tTypeError(); // validate range endpoints
        return switch (col_kind) {
            .Array => blk: {
                const r = self.context.type_store.get(.Array, col_ty);
                break :blk self.context.type_store.mkSlice(r.elem);
            },
            .Slice => blk2: {
                const r = self.context.type_store.get(.Slice, col_ty);
                break :blk2 self.context.type_store.mkSlice(r.elem);
            },
            .DynArray => blk3: {
                const r = self.context.type_store.get(.DynArray, col_ty);
                break :blk3 self.context.type_store.mkSlice(r.elem);
            },
            else => return self.context.type_store.tTypeError(),
        };
    }
    const it = try self.checkExpr(ctx, ast_unit, idx_expr);
    if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
    if (!check_types.isIntegerKind(self, self.typeKind(it))) {
        try self.context.diags.addError(loc, .non_integer_index, .{});
        return self.context.type_store.tTypeError();
    }
    return switch (col_kind) {
        .Array => self.context.type_store.get(.Array, col_ty).elem,
        .Slice => self.context.type_store.get(.Slice, col_ty).elem,
        .DynArray => self.context.type_store.get(.DynArray, col_ty).elem,
        else => self.context.type_store.tTypeError(),
    };
}

fn indexElemTypeFromTensor(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, col_ty: types.TypeId, idx_expr: ast.ExprId, loc: Loc) !types.TypeId {
    const tensor = self.context.type_store.get(.Tensor, col_ty);
    const rank: usize = @intCast(tensor.rank);
    if (rank == 0) {
        try self.context.diags.addError(loc, .not_indexable, .{});
        return self.context.type_store.tTypeError();
    }

    const idx_kind = exprKind(ast_unit, idx_expr);
    if (idx_kind == .Range) {
        // Tensor slicing is not yet supported.
        try self.context.diags.addError(loc, .non_integer_index, .{});
        return self.context.type_store.tTypeError();
    }

    const it = try self.checkExpr(ctx, ast_unit, idx_expr);
    if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
    if (!check_types.isIntegerKind(self, self.typeKind(it))) {
        try self.context.diags.addError(loc, .non_integer_index, .{});
        return self.context.type_store.tTypeError();
    }

    if (rank == 1) return tensor.elem;

    var dims = [_]usize{0} ** types.max_tensor_rank;
    var i: usize = 1;
    while (i < rank) : (i += 1) {
        dims[i - 1] = tensor.dims[i];
    }
    return self.context.type_store.mkTensor(tensor.elem, dims[0 .. rank - 1]);
}

fn tryRegisterDynArrayBuiltin(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    owner_ty: types.TypeId,
    receiver_ty: types.TypeId,
    field_name: ast.StrId,
    parent_kind: types.TypeKind,
    loc: Loc,
) !types.TypeId {
    if (self.context.type_store.getKind(owner_ty) != .DynArray) return self.context.type_store.tTypeError();
    const method_name = getStr(ast_unit, field_name);

    if (std.mem.eql(u8, method_name, "append")) {
        const dyn_info = self.context.type_store.get(.DynArray, owner_ty);
        const elem_ty = dyn_info.elem;
        const ptr_owner_ty = self.context.type_store.mkPtr(owner_ty, false);
        const params = [_]types.TypeId{ ptr_owner_ty, elem_ty };
        const fn_ty = self.context.type_store.mkFunction(&params, self.context.type_store.tVoid(), false, false);

        var needs_addr_of = true;
        if (parent_kind == .Ptr) {
            needs_addr_of = false;
            const ptr_row = self.context.type_store.get(.Ptr, receiver_ty);
            if (!ptr_row.elem.eq(owner_ty)) {
                try self.context.diags.addError(loc, .method_receiver_requires_pointer, .{getStr(ast_unit, field_name)});
                return error.MethodResolutionFailed;
            }
            if (ptr_row.is_const) {
                try self.context.diags.addError(loc, .method_receiver_requires_pointer, .{getStr(ast_unit, field_name)});
                return error.MethodResolutionFailed;
            }
        }

        const binding = types.MethodBinding{
            .owner_type = owner_ty,
            .method_name = field_name,
            .decl_id = ast.DeclId.fromRaw(0),
            .decl_ast = ast_unit,
            .func_type = fn_ty,
            .self_param_type = ptr_owner_ty,
            .receiver_kind = .pointer,
            .requires_implicit_receiver = parent_kind != .TypeType,
            .needs_addr_of = needs_addr_of,
            .builtin = .dynarray_append,
        };
        try ast_unit.type_info.setMethodBinding(expr_id, binding);
        return fn_ty;
    }

    return self.context.type_store.tTypeError();
}

fn resolveMethodFieldAccess(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    owner_ty: types.TypeId,
    receiver_ty: types.TypeId,
    field_name: ast.StrId,
    loc: Loc,
) !types.TypeId {
    const entry_opt = self.context.type_store.getMethod(owner_ty, field_name);

    const parent_kind = self.typeKind(receiver_ty);
    if (entry_opt == null) {
        return try self.tryRegisterDynArrayBuiltin(ast_unit, expr_id, owner_ty, receiver_ty, field_name, parent_kind, loc);
    }

    const entry = entry_opt.?;
    const decl_ast = entry.decl_ast;
    const wants_receiver = entry.receiver_kind != .none;
    const implicit_receiver = wants_receiver and parent_kind != .TypeType;

    var needs_addr_of = false;

    if (implicit_receiver) {
        switch (entry.receiver_kind) {
            .none => {},
            .value => {
                if (!receiver_ty.eq(owner_ty)) {
                    try self.context.diags.addError(loc, .method_receiver_requires_value, .{getStr(ast_unit, field_name)});
                    return error.MethodResolutionFailed;
                }
            },
            .pointer, .pointer_const => {
                if (self.typeKind(receiver_ty) == .Ptr) {
                    const ptr_row = self.context.type_store.get(.Ptr, receiver_ty);
                    if (!ptr_row.elem.eq(owner_ty)) {
                        try self.context.diags.addError(loc, .method_receiver_requires_pointer, .{getStr(ast_unit, field_name)});
                        return error.MethodResolutionFailed;
                    }
                } else if (receiver_ty.eq(owner_ty)) {
                    needs_addr_of = true;
                } else {
                    try self.context.diags.addError(loc, .method_receiver_requires_pointer, .{getStr(ast_unit, field_name)});
                    return error.MethodResolutionFailed;
                }
            },
        }
    }

    const fn_row = self.context.type_store.get(.Function, entry.func_type);
    const params = self.context.type_store.type_pool.slice(fn_row.params);
    const trimmed = blk: {
        if (implicit_receiver) {
            const rest = if (params.len <= 1) params[0..0] else params[1..];
            break :blk self.context.type_store.mkFunction(rest, fn_row.result, fn_row.is_variadic, fn_row.is_pure);
        }
        break :blk entry.func_type;
    };

    try ast_unit.type_info.setMethodBinding(expr_id, .{
        .owner_type = entry.owner_type,
        .method_name = entry.method_name,
        .decl_id = entry.decl_id,
        .decl_ast = decl_ast,
        .func_type = entry.func_type,
        .self_param_type = entry.self_param_type,
        .receiver_kind = entry.receiver_kind,
        .requires_implicit_receiver = implicit_receiver,
        .needs_addr_of = needs_addr_of,
        .builtin = entry.builtin,
    });

    return trimmed;
}

fn checkFieldAccess(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const field_expr = getExpr(ast_unit, .FieldAccess, id);
    const field_loc = exprLoc(ast_unit, field_expr);

    const parent_ty = try self.checkExpr(ctx, ast_unit, field_expr.parent);
    if (self.typeKind(parent_ty) == .TypeError) return self.context.type_store.tTypeError();

    var ty = parent_ty;
    const kind = self.typeKind(ty);
    if (kind == .Any) return self.context.type_store.tAny();

    if (kind == .Ast) {
        const ast_ty = self.context.type_store.get(.Ast, ty);
        const pkg_name = self.context.interner.get(ast_ty.pkg_name);
        const filepath = self.context.interner.get(ast_ty.filepath);
        const pkg = self.context.compilation_unit.packages.getPtr(pkg_name) orelse
            return self.context.type_store.tTypeError();
        const parent_unit = pkg.sources.getPtr(filepath) orelse
            return self.context.type_store.tTypeError();

        if (parent_unit.ast) |a| {
            // Re-intern field name into the imported unit's interner before lookup
            const field_name = getStr(ast_unit, field_expr.field);
            const target_sid = a.exprs.strs.intern(field_name);
            if (a.type_info.getExport(target_sid)) |ex| {
                return ex.ty;
            }
        }
        try self.context.diags.addError(field_loc, .unknown_module_field, .{getStr(ast_unit, field_expr.field)});
        return self.context.type_store.tTypeError();
    }

    const field_name = getStr(ast_unit, field_expr.field);
    if (std.mem.eql(u8, field_name, "len")) {
        switch (kind) {
            .Array, .Slice, .DynArray, .String => {
                try ast_unit.type_info.setFieldIndex(id, 1);
                return self.context.type_store.tUsize();
            },
            else => {},
        }
    } else if (std.mem.eql(u8, field_name, "capacity")) {
        switch (kind) {
            .DynArray => {
                try ast_unit.type_info.setFieldIndex(id, 2);
                return self.context.type_store.tUsize();
            },
            else => {},
        }
    }

    switch (kind) {
        .Complex => {
            const complex = self.context.type_store.get(.Complex, ty);
            const field_name_inner = getStr(ast_unit, field_expr.field);
            if (std.mem.eql(u8, field_name_inner, "real") or std.mem.eql(u8, field_name_inner, "re")) {
                try ast_unit.type_info.setFieldIndex(id, 0);
                return complex.elem;
            }
            if (std.mem.eql(u8, field_name_inner, "imag") or std.mem.eql(u8, field_name_inner, "im")) {
                try ast_unit.type_info.setFieldIndex(id, 1);
                return complex.elem;
            }
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_struct_field, .{});
            return self.context.type_store.tTypeError();
        },
        .Struct, .Union => {
            const fields = if (kind == .Struct)
                self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, ty).fields)
            else
                self.context.type_store.field_pool.slice(self.context.type_store.get(.Union, ty).fields);
            var i: usize = 0;
            while (i < fields.len) : (i += 1) {
                const f = self.context.type_store.Field.get(fields[i]);
                if (f.name.eq(field_expr.field)) {
                    try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                    return f.ty;
                }
            }
            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, ty, field_expr.field, field_loc) catch |err| switch (err) {
                else => return self.context.type_store.tTypeError(),
            };
            if (self.typeKind(method_ty) != .TypeError) return method_ty;
            try self.context.diags.addError(field_loc, .unknown_struct_field, .{});
            return self.context.type_store.tTypeError();
        },
        .Tuple => {
            const tuple_row = self.context.type_store.get(.Tuple, ty);
            const elems = self.context.type_store.type_pool.slice(tuple_row.elems);
            const index = std.fmt.parseInt(usize, getStr(ast_unit, field_expr.field), 10) catch {
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .expected_field_name_or_index, .{});
                return self.context.type_store.tTypeError();
            };
            if (index >= elems.len) {
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .tuple_index_out_of_bounds, .{});
                return self.context.type_store.tTypeError();
            }
            try ast_unit.type_info.setFieldIndex(id, @intCast(index));
            return elems[index];
        },
        .DynArray => {
            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, ty, field_expr.field, field_loc) catch |err| switch (err) {
                else => return self.context.type_store.tTypeError(),
            };
            if (self.typeKind(method_ty) != .TypeError) return method_ty;
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .field_access_on_non_aggregate, .{kind});
            return self.context.type_store.tTypeError();
        },
        .Ptr => {
            const ptr_row = self.context.type_store.get(.Ptr, ty);
            ty = ptr_row.elem;
            const inner_kind = self.typeKind(ty);
            if (inner_kind == .Complex) {
                const complex = self.context.type_store.get(.Complex, ty);
                const field_name_inner = getStr(ast_unit, field_expr.field);
                if (std.mem.eql(u8, field_name_inner, "real") or std.mem.eql(u8, field_name_inner, "re")) {
                    try ast_unit.type_info.setFieldIndex(id, 0);
                    return complex.elem;
                }
                if (std.mem.eql(u8, field_name_inner, "imag") or std.mem.eql(u8, field_name_inner, "im")) {
                    try ast_unit.type_info.setFieldIndex(id, 1);
                    return complex.elem;
                }
            }
            if (inner_kind == .Struct) {
                const struct_row = self.context.type_store.get(.Struct, ty);
                const fields = self.context.type_store.field_pool.slice(struct_row.fields);
                var i: usize = 0;
                while (i < fields.len) : (i += 1) {
                    const f = self.context.type_store.Field.get(fields[i]);
                    if (f.name.eq(field_expr.field)) {
                        try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                        return f.ty;
                    }
                }
            }
            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, parent_ty, field_expr.field, field_loc) catch |err| switch (err) {
                else => return self.context.type_store.tTypeError(),
            };
            if (self.typeKind(method_ty) != .TypeError) return method_ty;
            if (inner_kind == .Struct) {
                try self.context.diags.addError(field_loc, .unknown_struct_field, .{});
                return self.context.type_store.tTypeError();
            }
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .field_access_on_non_aggregate, .{kind});
            return self.context.type_store.tTypeError();
        },
        .Enum, .Error => {
            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, ty, field_expr.field, field_loc) catch |err| switch (err) {
                else => return self.context.type_store.tTypeError(),
            };
            if (self.typeKind(method_ty) != .TypeError) return method_ty;
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .field_access_on_non_aggregate, .{kind});
            return self.context.type_store.tTypeError();
        },
        .TypeType => {
            const tt = self.context.type_store.get(.TypeType, ty);
            ty = tt.of;
            const inner_kind = self.typeKind(ty);

            if (inner_kind == .Enum) {
                const en = self.context.type_store.get(.Enum, ty);
                const members = self.context.type_store.enum_member_pool.slice(en.members);
                var i: usize = 0;
                while (i < members.len) : (i += 1) {
                    const m = self.context.type_store.EnumMember.get(members[i]);
                    if (m.name.eq(field_expr.field)) {
                        // Selecting an enum tag as a value of the enum type.
                        try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                        return ty;
                    }
                }
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_enum_tag, .{});
                return self.context.type_store.tTypeError();
            } else if (inner_kind == .Struct) {
                const sr = self.context.type_store.get(.Struct, ty);
                const fields = self.context.type_store.field_pool.slice(sr.fields);
                var i: usize = 0;
                while (i < fields.len) : (i += 1) {
                    const f = self.context.type_store.Field.get(fields[i]);
                    if (f.name.eq(field_expr.field)) {
                        try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                        return ty;
                    }
                }
                // Not a struct field; attempt associated method/func resolution on the type.
                const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, parent_ty, field_expr.field, field_loc) catch |err| switch (err) {
                    else => return self.context.type_store.tTypeError(),
                };
                if (self.typeKind(method_ty) != .TypeError) return method_ty;
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_struct_field, .{});
                return self.context.type_store.tTypeError();
            } else if (inner_kind == .Variant) {
                const vr = self.context.type_store.get(.Variant, ty);
                const variants = self.context.type_store.field_pool.slice(vr.variants);
                var i: usize = 0;
                while (i < variants.len) : (i += 1) {
                    const v = self.context.type_store.Field.get(variants[i]);
                    if (v.name.eq(field_expr.field)) {
                        // In value position, selecting a variant *tag* without args:
                        // if payload is void => ok (value of the variant type)
                        // else => arity mismatch (should be constructed via call)
                        const pk = self.typeKind(v.ty);
                        if (pk == .Void) {
                            try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                            return ty;
                        }
                        try self.context.diags.addError(exprLoc(ast_unit, field_expr), .variant_payload_arity_mismatch, .{});
                        return self.context.type_store.tTypeError();
                    }
                }
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_variant_tag, .{});
                return self.context.type_store.tTypeError();
            } else if (inner_kind == .Error) {
                const er = self.context.type_store.get(.Error, ty);
                const tags = self.context.type_store.field_pool.slice(er.variants);
                var i: usize = 0;
                while (i < tags.len) : (i += 1) {
                    const t = self.context.type_store.Field.get(tags[i]);
                    if (t.name.eq(field_expr.field)) {
                        try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                        return ty;
                    }
                }
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_error_tag, .{});
                return self.context.type_store.tTypeError();
            } else if (inner_kind == .Ast) {
                // Accessing a member on a module in type position: treat like the .Ast branch
                const ast_ty = self.context.type_store.get(.Ast, ty);
                const pkg_name = self.context.interner.get(ast_ty.pkg_name);
                const filepath = self.context.interner.get(ast_ty.filepath);
                const pkg = self.context.compilation_unit.packages.getPtr(pkg_name) orelse
                    return self.context.type_store.tTypeError();
                const parent_unit = pkg.sources.getPtr(filepath) orelse
                    return self.context.type_store.tTypeError();

                if (parent_unit.ast) |a| {
                    // Re-intern field name into the imported unit's interner before lookup
                    const field_name_mod = getStr(ast_unit, field_expr.field);
                    const target_sid = a.exprs.strs.intern(field_name_mod);
                    if (a.type_info.getExport(target_sid)) |ex| {
                        return ex.ty;
                    }
                }
                try self.context.diags.addError(field_loc, .unknown_module_field, .{getStr(ast_unit, field_expr.field)});
                return self.context.type_store.tTypeError();
            }
            if (inner_kind == .Struct or inner_kind == .Union or inner_kind == .Enum or inner_kind == .Variant or inner_kind == .Error) {
                const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, parent_ty, field_expr.field, field_loc) catch |err| switch (err) {
                    else => return self.context.type_store.tTypeError(),
                };
                if (self.typeKind(method_ty) != .TypeError) return method_ty;
            }
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .field_access_on_non_aggregate, .{inner_kind});
            return self.context.type_store.tTypeError();
        },
        .Variant => {
            const vty = self.context.type_store.get(.Variant, ty);
            const variants = self.context.type_store.field_pool.slice(vty.variants);
            if (field_expr.is_tuple) {
                const index = std.fmt.parseInt(usize, getStr(ast_unit, field_expr.field), 10) catch {
                    try self.context.diags.addError(exprLoc(ast_unit, field_expr), .expected_field_name_or_index, .{});
                    return self.context.type_store.tTypeError();
                };
                const runtime_fields: usize = if (variants.len == 0) 1 else 2;
                if (index >= runtime_fields) {
                    try self.context.diags.addError(exprLoc(ast_unit, field_expr), .tuple_index_out_of_bounds, .{});
                    return self.context.type_store.tTypeError();
                }
                try ast_unit.type_info.setFieldIndex(id, @intCast(index));
                if (index == 0) {
                    return self.context.type_store.tI32();
                }

                var union_fields_args = try self.gpa.alloc(types.TypeStore.StructFieldArg, variants.len);
                defer self.gpa.free(union_fields_args);
                for (variants, 0..) |fid, i| {
                    const fld = self.context.type_store.Field.get(fid);
                    union_fields_args[i] = .{ .name = fld.name, .ty = fld.ty };
                }
                return self.context.type_store.mkUnion(union_fields_args);
            }
            var i: usize = 0;
            while (i < variants.len) : (i += 1) {
                const variant = self.context.type_store.Field.get(variants[i]);
                if (variant.name.eq(field_expr.field)) {
                    try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                    // get variant payload type
                    const ty_kind = self.typeKind(variant.ty);
                    if (ty_kind == .Void) return self.context.type_store.tI32();
                    return variant.ty;
                }
            }
            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, ty, field_expr.field, field_loc) catch |err| switch (err) {
                else => return self.context.type_store.tTypeError(),
            };
            if (self.typeKind(method_ty) != .TypeError) return method_ty;
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_variant_tag, .{});
            return self.context.type_store.tTypeError();
        },
        else => {
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .field_access_on_non_aggregate, .{kind});
            return self.context.type_store.tTypeError();
        },
    }
}

fn checkRange(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const range = getExpr(ast_unit, .Range, id);
    var start_ty = if (!range.start.isNone()) try self.checkExpr(ctx, ast_unit, range.start.unwrap()) else null;
    var end_ty = if (!range.end.isNone()) try self.checkExpr(ctx, ast_unit, range.end.unwrap()) else null;

    if (start_ty == null and end_ty == null) {
        try self.context.diags.addError(exprLoc(ast_unit, range), .cannot_infer_range_type, .{});
        return self.context.type_store.tTypeError();
    }

    if (start_ty != null and end_ty != null and !start_ty.?.eq(end_ty.?)) {
        var l = start_ty.?;
        var r = end_ty.?;
        var lkind = self.typeKind(l);
        var rkind = self.typeKind(r);
        const l_is_lit = if (!range.start.isNone()) exprKind(ast_unit, range.start.unwrap()) == .Literal else false;
        const r_is_lit = if (!range.end.isNone()) exprKind(ast_unit, range.end.unwrap()) == .Literal else false;

        if (l_is_lit and check_types.isIntegerKind(self, rkind)) {
            if (try self.updateCoercedLiteral(ast_unit, range.start.unwrap(), r, &l, &lkind)) {
                start_ty = l;
            }
        } else if (r_is_lit and check_types.isIntegerKind(self, lkind)) {
            if (try self.updateCoercedLiteral(ast_unit, range.end.unwrap(), l, &r, &rkind)) {
                end_ty = r;
            }
        }
    }

    const final_ty = if (start_ty) |st| st else if (end_ty) |et| et else return self.context.type_store.tTypeError();

    if (start_ty != null and end_ty != null and !start_ty.?.eq(end_ty.?)) {
        try self.context.diags.addError(exprLoc(ast_unit, range), .range_type_mismatch, .{});
        return self.context.type_store.tTypeError();
    }

    const k = self.typeKind(final_ty);
    if (!check_types.isIntegerKind(self, k) and k != .Any) {
        try self.context.diags.addError(exprLoc(ast_unit, range), .range_requires_integer_operands, .{});
        return self.context.type_store.tTypeError();
    }
    return self.context.type_store.mkSlice(self.context.type_store.tUsize());
}

fn checkStructLit(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const struct_lit = getExpr(ast_unit, .StructLit, id);
    const lit_fields = ast_unit.exprs.sfv_pool.slice(struct_lit.fields);
    var buf = try self.context.type_store.gpa.alloc(types.TypeStore.StructFieldArg, lit_fields.len);
    defer self.context.type_store.gpa.free(buf);
    var i: usize = 0;
    while (i < lit_fields.len) : (i += 1) {
        const f = ast_unit.exprs.StructFieldValue.get(lit_fields[i]);
        const ft = try self.checkExpr(ctx, ast_unit, f.value);
        if (self.typeKind(ft) == .TypeError) return self.context.type_store.tTypeError();
        if (f.name.isNone()) {
            // Positional field. We can't handle this yet — emit a diagnostic.
            try self.context.diags.addError(exprLoc(ast_unit, struct_lit), .struct_field_name_mismatch, .{});
            return self.context.type_store.tTypeError();
        }
        buf[i] = .{ .name = f.name.unwrap(), .ty = ft };
    }
    const struct_ty = self.context.type_store.mkStruct(buf);
    if (struct_lit.ty.isNone()) {
        return struct_ty;
    }
    const lit_ty = struct_lit.ty.unwrap();
    const expect_ty = blk: {
        const resolved = try check_types.typeFromTypeExpr(self, ctx, ast_unit, lit_ty);
        if (resolved[0]) break :blk resolved[1];
        try self.context.diags.addError(exprLocFromId(ast_unit, lit_ty), .undefined_identifier, .{});
        return self.context.type_store.tTypeError();
    };
    const is_assignable = self.assignable(struct_ty, expect_ty);
    switch (is_assignable) {
        .success => {},
        .struct_field_count_mismatch => {
            try self.context.diags.addError(exprLoc(ast_unit, struct_lit), .struct_missing_field, .{});
            return self.context.type_store.tTypeError();
        },
        .unknown_struct_field => {
            try self.context.diags.addError(exprLoc(ast_unit, struct_lit), .unknown_struct_field, .{});
            return self.context.type_store.tTypeError();
        },
        .union_literal_multiple_fields => {
            try self.context.diags.addError(exprLoc(ast_unit, struct_lit), .union_literal_multiple_fields, .{});
            return self.context.type_store.tTypeError();
        },
        .union_empty_literal => {
            try self.context.diags.addError(exprLoc(ast_unit, struct_lit), .union_empty_literal, .{});
            return self.context.type_store.tTypeError();
        },
        else => {
            try self.context.diags.addError(exprLoc(ast_unit, struct_lit), .struct_field_type_mismatch, .{});
            return self.context.type_store.tTypeError();
        },
    }
    return expect_ty;
}

fn checkDeref(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const row = getExpr(ast_unit, .Deref, id);
    const ptr_ty = try self.checkExpr(ctx, ast_unit, row.expr);
    if (self.typeKind(ptr_ty) == .TypeError) return self.context.type_store.tTypeError();
    const kind = self.typeKind(ptr_ty);
    if (kind != .Ptr) {
        try self.context.diags.addError(exprLoc(ast_unit, row), .deref_non_pointer, .{});
        return self.context.type_store.tTypeError();
    }
    const ptr_row = self.context.type_store.get(.Ptr, ptr_ty);
    return ptr_row.elem;
}

// =========================
// Calls & related helpers
// =========================

fn resolveTagPayloadType(self: *Checker, parent_ty: types.TypeId, tag: ast.StrId) ?types.TypeId {
    const pk = self.trow(parent_ty);
    switch (pk) {
        .Variant => {
            const vt = self.context.type_store.Variant.get(self.trow(parent_ty));
            const cases = self.context.type_store.field_pool.slice(vt.variants);
            for (cases) |fid| {
                const f = self.context.type_store.Field.get(fid.toRaw());
                if (f.name.eq(tag)) return f.ty;
            }
        },
        .Error => {
            const et = self.context.type_store.Error.get(self.trow(parent_ty));
            const cases = self.context.type_store.field_pool.slice(et.variants);
            for (cases) |fid| {
                const f = self.context.type_store.Field.get(fid.toRaw());
                if (f.name.eq(tag)) return f.ty;
            }
        },
        else => {},
    }
    return self.context.type_store.tTypeError();
}

/// Handles `(Type).Tag(args...)` where `Type` is a Variant or Error.
/// Supports payload kinds: Void, Tuple, Struct (new).
fn checkTagConstructorCall(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    parent_ty: types.TypeId,
    tag: ast.StrId,
    args: []const ast.ExprId,
    loc: Loc,
) !types.TypeId {
    const pk = self.typeKind(parent_ty);
    if (pk != .Variant and pk != .Error) return self.context.type_store.tTypeError();

    // Load tag table
    const cases = if (pk == .Variant)
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, parent_ty).variants)
    else
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, parent_ty).variants);

    // Find the tag & payload type
    var payload_ty_opt: ?types.TypeId = null;
    for (cases) |cid| {
        const c = self.context.type_store.Field.get(cid);
        if (c.name.eq(tag)) {
            payload_ty_opt = c.ty;
            break;
        }
    }
    if (payload_ty_opt == null) {
        if (pk == .Variant) {
            try self.context.diags.addError(loc, .unknown_variant_tag, .{});
        } else {
            try self.context.diags.addError(loc, .unknown_error_tag, .{});
        }
        return self.context.type_store.tTypeError();
    }

    const payload_ty = payload_ty_opt.?;
    const payload_kind = self.typeKind(payload_ty);

    switch (payload_kind) {
        .Void => {
            // Tag-only: must have zero args
            if (args.len != 0) {
                try self.context.diags.addError(loc, .argument_count_mismatch, .{});
                return self.context.type_store.tTypeError();
            }
            return parent_ty;
        },
        .Tuple => {
            // Exact arity, per-element type check
            const tup = self.context.type_store.get(.Tuple, payload_ty);
            const params = self.context.type_store.type_pool.slice(tup.elems);

            if (args.len != params.len) {
                // IMPORTANT: only one arity diagnostic
                try self.context.diags.addError(loc, .argument_count_mismatch, .{});
                return self.context.type_store.tTypeError();
            }

            var i: usize = 0;
            while (i < args.len) : (i += 1) {
                var at = try self.checkExpr(ctx, ast_unit, args[i]);
                if (self.typeKind(at) == .TypeError) return self.context.type_store.tTypeError();
                var at_kind = self.typeKind(at);
                if (self.assignable(at, params[i]) != .success) {
                    if (check_types.isNumericKind(self, self.typeKind(params[i]))) {
                        if (try self.updateCoercedLiteral(ast_unit, args[i], params[i], &at, &at_kind) and
                            self.assignable(at, params[i]) == .success)
                        {
                            continue;
                        }
                    }
                    const expected_kind = self.typeKind(params[i]);
                    const actual_kind = at_kind;
                    // IMPORTANT: only one type diagnostic
                    try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_kind, actual_kind });
                    return self.context.type_store.tTypeError();
                }
            }
            return parent_ty;
        },
        else => {
            // Non-void, non-tuple payloads (e.g. struct) are not callable: use literals like Type.Tag{...}
            try self.context.diags.addError(loc, .call_non_callable, .{});
            return self.context.type_store.tTypeError();
        },
    }
}

fn checkCall(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const call_expr = getExpr(ast_unit, .Call, id);
    const call_loc = exprLoc(ast_unit, call_expr);
    const callee_kind = exprKind(ast_unit, call_expr.callee);
    const args = ast_unit.exprs.expr_pool.slice(call_expr.args);

    if (callee_kind == .FieldAccess) {
        const fr = getExpr(ast_unit, .FieldAccess, call_expr.callee);
        // Fast path B: (Type).Tag(...) for Variant/Error constructors — handle ONCE and return.
        const parent_of_field_access_ty = try self.checkExpr(ctx, ast_unit, fr.parent);
        const pk = self.typeKind(parent_of_field_access_ty);
        if (pk == .TypeType) {
            const inner_ty = self.context.type_store.get(.TypeType, parent_of_field_access_ty).of;
            const inner_pk = self.typeKind(inner_ty);
            if (inner_pk == .Variant or inner_pk == .Error) {
                const result_ty = try self.checkTagConstructorCall(ctx, ast_unit, inner_ty, fr.field, args, call_loc);
                if (self.typeKind(result_ty) != .TypeError) {
                    // Also stamp the type of the callee expression as a function type
                    if (self.getPayloadTypeForCase(inner_ty, fr.field)) |payload_ty| {
                        const payload_kind = self.typeKind(payload_ty);
                        const params: []const types.TypeId = if (payload_kind == .Void)
                            &.{}
                        else if (payload_kind == .Tuple)
                            self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, payload_ty).elems)
                        else
                            &.{payload_ty};
                        const fn_ty = self.context.type_store.mkFunction(params, inner_ty, false, false);
                        ast_unit.type_info.expr_types.items[call_expr.callee.toRaw()] = fn_ty;
                    }
                }
                return result_ty;
            }
        }
    }

    // Builtin: sizeof(T) -> u64
    if (callee_kind == .Ident) {
        const idr = getExpr(ast_unit, .Ident, call_expr.callee);
        const name = getStr(ast_unit, idr.name);
        if (std.mem.eql(u8, name, "sizeof")) {
            if (args.len != 1) {
                try self.context.diags.addError(call_loc, .argument_count_mismatch, .{});
                return self.context.type_store.tTypeError();
            }
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, args[0]);
            ast_unit.type_info.expr_types.items[args[0].toRaw()] = self.context.type_store.mkTypeType(res[1]);
            if (!res[0]) return self.context.type_store.tTypeError();
            const ty = res[1];
            const sz = check_types.typeSize(self.context, ty) orelse {
                try self.context.diags.addError(call_loc, .could_not_resolve_type, .{});
                return self.context.type_store.tTypeError();
            };
            _ = sz; // ensure used
            // Record a comptime value for potential constant folding (optional)
            try ast_unit.type_info.ensureExpr(self.gpa, id);
            ast_unit.type_info.expr_types.items[id.toRaw()] = self.context.type_store.tU64();
            // Stamp callee type so lower_tir can query it
            const any_type_ty = self.context.type_store.mkTypeType(self.context.type_store.tAny());
            const fn_ty = self.context.type_store.mkFunction(&.{any_type_ty}, self.context.type_store.tU64(), false, true);
            try ast_unit.type_info.ensureExpr(self.gpa, call_expr.callee);
            ast_unit.type_info.expr_types.items[call_expr.callee.toRaw()] = fn_ty;
            return self.context.type_store.tU64();
        }
    }

    // General case: the callee is a value expression.
    const func_ty_opt = try self.checkExpr(ctx, ast_unit, call_expr.callee);
    if (self.typeKind(func_ty_opt) == .TypeError) {
        if (callee_kind == .Ident) {
            const idr = getExpr(ast_unit, .Ident, call_expr.callee);
            if (self.lookup(ctx, idr.name) == null) {
                // already reported as undeclared identifier
                self.context.diags.messages.items[self.context.diags.messages.items.len - 1].code = .unknown_function;
            }
        }
        return self.context.type_store.tTypeError();
    }
    var func_ty = func_ty_opt;
    var func_kind = self.typeKind(func_ty);

    if (callee_kind == .FieldAccess and ast_unit.type_info.getMethodBinding(call_expr.callee) == null) {
        const field_expr = getExpr(ast_unit, .FieldAccess, call_expr.callee);
        const field_loc = exprLoc(ast_unit, field_expr);
        const parent_ty = try self.checkExpr(ctx, ast_unit, field_expr.parent);
        if (self.typeKind(parent_ty) == .TypeError) return self.context.type_store.tTypeError();
        const parent_kind = self.typeKind(parent_ty);
        const owner_ty = switch (parent_kind) {
            .Ptr => self.context.type_store.get(.Ptr, parent_ty).elem,
            .TypeType => self.context.type_store.get(.TypeType, parent_ty).of,
            else => parent_ty,
        };
        const receiver_ty = switch (parent_kind) {
            .TypeType => owner_ty,
            else => parent_ty,
        };
        const method_ty = self.resolveMethodFieldAccess(ast_unit, call_expr.callee, owner_ty, receiver_ty, field_expr.field, field_loc) catch |err| switch (err) {
            else => return self.context.type_store.tTypeError(),
        };
        if (self.typeKind(method_ty) != .TypeError) {
            func_ty = method_ty;
            func_kind = self.typeKind(func_ty);
            try ast_unit.type_info.clearFieldIndex(call_expr.callee);
        }
    }
    if (ast_unit.type_info.getMethodBinding(call_expr.callee)) |binding| {
        return try self.checkMethodCall(ctx, ast_unit, &call_expr, binding, args);
    }
    func_kind = self.typeKind(func_ty);
    if (func_kind == .Any) return self.context.type_store.tTypeError();

    // Tuple-as-constructor: `(T0,T1,..)(a0,a1,..)` -> construct the tuple type.
    if (func_kind == .Tuple) {
        const tup = self.context.type_store.get(.Tuple, func_ty);
        const params = self.context.type_store.type_pool.slice(tup.elems);
        if (args.len != params.len) {
            try self.context.diags.addError(call_loc, .argument_count_mismatch, .{});
            return self.context.type_store.tTypeError();
        }
        var i: usize = 0;
        while (i < args.len) : (i += 1) {
            // Arguments must be evaluated in value context
            try self.pushValueReq(ctx, true);
            var at = try self.checkExpr(ctx, ast_unit, args[i]);
            self.popValueReq(ctx);
            if (self.typeKind(at) == .TypeError) return self.context.type_store.tTypeError();
            var at_kind = self.typeKind(at);
            if (self.assignable(at, params[i]) != .success) {
                if (check_types.isNumericKind(self, self.typeKind(params[i]))) {
                    if (try self.updateCoercedLiteral(ast_unit, args[i], params[i], &at, &at_kind) and
                        self.assignable(at, params[i]) == .success)
                    {
                        continue;
                    }
                }
                const expected_kind = self.typeKind(params[i]);
                const actual_kind = at_kind;
                const loc = exprLocFromId(ast_unit, args[i]);
                try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_kind, actual_kind });
                return self.context.type_store.tTypeError();
            }
        }
        return func_ty;
    }

    if (func_kind != .Function) {
        try self.context.diags.addError(call_loc, .call_non_callable, .{});
        return self.context.type_store.tTypeError();
    }

    // Purity bookkeeping / enforcement
    const fnrow = self.context.type_store.get(.Function, func_ty);
    if (self.inFunction(ctx)) {
        const fctx = self.currentFunc(ctx).?;
        if (fctx.require_pure and !fnrow.is_pure) {
            try self.context.diags.addError(call_loc, .purity_violation, .{});
            return self.context.type_store.tTypeError();
        }
        if (!fnrow.is_pure) {
            const idx = ctx.func_stack.items.len - 1;
            ctx.func_stack.items[idx].pure = false;
        }
    }

    // Arity & argument type checks
    const params = self.context.type_store.type_pool.slice(fnrow.params);
    if (!fnrow.is_variadic) {
        var min_required = params.len;
        // If callee is a direct identifier to a function declaration with defaulted trailing params,
        // allow omitting those arguments.
        if (callee_kind == .Ident) {
            const idr = getExpr(ast_unit, .Ident, call_expr.callee);
            if (self.lookup(ctx, idr.name)) |sid| {
                const srow = ctx.symtab.syms.get(sid);
                if (!srow.origin_decl.isNone()) {
                    const did = srow.origin_decl.unwrap();
                    if (ast_unit.exprs.index.kinds.items[ast_unit.exprs.Decl.get(did).value.toRaw()] == .FunctionLit) {
                        if (self.countTrailingDefaultParams(ast_unit, did)) |defaults| {
                            if (defaults <= params.len) {
                                min_required = params.len - defaults;
                            }
                        }
                    }
                }
            }
        } else if (callee_kind == .FieldAccess) {
            // Also allow defaulted trailing params for module member functions accessed via field
            const fr = getExpr(ast_unit, .FieldAccess, call_expr.callee);
            // Detect if the parent is an import (direct or via identifier bound to an import decl)
            var path_sid_opt: ?ast.StrId = null;
            const pk = exprKind(ast_unit, fr.parent);
            if (pk == .Import) {
                const ir = getExpr(ast_unit, .Import, fr.parent);
                path_sid_opt = ir.path;
            } else if (pk == .Ident) {
                const idr2 = getExpr(ast_unit, .Ident, fr.parent);
                if (self.lookup(ctx, idr2.name)) |sid2| {
                    const sym2 = ctx.symtab.syms.get(sid2);
                    if (!sym2.origin_decl.isNone()) {
                        const did2 = sym2.origin_decl.unwrap();
                        const drow2 = ast_unit.exprs.Decl.get(did2);
                        if (exprKind(ast_unit, drow2.value) == .Import) {
                            const ir = getExpr(ast_unit, .Import, drow2.value);
                            path_sid_opt = ir.path;
                        }
                    }
                }
            }
            if (path_sid_opt) |path_sid| {
                const path = getStr(ast_unit, path_sid);
                var pkg_iter = self.context.compilation_unit.packages.iterator();
                while (pkg_iter.next()) |pkg| {
                    if (pkg.value_ptr.sources.get(path)) |unit_ref| {
                        if (unit_ref.ast) |a| {
                            if (a.type_info.getExport(fr.field)) |ex| {
                                if (self.countTrailingDefaultParams(a, ex.decl_id)) |defaults| {
                                    if (defaults <= params.len) {
                                        min_required = params.len - defaults;
                                    }
                                }
                            }
                        }
                        break;
                    }
                }
            }
        }
        if (!(args.len >= min_required and args.len <= params.len)) {
            try self.context.diags.addError(call_loc, .argument_count_mismatch, .{});
            return self.context.type_store.tTypeError();
        }
    } else {
        const min_required = if (params.len == 0) 0 else params.len - 1;
        if (args.len < min_required) {
            try self.context.diags.addError(call_loc, .argument_count_mismatch, .{});
            return self.context.type_store.tTypeError();
        }
    }

    var i: usize = 0;
    while (i < args.len) : (i += 1) {
        // Arguments must be evaluated in value context by default
        try self.pushValueReq(ctx, true);
        var at = try self.checkExpr(ctx, ast_unit, args[i]);
        self.popValueReq(ctx);
        if (self.typeKind(at) == .TypeError) return self.context.type_store.tTypeError();
        var at_kind = self.typeKind(at);
        const pt = if (!fnrow.is_variadic)
            (if (i < params.len) params[i] else params[params.len - 1])
        else blk: {
            const fixed = if (params.len == 0) 0 else params.len - 1;
            break :blk if (i < fixed) params[i] else params[params.len - 1];
        };
        // If the parameter expects a type (TypeType), interpret the argument as a type-expression when possible.
        if (self.typeKind(pt) == .TypeType and at_kind != .TypeType) {
            const type_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, args[i]);
            if (type_res[0]) {
                const tt = self.context.type_store.mkTypeType(type_res[1]);
                at = tt;
                at_kind = .TypeType;
                // Stamp expression type for tooling/lowering
                try ast_unit.type_info.ensureExpr(self.gpa, args[i]);
                ast_unit.type_info.expr_types.items[args[i].toRaw()] = tt;
            }
        }
        if (self.assignable(at, pt) != .success) {
            if (check_types.isNumericKind(self, self.typeKind(pt))) {
                if (try self.updateCoercedLiteral(ast_unit, args[i], pt, &at, &at_kind) and
                    self.assignable(at, pt) == .success)
                {
                    continue;
                }
            }
            const expected_kind = self.typeKind(pt);
            const actual_kind = at_kind;
            const loc = exprLocFromId(ast_unit, args[i]);
            try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_kind, actual_kind });
            return self.context.type_store.tTypeError();
        }
    }
    return fnrow.result;
}

fn countTrailingDefaultParams(_: *Checker, ast_unit: *ast.Ast, did: ast.DeclId) ?usize {
    const decl = ast_unit.exprs.Decl.get(did);
    if (ast_unit.exprs.index.kinds.items[decl.value.toRaw()] != .FunctionLit) return null;
    const fnr = ast_unit.exprs.get(.FunctionLit, decl.value);
    const params = ast_unit.exprs.param_pool.slice(fnr.params);
    if (params.len == 0) return 0;
    var count: usize = 0;
    var i: usize = params.len;
    while (i > 0) {
        i -= 1;
        const p = ast_unit.exprs.Param.get(params[i]);
        // Only consider runtime params; comptime params are always required
        if (p.is_comptime) break;
        if (p.value.isNone()) break;
        count += 1;
    }
    return count;
}

fn checkMethodCall(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    call_expr: *const ast.Rows.Call,
    binding: types.MethodBinding,
    args: []const ast.ExprId,
) !types.TypeId {
    const field_expr = getExpr(ast_unit, .FieldAccess, call_expr.callee);
    const receiver_ty = try self.checkExpr(ctx, ast_unit, field_expr.parent);
    if (self.typeKind(receiver_ty) == .TypeError) return self.context.type_store.tTypeError();

    if (binding.receiver_kind == .pointer or binding.receiver_kind == .pointer_const) {
        if (!binding.needs_addr_of and self.lvalueRootKind(ctx, ast_unit, field_expr.parent) == .Unknown and self.typeKind(receiver_ty) != .Ptr) {
            try self.context.diags.addError(exprLocFromId(ast_unit, field_expr.parent), .method_receiver_not_addressable, .{});
            return self.context.type_store.tTypeError();
        }
    }

    const fn_row = self.context.type_store.get(.Function, binding.func_type);
    const params = self.context.type_store.type_pool.slice(fn_row.params);
    const implicit_count: usize = if (binding.requires_implicit_receiver) 1 else 0;
    const total_args = args.len + implicit_count;

    if (!fn_row.is_variadic) {
        var min_required = params.len;
        // For method calls, allow defaulted trailing params defined on the method decl.
        if (ast_unit == binding.decl_ast) {
            if (self.countTrailingDefaultParams(binding.decl_ast, binding.decl_id)) |defaults| {
                if (defaults <= params.len) {
                    min_required = params.len - defaults;
                }
            }
        } else {
            if (self.countTrailingDefaultParams(binding.decl_ast, binding.decl_id)) |defaults| {
                if (defaults <= params.len) {
                    min_required = params.len - defaults;
                }
            }
        }
        if (!(total_args >= min_required and total_args <= params.len)) {
            try self.context.diags.addError(exprLoc(ast_unit, call_expr.*), .argument_count_mismatch, .{});
            return self.context.type_store.tTypeError();
        }
    } else {
        const min_required = if (params.len == 0) 0 else params.len - 1;
        if (total_args < min_required) {
            try self.context.diags.addError(exprLoc(ast_unit, call_expr.*), .argument_count_mismatch, .{});
            return self.context.type_store.tTypeError();
        }
    }

    if (binding.requires_implicit_receiver) {
        if (params.len == 0) {
            try self.context.diags.addError(exprLoc(ast_unit, call_expr.*), .argument_count_mismatch, .{});
            return self.context.type_store.tTypeError();
        }
        const self_param_ty = params[0];
        if (!binding.needs_addr_of) {
            if (self.assignable(receiver_ty, self_param_ty) != .success) {
                const expected_kind = self.typeKind(self_param_ty);
                const actual_kind = self.typeKind(receiver_ty);
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .argument_type_mismatch, .{ expected_kind, actual_kind });
                return self.context.type_store.tTypeError();
            }
        } else if (!receiver_ty.eq(binding.owner_type)) {
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .method_receiver_requires_pointer, .{getStr(ast_unit, binding.method_name)});
            return self.context.type_store.tTypeError();
        }
    }

    var i: usize = 0;
    while (i < args.len) : (i += 1) {
        // Arguments must be evaluated in value context
        try self.pushValueReq(ctx, true);
        var at = try self.checkExpr(ctx, ast_unit, args[i]);
        self.popValueReq(ctx);
        if (self.typeKind(at) == .TypeError) return self.context.type_store.tTypeError();
        var at_kind = self.typeKind(at);
        const param_index = i + implicit_count;
        const pt = if (!fn_row.is_variadic)
            (if (param_index < params.len) params[param_index] else params[params.len - 1])
        else blk: {
            const fixed = if (params.len == 0) 0 else params.len - 1;
            break :blk if (param_index < fixed) params[param_index] else params[params.len - 1];
        };
        // If the parameter expects a type (TypeType), interpret the argument as a type-expression when possible.
        if (self.typeKind(pt) == .TypeType and at_kind != .TypeType) {
            const type_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, args[i]);
            if (type_res[0]) {
                const tt = self.context.type_store.mkTypeType(type_res[1]);
                at = tt;
                at_kind = .TypeType;
                try ast_unit.type_info.ensureExpr(self.gpa, args[i]);
                ast_unit.type_info.expr_types.items[args[i].toRaw()] = tt;
            }
        }
        if (self.assignable(at, pt) != .success) {
            if (check_types.isNumericKind(self, self.typeKind(pt))) {
                if (try self.updateCoercedLiteral(ast_unit, args[i], pt, &at, &at_kind) and
                    self.assignable(at, pt) == .success)
                {
                    continue;
                }
            }
            const expected_kind = self.typeKind(pt);
            const actual_kind = at_kind;
            const loc = exprLocFromId(ast_unit, args[i]);
            try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_kind, actual_kind });
            return self.context.type_store.tTypeError();
        }
    }

    return fn_row.result;
}

// =========================
// Blocks, Return & Control
// =========================

fn checkCodeBlock(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const cb = getExpr(ast_unit, .CodeBlock, id);
    if (!ctx.warned_code) {
        try self.context.diags.addNote(exprLoc(ast_unit, cb), .checker_code_block_not_executed, .{});
        ctx.warned_code = true;
    }
    return try self.checkExpr(ctx, ast_unit, cb.block);
}

fn checkAsyncBlock(self: *Checker, id: ast.ExprId) !types.TypeId {
    _ = id;
    // Treat async blocks as opaque for typing.
    return self.context.type_store.tAny();
}

fn checkMlirBlock(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const row = ast_unit.exprs.get(.MlirBlock, id);
    const args = ast_unit.exprs.expr_pool.slice(row.args);
    for (args) |arg_id| {
        _ = try self.checkExpr(ctx, ast_unit, arg_id);
    }

    var has_splices = false;
    const pieces = ast_unit.exprs.mlir_piece_pool.slice(row.pieces);
    for (pieces) |pid| {
        const piece = ast_unit.exprs.MlirPiece.get(pid);
        if (piece.kind != .splice) continue;
        has_splices = true;

        const name = piece.text;
        const loc = exprLoc(ast_unit, row);
        const sym_id = self.lookup(ctx, name) orelse {
            try self.context.diags.addError(loc, .mlir_splice_unknown_identifier, .{getStr(ast_unit, name)});
            return self.context.type_store.tTypeError();
        };
        const sym = ctx.symtab.syms.get(sym_id);

        if (!sym.is_comptime) {
            std.debug.print("sym: {}\n", .{sym});
            try self.context.diags.addError(loc, .mlir_splice_not_comptime, .{getStr(ast_unit, name)});
            return self.context.type_store.tTypeError();
        }

        if (!sym.origin_decl.isNone() and sym.is_comptime) {
            const did = sym.origin_decl.unwrap();
            try ast_unit.type_info.setMlirSpliceInfo(pid, .{ .decl = .{ .decl_id = did, .name = name } });
            continue;
        }

        switch (sym.kind) {
            .Param => {
                if (!sym.is_comptime or sym.origin_param.isNone()) {
                    try self.context.diags.addError(loc, .mlir_splice_not_comptime, .{getStr(ast_unit, name)});
                    return self.context.type_store.tTypeError();
                }

                const pid_param = sym.origin_param.unwrap();
                const param_row = ast_unit.exprs.Param.get(pid_param);
                var param_ty = self.context.type_store.tAny();
                if (!param_row.ty.isNone()) {
                    const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, param_row.ty.unwrap());
                    if (res[0]) param_ty = res[1];
                }

                if (self.context.type_store.getKind(param_ty) == .TypeType) {
                    try ast_unit.type_info.setMlirSpliceInfo(pid, .{ .type_param = .{ .param_id = pid_param, .name = name, .ty = param_ty } });
                } else {
                    try ast_unit.type_info.setMlirSpliceInfo(pid, .{ .value_param = .{ .param_id = pid_param, .name = name, .ty = param_ty } });
                }
            },
            else => {
                try self.context.diags.addError(loc, .mlir_splice_not_comptime, .{getStr(ast_unit, name)});
                return self.context.type_store.tTypeError();
            },
        }
    }

    if (row.kind != .Operation and !ast_unit.type_info.hasComptimeValue(id) and !has_splices) {
        const ctx_ptr = self.pipeline.ensureMlirContext();
        const mlir_ctx = ctx_ptr.*;
        const text = getStr(ast_unit, row.text);
        const loc = exprLoc(ast_unit, row);

        var has_value: bool = false;
        var value: comp.ComptimeValue = .Void;
        switch (row.kind) {
            .Module => {
                var parsed_module = mlir.Module.createParse(mlir_ctx, mlir.StringRef.from(text));
                if (parsed_module.isNull()) {
                    try self.context.diags.addError(loc, .mlir_parse_error, .{text});
                    return self.context.type_store.tTypeError();
                }
                value = .{ .MlirModule = parsed_module };
                has_value = true;
            },
            .Type => {
                const parsed_type = mlir.Type.parseGet(mlir_ctx, mlir.StringRef.from(text));
                if (parsed_type.isNull()) {
                    try self.context.diags.addError(loc, .mlir_parse_error, .{text});
                    return self.context.type_store.tTypeError();
                }
                value = .{ .MlirType = parsed_type };
                has_value = true;
            },
            .Attribute => {
                const parsed_attr = mlir.Attribute.parseGet(mlir_ctx, mlir.StringRef.from(text));
                if (parsed_attr.isNull()) {
                    try self.context.diags.addError(loc, .mlir_parse_error, .{text});
                    return self.context.type_store.tTypeError();
                }
                value = .{ .MlirAttribute = parsed_attr };
                has_value = true;
            },
            .Operation => {},
        }

        if (has_value) {
            try ast_unit.type_info.setComptimeValue(id, value);
        }
    }

    const ts = self.context.type_store;
    return switch (row.kind) {
        .Module => ts.tMlirModule(),
        .Attribute => ts.tMlirAttribute(),
        .Type => ts.tMlirType(),
        .Operation => ts.tAny(),
    };
}

fn checkInsert(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const r = getExpr(ast_unit, .Insert, id);
    _ = try self.checkExpr(ctx, ast_unit, r.expr);
    return self.context.type_store.tAny();
}

fn checkReturn(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, rr: ast.Rows.Return) !types.TypeId {
    if (ctx.func_stack.items.len == 0) {
        try self.context.diags.addError(exprLoc(ast_unit, rr), .return_outside_function, .{});
        return self.context.type_store.tTypeError();
    }
    const current_func = ctx.func_stack.items[ctx.func_stack.items.len - 1];

    if (current_func.has_result and rr.value.isNone()) {
        try self.context.diags.addError(exprLoc(ast_unit, rr), .missing_return_value, .{});
        return self.context.type_store.tTypeError();
    }
    if (!current_func.has_result and !rr.value.isNone()) {
        try self.context.diags.addError(exprLoc(ast_unit, rr), .return_value_in_void_function, .{});
        return self.context.type_store.tTypeError();
    }

    const expect_ty = current_func.result;
    const ret_ty = if (rr.value.isNone()) self.context.type_store.tVoid() else blk: {
        try self.pushValueReq(ctx, true);
        const t = try self.checkExpr(ctx, ast_unit, rr.value.unwrap());
        self.popValueReq(ctx);
        break :blk t;
    };
    if (self.typeKind(ret_ty) == .TypeError) return self.context.type_store.tTypeError();

    if (self.assignable(ret_ty, expect_ty) != .success) {
        if (check_types.isNumericKind(self, self.typeKind(expect_ty))) {
            var coerced = ret_ty;
            var coerced_kind = self.typeKind(coerced);
            if (!rr.value.isNone() and
                try self.updateCoercedLiteral(ast_unit, rr.value.unwrap(), expect_ty, &coerced, &coerced_kind) and
                self.assignable(coerced, expect_ty) == .success)
            {
                return coerced;
            }
        }
        try self.context.diags.addError(exprLoc(ast_unit, rr), .return_type_mismatch, .{});
        return self.context.type_store.tTypeError();
    }
    return ret_ty;
}

fn checkIf(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const if_expr = getExpr(ast_unit, .If, id);
    const cond = try self.checkExpr(ctx, ast_unit, if_expr.cond);
    if (cond.toRaw() != self.context.type_store.tBool().toRaw()) {
        const cond_ty = self.typeKind(cond);
        try self.context.diags.addError(exprLoc(ast_unit, if_expr), .non_boolean_condition, .{cond_ty});
        return self.context.type_store.tTypeError();
    }

    const value_required = self.isValueReq(ctx);
    if (!value_required) {
        _ = try self.checkExpr(ctx, ast_unit, if_expr.then_block);
        if (!if_expr.else_block.isNone()) _ = try self.checkExpr(ctx, ast_unit, if_expr.else_block.unwrap());
        return self.context.type_store.tVoid();
    }

    const then_ty = try self.checkExpr(ctx, ast_unit, if_expr.then_block);
    if (self.typeKind(then_ty) == .TypeError) return self.context.type_store.tTypeError();
    if (if_expr.else_block.isNone()) {
        if (self.typeKind(then_ty) == .Noreturn) {
            return self.context.type_store.tNoreturn();
        }
        try self.context.diags.addError(exprLoc(ast_unit, if_expr), .if_expression_requires_else, .{});
        return self.context.type_store.tTypeError();
    }
    const else_ty = try self.checkExpr(ctx, ast_unit, if_expr.else_block.unwrap());
    if (self.typeKind(else_ty) == .TypeError) return self.context.type_store.tTypeError();

    const then_is_noreturn = self.typeKind(then_ty) == .Noreturn;
    const else_is_noreturn = self.typeKind(else_ty) == .Noreturn;

    if (then_is_noreturn and else_is_noreturn) {
        return self.context.type_store.tNoreturn();
    } else if (then_is_noreturn) {
        return else_ty;
    } else if (else_is_noreturn) {
        return then_ty;
    }

    if (then_ty.toRaw() != else_ty.toRaw()) {
        if (self.unifyTypes(then_ty, else_ty)) |u| {
            return u;
        }
        try self.context.diags.addError(exprLoc(ast_unit, if_expr), .if_branch_type_mismatch, .{});
        return self.context.type_store.tTypeError();
    }
    return then_ty;
}

fn unifyTypes(self: *Checker, a: types.TypeId, b: types.TypeId) ?types.TypeId {
    if (a.toRaw() == b.toRaw()) return a;
    const ak = self.typeKind(a);
    const bk = self.typeKind(b);

    // Any unifies to the other side
    if (ak == .Any) return b;
    if (bk == .Any) return a;

    // Optionals: unify payloads and rewrap
    if (ak == .Optional and bk == .Optional) {
        const ao = self.context.type_store.get(.Optional, a);
        const bo = self.context.type_store.get(.Optional, b);
        if (self.unifyTypes(ao.elem, bo.elem)) |elem|
            return self.context.type_store.mkOptional(elem);
        return null;
    }

    // Reuse assignability: prefer keeping the left if right can coerce into it, else vice-versa.
    if (self.assignable(b, a) == .success or self.castable(b, a)) return a;
    if (self.assignable(a, b) == .success or self.castable(a, b)) return b;

    // Numeric promotion: choose a common numeric type
    const a_is_num = check_types.isNumericKind(self, ak);
    const b_is_num = check_types.isNumericKind(self, bk);
    if (a_is_num and b_is_num) return self.unifyNumeric(a, b);

    return null;
}

fn unifyNumeric(self: *Checker, a: types.TypeId, b: types.TypeId) types.TypeId {
    const ak = self.typeKind(a);
    const bk = self.typeKind(b);

    // If either is float, pick the wider float
    const a_is_f32 = ak == .F32;
    const a_is_f64 = ak == .F64;
    const b_is_f32 = bk == .F32;
    const b_is_f64 = bk == .F64;
    if (a_is_f64 or b_is_f64) return self.context.type_store.tF64();
    if (a_is_f32 or b_is_f32) return self.context.type_store.tF32();

    // Prefer usize if present (index-sized math)
    if (ak == .Usize or bk == .Usize) return self.context.type_store.tUsize();

    // Otherwise, choose the wider integer width; on tie, prefer unsigned if one side is unsigned.
    const asz_opt = check_types.typeSize(self.context, a);
    const bsz_opt = check_types.typeSize(self.context, b);
    const asz: usize = asz_opt orelse 0;
    const bsz: usize = bsz_opt orelse 0;
    if (asz > bsz) return a;
    if (bsz > asz) return b;

    // Same width: prefer unsigned kind if any
    const a_unsigned = (ak == .U8 or ak == .U16 or ak == .U32 or ak == .U64);
    const b_unsigned = (bk == .U8 or bk == .U16 or bk == .U32 or bk == .U64);
    if (a_unsigned and !b_unsigned) return a;
    if (b_unsigned and !a_unsigned) return b;
    // Fallback: keep left
    return a;
}

fn checkWhile(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const wr = getExpr(ast_unit, .While, id);

    if (!wr.cond.isNone() and wr.pattern.isNone()) {
        // C-like while loop
        const cond_ty = try self.checkExpr(ctx, ast_unit, wr.cond.unwrap());
        if (self.typeKind(cond_ty) == .TypeError) return self.context.type_store.tTypeError();
        const ck = self.typeKind(cond_ty);
        if (ck != .Bool and ck != .Any) {
            try self.context.diags.addError(exprLoc(ast_unit, wr), .non_boolean_condition, .{ck});
            return self.context.type_store.tTypeError();
        }
    } else if (!wr.cond.isNone() and !wr.pattern.isNone()) {
        // Pattern-matching while
        const subj_ty = try self.checkExpr(ctx, ast_unit, wr.cond.unwrap());
        if (self.typeKind(subj_ty) == .TypeError) return self.context.type_store.tTypeError();
        if (!(try pattern_matching.checkPattern(self, ctx, ast_unit, wr.pattern.unwrap(), subj_ty, true))) {
            return self.context.type_store.tTypeError();
        }
        // Declare pattern bindings into the current (enclosing) scope so they persist after the loop
        try pattern_matching.declareBindingsInPattern(self, ctx, ast_unit, wr.pattern.unwrap(), wr.loc, .anonymous);
        try self.pushLoopBinding(ctx, wr.pattern, subj_ty);
    } else if (wr.cond.isNone() and wr.pattern.isNone()) {
        // Infinite loop: ok
    } else {
        // Defensive: unexpected combination; treat as a plain loop.
    }

    try self.pushLoop(ctx, wr.label);
    defer self.popLoop(ctx);
    const need_pop_loop_binding = (!wr.cond.isNone() and !wr.pattern.isNone());
    defer {
        if (need_pop_loop_binding) self.popLoopBinding(ctx);
    }

    const body_ty = try self.checkExpr(ctx, ast_unit, wr.body);

    if (self.isValueReq(ctx)) {
        if (self.loopCtxForLabel(ctx, wr.label)) |context| {
            if (context.result_ty) |ty| return ty;
            return self.context.type_store.tTypeError();
        }
    }
    return body_ty;
}

fn checkUnreachable(self: *Checker, _: ast.ExprId) !types.TypeId {
    return self.context.type_store.tAny();
}

fn checkFor(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const fr = getExpr(ast_unit, .For, id);
    const it = try self.checkExpr(ctx, ast_unit, fr.iterable);
    const kind = self.typeKind(it);

    switch (kind) {
        .Array, .Slice, .DynArray => {
            const pat_kind = ast_unit.pats.index.kinds.items[fr.pattern.toRaw()];
            const subject_ty: types.TypeId = switch (pat_kind) {
                .Slice => it,
                else => switch (kind) {
                    .Array => self.context.type_store.get(.Array, it).elem,
                    .Slice => self.context.type_store.get(.Slice, it).elem,
                    .DynArray => self.context.type_store.get(.DynArray, it).elem,
                    else => self.context.type_store.tAny(),
                },
            };
            if (!(try pattern_matching.checkPattern(self, ctx, ast_unit, fr.pattern, subject_ty, true))) {
                return self.context.type_store.tTypeError();
            }
            try self.pushLoopBinding(ctx, .some(fr.pattern), subject_ty);
        },
        else => {
            try self.context.diags.addError(exprLoc(ast_unit, fr), .non_iterable_in_for, .{});
            return self.context.type_store.tTypeError();
        },
    }
    try self.pushLoop(ctx, fr.label);
    defer self.popLoop(ctx);
    defer self.popLoopBinding(ctx);

    const body_ty = try self.checkExpr(ctx, ast_unit, fr.body);
    if (self.isValueReq(ctx)) {
        if (self.loopCtxForLabel(ctx, fr.label)) |context| {
            if (context.result_ty) |ty| return ty;
            return self.context.type_store.tTypeError();
        }
    }
    return body_ty;
}

// =========================
// Casts, Catch, Optionals
// =========================

fn castable(self: *Checker, got: types.TypeId, expect: types.TypeId) bool {
    if (got.eq(expect)) return true;
    const gk = self.typeKind(got);
    const ek = self.typeKind(expect);

    // Optional promotion: allow T -> Optional(T)
    if (ek == .Optional) {
        const opt = self.context.type_store.get(.Optional, expect);
        if (self.assignable(got, opt.elem) == .success) return true;
        // Reuse castability rules for the element type
        if (self.castable(got, opt.elem)) return true;
    }

    // SIMD vector casts
    if (gk == .Simd and ek == .Simd) {
        const vsimd = self.context.type_store.get(.Simd, got);
        const tsimd = self.context.type_store.get(.Simd, expect);
        if (vsimd.lanes == tsimd.lanes) {
            const velem_kind = self.typeKind(vsimd.elem);
            const telem_kind = self.typeKind(tsimd.elem);

            const velem_is_num = check_types.isNumericKind(self, velem_kind);
            const telem_is_num = check_types.isNumericKind(self, telem_kind);

            if (velem_is_num and telem_is_num) {
                return true;
            }
        }
    }

    // Numeric <-> numeric (no implicit *value* coercion, but casts allowed)
    const num_ok =
        switch (gk) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize => true,
            else => false,
        } and
        switch (ek) {
            .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Usize => true,
            else => false,
        };
    if (num_ok) return true;

    // Pointer-to-pointer
    if (gk == .Ptr and ek == .Ptr) return true;

    return false;
}

fn checkBreak(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, br: ast.Rows.Break) !types.TypeId {
    if (!self.inLoop(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, br), .break_outside_loop, .{});
        return self.context.type_store.tTypeError();
    }

    var val_ty: ?types.TypeId = null;
    if (!br.value.isNone()) {
        val_ty = try self.checkExpr(ctx, ast_unit, br.value.unwrap());
        if (val_ty == null) return self.context.type_store.tTypeError();
    }

    if (self.loopCtxForLabel(ctx, br.label)) |context| {
        if (!br.value.isNone()) {
            if (context.result_ty) |rt| {
                if (val_ty.?.toRaw() != rt.toRaw()) {
                    try self.context.diags.addError(exprLoc(ast_unit, br), .loop_break_value_type_conflict, .{});
                    return self.context.type_store.tTypeError();
                }
            } else context.result_ty = val_ty.?;
            return val_ty.?;
        } else {
            // unlabeled/valueless break in value position yields void
            return self.context.type_store.tVoid();
        }
    }
    return self.context.type_store.tTypeError();
}

fn checkContinue(self: *Checker, id: ast.ExprId) !types.TypeId {
    _ = id;
    return self.context.type_store.tVoid();
}

fn checkDefer(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, defer_expr: ast.Rows.Defer) !types.TypeId {
    if (!self.inFunction(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, defer_expr), .defer_outside_function, .{});
    }
    _ = try self.checkExpr(ctx, ast_unit, defer_expr.expr);
    return self.context.type_store.tVoid();
}

fn checkErrDefer(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, errdefer_expr: ast.Rows.ErrDefer) !types.TypeId {
    if (!self.inFunction(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, errdefer_expr), .errdefer_outside_function, .{});
        return self.context.type_store.tTypeError();
    }
    const current_func = self.currentFunc(ctx).?;
    if (!current_func.has_result or self.typeKind(current_func.result) != .ErrorSet) {
        try self.context.diags.addError(exprLoc(ast_unit, errdefer_expr), .errdefer_in_non_error_function, .{});
        return self.context.type_store.tTypeError();
    }
    const ty = try self.checkExpr(ctx, ast_unit, errdefer_expr.expr);
    if (self.typeKind(ty) == .TypeError)
        return self.context.type_store.tTypeError();
    return self.context.type_store.tVoid();
}

fn checkErrUnwrap(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const eur = getExpr(ast_unit, .ErrUnwrap, id);
    const et = try self.checkExpr(ctx, ast_unit, eur.expr);
    if (self.typeKind(et) == .TypeError)
        return self.context.type_store.tTypeError();
    if (self.typeKind(et) != .ErrorSet) {
        try self.context.diags.addError(exprLoc(ast_unit, eur), .error_propagation_on_non_error, .{});
        return self.context.type_store.tTypeError();
    }
    const er = self.context.type_store.get(.ErrorSet, et);

    if (!self.inFunction(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, eur), .error_propagation_mismatched_function_result, .{});
        return self.context.type_store.tTypeError();
    }
    const fctx = self.currentFunc(ctx).?;
    const fk = self.typeKind(fctx.result);
    if (fk != .ErrorSet) {
        try self.context.diags.addError(exprLoc(ast_unit, eur), .error_propagation_mismatched_function_result, .{});
        return self.context.type_store.tTypeError();
    }

    // Ensure the error/value halves align with the function result type
    const fr = self.context.type_store.get(.ErrorSet, fctx.result);
    if (self.assignable(er.error_ty, fr.error_ty) != .success or self.assignable(er.value_ty, fr.value_ty) != .success) {
        try self.context.diags.addError(exprLoc(ast_unit, eur), .error_propagation_mismatched_function_result, .{});
        return self.context.type_store.tTypeError();
    }
    return er.value_ty;
}

fn checkOptionalUnwrap(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const our = getExpr(ast_unit, .OptionalUnwrap, id);
    const ot = try self.checkExpr(ctx, ast_unit, our.expr);
    if (self.typeKind(ot) == .TypeError)
        return self.context.type_store.tTypeError();
    if (self.typeKind(ot) != .Optional) {
        try self.context.diags.addError(exprLoc(ast_unit, our), .invalid_optional_unwrap_target, .{});
        return self.context.type_store.tTypeError();
    }
    const ore = self.context.type_store.get(.Optional, ot);
    return ore.elem;
}

fn checkAwait(self: *Checker, id: ast.ExprId) !types.TypeId {
    _ = id;
    return self.context.type_store.tAny();
}

fn checkClosure(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const cr = getExpr(ast_unit, .Closure, id);
    const params = ast_unit.exprs.param_pool.slice(cr.params);

    var param_tys = try self.context.type_store.gpa.alloc(types.TypeId, params.len);
    defer self.context.type_store.gpa.free(param_tys);

    var i: usize = 0;
    while (i < params.len) : (i += 1) {
        const p = ast_unit.exprs.Param.get(params[i]);
        if (p.ty.isNone()) {
            try self.context.diags.addError(exprLoc(ast_unit, p), .type_annotation_mismatch, .{});
            return self.context.type_store.tTypeError();
        }
        const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, p.ty.unwrap());
        if (!res[0])
            return self.context.type_store.tTypeError();
        const pt = res[1];
        param_tys[i] = pt;
    }

    const body_ty = try self.checkExpr(ctx, ast_unit, cr.body);
    if (self.typeKind(body_ty) == .TypeError)
        return self.context.type_store.tTypeError();
    // Closures are always pure function *types* (no side-effect tracking here).
    return self.context.type_store.mkFunction(param_tys, body_ty, false, true);
}

fn checkCast(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const cr = getExpr(ast_unit, .Cast, id);
    const et_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, cr.ty);
    if (!et_res[0]) {
        try self.context.diags.addError(exprLoc(ast_unit, cr), .cast_target_not_type, .{});
        return self.context.type_store.tTypeError();
    }
    const et = et_res[1];
    const vt = try self.checkExpr(ctx, ast_unit, cr.expr);
    if (self.typeKind(vt) == .TypeError)
        return self.context.type_store.tTypeError();

    const vk = self.typeKind(vt);
    const ek = self.typeKind(et);

    switch (cr.kind) {
        .normal => {
            if (self.assignable(vt, et) != .success and !self.castable(vt, et)) {
                try self.context.diags.addError(exprLoc(ast_unit, cr), .invalid_cast, .{ vk, ek });
                return self.context.type_store.tTypeError();
            }
        },
        .bitcast => {
            const gsize = check_types.typeSize(self.context, vt);
            const tsize = check_types.typeSize(self.context, et);
            if (vk == .Any or ek == .Any) {} else if (gsize == null or tsize == null or gsize.? != tsize.?) {
                try self.context.diags.addError(exprLoc(ast_unit, cr), .invalid_bitcast, .{ vk, ek });
            }
        },
        .saturate, .wrap => {
            if (!check_types.isNumericKind(self, vk) or !check_types.isNumericKind(self, ek)) {
                try self.context.diags.addError(exprLoc(ast_unit, cr), .numeric_cast_on_non_numeric, .{});
                return self.context.type_store.tTypeError();
            }
        },
        .checked => {
            if (self.assignable(vt, et) != .success and !self.castable(vt, et)) {
                try self.context.diags.addError(exprLoc(ast_unit, cr), .invalid_checked_cast, .{});
                return self.context.type_store.tTypeError();
            }
            return self.context.type_store.mkOptional(et);
        },
    }
    return et;
}

fn checkCatch(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const row = getExpr(ast_unit, .Catch, id);
    const lhs_ty = try self.checkExpr(ctx, ast_unit, row.expr);

    if (self.typeKind(lhs_ty) == .TypeError) return self.context.type_store.tTypeError();

    const lhs_kind = self.typeKind(lhs_ty);
    var result_ty: types.TypeId = undefined;
    var es_info: types.Rows.ErrorSet = undefined;
    if (lhs_kind == .ErrorSet) {
        es_info = self.context.type_store.get(.ErrorSet, lhs_ty);
        result_ty = es_info.value_ty;
    } else {
        try self.context.diags.addError(exprLoc(ast_unit, row), .catch_on_non_error, .{});
        return self.context.type_store.tTypeError();
    }

    // TODO: Support full patterns in `catch` expressions. This would require
    // changing the AST and parser to use a pattern ID instead of just a binding name.
    var handler_ty: ?types.TypeId = null;
    if (!row.binding_name.isNone()) {
        const name = row.binding_name.unwrap();
        try self.pushCatchBinding(ctx, name, es_info.error_ty);
        handler_ty = try self.checkExpr(ctx, ast_unit, row.handler);
        self.popCatchBinding(ctx);
    } else {
        handler_ty = try self.checkExpr(ctx, ast_unit, row.handler);
    }

    if (handler_ty == null) return self.context.type_store.tTypeError();

    // If this catch expression is used in a statement (no value required),
    // allow a void handler (side effects only). The overall expression then
    // has type void, unless the handler is noreturn.
    if (!self.isValueReq(ctx)) {
        if (self.typeKind(handler_ty.?) == .Noreturn) {
            return self.context.type_store.tNoreturn();
        }
        return self.context.type_store.tVoid();
    }

    // Allow handler to be noreturn (early exit), in which case the
    // overall catch expression has the value type on the success path.
    if (self.typeKind(handler_ty.?) == .Noreturn) {
        return result_ty;
    }

    const want_ok_ty = es_info.value_ty;
    if (self.assignable(handler_ty.?, want_ok_ty) != .success and !self.castable(handler_ty.?, want_ok_ty)) {
        try self.context.diags.addError(exprLoc(ast_unit, row), .catch_handler_type_mismatch, .{});
        return self.context.type_store.tTypeError();
    }

    return result_ty;
}

fn checkImport(self: *Checker, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ir = getExpr(ast_unit, .Import, id);
    const filepath = getStr(ast_unit, ir.path);
    for (self.context.compilation_unit.packages.values()) |pkg| {
        if (pkg.sources.get(filepath) == null) continue;
        const pkg_name = self.context.interner.intern(pkg.name);
        const ast_ty = self.context.type_store.mkAst(pkg_name, ir.path);
        ast_unit.type_info.expr_types.items[id.toRaw()] = ast_ty; // Explicitly store here
        return ast_ty;
    }

    try self.context.diags.addError(ast_unit.exprs.locs.get(ir.loc), .import_not_found, .{});
    return self.context.type_store.tTypeError();
}

// =========================
// Misc helpers
// =========================

fn checkDivByZero(self: *Checker, ast_unit: *ast.Ast, rhs: ast.ExprId, loc: Loc) !void {
    if (exprKind(ast_unit, rhs) != .Literal) return;
    const lit = getExpr(ast_unit, .Literal, rhs);
    switch (lit.kind) {
        .int => {
            const info = switch (lit.data) {
                .int => |int_info| int_info,
                else => return,
            };
            if (!info.valid) return;
            if (info.value == 0) {
                try self.context.diags.addError(loc, .division_by_zero, .{});
            }
        },
        .float, .imaginary => {
            const f = switch (lit.data) {
                .float => |float_info| float_info,
                .imaginary => |imag_info| imag_info,
                else => return,
            };
            if (!f.valid) return;
            if (f.value == 0.0) try self.context.diags.addError(loc, .division_by_zero, .{});
        },
        else => {},
    }
}

fn checkIntZeroLiteral(self: *Checker, ast_unit: *ast.Ast, rhs: ast.ExprId, loc: Loc) !void {
    if (exprKind(ast_unit, rhs) != .Literal) return;
    const lit = getExpr(ast_unit, .Literal, rhs);
    if (lit.kind == .int) {
        const info = switch (lit.data) {
            .int => |int_info| int_info,
            else => return,
        };
        if (!info.valid) return;
        if (info.value == 0) try self.context.diags.addError(loc, .division_by_zero, .{});
    }
}

const LvalueRootKind = enum { LocalDecl, Param, NonLocalDecl, Unknown };
fn lvalueRootKind(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, expr: ast.ExprId) LvalueRootKind {
    const k = exprKind(ast_unit, expr);
    switch (k) {
        .Ident => {
            const idr = getExpr(ast_unit, .Ident, expr);
            // Discard assignment '_' is considered local
            if (std.mem.eql(u8, getStr(ast_unit, idr.name), "_")) return .LocalDecl;
            if (self.lookup(ctx, idr.name)) |sid_sym| {
                const sym = ctx.symtab.syms.get(sid_sym);
                if (!sym.origin_param.isNone()) return .Param;
                if (!sym.origin_decl.isNone()) {
                    const did = sym.origin_decl.unwrap();
                    if (self.inFunction(ctx)) {
                        const fctx = self.currentFunc(ctx).?;
                        return if (fctx.locals.contains(did.toRaw())) .LocalDecl else .NonLocalDecl;
                    }
                    return .NonLocalDecl;
                }
            }
            return .Unknown;
        },
        .Deref => {
            const dr = getExpr(ast_unit, .Deref, expr);
            return self.lvalueRootKind(ctx, ast_unit, dr.expr);
        },
        .FieldAccess => {
            const fr = getExpr(ast_unit, .FieldAccess, expr);
            return self.lvalueRootKind(ctx, ast_unit, fr.parent);
        },
        .IndexAccess => {
            const ir = getExpr(ast_unit, .IndexAccess, expr);
            return self.lvalueRootKind(ctx, ast_unit, ir.collection);
        },
        else => return .Unknown,
    }
}
