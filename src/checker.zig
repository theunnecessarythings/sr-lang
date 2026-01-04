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
const call_resolution = @import("call_resolution.zig");
const interpreter = @import("interpreter.zig");
const symbols = @import("symbols.zig");
const types = @import("types.zig");
const TypeInfo = types.TypeInfo;
const MethodBinding = types.MethodBinding;
const MethodEntry = types.MethodEntry;
const mlir = @import("mlir_bindings.zig");

const List = std.ArrayList;
const Map = std.AutoArrayHashMapUnmanaged;
const SpecializationCache = std.HashMapUnmanaged(types.SpecializationKey, ast.DeclId, types.SpecializationKeyContext, std.hash_map.default_max_load_percentage);

/// Primary semantic analysis driver that owns global/checker-wide data.
pub const Checker = @This();

gpa: std.mem.Allocator,
context: *Context,
pipeline: *Pipeline,
checker_ctx: List(?*CheckerContext), // Indexed by file_id
expr_id_scratch: List(ast.ExprId) = .{},
expr_id_scratch_marks: List(usize) = .{},
cached_typeinfo_ty: ?types.TypeId = null,
cached_codeinfo_ty: ?types.TypeId = null,

/// Per-AST context that tracks symbol tables, loops, matches, and diagnostic state.
pub const CheckerContext = struct {
    symtab: symbols.SymbolStore,
    interp: ?interpreter.Interpreter = null,

    // Stacks
    func_stack: List(FunctionCtx) = .{},
    loop_stack: List(LoopCtx) = .{},
    value_ctx: List(bool) = .{},
    expected_ty_stack: List(?types.TypeId) = .{},
    allow_nested_fn: List(bool) = .{},
    allow_insert_target: List(bool) = .{},
    insert_target_stack: List(InsertTarget) = .{},
    insert_site_stack: List(InsertSite) = .{},
    // Binding Scopes
    loop_binding_stack: List(LoopBindingCtx) = .{},
    catch_binding_stack: List(CatchBindingCtx) = .{},
    match_binding_stack: List(MatchBindingCtx) = .{},

    // State & Cache
    resolving_type_decls: std.DynamicBitSetUnmanaged = .{},
    resolving_type_exprs: std.DynamicBitSetUnmanaged = .{},
    param_specializations: List(ParamSpecialization) = .{},
    specialization_cache: SpecializationCache = .{},
    spec_arena: std.heap.ArenaAllocator,
    temp_arena: std.heap.ArenaAllocator,
    comptime_alias_bindings: List(interpreter.Binding) = .{},

    // Flags & Handles
    warned_code: bool = false,
    interp_loaded_stored_bindings: bool = false,
    stored_comptime_scope: ?interpreter.Interpreter.BindingScope = null,

    pub fn init(gpa: std.mem.Allocator) CheckerContext {
        return .{
            .symtab = symbols.SymbolStore.init(gpa),
            .spec_arena = std.heap.ArenaAllocator.init(gpa),
            .temp_arena = std.heap.ArenaAllocator.init(gpa),
        };
    }

    pub fn deinit(self: *CheckerContext, gpa: std.mem.Allocator) void {
        self.symtab.deinit();
        self.func_stack.deinit(gpa);
        self.loop_stack.deinit(gpa);
        self.value_ctx.deinit(gpa);
        self.expected_ty_stack.deinit(gpa);
        self.allow_nested_fn.deinit(gpa);
        self.allow_insert_target.deinit(gpa);
        self.insert_target_stack.deinit(gpa);
        self.insert_site_stack.deinit(gpa);
        self.loop_binding_stack.deinit(gpa);
        self.catch_binding_stack.deinit(gpa);
        self.match_binding_stack.deinit(gpa);
        self.resolving_type_decls.deinit(gpa);
        self.resolving_type_exprs.deinit(gpa);
        self.param_specializations.deinit(gpa);
        self.comptime_alias_bindings.deinit(gpa);
        self.specialization_cache.deinit(gpa);
        self.spec_arena.deinit();
        self.temp_arena.deinit();
        if (self.stored_comptime_scope) |*s| s.deinit();
        if (self.interp) |*i| i.deinit();
    }
};

// Context Helpers
const LoopBindingCtx = struct { pat: ast.OptPatternId, subject_ty: types.TypeId };
const MatchBindingCtx = struct { pat: ast.PatternId, subject_ty: types.TypeId };
const CatchBindingCtx = struct { name: ast.StrId, ty: types.TypeId };
const StringPayload = struct { value: []const u8 };
pub const ParamSpecialization = struct { name: ast.StrId, ty: types.TypeId };
pub const ComptimeParamBinding = struct { name: ast.StrId, ty: types.TypeId, value: comp.ValueId };
const InsertTarget = union(enum) {
    unit: void,
    block: struct { block_id: ast.ExprId, scope_id: symbols.ScopeId },
};
const InsertSite = struct { block_id: ast.ExprId, index: u32 };

const FunctionCtx = struct {
    result: types.TypeId,
    has_result: bool,
    pure: bool,
    require_pure: bool,
    locals: std.DynamicBitSetUnmanaged = .{},
    inferred_result: ?types.TypeId = null,
};

const LoopCtx = struct {
    label: ast.OptStrId,
    result_ty: ?types.TypeId = null,
};

// --- Checker Lifecycle ---

pub fn init(gpa: std.mem.Allocator, context: *Context, pipeline: *Pipeline) Checker {
    return .{ .gpa = gpa, .context = context, .pipeline = pipeline, .checker_ctx = .{}, .expr_id_scratch = .{}, .expr_id_scratch_marks = .{}, .cached_typeinfo_ty = null, .cached_codeinfo_ty = null };
}

pub fn deinit(self: *Checker) void {
    for (self.checker_ctx.items) |maybe| if (maybe) |ctx| {
        ctx.deinit(self.gpa);
        self.gpa.destroy(ctx);
    };
    self.checker_ctx.deinit(self.gpa);
    self.expr_id_scratch_marks.deinit(self.gpa);
    self.expr_id_scratch.deinit(self.gpa);
}

// --- Driver & Passes ---

/// Execute the checker across all AST units ordered by `levels`.
pub fn run(self: *Checker, levels: *const compile.DependencyLevels) !void {
    var max_file_id: u32 = 0;

    // 1. Index ASTs and find max ID
    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var src_iter = pkg.value_ptr.sources.iterator();
        while (src_iter.next()) |unit| if (unit.value_ptr.ast) |_| {
            max_file_id = @max(max_file_id, unit.value_ptr.file_id);
        };
    }

    var ast_by_file_id = try self.gpa.alloc(?*ast.Ast, max_file_id + 1);
    defer self.gpa.free(ast_by_file_id);
    @memset(ast_by_file_id, null);

    pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var src_iter = pkg.value_ptr.sources.iterator();
        while (src_iter.next()) |unit| if (unit.value_ptr.ast) |a| {
            ast_by_file_id[unit.value_ptr.file_id] = a;
        };
    }

    try self.checker_ctx.resize(self.gpa, max_file_id + 1);
    @memset(self.checker_ctx.items, null);

    // 2. Initialize Contexts & Predeclare (Order matters)
    for (levels.levels.items) |level| {
        for (level.items) |fid| {
            const ast_unit = ast_by_file_id[fid] orelse continue;
            var ctx = try self.gpa.create(CheckerContext);
            ctx.* = CheckerContext.init(self.gpa);

            // Pre-warm stacks
            try ctx.func_stack.ensureTotalCapacity(self.gpa, 8);
            try ctx.loop_stack.ensureTotalCapacity(self.gpa, 8);
            try ctx.value_ctx.ensureTotalCapacity(self.gpa, 16);

            self.checker_ctx.items[fid] = ctx;
            try self.ensureInterpreter(ast_unit, ctx);
            try self.predeclare(ast_unit, ctx);
        }
    }

    // 3. Type Check Declarations
    for (levels.levels.items) |level| {
        for (level.items) |fid| {
            const ast_unit = ast_by_file_id[fid] orelse continue;
            const ctx = self.checker_ctx.items[fid].?;
            const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
            // Copy to avoid invalidation if inserts mutate decl_pool during checking.
            const decl_copy = try self.gpa.alloc(ast.DeclId, decl_ids.len);
            defer self.gpa.free(decl_copy);
            @memcpy(decl_copy, decl_ids);
            for (decl_copy) |did| try self.checkDecl(ctx, ast_unit, did);
        }
    }
}

/// Walk the AST for `ast_unit`, binding top-level declarations and checking each node.
pub fn runAst(self: *Checker, ast_unit: *ast.Ast, ctx: *CheckerContext) !void {
    try self.ensureInterpreter(ast_unit, ctx);
    try self.predeclare(ast_unit, ctx);
    const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
    // Copy to avoid invalidation if inserts mutate decl_pool during checking.
    const decl_copy = try self.gpa.alloc(ast.DeclId, decl_ids.len);
    defer self.gpa.free(decl_copy);
    @memcpy(decl_copy, decl_ids);
    for (decl_copy) |did| try self.checkDecl(ctx, ast_unit, did);
}

// --- Stack & State Management Helpers ---

inline fn stmtLoc(ast_unit: *ast.Ast, sid: ast.StmtId) Loc {
    return switch (ast_unit.kind(sid)) {
        .Expr => exprLocFromId(ast_unit, getStmt(ast_unit, .Expr, sid).expr),
        .Decl => exprLoc(ast_unit, ast_unit.exprs.Decl.get(getStmt(ast_unit, .Decl, sid).decl)),
        inline else => |x| exprLoc(ast_unit, getStmt(ast_unit, x, sid)),
    };
}

pub inline fn typeKind(self: *const Checker, t: types.TypeId) types.TypeKind {
    return self.context.type_store.getKind(t);
}
inline fn exprLocFromId(ast_unit: *ast.Ast, eid: ast.ExprId) Loc {
    @setEvalBranchQuota(10000);
    return switch (ast_unit.kind(eid)) {
        inline else => |x| exprLoc(ast_unit, getExpr(ast_unit, x, eid)),
    };
}
inline fn exprLoc(ast_unit: *ast.Ast, expr: anytype) Loc {
    return ast_unit.exprs.locs.get(expr.loc);
}
inline fn patternLoc(ast_unit: *ast.Ast, pid: ast.PatternId) Loc {
    const loc_id = switch (ast_unit.kind(pid)) {
        .Wildcard => ast_unit.pats.get(.Wildcard, pid).loc,
        .Literal => ast_unit.pats.get(.Literal, pid).loc,
        .Path => ast_unit.pats.get(.Path, pid).loc,
        .Binding => ast_unit.pats.get(.Binding, pid).loc,
        .Tuple => ast_unit.pats.get(.Tuple, pid).loc,
        .Slice => ast_unit.pats.get(.Slice, pid).loc,
        .Struct => ast_unit.pats.get(.Struct, pid).loc,
        .VariantTuple => ast_unit.pats.get(.VariantTuple, pid).loc,
        .VariantStruct => ast_unit.pats.get(.VariantStruct, pid).loc,
        .Range => ast_unit.pats.get(.Range, pid).loc,
        .Or => ast_unit.pats.get(.Or, pid).loc,
        .At => ast_unit.pats.get(.At, pid).loc,
    };
    return ast_unit.exprs.locs.get(loc_id);
}
inline fn getStmt(ast_unit: *ast.Ast, comptime K: ast.StmtKind, id: ast.StmtId) ast.StmtRowT(K) {
    return ast_unit.stmts.get(K, id);
}
pub inline fn getStr(ast_unit: *const ast.Ast, sid: ast.StrId) []const u8 {
    return ast_unit.exprs.strs.get(sid);
}
inline fn getExpr(ast_unit: *ast.Ast, comptime K: ast.ExprKind, id: ast.ExprId) ast.RowT(K) {
    return ast_unit.exprs.get(K, id);
}

pub fn acquireExprIdsScratch(self: *Checker) !void {
    try self.expr_id_scratch_marks.append(self.gpa, self.expr_id_scratch.items.len);
}
pub fn releaseExprIdsScratch(self: *Checker) void {
    self.expr_id_scratch.shrinkRetainingCapacity(self.expr_id_scratch_marks.pop().?);
}

fn pushAllowNestedFn(self: *Checker, ctx: *CheckerContext, v: bool) !void {
    try ctx.allow_nested_fn.append(self.gpa, v);
}
fn popAllowNestedFn(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.allow_nested_fn.items.len > 0) _ = ctx.allow_nested_fn.pop();
}
fn isNestedFnAllowed(_: *const Checker, ctx: *CheckerContext) bool {
    return if (ctx.allow_nested_fn.items.len > 0) ctx.allow_nested_fn.items[ctx.allow_nested_fn.items.len - 1] else false;
}

fn pushAllowInsertTarget(self: *Checker, ctx: *CheckerContext, v: bool) !void {
    try ctx.allow_insert_target.append(self.gpa, v);
}
fn popAllowInsertTarget(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.allow_insert_target.items.len > 0) _ = ctx.allow_insert_target.pop();
}
fn isInsertTargetAllowed(_: *const Checker, ctx: *CheckerContext) bool {
    return if (ctx.allow_insert_target.items.len > 0) ctx.allow_insert_target.items[ctx.allow_insert_target.items.len - 1] else true;
}
fn pushInsertTarget(self: *Checker, ctx: *CheckerContext, target: InsertTarget) !void {
    try ctx.insert_target_stack.append(self.gpa, target);
}
fn popInsertTarget(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.insert_target_stack.items.len > 0) _ = ctx.insert_target_stack.pop();
}
fn currentInsertTarget(_: *const Checker, ctx: *CheckerContext) InsertTarget {
    return if (ctx.insert_target_stack.items.len > 0) ctx.insert_target_stack.items[ctx.insert_target_stack.items.len - 1] else .{ .unit = {} };
}
fn pushInsertSite(self: *Checker, ctx: *CheckerContext, site: InsertSite) !void {
    try ctx.insert_site_stack.append(self.gpa, site);
}
fn popInsertSite(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.insert_site_stack.items.len > 0) _ = ctx.insert_site_stack.pop();
}
fn currentInsertSite(_: *const Checker, ctx: *CheckerContext) ?*InsertSite {
    if (ctx.insert_site_stack.items.len == 0) return null;
    return &ctx.insert_site_stack.items[ctx.insert_site_stack.items.len - 1];
}
pub fn bindDeclPattern(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, did: ast.DeclId) !void {
    const decl = ast_unit.exprs.Decl.get(did);
    if (!decl.pattern.isNone()) try pattern_matching.declareBindingsInPattern(self, ctx, ast_unit, decl.pattern.unwrap(), decl.loc, .{ .decl = did });
}

fn bindParamPattern(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, pid: ast.ParamId, p: ast.Rows.Param) !void {
    if (!p.pat.isNone()) try pattern_matching.declareBindingsInPattern(self, ctx, ast_unit, p.pat.unwrap(), p.loc, .{ .param = pid });
}

fn pushFunc(self: *Checker, ctx: *CheckerContext, r_ty: types.TypeId, has_res: bool, req_pure: bool) !void {
    try ctx.func_stack.append(self.gpa, .{ .result = r_ty, .has_result = has_res, .pure = true, .require_pure = req_pure });
    try ctx.func_stack.items[ctx.func_stack.items.len - 1].locals.resize(self.gpa, 64, false);
}
fn popFunc(self: *Checker, ctx: *CheckerContext) void {
    if (ctx.func_stack.items.len > 0) {
        var c = &ctx.func_stack.items[ctx.func_stack.items.len - 1];
        c.locals.deinit(self.gpa);
        _ = ctx.func_stack.pop();
    }
}
fn inFunction(_: *const Checker, ctx: *CheckerContext) bool {
    return ctx.func_stack.items.len > 0;
}
fn currentFunc(_: *const Checker, ctx: *CheckerContext) ?*FunctionCtx {
    return if (ctx.func_stack.items.len > 0) &ctx.func_stack.items[ctx.func_stack.items.len - 1] else null;
}

fn pushLoop(self: *Checker, ctx: *CheckerContext, label: ast.OptStrId) !void {
    try ctx.loop_stack.append(self.gpa, .{ .label = label });
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
    return if (ast_unit.kind(pid) == .Binding) ast_unit.pats.get(.Binding, pid).name else null;
}

fn destroyComptimeBindings(_: *Checker, _: []const check_types.Binding) void {}

fn recordComptimeBlockSnapshot(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    baseline: *const std.AutoArrayHashMapUnmanaged(ast.StrId, comp.ValueId),
) !void {
    const count = ast_unit.type_info.comptime_bindings.count();
    if (count == 0) return;

    var diff_count: usize = 0;
    var it = ast_unit.type_info.comptime_bindings.iterator();
    while (it.next()) |entry| {
        if (baseline.get(entry.key_ptr.*)) |prev| {
            if (prev == entry.value_ptr.value) continue;
        }
        diff_count += 1;
    }
    if (diff_count == 0) return;

    const names = try self.gpa.alloc(ast.StrId, diff_count);
    const tys = try self.gpa.alloc(types.TypeId, diff_count);
    const vals = try self.gpa.alloc(comp.ValueId, diff_count);
    defer {
        self.gpa.free(names);
        self.gpa.free(tys);
        self.gpa.free(vals);
    }

    var i: usize = 0;
    it = ast_unit.type_info.comptime_bindings.iterator();
    while (it.next()) |entry| {
        if (baseline.get(entry.key_ptr.*)) |prev| {
            if (prev == entry.value_ptr.value) continue;
        }
        names[i] = entry.key_ptr.*;
        tys[i] = entry.value_ptr.ty;
        vals[i] = entry.value_ptr.value;
        i += 1;
    }
    try ast_unit.type_info.storeComptimeBlockSnapshot(expr_id, names, tys, vals);
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
    var i = @as(isize, @intCast(ctx.catch_binding_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        if (ctx.catch_binding_stack.items[@intCast(i)].name.eq(name)) return ctx.catch_binding_stack.items[@intCast(i)].ty;
    }
    return null;
}

inline fn bindingTypeFromActiveMatches(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, name: ast.StrId) ?types.TypeId {
    var i = @as(isize, @intCast(ctx.match_binding_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const c = ctx.match_binding_stack.items[@intCast(i)];
        if (pattern_matching.bindingTypeInPattern(self, ast_unit, c.pat, name, c.subject_ty)) |t| return t;
    }
    return null;
}

inline fn bindingTypeFromActiveLoops(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, name: ast.StrId) ?types.TypeId {
    var i = @as(isize, @intCast(ctx.loop_binding_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const c = ctx.loop_binding_stack.items[@intCast(i)];
        if (!c.pat.isNone()) if (pattern_matching.bindingTypeInPattern(self, ast_unit, c.pat.unwrap(), name, c.subject_ty)) |t| return t;
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
    return if (ctx.value_ctx.items.len > 0) ctx.value_ctx.items[ctx.value_ctx.items.len - 1] else true;
}

fn pushExpectedType(self: *Checker, ctx: *CheckerContext, ty: ?types.TypeId) !void {
    try ctx.expected_ty_stack.append(self.gpa, ty);
}
fn popExpectedType(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.expected_ty_stack.items.len > 0) _ = ctx.expected_ty_stack.pop();
}
pub fn getExpectedType(_: *const Checker, ctx: *CheckerContext) ?types.TypeId {
    return if (ctx.expected_ty_stack.items.len > 0) ctx.expected_ty_stack.items[ctx.expected_ty_stack.items.len - 1] else null;
}

pub fn lookup(_: *Checker, ctx: *CheckerContext, name: ast.StrId) ?symbols.SymbolId {
    return ctx.symtab.lookup(ctx.symtab.currentId(), name);
}

fn loopCtxForLabel(_: *Checker, ctx: *CheckerContext, opt_label: ast.OptStrId) ?*LoopCtx {
    if (ctx.loop_stack.items.len == 0) return null;
    const want = if (!opt_label.isNone()) opt_label.unwrap() else null;
    var i = @as(isize, @intCast(ctx.loop_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const lc = &ctx.loop_stack.items[@intCast(i)];
        if (want == null or (!lc.label.isNone() and lc.label.unwrap().eq(want.?))) return lc;
    }
    return null;
}

fn appendComptimeValueBinding(self: *Checker, ast_unit: *ast.Ast, bindings: *List(check_types.Binding), pname: ast.StrId, ty: types.TypeId) !void {
    if (ast_unit.type_info.comptime_bindings.get(pname)) |e| try bindings.append(self.gpa, .{ .Value = .{ .name = pname, .value = e.value, .ty = ty } });
}

fn getModuleSymtab(ctx: *anyopaque, file_id: u32) ?*symbols.SymbolStore {
    const self: *Checker = @ptrCast(@alignCast(ctx));
    if (file_id >= self.checker_ctx.items.len) return null;
    return if (self.checker_ctx.items[file_id]) |c| &c.symtab else null;
}

pub const StringNotePayload = struct { value: ast.StrId };

fn levenshteinDistance(allocator: std.mem.Allocator, s1: []const u8, s2: []const u8) ?usize {
    const s1_len = s1.len;
    const s2_len = s2.len;
    if (s1_len == 0) return s2_len;
    if (s2_len == 0) return s1_len;

    // Optimization: Use stack buffer for small strings to avoid allocation
    var stack_buf: [64]usize = undefined;
    var dp: []usize = &stack_buf;

    if (s1_len + 1 > stack_buf.len) {
        dp = allocator.alloc(usize, s1_len + 1) catch return null;
    }
    defer if (s1_len + 1 > stack_buf.len) allocator.free(dp);

    for (0..s1_len + 1) |i| dp[i] = i;

    for (1..s2_len + 1) |j| {
        var prev = dp[0];
        dp[0] = j;
        for (1..s1_len + 1) |i| {
            const temp = dp[i];
            const cost: usize = if (s1[i - 1] == s2[j - 1]) 0 else 1;
            dp[i] = @min(@min(dp[i - 1] + 1, dp[i] + 1), prev + cost);
            prev = temp;
        }
    }
    return dp[s1_len];
}

fn findBestSuggestion(self: *Checker, target: []const u8, candidates: []const []const u8) ?[]const u8 {
    var best: ?[]const u8 = null;
    var min_dist: usize = 3;
    for (candidates) |c| if (levenshteinDistance(self.gpa, target, c)) |d| if (d < min_dist) {
        min_dist = d;
        best = c;
    };
    return best;
}

fn appendFieldNames(self: *Checker, list: *List([]const u8), fields: []const types.FieldId) !void {
    for (fields) |id| try list.append(self.gpa, self.context.interner.get(self.context.type_store.Field.get(id).name));
}

fn appendEnumMemberNames(self: *Checker, list: *List([]const u8), members: []const types.EnumMemberId) !void {
    for (members) |id| try list.append(self.gpa, self.context.interner.get(self.context.type_store.EnumMember.get(id).name));
}

fn attachSuggestionListNotes(self: *Checker, diag_idx: usize, target: []const u8, candidates: []const []const u8, comptime sugg_code: diag.NoteCode, comptime avail_code: ?diag.NoteCode) !void {
    if (candidates.len == 0) return;
    if (self.findBestSuggestion(target, candidates)) |s| try self.context.diags.attachNoteArgs(diag_idx, null, sugg_code, .{s});
    if (avail_code) |c| {
        const joined = try diag.joinStrings(self.gpa, ", ", candidates);
        defer self.gpa.free(joined);
        if (joined.len > 0) try self.context.diags.attachNoteArgs(diag_idx, null, c, StringNotePayload{ .value = self.context.interner.intern(joined) });
    }
}

fn considerSymbolSuggestion(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, name: []const u8, seen: *List(ast.StrId), best: *?[]const u8, min: *usize, sym_id: symbols.SymbolId) !void {
    const sym = ctx.symtab.syms.get(sym_id);
    for (seen.items) |s| if (s.eq(sym.name)) return;
    try seen.append(self.gpa, sym.name);
    const sname = ast_unit.exprs.strs.get(sym.name);
    if (sname.len == 0) return;
    if (levenshteinDistance(self.gpa, name, sname)) |d| if (d < min.*) {
        min.* = d;
        best.* = sname;
    };
}

fn formatTypeForNote(self: *Checker, type_id: types.TypeId) !ast.StrId {
    var buf = List(u8){};
    defer buf.deinit(self.gpa);
    try self.context.type_store.formatTypeForDiagnostic(type_id, .{}, buf.writer(self.gpa));
    return self.context.interner.intern(buf.items);
}

fn attachFunctionSignatureNote(self: *Checker, idx: usize, func_ty: types.TypeId) !void {
    try self.context.diags.attachNoteArgs(idx, null, .function_signature, StringNotePayload{ .value = try formatTypeForNote(self, func_ty) });
}

fn attachTryCastNote(self: *Checker, idx: usize, expected_ty: types.TypeId) !void {
    var buf = List(u8){};
    defer buf.deinit(self.gpa);
    try buf.writer(self.gpa).print("cast to ", .{});
    try self.context.type_store.formatTypeForDiagnostic(expected_ty, .{}, buf.writer(self.gpa));
    try self.context.diags.attachNoteArgs(idx, null, .try_cast, StringNotePayload{ .value = self.context.interner.intern(buf.items) });
}

fn checkDivByZero(self: *Checker, ast_unit: *ast.Ast, rhs: ast.ExprId, loc: Loc) !void {
    if (ast_unit.kind(rhs) != .Literal) return;
    const lit = getExpr(ast_unit, .Literal, rhs);
    switch (lit.kind) {
        .int => if (lit.data.int.valid and lit.data.int.value == 0) try self.context.diags.addError(loc, .division_by_zero, .{}),
        .float, .imaginary => {
            const v = if (lit.kind == .float) lit.data.float.value else lit.data.imaginary.value;
            if (v == 0.0) try self.context.diags.addError(loc, .division_by_zero, .{});
        },
        else => {},
    }
}

fn checkIntZeroLiteral(self: *Checker, ast_unit: *ast.Ast, rhs: ast.ExprId, loc: Loc) !void {
    if (ast_unit.kind(rhs) != .Literal) return;
    const lit = getExpr(ast_unit, .Literal, rhs);
    if (lit.kind == .int and lit.data.int.valid and lit.data.int.value == 0) try self.context.diags.addError(loc, .division_by_zero, .{});
}

const LvalueRootKind = enum { LocalDecl, Param, NonLocalDecl, Unknown };

fn lvalueRootKind(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, expr: ast.ExprId) LvalueRootKind {
    switch (ast_unit.kind(expr)) {
        .Ident => {
            const id = getExpr(ast_unit, .Ident, expr);
            if (std.mem.eql(u8, getStr(ast_unit, id.name), "_")) return .LocalDecl;
            if (self.lookup(ctx, id.name)) |sid| {
                const sym = ctx.symtab.syms.get(sid);
                if (!sym.origin_param.isNone()) return .Param;
                if (!sym.origin_decl.isNone()) {
                    if (self.inFunction(ctx)) {
                        const f = self.currentFunc(ctx).?;
                        const raw = sym.origin_decl.unwrap().toRaw();
                        return if (f.locals.capacity() > raw and f.locals.isSet(raw)) .LocalDecl else .NonLocalDecl;
                    }
                    return .NonLocalDecl;
                }
            }
            return .Unknown;
        },
        .Deref => return self.lvalueRootKind(ctx, ast_unit, getExpr(ast_unit, .Deref, expr).expr),
        .FieldAccess => return self.lvalueRootKind(ctx, ast_unit, getExpr(ast_unit, .FieldAccess, expr).parent),
        .IndexAccess => return self.lvalueRootKind(ctx, ast_unit, getExpr(ast_unit, .IndexAccess, expr).collection),
        else => return .Unknown,
    }
}

pub fn ensureInterpreter(self: *Checker, ast_unit: *ast.Ast, ctx: *CheckerContext) anyerror!void {
    if (ctx.interp == null) ctx.interp = try interpreter.Interpreter.init(self.gpa, ast_unit, &ctx.symtab, &self.context.compilation_unit, getModuleSymtab, self);
    if (!ctx.interp_loaded_stored_bindings) {
        ctx.interp_loaded_stored_bindings = true;
        if (ast_unit.type_info.comptime_bindings.count() > 0) {
            var tmp = List(interpreter.Binding){};
            defer tmp.deinit(self.gpa);
            var it = ast_unit.type_info.comptime_bindings.iterator();
            while (it.next()) |e| try tmp.append(self.gpa, .{ .name = e.key_ptr.*, .value = e.value_ptr.value, .store = &ast_unit.type_info.val_store });
            ctx.stored_comptime_scope = try ctx.interp.?.pushBindings(&tmp);
        }
    }
}

fn predeclare(self: *Checker, ast_unit: *ast.Ast, ctx: *CheckerContext) !void {
    const expr_len = ast_unit.exprs.index.kinds.items.len;
    const decl_len = ast_unit.exprs.Decl.list.len;

    // Batch allocations and initialization
    try ast_unit.type_info.expr_types.resize(ast_unit.type_info.gpa, expr_len);
    @memset(ast_unit.type_info.expr_types.items, null);

    try ast_unit.type_info.decl_types.resize(ast_unit.type_info.gpa, decl_len);
    @memset(ast_unit.type_info.decl_types.items, null);

    try ctx.resolving_type_exprs.resize(self.gpa, expr_len, false);
    try ctx.resolving_type_decls.resize(self.gpa, decl_len, false);

    _ = try ctx.symtab.push(null);
    if (ctx.allow_insert_target.items.len == 0) {
        try self.pushAllowInsertTarget(ctx, true);
        try self.pushInsertTarget(ctx, .{ .unit = {} });
    }

    const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);

    // Pass 1: Bind names
    for (decl_ids) |did| {
        try self.bindDeclPattern(ctx, ast_unit, did);
    }

    // Pass 2: Signatures & Methods
    for (decl_ids) |did| {
        const decl = ast_unit.exprs.Decl.get(did);
        if (ast_unit.kind(decl.value) == .FunctionLit) {
            try self.predeclareFunction(ctx, ast_unit, did);
            if (!decl.method_path.isNone()) {
                const sig_ty = ast_unit.type_info.decl_types.items[did.toRaw()] orelse self.context.type_store.tAny();
                _ = try self.registerMethodDecl(ctx, ast_unit, did, decl, sig_ty);
            }
        }
    }
}

pub fn evalComptimeExprBorrowed(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    expr: ast.ExprId,
    bindings: []const Pipeline.ComptimeBinding,
) anyerror!*const comp.ValueId {
    try self.ensureInterpreter(ast_unit, ctx);

    if (ast_unit.type_info.getComptimeValue(expr)) |cached| return cached;

    const interp = &ctx.interp.?;
    var alias_bindings = &ctx.comptime_alias_bindings;
    var binding_scope: interpreter.Interpreter.BindingScope = undefined;
    const has_scope = bindings.len > 0;

    defer {
        if (has_scope) {
            binding_scope.deinit();
            alias_bindings.clearRetainingCapacity();
        }
    }

    if (has_scope) {
        try alias_bindings.ensureTotalCapacity(self.gpa, bindings.len);
        for (bindings) |b| {
            const val = switch (b) {
                .type_param => interpreter.Binding{ .name = b.type_param.name, .value = interp.store().add(.Type, .{ .ty = b.type_param.ty }), .store = interp.store() },
                .value_param => blk: {
                    const src_store = @constCast(b.value_param.store);
                    const value_id = if (src_store == interp.store()) b.value_param.value else try interp.store().cloneValue(src_store, b.value_param.value);
                    break :blk interpreter.Binding{ .name = b.value_param.name, .value = value_id, .store = interp.store() };
                },
            };
            alias_bindings.appendAssumeCapacity(val);
        }
        binding_scope = try interp.pushBindings(alias_bindings);
    }

    const computed = try interp.evalExpr(expr);
    try ast_unit.type_info.setComptimeValue(expr, computed);
    return ast_unit.type_info.getComptimeValue(expr).?;
}

pub fn evalComptimeExpr(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, expr: ast.ExprId, bindings: []const Pipeline.ComptimeBinding) anyerror!comp.ValueId {
    const borrowed = try self.evalComptimeExprBorrowed(ctx, ast_unit, expr, bindings);
    return borrowed.*;
}

// =========================================================
// Declarations & Statements
// =========================================================

pub fn checkDecl(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, decl_id: ast.DeclId) !void {
    const decl = ast_unit.exprs.Decl.get(decl_id);

    if (!decl.pattern.isNone()) {
        try pattern_matching.declareBindingsInPattern(self, ctx, ast_unit, decl.pattern.unwrap(), decl.loc, .{ .decl = decl_id });
    }

    var expect_ty: ?types.TypeId = null;
    var expect_ok = true;
    if (!decl.ty.isNone()) {
        const ty_expr = decl.ty.unwrap();
        if (try check_types.findAnyTypeExpr(self.gpa, ast_unit, ty_expr)) |any_id| {
            try self.context.diags.addError(exprLocFromId(ast_unit, any_id), .invalid_any_type_annotation, .{});
            return;
        }
        const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, ty_expr);
        expect_ok = res[0];
        if (expect_ok) {
            expect_ty = res[1];
            ast_unit.type_info.decl_types.items[decl_id.toRaw()] = expect_ty.?;
        }
    }

    if (decl.ty.isNone()) {
        const vkind = ast_unit.kind(decl.value);
        const is_type_expr = switch (vkind) {
            .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => true,
            else => false,
        };
        if (is_type_expr) {
            if (try check_types.findAnyTypeExpr(self.gpa, ast_unit, decl.value)) |any_id| {
                try self.context.diags.addError(exprLocFromId(ast_unit, any_id), .invalid_any_type_annotation, .{});
                return;
            }
        }
    }

    try self.pushValueReq(ctx, true);
    defer self.popValueReq(ctx);

    const is_fn_lit = ast_unit.kind(decl.value) == .FunctionLit;
    const is_method = is_fn_lit and !decl.method_path.isNone();
    const in_func = self.inFunction(ctx);
    const push_nested = in_func and is_method;

    if (push_nested) try self.pushAllowNestedFn(ctx, true);

    try self.pushExpectedType(ctx, expect_ty);
    var rhs_ty = try self.checkExpr(ctx, ast_unit, decl.value);
    self.popExpectedType(ctx);

    if (push_nested) self.popAllowNestedFn(ctx);

    if (self.typeKind(rhs_ty) == .TypeError) return;

    if (push_nested) {
        _ = try self.registerMethodDecl(ctx, ast_unit, decl_id, decl, rhs_ty);
    }

    if (expect_ok) {
        try self.tryTypeCoercion(ctx, ast_unit, decl_id, rhs_ty, expect_ty);
    }

    if (!decl.pattern.isNone()) {
        const pat_id = decl.pattern.unwrap();

        switch (pattern_matching.checkPatternShapeForDecl(self, ast_unit, pat_id, rhs_ty)) {
            .ok => {},
            .tuple_arity_mismatch => {
                try self.context.diags.addError(exprLoc(ast_unit, decl), .tuple_arity_mismatch, .{ @as(i64, @intCast(tuplePatternLength(ast_unit, pat_id))), @as(i64, @intCast(tupleTypeLength(self, rhs_ty))) });
                return;
            },
            .struct_pattern_field_mismatch => {
                const fstr = if (structPatternFieldName(ast_unit, pat_id)) |n| ast_unit.exprs.strs.get(n) else "struct field";
                try self.context.diags.addError(exprLoc(ast_unit, decl), .struct_pattern_field_mismatch, StringPayload{ .value = fstr });
                return;
            },
            .pattern_shape_mismatch => {
                try self.context.diags.addError(exprLoc(ast_unit, decl), .pattern_shape_mismatch, StringPayload{ .value = "pattern shape mismatch" });
                return;
            },
        }

        // Comptime Binding & Type Narrowing
        if (ast_unit.kind(pat_id) == .Binding) {
            const binding = ast_unit.pats.get(.Binding, pat_id);
            var binding_ty = expect_ty orelse rhs_ty;

            if (self.evalComptimeExpr(ctx, ast_unit, decl.value, &[_]Pipeline.ComptimeBinding{}) catch null) |computed| {
                const s = &ast_unit.type_info.val_store;

                // Narrow `const T: type = int`
                if (self.typeKind(binding_ty) == .TypeType and s.kind(computed) == .Type) {
                    const of = self.context.type_store.get(.TypeType, binding_ty).of;
                    if (self.typeKind(of) == .Any or of.eq(binding_ty)) {
                        binding_ty = self.context.type_store.mkTypeType(s.get(.Type, computed).ty);
                        rhs_ty = binding_ty;
                        ast_unit.type_info.decl_types.items[decl_id.toRaw()] = binding_ty;
                        ast_unit.type_info.expr_types.items[decl.value.toRaw()] = binding_ty;
                    }
                }

                try ast_unit.type_info.setComptimeBinding(binding.name, binding_ty, computed);

                if (ctx.interp) |*interp| {
                    interp.setBinding(binding.name, computed) catch |e| return e;
                }
            }
        }
    }

    if (!in_func) {
        const final_ty = ast_unit.type_info.decl_types.items[decl_id.toRaw()] orelse rhs_ty;
        try self.recordExportsForDecl(ctx, ast_unit, decl_id, final_ty);
    }
}

// Inlined helpers for performance
inline fn tuplePatternLength(ast_unit: *ast.Ast, pid: ast.PatternId) usize {
    return if (ast_unit.kind(pid) == .Tuple) ast_unit.pats.pat_pool.slice(ast_unit.pats.get(.Tuple, pid).elems).len else 0;
}
inline fn tupleTypeLength(self: *Checker, ty: types.TypeId) usize {
    return if (self.typeKind(ty) == .Tuple) self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, ty).elems).len else 0;
}
inline fn structPatternFieldName(ast_unit: *ast.Ast, pid: ast.PatternId) ?ast.StrId {
    if (ast_unit.kind(pid) != .Struct) return null;
    const f = ast_unit.pats.field_pool.slice(ast_unit.pats.get(.Struct, pid).fields);
    return if (f.len > 0) ast_unit.pats.StructField.get(f[0]).name else null;
}

fn recordExportsForDecl(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, decl_id: ast.DeclId, value_ty: types.TypeId) !void {
    const decl = ast_unit.exprs.Decl.get(decl_id);
    if (decl.pattern.isNone()) return;

    const pattern = decl.pattern.unwrap();
    const sid = ctx.symtab.currentId();
    const scope = ctx.symtab.scopes.get(sid);

    // Check finalized symbols
    for (ctx.symtab.sym_pool.slice(scope.symbols)) |sym_id| {
        const s = ctx.symtab.syms.get(sym_id);
        if (!s.origin_decl.isNone() and s.origin_decl.unwrap().eq(decl_id)) {
            const bty = pattern_matching.bindingTypeInPattern(self, ast_unit, pattern, s.name, value_ty) orelse value_ty;
            try ast_unit.type_info.addExport(s.name, bty, decl_id);
        }
    }

    // Check active stack
    if (ctx.symtab.stack.items.len > 0) {
        const frame = ctx.symtab.stack.items[ctx.symtab.stack.items.len - 1];
        if (frame.id.eq(sid)) {
            for (frame.list.items) |sym_id| {
                const s = ctx.symtab.syms.get(sym_id);
                if (!s.origin_decl.isNone() and s.origin_decl.unwrap().eq(decl_id)) {
                    const bty = pattern_matching.bindingTypeInPattern(self, ast_unit, pattern, s.name, value_ty) orelse value_ty;
                    try ast_unit.type_info.addExport(s.name, bty, decl_id);
                }
            }
        }
    }
}

fn predeclareFunction(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, did: ast.DeclId) !void {
    const func = getExpr(ast_unit, .FunctionLit, ast_unit.exprs.Decl.get(did).value);
    const params = ast_unit.exprs.param_pool.slice(func.params);

    // Stack optimization for param types
    var pt_buf: [32]types.TypeId = undefined;
    const param_types = if (params.len <= 32) pt_buf[0..params.len] else try self.gpa.alloc(types.TypeId, params.len);
    defer if (params.len > 32) self.gpa.free(param_types);

    var bindings = List(check_types.Binding){};
    defer {
        self.destroyComptimeBindings(bindings.items);
        bindings.deinit(self.gpa);
    }

    var comptime_names = std.DynamicBitSetUnmanaged{};
    defer comptime_names.deinit(self.gpa);

    // Collect comptime names
    for (params) |pid| {
        const p = ast_unit.exprs.Param.get(pid);
        if (p.is_comptime and !p.pat.isNone()) {
            if (ast_unit.kind(p.pat.unwrap()) == .Binding) {
                const name = ast_unit.pats.get(.Binding, p.pat.unwrap()).name;
                const raw = name.toRaw();
                if (raw >= comptime_names.capacity()) try comptime_names.resize(self.gpa, raw + 1, false);
                comptime_names.set(raw);
            }
        }
    }

    for (params, 0..) |pid, i| {
        const p = ast_unit.exprs.Param.get(pid);
        var pty: types.TypeId = self.context.type_store.tAny();

        if (!p.ty.isNone()) {
            const ty_expr = p.ty.unwrap();
            if (ast_unit.kind(ty_expr) == .AnyType) {
                pty = self.context.type_store.tAny();
            } else if (try check_types.findAnyTypeExpr(self.gpa, ast_unit, ty_expr)) |any_id| {
                try self.context.diags.addError(exprLocFromId(ast_unit, any_id), .invalid_any_type_annotation, .{});
                pty = self.context.type_store.tTypeError();
            } else {
                const mentions = try check_types.exprMentionsAnyNameBitset(self.gpa, ast_unit, ty_expr, &comptime_names);
                if (!mentions) {
                    const res = try check_types.typeFromTypeExprWithBindings(self, ctx, ast_unit, ty_expr, bindings.items);
                    if (self.typeKind(res[1]) != .TypeError) pty = res[1];
                }
            }

            if (!p.pat.isNone()) {
                const pat_id = p.pat.unwrap();
                if (ast_unit.kind(pat_id) == .Binding) {
                    const name = ast_unit.pats.get(.Binding, pat_id).name;
                    if (self.typeKind(pty) != .TypeError) {
                        try bindings.append(self.gpa, .{ .Type = .{ .name = name, .ty = pty } });
                        if (p.is_comptime) try self.appendComptimeValueBinding(ast_unit, &bindings, name, pty);
                    }
                }
            }
        } else if (p.is_comptime) {
            pty = self.context.type_store.mkTypeType(pty);
        }
        param_types[i] = pty;
    }

    const res = if (!func.result_ty.isNone()) blk: {
        const ty_expr = func.result_ty.unwrap();
        if (try check_types.exprMentionsAnyNameBitset(self.gpa, ast_unit, ty_expr, &comptime_names)) break :blk self.context.type_store.tAny();
        break :blk (try check_types.typeFromTypeExprWithBindings(self, ctx, ast_unit, ty_expr, bindings.items))[1];
    } else self.context.type_store.tVoid();

    if (self.typeKind(res) == .TypeError) return;
    ast_unit.type_info.decl_types.items[did.toRaw()] = self.context.type_store.mkFunction(param_types, res, func.flags.is_variadic, true, func.flags.is_extern);
}

pub fn lookupParamSpecialization(_: *const Checker, ctx: *CheckerContext, name: ast.StrId) ?types.TypeId {
    var i = ctx.param_specializations.items.len;
    while (i > 0) {
        i -= 1;
        if (ctx.param_specializations.items[i].name.eq(name)) return ctx.param_specializations.items[i].ty;
    }
    return null;
}

pub fn checkSpecializedFunction(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    decl_id: ast.DeclId,
    specs: []const ParamSpecialization,
    snapshot_decl: ?ast.DeclId,
    comptime_params: []const ComptimeParamBinding,
) !types.TypeId {
    const decl = ast_unit.exprs.Decl.get(decl_id);

    // 1. Setup Scope
    const need_scope = ctx.symtab.stack.items.len == 0;
    if (need_scope) {
        _ = try ctx.symtab.push(null);
        // Bind decls to avoid resolving issues
        const decls = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
        for (decls) |did| try self.bindDeclPattern(ctx, ast_unit, did);
    }
    defer if (need_scope) ctx.symtab.pop();

    // 2. Setup Params
    const base_spec_len = ctx.param_specializations.items.len;
    if (specs.len > 0) try ctx.param_specializations.appendSlice(self.gpa, specs);
    defer ctx.param_specializations.items.len = base_spec_len;

    var interp_scope: ?interpreter.Interpreter.BindingScope = null;
    defer if (interp_scope) |*s| s.deinit();

    if (comptime_params.len > 0 and ctx.interp != null) {
        var tmp = std.ArrayListUnmanaged(interpreter.Binding){};
        defer tmp.deinit(self.gpa);
        try tmp.ensureTotalCapacity(self.gpa, comptime_params.len);
        for (comptime_params) |b| tmp.appendAssumeCapacity(.{ .name = b.name, .value = b.value, .store = &ast_unit.type_info.val_store });
        interp_scope = try ctx.interp.?.pushBindings(&tmp);
    }

    // 3. Backup Comptime Bindings & Setup Values
    const backup_struct = struct { name: ast.StrId, ty: ?types.TypeId, value: ?comp.ValueId };
    var ct_backups = try std.ArrayListUnmanaged(backup_struct).initCapacity(self.gpa, comptime_params.len);

    var val_bindings = List(check_types.Binding){};
    try val_bindings.ensureTotalCapacity(self.gpa, comptime_params.len);

    defer {
        // Restore backups
        for (ct_backups.items) |bk| {
            ast_unit.type_info.removeComptimeBinding(bk.name);
            if (bk.ty) |t| {
                if (bk.value) |v| {
                    ast_unit.type_info.setComptimeBinding(bk.name, t, v) catch {};
                }
            }
        }
        ct_backups.deinit(self.gpa);

        // Clean bindings
        self.destroyComptimeBindings(val_bindings.items);
        val_bindings.deinit(self.gpa);
    }

    for (comptime_params) |b| {
        const existing_val = if (ast_unit.type_info.comptime_bindings.get(b.name)) |e| e.value else null;
        ct_backups.appendAssumeCapacity(.{ .name = b.name, .ty = ast_unit.type_info.lookupComptimeBindingType(b.name), .value = existing_val });

        try ast_unit.type_info.setComptimeBinding(b.name, b.ty, b.value);

        const v = check_types.Binding{ .Value = .{ .name = b.name, .value = b.value, .ty = b.ty } };
        val_bindings.appendAssumeCapacity(v);
    }

    // 4. Snapshot Expr Types
    const backup_len = ast_unit.type_info.expr_types.items.len;
    const mark = self.expr_id_scratch.items.len;
    try self.acquireExprIdsScratch();
    defer self.releaseExprIdsScratch();

    try check_types.collectDeclExprs(self.gpa, ast_unit, decl_id, &self.expr_id_scratch);
    const expr_ids = self.expr_id_scratch.items[mark..];

    var removed_cv = List(comp.ValueId){};
    defer removed_cv.deinit(self.gpa);

    const TypeBackup = struct { idx: u32, ty: ?types.TypeId };
    var type_backups = try self.gpa.alloc(TypeBackup, expr_ids.len);
    defer self.gpa.free(type_backups);

    var tb_count: usize = 0;
    for (expr_ids) |eid| {
        // Clear comptime
        if (ast_unit.type_info.comptime_values.getEntry(eid)) |e| {
            _ = ast_unit.type_info.comptime_values.orderedRemove(eid);
            try removed_cv.append(self.gpa, e.value_ptr.*);
        }

        const raw = eid.toRaw();
        if (raw >= backup_len) continue;
        type_backups[tb_count] = .{ .idx = raw, .ty = ast_unit.type_info.expr_types.items[raw] };
        tb_count += 1;
        ast_unit.type_info.expr_types.items[raw] = null;
    }

    // Restore on exit
    defer {
        // Only restore valid range, items.len might have grown
        if (ast_unit.type_info.expr_types.items.len > backup_len)
            ast_unit.type_info.expr_types.items.len = backup_len;

        for (type_backups[0..tb_count]) |tb| {
            ast_unit.type_info.expr_types.items[tb.idx] = tb.ty;
        }
    }

    // 5. Check
    try self.pushAllowNestedFn(ctx, true);
    const res_ty = try self.checkFunctionLit(ctx, ast_unit, decl.value);
    self.popAllowNestedFn(ctx);

    // 6. Store Snapshot
    if (snapshot_decl) |tgt| {
        try check_types.storeSpecializationSnapshots(self, ast_unit, expr_ids, tgt);

        var cids = List(u32){};
        var cspecs = List(types.CallSpecialization){};
        defer {
            cids.deinit(self.gpa);
            cspecs.deinit(self.gpa);
        }

        for (expr_ids) |eid| if (ast_unit.type_info.call_specializations.get(eid.toRaw())) |s| {
            try cids.append(self.gpa, eid.toRaw());
            try cspecs.append(self.gpa, s);
        };

        if (cids.items.len > 0) try ast_unit.type_info.storeSpecializationCallSnapshot(tgt, cids.items, cspecs.items);

        if (comptime_params.len > 0) {
            _ = ctx.temp_arena.reset(.retain_capacity);
            const a = ctx.temp_arena.allocator();
            const names = try a.alloc(ast.StrId, comptime_params.len);
            const tys = try a.alloc(types.TypeId, comptime_params.len);
            const vals = try a.alloc(comp.ValueId, comptime_params.len);
            for (comptime_params, 0..) |b, i| {
                names[i] = b.name;
                tys[i] = b.ty;
                vals[i] = b.value;
            }
            try ast_unit.type_info.storeSpecializationComptimeSnapshot(self.gpa, tgt, names, tys, vals);
        }
    }

    return res_ty;
}

pub fn getOrInstantiateSpecialization(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    orig_decl: ast.DeclId,
    params: []const types.TypeId,
    ct_params: []const ComptimeParamBinding,
    ct_hashes: []const u64,
) !ast.DeclId {
    const digest = types.hashSpecialization(orig_decl.toRaw(), params, ct_hashes);
    const key = types.SpecializationKey{ .digest = digest, .original_decl_id = orig_decl.toRaw(), .param_types = params, .comptime_hashes = ct_hashes };

    if (ctx.specialization_cache.get(key)) |ex| {
        if (ex.toRaw() < ast_unit.type_info.decl_types.items.len) {
            if (ast_unit.type_info.decl_types.items[ex.toRaw()]) |sig| {
                if (self.typeKind(sig) == .Function) {
                    const fr = self.context.type_store.get(.Function, sig);
                    if (self.typeKind(fr.result) != .Any) return ex;
                }
            }
        }
    }

    const syn_id = ast.DeclId.fromRaw(@intCast(ast_unit.type_info.decl_types.items.len));
    try ast_unit.type_info.decl_types.append(ast_unit.type_info.gpa, null);

    const a = ctx.spec_arena.allocator();
    const k_dup = types.SpecializationKey{ .digest = digest, .original_decl_id = orig_decl.toRaw(), .param_types = try a.dupe(types.TypeId, params), .comptime_hashes = try a.dupe(u64, ct_hashes) };
    try ctx.specialization_cache.put(self.gpa, k_dup, syn_id);
    try ast_unit.type_info.synthetic_decls.append(self.gpa, syn_id.toRaw());

    const decl = ast_unit.exprs.Decl.get(orig_decl);
    if (ast_unit.kind(decl.value) != .FunctionLit) return syn_id;

    // Spec Collection Optimization: Use stack buffer for common case
    var spec_buf: [16]ParamSpecialization = undefined;
    var specs_list = if (params.len > 16) List(ParamSpecialization){} else null;
    defer if (specs_list) |*l| l.deinit(self.gpa);

    const fn_params = ast_unit.exprs.param_pool.slice(ast_unit.exprs.get(.FunctionLit, decl.value).params);
    var count: usize = 0;

    for (fn_params, 0..) |pid, i| {
        if (i >= params.len) break;
        const p = ast_unit.exprs.Param.get(pid);
        if (p.pat.isNone()) continue;
        if (bindingNameOfPattern(ast_unit, p.pat.unwrap())) |name| {
            const spec = ParamSpecialization{ .name = name, .ty = params[i] };
            if (specs_list) |*l| try l.append(self.gpa, spec) else {
                spec_buf[count] = spec;
                count += 1;
            }
        }
    }
    const specs = if (specs_list) |l| l.items else spec_buf[0..count];

    const fn_ty = try self.checkSpecializedFunction(ctx, ast_unit, orig_decl, specs, syn_id, ct_params);
    const fr = self.context.type_store.get(.Function, fn_ty);
    ast_unit.type_info.decl_types.items[syn_id.toRaw()] = self.context.type_store.mkFunction(params, fr.result, fr.is_variadic, fr.is_pure, fr.is_extern);
    return syn_id;
}

fn checkAttributes(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, attrs_opt: ast.OptRangeAttr) !void {
    if (attrs_opt.isNone()) return;
    const attrs = ast_unit.exprs.attr_pool.slice(attrs_opt.asRange());

    for (attrs) |aid| {
        const val_expr = ast_unit.exprs.Attribute.get(aid).value;
        if (val_expr.isNone()) continue;

        const expr = val_expr.unwrap();
        try self.pushValueReq(ctx, true);
        _ = try self.checkExpr(ctx, ast_unit, expr);
        self.popValueReq(ctx);

        _ = self.evalComptimeExprBorrowed(ctx, ast_unit, expr, &[_]Pipeline.ComptimeBinding{}) catch {
            try self.context.diags.addError(exprLocFromId(ast_unit, expr), .checker_comptime_not_executed, .{});
            continue;
        };
    }
}

fn ensureMethodIsFunction(self: *Checker, ast_unit: *ast.Ast, decl: ast.Rows.Decl, func_ty_id: types.TypeId) !bool {
    if (self.typeKind(func_ty_id) == .Function and ast_unit.kind(decl.value) == .FunctionLit) return true;
    try self.context.diags.addError(exprLoc(ast_unit, decl), .method_requires_function_value, .{});
    return false;
}

fn resolveOwnerType(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    owner_seg: ast.Rows.MethodPathSeg,
    out_owner_ty: *types.TypeId,
) !bool {
    const loc = ast_unit.exprs.locs.get(owner_seg.loc);
    const sym_id = self.lookup(ctx, owner_seg.name) orelse {
        try self.context.diags.addError(loc, .undefined_identifier, .{ast_unit.exprs.strs.get(owner_seg.name)});
        return false;
    };

    const sym = ctx.symtab.syms.get(sym_id);
    if (sym.origin_decl.isNone()) {
        try self.context.diags.addError(loc, .method_owner_not_struct, StringPayload{ .value = ast_unit.exprs.strs.get(owner_seg.name) });
        return false;
    }

    const decl_id = sym.origin_decl.unwrap();
    var owner_ty = if (ast_unit.type_info.decl_types.items[decl_id.toRaw()]) |t| t else blk: {
        const val = ast_unit.exprs.Decl.get(decl_id).value;
        const res = check_types.typeFromTypeExpr(self, ctx, ast_unit, val) catch .{ false, self.context.type_store.tTypeError() };
        var ty = res[1];

        if (self.typeKind(ty) == .TypeError) {
            ty = try self.checkExpr(ctx, ast_unit, val);
        }
        if (self.typeKind(ty) == .TypeError) return false;

        const wrapped = self.context.type_store.mkTypeType(ty);
        ast_unit.type_info.decl_types.items[decl_id.toRaw()] = wrapped;
        break :blk wrapped;
    };

    if (self.typeKind(owner_ty) == .TypeType) {
        owner_ty = self.context.type_store.get(.TypeType, owner_ty).of;
    }

    switch (self.typeKind(owner_ty)) {
        .Struct, .Union, .Enum, .Variant, .Error => {},
        else => {
            try self.context.diags.addError(loc, .method_owner_not_struct, .{owner_ty});
            return false;
        },
    }

    out_owner_ty.* = owner_ty;
    return true;
}

fn analyzeSelfParam(
    self: *Checker,
    ast_unit: *ast.Ast,
    owner_ty: types.TypeId,
    fn_lit: ast.Rows.FunctionLit,
    func_params: []const types.TypeId,
    receiver_kind_out: *types.MethodReceiverKind,
    self_param_type_out: *?types.TypeId,
) !bool {
    const params = ast_unit.exprs.param_pool.slice(fn_lit.params);
    if (params.len == 0) return true;

    const first = ast_unit.exprs.Param.get(params[0]);
    if (first.pat.isNone()) return true;

    const pat_id = first.pat.unwrap();
    if (ast_unit.kind(pat_id) != .Binding) return true;

    // Check if name is "self"
    const bname = ast_unit.pats.get(.Binding, pat_id).name;
    if (!std.mem.eql(u8, getStr(ast_unit, bname), "self")) return true;

    const loc = ast_unit.exprs.locs.get(first.loc);
    if (first.ty.isNone()) {
        try self.context.diags.addError(loc, .method_self_requires_type, .{});
        return false;
    }

    const sty = func_params[0];
    const skind = self.typeKind(sty);

    if (skind == .Ptr) {
        const ptr = self.context.type_store.get(.Ptr, sty);
        if (!ptr.elem.eq(owner_ty)) {
            try self.context.diags.addError(loc, .method_self_type_mismatch, .{ sty, owner_ty });
            return false;
        }
        receiver_kind_out.* = if (ptr.is_const) .pointer_const else .pointer;
    } else {
        if (!sty.eq(owner_ty)) {
            try self.context.diags.addError(loc, .method_self_type_mismatch, .{ sty, owner_ty });
            return false;
        }
        receiver_kind_out.* = .value;
    }

    self_param_type_out.* = sty;
    return true;
}

/// Register the method declaration `decl_id` with receiver type and signature `fn_ty`.
fn registerMethodDecl(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    decl_id: ast.DeclId,
    decl: ast.Rows.Decl,
    func_ty_id: types.TypeId,
) !bool {
    const seg_ids = ast_unit.exprs.method_path_pool.slice(decl.method_path.asRange());
    if (seg_ids.len != 2) {
        const loc = ast_unit.exprs.locs.get(ast_unit.exprs.MethodPathSeg.get(seg_ids[0]).loc);
        try self.context.diags.addError(loc, .method_invalid_owner_path, .{});
        return false;
    }

    const owner_seg = ast_unit.exprs.MethodPathSeg.get(seg_ids[0]);
    const method_seg = ast_unit.exprs.MethodPathSeg.get(seg_ids[1]);

    var owner_ty: types.TypeId = undefined;
    if (!try self.resolveOwnerType(ctx, ast_unit, owner_seg, &owner_ty)) return false;
    if (!try self.ensureMethodIsFunction(ast_unit, decl, func_ty_id)) return false;

    const fn_lit = getExpr(ast_unit, .FunctionLit, decl.value);
    const func_ty = self.context.type_store.get(.Function, func_ty_id);
    const func_params = self.context.type_store.type_pool.slice(func_ty.params);

    var recv_kind: types.MethodReceiverKind = .none;
    var self_ty: ?types.TypeId = null;

    if (!try self.analyzeSelfParam(ast_unit, owner_ty, fn_lit, func_params, &recv_kind, &self_ty)) return false;

    if (self.context.type_store.getMethod(owner_ty, method_seg.name)) |existing| {
        if (!existing.decl_id.eq(decl_id)) {
            try self.context.diags.addError(ast_unit.exprs.locs.get(method_seg.loc), .duplicate_method_on_type, .{getStr(ast_unit, method_seg.name)});
            return false;
        }
    }

    try self.context.type_store.putMethod(.{
        .owner_type = owner_ty,
        .method_name = method_seg.name,
        .decl_id = decl_id,
        .decl_ast = ast_unit,
        .func_expr = decl.value,
        .func_type = func_ty_id,
        .self_param_type = self_ty,
        .receiver_kind = recv_kind,
        .builtin = null,
    });
    try check_types.storeMethodExprTypes(self, ast_unit, owner_ty, method_seg.name, decl.value);
    return true;
}

/// Diagnostics representing why `got` cannot be assigned to `expect`.
const AssignErrors = union(enum) {
    array_length_mismatch,
    tuple_arity_mismatch,
    assign_null_to_non_optional,
    pointer_type_mismatch,
    pointer_constness_violation,
    slice_constness_violation,
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
    struct_field_type_mismatch: struct { index: usize, tag_index: usize },
    failure,
    success,
};

fn assignableSlice(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const et = self.context.type_store.get(.Slice, expect);
    const k = self.typeKind(got);
    if (k == .Slice) {
        const gt = self.context.type_store.get(.Slice, got);
        if (!et.is_const and gt.is_const) return .slice_constness_violation;
        return self.assignable(gt.elem, et.elem);
    }
    const elem = if (k == .Array) self.context.type_store.get(.Array, got).elem else if (k == .DynArray) self.context.type_store.get(.DynArray, got).elem else return .failure;
    return self.assignable(elem, et.elem);
}

fn assignableArray(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    if (self.typeKind(got) != .Array) return .expected_array_type;
    const et = self.context.type_store.get(.Array, expect);
    const gt = self.context.type_store.get(.Array, got);
    if (gt.len != et.len) return .array_length_mismatch;
    return self.assignable(gt.elem, et.elem);
}

fn assignableDynArray(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const et = self.context.type_store.get(.DynArray, expect);
    const elem = switch (self.typeKind(got)) {
        .DynArray => self.context.type_store.get(.DynArray, got).elem,
        .Array => self.context.type_store.get(.Array, got).elem,
        .Slice => self.context.type_store.get(.Slice, got).elem,
        else => return .expected_array_type,
    };
    return self.assignable(elem, et.elem);
}

fn assignableTuple(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    if (self.typeKind(got) != .Tuple) return .expected_tuple_type;
    const et = self.context.type_store.get(.Tuple, expect);
    const gt = self.context.type_store.get(.Tuple, got);
    if (et.elems.len != gt.elems.len) return .tuple_arity_mismatch;
    const ge = self.context.type_store.type_pool.slice(gt.elems);
    const ee = self.context.type_store.type_pool.slice(et.elems);
    for (ee, 0..) |e, i| {
        const r = self.assignable(ge[i], e);
        if (r != .success) return r;
    }
    return .success;
}

fn assignableMap(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const k = self.typeKind(got);
    if (k == .Array and self.context.type_store.get(.Array, got).len == 0) return .success;
    if (k != .Map) return .expected_map_type;
    const et = self.context.type_store.get(.Map, expect);
    const gt = self.context.type_store.get(.Map, got);
    if (self.assignable(gt.key, et.key) != .success) return .map_wrong_key_type;
    return self.assignable(gt.value, et.value);
}

fn assignableSimd(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const et = self.context.type_store.get(.Simd, expect);
    const k = self.typeKind(got);
    var gl: u32 = 0;
    var ge: types.TypeId = undefined;
    if (k == .Simd) {
        const g = self.context.type_store.get(.Simd, got);
        gl = g.lanes;
        ge = g.elem;
    } else if (k == .Array) {
        const g = self.context.type_store.get(.Array, got);
        gl = @intCast(g.len);
        ge = g.elem;
    } else return .failure;
    if (gl != et.lanes) return .array_length_mismatch;
    return self.assignable(ge, et.elem);
}

fn assignableTensor(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const et = self.context.type_store.get(.Tensor, expect);
    var cur = got;
    var dims_buf = [_]usize{0} ** types.max_tensor_rank;
    var rank: usize = 0;

    if (self.typeKind(got) == .Tensor) {
        const gt = self.context.type_store.get(.Tensor, got);
        if (gt.rank != et.rank) return .tensor_rank_mismatch;
        for (gt.dims[0..gt.rank], 0..) |d, i| if (d != et.dims[i]) return .tensor_dimension_mismatch;
        return self.assignable(gt.elem, et.elem);
    }

    while (self.typeKind(cur) == .Array) : (rank += 1) {
        if (rank >= types.max_tensor_rank) return .tensor_rank_mismatch;
        const arr = self.context.type_store.get(.Array, cur);
        dims_buf[rank] = arr.len;
        cur = arr.elem;
    }
    if (rank == 0) return .expected_tensor_type;
    if (rank != et.rank) return .tensor_rank_mismatch;
    for (dims_buf[0..rank], 0..) |d, i| if (d != et.dims[i]) return .tensor_dimension_mismatch;
    return self.assignable(cur, et.elem);
}

fn assignableOptional(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const expected_ty = self.context.type_store.get(.Optional, expect);
    const got_kind = self.typeKind(got);

    if (got_kind == .Optional) {
        const got_ty = self.context.type_store.get(.Optional, got);
        return self.assignable(got_ty.elem, expected_ty.elem);
    }

    // Non-optional value into Optional(T) – allow if value is assignable to T.
    return self.assignable(got, expected_ty.elem);
}

fn assignablePtr(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    if (self.typeKind(got) != .Ptr) return .expected_pointer_type;
    const et = self.context.type_store.get(.Ptr, expect);
    const gt = self.context.type_store.get(.Ptr, got);
    if (!et.is_const and gt.is_const) return .pointer_constness_violation;
    if (self.assignable(gt.elem, et.elem) != .success) return .pointer_type_mismatch;
    return .success;
}

fn findFieldByName(
    self: *Checker,
    fields: []const types.FieldId,
    name: ast.StrId,
) ?struct { index: usize, field: types.Rows.Field } {
    for (fields, 0..) |fid, i| {
        const f = self.context.type_store.Field.get(fid);
        if (f.name.eq(name)) {
            return .{ .index = i, .field = f };
        }
    }
    return null;
}

fn assignableUnion(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    if (self.typeKind(got) != .Struct) return .expected_struct_type;
    const gt = self.context.type_store.get(.Struct, got);
    const gfields = self.context.type_store.field_pool.slice(gt.fields);
    if (gfields.len == 0) return .union_empty_literal;
    if (gfields.len != 1) return .union_literal_multiple_fields;

    const et = self.context.type_store.get(.Union, expect);
    const gf = self.context.type_store.Field.get(gfields[0]);

    for (self.context.type_store.field_pool.slice(et.fields)) |fid| {
        const ef = self.context.type_store.Field.get(fid);
        if (ef.name.eq(gf.name)) return self.assignable(gf.ty, ef.ty);
    }
    return .unknown_struct_field;
}

fn assignableStruct(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    if (self.typeKind(got) != .Struct) return .expected_struct_type;
    const et = self.context.type_store.get(.Struct, expect);
    const gt = self.context.type_store.get(.Struct, got);
    const efields = self.context.type_store.field_pool.slice(et.fields);
    const gfields = self.context.type_store.field_pool.slice(gt.fields);

    if (efields.len < gfields.len) return .unknown_struct_field;
    if (efields.len > gfields.len) return .struct_field_count_mismatch;

    for (efields, 0..) |eid, i| {
        const ef = self.context.type_store.Field.get(eid);
        var found = false;
        for (gfields) |gid| {
            const gf = self.context.type_store.Field.get(gid);
            if (gf.name.eq(ef.name)) {
                found = true;
                const r = self.assignable(gf.ty, ef.ty);
                if (r != .success) return .{ .struct_field_type_mismatch = .{ .index = i, .tag_index = @intFromEnum(r) } };
                break;
            }
        }
        if (!found) return .struct_field_name_mismatch;
    }
    return .success;
}

fn assignableErrorSet(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const expected_ty = self.context.type_store.get(.ErrorSet, expect);
    const got_kind = self.typeKind(got);

    if (got_kind == .Error) {
        return self.assignable(got, expected_ty.error_ty);
    } else {
        return self.assignable(got, expected_ty.value_ty);
    }
}

fn assignableInteger(self: *Checker, got: types.TypeId) AssignErrors {
    const got_kind = self.typeKind(got);
    if (!check_types.isIntegerKind(self, got_kind)) return .expected_integer_type;
    return .success;
}

fn assignableFloat(self: *Checker, got: types.TypeId) AssignErrors {
    const got_kind = self.typeKind(got);
    if (got_kind != .F32 and got_kind != .F64) return .expected_float_type;
    return .success;
}

/// Determine if `got` can be assigned to `expect`, returning an `AssignErrors` tag.
pub fn assignable(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    if (got.eq(expect)) return .success;
    const gk = self.typeKind(got);
    const ek = self.typeKind(expect);

    if (ek == .Any or gk == .Any) return .success;
    if (gk == .Undef) return if (ek == .Noreturn) .noreturn_not_storable else .success;

    if (gk == .Optional and ek != .Optional) {
        const elem = self.context.type_store.get(.Optional, got).elem;
        return if (self.typeKind(elem) == .Any) .assign_null_to_non_optional else .failure;
    }

    return switch (ek) {
        .Slice => self.assignableSlice(got, expect),
        .Array => self.assignableArray(got, expect),
        .DynArray => self.assignableDynArray(got, expect),
        .Tuple => self.assignableTuple(got, expect),
        .Map => self.assignableMap(got, expect),
        .Simd => self.assignableSimd(got, expect),
        .Tensor => self.assignableTensor(got, expect),
        .Optional => {
            if (gk == .Optional) return self.assignable(self.context.type_store.get(.Optional, got).elem, self.context.type_store.get(.Optional, expect).elem);
            return self.assignable(got, self.context.type_store.get(.Optional, expect).elem);
        },
        .Ptr => self.assignablePtr(got, expect),
        .TypeType => if (gk == .TypeType) .success else .type_value_mismatch,
        .Noreturn => .noreturn_not_storable,
        .Union => self.assignableUnion(got, expect),
        .Struct => self.assignableStruct(got, expect),
        .Enum => if (gk == .Enum and got.eq(expect)) .success else if (gk != .Enum) .expected_enum_type else .failure,
        .Function => if (gk == .Function) .success else .failure,
        .ErrorSet => {
            const es = self.context.type_store.get(.ErrorSet, expect);
            return self.assignable(got, if (gk == .Error) es.error_ty else es.value_ty);
        },
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => if (check_types.isIntegerKind(self, gk)) .success else .expected_integer_type,
        .F32, .F64 => if (gk == .F32 or gk == .F64) .success else .expected_float_type,
        else => .failure,
    };
}
fn typeInferFromRHS(self: *Checker, ast_unit: *ast.Ast, decl_id: ast.DeclId, rhs_ty: types.TypeId) !void {
    const decl = ast_unit.exprs.Decl.get(decl_id);
    const k = self.typeKind(rhs_ty);
    if (k == .Array and self.context.type_store.get(.Array, rhs_ty).len == 0) {
        try self.context.diags.addError(exprLoc(ast_unit, decl), .cannot_infer_type_from_empty_array, .{});
        return;
    }
    if (k == .Optional and self.typeKind(self.context.type_store.get(.Optional, rhs_ty).elem) == .Any) {
        try self.context.diags.addError(exprLoc(ast_unit, decl), .cannot_infer_type_from_null, .{});
        return;
    }
    ast_unit.type_info.decl_types.items[decl_id.toRaw()] = rhs_ty;
    ast_unit.type_info.expr_types.items[decl.value.toRaw()] = rhs_ty;
}

fn updateCoercedLiteral(self: *Checker, ast_unit: *ast.Ast, expr_id: ast.ExprId, target_ty: types.TypeId, value_ty: *types.TypeId, kind: *types.TypeKind) !bool {
    if (!try self.coerceNumericLiteral(ast_unit, expr_id, target_ty)) return false;
    value_ty.* = ast_unit.type_info.expr_types.items[expr_id.toRaw()] orelse target_ty;
    kind.* = self.typeKind(value_ty.*);
    return true;
}

// Determine if an expression is a comptime numeric expression (integer or float).
const ConstNumKind = enum { none, int, float };

/// Determine whether `expr_id` is a compile-time numeric literal/expression.
fn constNumericKind(self: *Checker, ast_unit: *ast.Ast, expr_id: ast.ExprId) ConstNumKind {
    switch (ast_unit.kind(expr_id)) {
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

/// Determine whether `expr_id` yields a compile-time numeric value, including block expressions.
fn constNumericKindForValue(self: *Checker, ast_unit: *ast.Ast, expr_id: ast.ExprId) ConstNumKind {
    if (ast_unit.kind(expr_id) != .Block) {
        return self.constNumericKind(ast_unit, expr_id);
    }
    const br = getExpr(ast_unit, .Block, expr_id);
    const stmts = ast_unit.stmts.stmt_pool.slice(br.items);
    if (stmts.len == 0) return .none;
    const last = stmts[stmts.len - 1];
    if (ast_unit.kind(last) != .Expr) return .none;
    const row = getStmt(ast_unit, .Expr, last);
    return self.constNumericKind(ast_unit, row.expr);
}

/// Attempt to coerce a compile-time numeric expression to `target_ty`.
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

/// Update compile-time numeric constant `expr_id` to `target_ty` on successful coercion.
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

/// Coerce literal `expr_id` to `target_ty` (int, float, imaginary).
fn coerceNumericLiteral(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    target_ty: types.TypeId,
) !bool {
    if (ast_unit.kind(expr_id) != .Literal) return false;
    const lit = getExpr(ast_unit, .Literal, expr_id);
    const target_kind = self.typeKind(target_ty);
    return switch (lit.kind) {
        .int => coerceIntLiteral(ast_unit, expr_id, target_ty, target_kind, lit),
        .float => coerceFloatLiteral(ast_unit, expr_id, target_ty, target_kind, lit),
        .imaginary => self.coerceImaginaryLiteral(ast_unit, expr_id, target_ty, target_kind, lit),
        else => false,
    };
}

/// Attempt to coerce integer literal `expr_id` to `target_ty`.
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
        .I8 => value <= @as(u128, @intCast(std.math.maxInt(i8))),
        .I16 => value <= @as(u128, @intCast(std.math.maxInt(i16))),
        .I32 => value <= @as(u128, @intCast(std.math.maxInt(i32))),
        .I64 => value <= @as(u128, @intCast(std.math.maxInt(i64))),
        .U8 => value <= @as(u128, @intCast(std.math.maxInt(u8))),
        .U16 => value <= @as(u128, @intCast(std.math.maxInt(u16))),
        .U32 => value <= @as(u128, @intCast(std.math.maxInt(u32))),
        .U64 => value <= @as(u128, @intCast(std.math.maxInt(u64))),
        .Usize => value <= @as(u128, @intCast(std.math.maxInt(usize))),
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

/// Attempt to coerce floating literal `expr_id` to `target_ty`.
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

/// Attempt to coerce imaginary literal `expr_id` to complex `target_ty`.
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

/// Attempt to coerce a null literal to a given optional type.
fn tryCoerceNullLiteral(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    expect_ty: types.TypeId,
) bool {
    if (ast_unit.kind(expr_id) == .NullLit) {
        if (self.typeKind(expect_ty) == .Optional) {
            return true;
        }
    }
    return false;
}

/// Try to coerce variant/error literals like `V.C(...)` or `V.C{...}` to `expect_ty`.
fn tryCoerceVariantOrErrorLiteral(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, expr_id: ast.ExprId, expect_ty: types.TypeId) !bool {
    return switch (ast_unit.kind(expr_id)) {
        .Call => try self.tryCoerceCallLike(ctx, ast_unit, &getExpr(ast_unit, .Call, expr_id), expect_ty),
        .StructLit => try self.tryCoerceStructLitLike(ctx, ast_unit, &getExpr(ast_unit, .StructLit, expr_id), expect_ty),
        else => false,
    };
}

fn tryCoerceCallLike(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, call: *const ast.Rows.Call, expect_ty: types.TypeId) !bool {
    var cur = call.callee;
    var last: ?ast.StrId = null;
    while (ast_unit.kind(cur) == .FieldAccess) {
        const fr = getExpr(ast_unit, .FieldAccess, cur);
        last = fr.field;
        cur = fr.parent;
    }
    if (last) |ln| if (self.getPayloadTypeForCase(expect_ty, ln)) |pt|
        return try self.checkCallArgsAgainstPayload(ctx, ast_unit, pt, call);
    return false;
}

fn tryCoerceStructLitLike(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, sl: *const ast.Rows.StructLit, expect_ty: types.TypeId) !bool {
    if (sl.ty.isNone()) return false;
    var cur = sl.ty.unwrap();
    var last: ?ast.StrId = null;
    while (ast_unit.kind(cur) == .FieldAccess) {
        const fr = getExpr(ast_unit, .FieldAccess, cur);
        last = fr.field;
        cur = fr.parent;
    }
    if (last) |ln| if (self.getPayloadTypeForCase(expect_ty, ln)) |pt|
        return try self.checkStructLitAgainstPayload(ctx, ast_unit, pt, sl);
    return false;
}

/// Look up the payload type for case `lname` inside the variant/error `expect_ty`.
fn getPayloadTypeForCase(self: *Checker, expect_ty: types.TypeId, lname: ast.StrId) ?types.TypeId {
    const k = self.context.type_store.getKind(expect_ty);
    const fields = if (k == .Variant) self.context.type_store.get(.Variant, expect_ty).variants else self.context.type_store.get(.Error, expect_ty).variants;
    for (self.context.type_store.field_pool.slice(fields)) |fid| {
        const f = self.context.type_store.Field.get(fid);
        if (f.name.eq(lname)) return f.ty;
    }
    return null;
}

/// Verify that call arguments match the payload `pay_ty`.
fn checkCallArgsAgainstPayload(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, pay_ty: types.TypeId, call: *const ast.Rows.Call) !bool {
    const args = ast_unit.exprs.expr_pool.slice(call.args);
    const pk = self.context.type_store.getKind(pay_ty);

    if (pk == .Void) return args.len == 0;

    // Normalize into a loop
    var targets_buf: [1]types.TypeId = undefined;
    var targets: []const types.TypeId = &targets_buf;

    if (pk == .Tuple) {
        targets = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, pay_ty).elems);
    } else {
        targets_buf[0] = pay_ty;
    }

    if (args.len != targets.len) return false;

    for (args, 0..) |aid, i| {
        try self.pushValueReq(ctx, true);
        var at = try self.checkExpr(ctx, ast_unit, aid);
        self.popValueReq(ctx);

        if (self.typeKind(at) == .TypeError) return false;
        if (self.assignable(at, targets[i]) != .success) {
            if (check_types.isNumericKind(self, self.typeKind(targets[i]))) {
                var ak = self.typeKind(at);
                if (try self.updateCoercedLiteral(ast_unit, aid, targets[i], &at, &ak) and self.assignable(at, targets[i]) == .success) continue;
            }
            return false;
        }
    }
    return true;
}

/// Verify that struct literal `sl` matches the payload struct type `pay_ty`.
fn checkStructLitAgainstPayload(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, pay_ty: types.TypeId, sl: *const ast.Rows.StructLit) !bool {
    if (self.context.type_store.getKind(pay_ty) != .Struct) return false;
    const st = self.context.type_store.get(.Struct, pay_ty);
    const tfields = self.context.type_store.field_pool.slice(st.fields);

    for (ast_unit.exprs.sfv_pool.slice(sl.fields)) |sfid| {
        const sf = ast_unit.exprs.StructFieldValue.get(sfid);
        if (sf.name.isNone()) return false;
        const nm = sf.name.unwrap();

        var want: ?types.TypeId = null;
        for (tfields) |tfid| {
            const tf = self.context.type_store.Field.get(tfid);
            if (tf.name.eq(nm)) {
                want = tf.ty;
                break;
            }
        }
        if (want == null) return false;

        var at = try self.checkExpr(ctx, ast_unit, sf.value);
        if (self.typeKind(at) == .TypeError) return false;

        if (self.assignable(at, want.?) != .success) {
            if (check_types.isNumericKind(self, self.typeKind(want.?))) {
                var ak = self.typeKind(at);
                if (try self.updateCoercedLiteral(ast_unit, sf.value, want.?, &at, &ak) and self.assignable(at, want.?) == .success) continue;
            }
            return false;
        }
    }
    return true;
}
/// Attempt to coerce the RHS type `rhs_ty` to `expect_ty` for declaration `decl_id`.
fn tryTypeCoercion(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, decl_id: ast.DeclId, rhs_ty: types.TypeId, expect_ty: ?types.TypeId) !void {
    if (expect_ty == null) return try self.typeInferFromRHS(ast_unit, decl_id, rhs_ty);

    const target = expect_ty.?;
    var cur = rhs_ty;
    var res = self.assignable(cur, target);
    const val_id = ast_unit.exprs.Decl.get(decl_id).value;

    // Chain of Coercion attempts
    if (res != .success and check_types.isNumericKind(self, self.typeKind(target))) {
        var k = self.typeKind(cur);
        if (try self.updateCoercedLiteral(ast_unit, val_id, target, &cur, &k)) res = self.assignable(cur, target);
    }

    if (res == .failure) {
        const k = self.context.type_store.getKind(target);
        if (k == .Variant or k == .Error) {
            if (try self.tryCoerceVariantOrErrorLiteral(ctx, ast_unit, val_id, target)) res = .success;
        }
    }

    if (res == .failure and self.tryCoerceNullLiteral(ast_unit, val_id, target)) res = .success;

    if (res == .success and self.typeKind(target) == .TypeType and self.typeKind(cur) == .TypeType) {
        const target_of = self.context.type_store.get(.TypeType, target).of;
        const got_of = self.context.type_store.get(.TypeType, cur).of;
        if ((self.typeKind(target_of) == .Any or target_of.eq(target)) and self.typeKind(got_of) != .Any) {
            ast_unit.type_info.decl_types.items[decl_id.toRaw()] = cur;
            ast_unit.type_info.expr_types.items[val_id.toRaw()] = cur;
            return;
        }
    }

    switch (res) {
        .success => {
            ast_unit.type_info.decl_types.items[decl_id.toRaw()] = target;
            ast_unit.type_info.expr_types.items[val_id.toRaw()] = target;
        },
        .failure => try self.context.diags.addError(exprLoc(ast_unit, ast_unit.exprs.Decl.get(decl_id)), .type_annotation_mismatch, .{ target, cur }),
        inline else => |_, t| try self.context.diags.addError(exprLoc(ast_unit, ast_unit.exprs.Decl.get(decl_id)), @field(diag.DiagnosticCode, @tagName(t)), .{}),
    }
}
/// Validate the assignment statement `stmt`, handling destructuring and coercions.
fn lookupAssignBindingType(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, name: ast.StrId) ?types.TypeId {
    if (self.resolveDynamicBinding(ctx, ast_unit, name)) |t| return t;
    if (self.lookup(ctx, name)) |sid| {
        const srow = ctx.symtab.syms.get(sid);
        if (!srow.origin_decl.isNone()) return self.resolveDeclType(ctx, ast_unit, name, srow.origin_decl.unwrap()) catch null;
        if (!srow.origin_param.isNone()) return self.resolveParamType(ctx, ast_unit, name, srow.origin_param.unwrap()) catch null;
    }
    return null;
}

fn checkAssignPatternBindings(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, vty: types.TypeId) anyerror!void {
    switch (ast_unit.kind(pid)) {
        .Wildcard => return,
        .Binding => {
            const name = ast_unit.pats.get(.Binding, pid).name;
            const bind_ty = lookupAssignBindingType(self, ctx, ast_unit, name) orelse {
                try self.context.diags.addError(patternLoc(ast_unit, pid), .undefined_identifier, .{ast_unit.pats.strs.get(name)});
                return;
            };
            if (self.assignable(vty, bind_ty) != .success) {
                try self.context.diags.addError(patternLoc(ast_unit, pid), .type_annotation_mismatch, .{ bind_ty, vty });
            }
        },
        .Tuple => {
            const elems = ast_unit.pats.pat_pool.slice(ast_unit.pats.get(.Tuple, pid).elems);
            const tuple_elems = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, vty).elems);
            for (elems, 0..) |e, i| try checkAssignPatternBindings(self, ctx, ast_unit, e, tuple_elems[i]);
        },
        .Struct => {
            const fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, vty).fields);
            for (ast_unit.pats.field_pool.slice(ast_unit.pats.get(.Struct, pid).fields)) |fid| {
                const pf = ast_unit.pats.StructField.get(fid);
                var fty: ?types.TypeId = null;
                for (fields) |field_id| {
                    const f = self.context.type_store.Field.get(field_id);
                    if (f.name.eq(pf.name)) {
                        fty = f.ty;
                        break;
                    }
                }
                if (fty) |t| try checkAssignPatternBindings(self, ctx, ast_unit, pf.pattern, t);
            }
        },
        .Slice => {
            const elem_ty = switch (self.typeKind(vty)) {
                .Array => self.context.type_store.get(.Array, vty).elem,
                .Slice => self.context.type_store.get(.Slice, vty).elem,
                .DynArray => self.context.type_store.get(.DynArray, vty).elem,
                else => self.context.type_store.tAny(),
            };
            const sl = ast_unit.pats.get(.Slice, pid);
            const elems = ast_unit.pats.pat_pool.slice(sl.elems);
            for (elems) |e| try checkAssignPatternBindings(self, ctx, ast_unit, e, elem_ty);
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const is_const = if (self.typeKind(vty) == .Slice) self.context.type_store.get(.Slice, vty).is_const else false;
                const slice_ty = self.context.type_store.mkSlice(elem_ty, is_const);
                try checkAssignPatternBindings(self, ctx, ast_unit, sl.rest_binding.unwrap(), slice_ty);
            }
        },
        else => {},
    }
}

fn checkAssign(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, stmt: *const ast.StmtRows.Assign) !void {
    switch (stmt.left) {
        .expr => |left_expr| {
            // 1. Discard
            if (ast_unit.kind(left_expr) == .Ident and std.mem.eql(u8, ast_unit.exprs.strs.get(getExpr(ast_unit, .Ident, left_expr).name), "_")) {
                try self.pushValueReq(ctx, false);
                _ = try self.checkExpr(ctx, ast_unit, stmt.right);
                self.popValueReq(ctx);
                return;
            }

            // 2. Standard Assign
            const lt = try self.checkExpr(ctx, ast_unit, left_expr);
            try self.pushValueReq(ctx, true);
            var rt = try self.checkExpr(ctx, ast_unit, stmt.right);
            self.popValueReq(ctx);

            if (self.tryCoerceNullLiteral(ast_unit, stmt.right, lt)) {
                ast_unit.type_info.expr_types.items[stmt.right.toRaw()] = lt;
                rt = lt;
            }

            if (self.typeKind(lt) != .TypeError and self.typeKind(rt) != .TypeError) {
                var val = rt;
                if (self.assignable(val, lt) != .success) {
                    var ok = false;
                    if (check_types.isNumericKind(self, self.typeKind(lt))) {
                        var vk = self.typeKind(val);
                        if (try self.updateCoercedLiteral(ast_unit, stmt.right, lt, &val, &vk) and self.assignable(val, lt) == .success) ok = true;
                    }
                    if (!ok) try self.context.diags.addError(exprLoc(ast_unit, stmt), .type_annotation_mismatch, .{ lt, val });
                }
            }
        },
        .pattern => |pid| {
            try self.pushValueReq(ctx, true);
            const rv = try self.checkExpr(ctx, ast_unit, stmt.right);
            self.popValueReq(ctx);
            if (self.typeKind(rv) != .TypeError) {
                const shape = pattern_matching.checkPatternShapeForAssignPattern(self, ast_unit, pid, rv);
                switch (shape) {
                    .ok => try checkAssignPatternBindings(self, ctx, ast_unit, pid, rv),
                    inline else => |x| try self.context.diags.addError(exprLoc(ast_unit, stmt), @field(diag.DiagnosticCode, @tagName(x)), .{}),
                }
            }
        },
    }

    // 3. Purity
    if (self.inFunction(ctx) and self.currentFunc(ctx).?.require_pure) {
        switch (stmt.left) {
            .expr => |left_expr| {
                if (self.lvalueRootKind(ctx, ast_unit, left_expr) != .LocalDecl) {
                    try self.context.diags.addError(exprLoc(ast_unit, stmt), .purity_violation, StringPayload{ .value = "assignment touches non-local" });
                    ctx.func_stack.items[ctx.func_stack.items.len - 1].pure = false;
                }
            },
            .pattern => {},
        }
    }
}
/// Type-check statement `sid`, returning the resulting type (usually void).
fn checkStmt(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, sid: ast.StmtId) !types.TypeId {
    switch (ast_unit.kind(sid)) {
        .Expr => {
            try self.pushValueReq(ctx, false);
            _ = try self.checkExpr(ctx, ast_unit, getStmt(ast_unit, .Expr, sid).expr);
            self.popValueReq(ctx);
        },
        .Decl => {
            const decl = getStmt(ast_unit, .Decl, sid).decl;
            try self.checkDecl(ctx, ast_unit, decl);
            if (self.inFunction(ctx)) {
                const idx = ctx.func_stack.items.len - 1;
                var locals = &ctx.func_stack.items[idx].locals;
                const raw = decl.toRaw();
                if (raw >= locals.capacity()) locals.resize(self.gpa, raw + 1, false) catch {};
                locals.set(raw);
            }
        },
        .Assign => try self.checkAssign(ctx, ast_unit, &getStmt(ast_unit, .Assign, sid)),
        .Insert => {
            const row = getStmt(ast_unit, .Insert, sid);
            _ = try self.checkExpr(ctx, ast_unit, row.expr);
            const computed = try self.evalComptimeExpr(ctx, ast_unit, row.expr, &.{});
            try self.expandInsertValue(ctx, ast_unit, computed, exprLoc(ast_unit, row));
        },
        .Return => return try self.checkReturn(ctx, ast_unit, getStmt(ast_unit, .Return, sid)),
        .Break => return try self.checkBreak(ctx, ast_unit, getStmt(ast_unit, .Break, sid)),
        .Continue => if (!self.inLoop(ctx)) try self.context.diags.addError(exprLoc(ast_unit, getStmt(ast_unit, .Continue, sid)), .continue_outside_loop, .{}),
        .Defer => _ = try self.checkDefer(ctx, ast_unit, getStmt(ast_unit, .Defer, sid)),
        .ErrDefer => _ = try self.checkErrDefer(ctx, ast_unit, getStmt(ast_unit, .ErrDefer, sid)),
        .Unreachable => {},
    }
    return self.context.type_store.tVoid();
}
// =========================================================
// Expressions
// =========================================================
pub fn checkExpr(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) anyerror!types.TypeId {
    if (ast_unit.type_info.expr_types.items[id.toRaw()]) |cached| return cached;

    const kind = ast_unit.kind(id);
    const tid: types.TypeId = switch (kind) {
        .Literal => try self.checkLiteral(ast_unit, id),
        .Ident => try self.checkIdent(ctx, ast_unit, id),
        .Splice => try self.checkSplice(ctx, ast_unit, id),
        .Binary => try self.checkBinary(ctx, ast_unit, id),
        .Unary => try self.checkUnary(ctx, ast_unit, id),
        .FunctionLit => try self.checkFunctionLit(ctx, ast_unit, id),
        .ArrayLit => try self.checkArrayLit(ctx, ast_unit, id),
        .TupleLit => try self.checkTupleLit(ctx, ast_unit, id),
        .MapLit => try self.checkMapLit(ctx, ast_unit, id),
        .StructLit => try self.checkStructLit(ctx, ast_unit, id),
        .IndexAccess => try self.checkIndexAccess(ctx, ast_unit, id),
        .FieldAccess => try self.checkFieldAccess(ctx, ast_unit, id),
        .Call => try self.checkCall(ctx, ast_unit, id),
        .Range => try self.checkRange(ctx, ast_unit, id),
        .Deref => try self.checkDeref(ctx, ast_unit, id),

        // Blocks & Control Flow
        .Block => try self.checkBlock(ctx, ast_unit, id),
        .CodeBlock => try self.checkCodeBlock(ctx, ast_unit, id),
        .ComptimeBlock => blk: {
            const cb = ast_unit.exprs.get(.ComptimeBlock, id);
            try self.pushAllowInsertTarget(ctx, false);
            defer self.popAllowInsertTarget(ctx);
            const res = try self.checkExpr(ctx, ast_unit, cb.block);
            var baseline = std.AutoArrayHashMapUnmanaged(ast.StrId, comp.ValueId){};
            defer baseline.deinit(self.gpa);
            if (!self.isValueReq(ctx)) {
                const count = ast_unit.type_info.comptime_bindings.count();
                if (count > 0) {
                    try baseline.ensureTotalCapacity(self.gpa, count);
                    var it = ast_unit.type_info.comptime_bindings.iterator();
                    while (it.next()) |entry| {
                        try baseline.put(self.gpa, entry.key_ptr.*, entry.value_ptr.value);
                    }
                }
            }
            _ = self.evalComptimeExpr(ctx, ast_unit, cb.block, &.{}) catch |err| {
                const err_name: []const u8 = @errorName(err);
                try self.context.diags.addError(exprLoc(ast_unit, cb), .comptime_eval_failed, .{err_name});
                return self.context.type_store.tTypeError();
            };
            if (!self.isValueReq(ctx)) {
                try self.recordComptimeBlockSnapshot(ast_unit, id, &baseline);
            }
            break :blk res;
        },
        .AsyncBlock => try self.checkAsyncBlock(ctx, ast_unit, id),
        .MlirBlock => try self.checkMlirBlock(ctx, ast_unit, id),
        .If => try self.checkIf(ctx, ast_unit, id),
        .While => try self.checkWhile(ctx, ast_unit, id),
        .For => try self.checkFor(ctx, ast_unit, id),
        .Match => try pattern_matching.checkMatch(self, ctx, ast_unit, id),

        // Control Statements (returning Noreturn or Void)
        .Return => try self.checkReturn(ctx, ast_unit, getExpr(ast_unit, .Return, id)),
        .Break => try self.checkBreak(ctx, ast_unit, getExpr(ast_unit, .Break, id)),
        .Continue => try self.checkContinue(id),
        .Unreachable => try self.checkUnreachable(id),

        // Misc
        .Insert => try self.checkInsert(ctx, ast_unit, id),
        .Defer => try self.checkDefer(ctx, ast_unit, getExpr(ast_unit, .Defer, id)),
        .ErrDefer => try self.checkErrDefer(ctx, ast_unit, getExpr(ast_unit, .ErrDefer, id)),
        .ErrUnwrap => try self.checkErrUnwrap(ctx, ast_unit, id),
        .OptionalUnwrap => try self.checkOptionalUnwrap(ctx, ast_unit, id),
        .Await => try self.checkAwait(ctx, ast_unit, id),
        .Closure => try self.checkClosure(ctx, ast_unit, id),
        .Cast => try self.checkCast(ctx, ast_unit, id),
        .Catch => try self.checkCatch(ctx, ast_unit, id),
        .Import => try self.checkImport(ast_unit, id),
        .TypeOf => try check_types.checkTypeOf(self, ctx, ast_unit, id),
        .UndefLit => self.context.type_store.tUndef(),
        .NullLit => if (self.getExpectedType(ctx)) |exp|
            (if (self.typeKind(exp) == .Optional) exp else self.context.type_store.mkOptional(self.context.type_store.tAny()))
        else
            self.context.type_store.mkOptional(self.context.type_store.tAny()),

        // Type Expressions
        .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => blk: {
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, id);
            break :blk if (res[0]) self.context.type_store.mkTypeType(res[1]) else self.context.type_store.tTypeError();
        },
        .MapType => blk: {
            const row = getExpr(ast_unit, .MapType, id);
            // Try resolving as explicit types first
            const k_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, row.key);
            const v_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, row.value);
            if (k_res[0] or v_res[0]) {
                break :blk self.context.type_store.mkTypeType(self.context.type_store.mkMap(k_res[1], v_res[1]));
            }
            // Fallback: Resolve as values (dependent types)
            const k_vt = try self.checkExpr(ctx, ast_unit, row.key);
            const v_vt = try self.checkExpr(ctx, ast_unit, row.value);
            if (self.typeKind(k_vt) == .TypeError or self.typeKind(v_vt) == .TypeError) break :blk self.context.type_store.tTypeError();
            break :blk self.context.type_store.mkMap(k_vt, v_vt);
        },
    };

    ast_unit.type_info.expr_types.items[id.toRaw()] = tid;
    return tid;
}

/// Determine the declared type for literal expression `id`.
fn checkLiteral(self: *Checker, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const lit = getExpr(ast_unit, .Literal, id);
    const loc = exprLoc(ast_unit, lit);

    switch (lit.kind) {
        .int => {
            const info = lit.data.int;
            if (!info.valid or info.value > std.math.maxInt(i64)) {
                try self.context.diags.addError(loc, .invalid_integer_literal, StringPayload{ .value = self.context.interner.get(info.text) });
                return self.context.type_store.tTypeError();
            }
            return self.context.type_store.tI64();
        },
        .imaginary => {
            const info = lit.data.imaginary;
            const text = getStr(ast_unit, info.text);
            if (!info.valid) {
                try self.context.diags.addError(loc, .invalid_imaginary_literal, StringPayload{ .value = text });
                return self.context.type_store.tTypeError();
            }

            // Heuristic: If it lacks float markers (.eE) and fits in i64, it's an Int Complex.
            var is_int = std.mem.indexOfAny(u8, text, ".eEpP") == null;
            if (is_int) {
                var acc: u128 = 0;
                for (text) |c| {
                    if (c == '_') continue;
                    if (c < '0' or c > '9') {
                        is_int = false;
                        break;
                    }
                    acc = acc * 10 + (c - '0');
                    if (acc > std.math.maxInt(i64)) {
                        is_int = false;
                        break;
                    }
                }
            }
            return self.context.type_store.mkComplex(if (is_int) self.context.type_store.tI64() else self.context.type_store.tF64());
        },
        .float => {
            const info = lit.data.float;
            if (!info.valid) {
                try self.context.diags.addError(loc, .invalid_float_literal, StringPayload{ .value = self.context.interner.get(info.text) });
                return self.context.type_store.tTypeError();
            }
            return self.context.type_store.tF64();
        },
        .bool => return self.context.type_store.tBool(),
        .string => return self.context.type_store.tString(),
        .char => return self.context.type_store.tU32(),
    }
}

/// Main entry point: Orchestrates identifier resolution using a hierarchical strategy.
fn checkIdent(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const name = getExpr(ast_unit, .Ident, id).name;

    // 1. Dynamic Scope (Locals, Loops, Catches)
    if (self.resolveDynamicBinding(ctx, ast_unit, name)) |t| return t;

    // 2. Symbol Table (Declarations, Params)
    if (self.lookup(ctx, name)) |sid| {
        const srow = ctx.symtab.syms.get(sid);
        if (!srow.origin_decl.isNone()) return try self.resolveDeclType(ctx, ast_unit, name, srow.origin_decl.unwrap());
        if (!srow.origin_param.isNone()) return try self.resolveParamType(ctx, ast_unit, name, srow.origin_param.unwrap());
        return self.resolveDynamicBinding(ctx, ast_unit, name) orelse self.context.type_store.tTypeError();
    }

    // 3. Type Name Resolution
    const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, id);
    if (res[0]) return self.context.type_store.mkTypeType(res[1]);

    // 4. Failure
    return try self.reportUndefinedIdentifier(ctx, ast_unit, getExpr(ast_unit, .Ident, id));
}

// --- Resolution Helpers ---

fn resolveDynamicBinding(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, name: ast.StrId) ?types.TypeId {
    if (self.bindingTypeFromActiveCatches(ctx, name)) |t| return t;
    if (self.bindingTypeFromActiveLoops(ctx, ast_unit, name)) |t| return t;
    if (self.bindingTypeFromActiveMatches(ctx, ast_unit, name)) |t| return t;
    return null;
}

fn resolveDeclType(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, name: ast.StrId, did: ast.DeclId) !types.TypeId {
    const drow = ast_unit.exprs.Decl.get(did);
    var rhs_ty = if (ast_unit.type_info.decl_types.items[did.toRaw()]) |t| t else try self.checkExpr(ctx, ast_unit, drow.value);

    // Narrowing: `const x: type = T` -> TypeType(T)
    if (!drow.pattern.isNone() and ast_unit.kind(drow.pattern.unwrap()) == .Binding and self.typeKind(rhs_ty) == .TypeType) {
        const tt = self.context.type_store.get(.TypeType, rhs_ty);
        if (self.typeKind(tt.of) == .Any or tt.of.eq(rhs_ty)) {
            const tr = try check_types.typeFromTypeExpr(self, ctx, ast_unit, drow.value);
            if (tr[0] and self.typeKind(tr[1]) != .TypeError) {
                rhs_ty = self.context.type_store.mkTypeType(tr[1]);
                ast_unit.type_info.decl_types.items[did.toRaw()] = rhs_ty;
                ast_unit.type_info.expr_types.items[drow.value.toRaw()] = rhs_ty;
            }
        }
    }

    if (!drow.pattern.isNone()) {
        return pattern_matching.bindingTypeInPattern(self, ast_unit, drow.pattern.unwrap(), name, rhs_ty) orelse self.context.type_store.tTypeError();
    }
    return rhs_ty;
}

fn resolveParamType(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, name: ast.StrId, pid: ast.ParamId) !types.TypeId {
    const p = ast_unit.exprs.Param.get(pid);
    var pt = self.context.type_store.tAny();

    if (!p.ty.isNone()) {
        const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, p.ty.unwrap());
        if (!res[0]) return self.context.type_store.tTypeError();
        pt = res[1];
    } else if (p.is_comptime) {
        return self.context.type_store.mkTypeType(self.context.type_store.tAny());
    }

    if (self.typeKind(pt) == .Any) {
        if (self.lookupParamSpecialization(ctx, name)) |over| pt = over;
    }
    if (self.typeKind(pt) == .TypeError) return pt;

    return if (!p.pat.isNone()) pattern_matching.bindingTypeInPattern(self, ast_unit, p.pat.unwrap(), name, pt) orelse pt else pt;
}

fn reportUndefinedIdentifier(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, row: ast.Rows.Ident) !types.TypeId {
    const target = ast_unit.exprs.strs.get(row.name);
    try self.context.diags.addError(exprLoc(ast_unit, row), .undefined_identifier, .{target});

    var candidates = List([]const u8){};
    defer candidates.deinit(self.gpa);

    var cur: ?symbols.ScopeId = ctx.symtab.currentId();
    while (cur) |sid| {
        const scope = ctx.symtab.scopes.get(sid);
        for (ctx.symtab.sym_pool.slice(scope.symbols)) |id| try candidates.append(self.gpa, ast_unit.exprs.strs.get(ctx.symtab.syms.get(id).name));

        // Check active stack frames
        for (ctx.symtab.stack.items) |frame| {
            if (frame.id.eq(sid)) {
                for (frame.list.items) |id| try candidates.append(self.gpa, ast_unit.exprs.strs.get(ctx.symtab.syms.get(id).name));
                break;
            }
        }
        cur = if (scope.parent.isNone()) null else scope.parent.unwrap();
    }

    if (self.findBestSuggestion(target, candidates.items)) |sug| {
        try self.context.diags.attachNoteArgs(self.context.diags.count() - 1, null, .did_you_mean, .{sug});
    }
    return self.context.type_store.tTypeError();
}

/// Type-check block expression `id` while respecting value vs statement context.
fn checkBlock(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const stmt_range = getExpr(ast_unit, .Block, id).items;
    if (stmt_range.len == 0) return self.context.type_store.tVoid();
    const allow_insert_target = self.isInsertTargetAllowed(ctx);

    _ = try ctx.symtab.push(ctx.symtab.currentId());
    defer ctx.symtab.pop();
    if (allow_insert_target) {
        try self.pushInsertTarget(ctx, .{ .block = .{ .block_id = id, .scope_id = ctx.symtab.currentId() } });
    }
    defer if (allow_insert_target) self.popInsertTarget(ctx);

    const value_req = self.isValueReq(ctx);
    var after_break = false;

    // Process all statements. The last one needs special handling if value_req is true.
    var i: u32 = 0;
    while (i < stmt_range.len) : (i += 1) {
        const stmt = ast_unit.stmts.stmt_pool.slice(stmt_range)[i];
        if (after_break) {
            try self.context.diags.addError(stmtLoc(ast_unit, stmt), .unreachable_code_after_break, .{});
            return self.context.type_store.tTypeError();
        }

        const is_last = (i + 1 == stmt_range.len);
        const kind = ast_unit.kind(stmt);

        {
            var pushed_site = false;
            const target = self.currentInsertTarget(ctx);
            if (target == .block and target.block.block_id.eq(id)) {
                try self.pushInsertSite(ctx, .{ .block_id = id, .index = i });
                pushed_site = true;
            }
            defer if (pushed_site) self.popInsertSite(ctx);

            // Value Context: Last statement must be an Expr and we return its type.
            if (is_last and value_req) {
                if (kind == .Expr) return try self.checkExpr(ctx, ast_unit, getStmt(ast_unit, .Expr, stmt).expr);
                // Fallthrough: Last stmt is not an Expr, but value was required -> Void (which might error at call site)
            }

            // Normal Statement Check
            _ = try self.checkStmt(ctx, ast_unit, stmt);
        }

        // Check for control flow break
        if (kind == .Break or kind == .Return) {
            after_break = true;
            if (is_last) return self.context.type_store.tNoreturn();
        } else if (kind == .Expr) {
            if (ast_unit.kind(getStmt(ast_unit, .Expr, stmt).expr) == .Break) after_break = true;
        }
    }

    return self.context.type_store.tVoid();
}
/// Validate binary operation `id`, ensuring operand types/coercion rules hold.
fn checkBinary(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const bin: ast.Rows.Binary = getExpr(ast_unit, .Binary, id);
    const loc = exprLoc(ast_unit, bin);

    var l = try self.checkExpr(ctx, ast_unit, bin.left);
    var r = try self.checkExpr(ctx, ast_unit, bin.right);
    var l_k = self.typeKind(l);
    var r_k = self.typeKind(r);

    if (l_k == .TypeError or r_k == .TypeError) return self.context.type_store.tTypeError();
    if (l_k == .Undef or r_k == .Undef) {
        try self.context.diags.addError(loc, .invalid_binary_op_operands, .{ bin.op, l_k, r_k });
        return self.context.type_store.tTypeError();
    }

    const l_lit = ast_unit.kind(bin.left) == .Literal;
    const r_lit = ast_unit.kind(bin.right) == .Literal;

    switch (bin.op) {
        // --- Arithmetic & Bitwise ---
        .add, .sub, .mul, .div, .mod, .bit_and, .bit_or, .bit_xor, .shl, .shr => arith_blk: {
            // 1. Pointer Arith (Triton-style: Ptr + Tensor)
            if (bin.op == .add or bin.op == .sub) {
                const l_ptr = l_k == .Ptr or l_k == .MlirType;
                const r_ptr = r_k == .Ptr or r_k == .MlirType;
                if ((l_ptr and r_k == .Tensor) or (r_ptr and l_k == .Tensor)) {
                    const tensor_ty = if (l_ptr) r else l;
                    const ptr_ty = if (l_ptr) l else r;
                    const t_info = self.context.type_store.get(.Tensor, tensor_ty);

                    if (!check_types.isNumericKind(self, self.typeKind(t_info.elem))) break :arith_blk; // Error

                    // Coerce literal offsets
                    if (l_ptr and l_lit) _ = try self.updateCoercedLiteral(ast_unit, bin.left, t_info.elem, &l, &l_k);
                    if (r_ptr and r_lit) _ = try self.updateCoercedLiteral(ast_unit, bin.right, t_info.elem, &r, &r_k);

                    return self.context.type_store.mkTensor(ptr_ty, t_info.dims[0..t_info.rank]);
                }
            }

            // 2. Tensor Arithmetic
            if (l_k == .Tensor or r_k == .Tensor) {
                if (bin.op != .add and bin.op != .sub and bin.op != .mul and bin.op != .div) break :arith_blk; // Error

                if (l_k == .Tensor and r_k == .Tensor) {
                    if (!l.eq(r)) break :arith_blk; // Error
                    return l;
                }

                const t_ty = if (l_k == .Tensor) l else r;
                const s_ty = if (l_k == .Tensor) r else l;
                const t_info = self.context.type_store.get(.Tensor, t_ty);
                var s_kind = if (l_k == .Tensor) r_k else l_k;

                if (!check_types.isNumericKind(self, s_kind)) break :arith_blk; // Error

                // Coerce literal scalar to tensor element type
                if (l_k == .Tensor and r_lit) {
                    _ = try self.updateCoercedLiteral(ast_unit, bin.right, t_info.elem, &r, &s_kind);
                } else if (r_k == .Tensor and l_lit) _ = try self.updateCoercedLiteral(ast_unit, bin.left, t_info.elem, &l, &s_kind);

                if (self.assignable(s_ty, t_info.elem) != .success) break :arith_blk; // Error
                return t_ty;
            }

            // Bitwise/Shift restrictions (Integer Only)
            const is_bitwise = (bin.op == .bit_and or bin.op == .bit_or or bin.op == .bit_xor or bin.op == .shl or bin.op == .shr);
            if (is_bitwise) {
                if (!check_types.isIntegerKind(self, l_k) or !check_types.isIntegerKind(self, r_k)) break :arith_blk;
            }

            // 3. SIMD Arithmetic
            if (l_k == .Simd or r_k == .Simd) {
                if (bin.op != .add and bin.op != .sub and bin.op != .mul and bin.op != .div) break :arith_blk;

                if (l_k == .Simd and r_k == .Simd) {
                    const ls = self.context.type_store.get(.Simd, l);
                    const rs = self.context.type_store.get(.Simd, r);
                    if (ls.lanes != rs.lanes or !ls.elem.eq(rs.elem)) break :arith_blk;
                    return l;
                }

                // Simd + Scalar
                const simd_ty = if (l_k == .Simd) l else r;
                const s_ty = if (l_k == .Simd) r else l;
                const s_expr = if (l_k == .Simd) bin.right else bin.left;
                var s_kind = if (l_k == .Simd) r_k else l_k;
                const s_is_lit = if (l_k == .Simd) r_lit else l_lit;

                if (!check_types.isNumericKind(self, s_kind)) break :arith_blk;

                const simd_info = self.context.type_store.get(.Simd, simd_ty);
                if (self.assignable(s_ty, simd_info.elem) != .success) {
                    // Try coercion
                    if (!s_is_lit) break :arith_blk;
                    var s_copy = s_ty;
                    if (try self.updateCoercedLiteral(ast_unit, s_expr, simd_info.elem, &s_copy, &s_kind) and self.assignable(s_copy, simd_info.elem) == .success) {
                        return simd_ty;
                    }
                    break :arith_blk;
                }
                return simd_ty;
            }

            // 4. Div/Mod specific checks
            if (bin.op == .div) try self.checkDivByZero(ast_unit, bin.right, loc);
            if (bin.op == .mod) {
                if ((l_k == .F32 or l_k == .F64) or (r_k == .F32 or r_k == .F64)) break :arith_blk;
                if (check_types.isIntegerKind(self, l_k) and check_types.isIntegerKind(self, r_k)) {
                    try self.checkIntZeroLiteral(ast_unit, bin.right, loc);
                }
            }

            // 5. Complex Arithmetic
            if (l_k == .Complex or r_k == .Complex) {
                if (bin.op != .add and bin.op != .sub and bin.op != .mul and bin.op != .div) break :arith_blk;

                if (l_k == .Complex and r_k == .Complex) {
                    const lc = self.context.type_store.get(.Complex, l);
                    const rc = self.context.type_store.get(.Complex, r);
                    if (lc.elem.eq(rc.elem)) return l;
                    break :arith_blk;
                }

                const c_ty = if (l_k == .Complex) l else r;
                var s_ty = if (l_k == .Complex) r else l;
                var s_kind = if (l_k == .Complex) r_k else l_k;
                const s_expr = if (l_k == .Complex) bin.right else bin.left;
                const s_lit = if (l_k == .Complex) r_lit else l_lit;

                if (!check_types.isNumericKind(self, s_kind)) break :arith_blk;

                const c_elem = self.context.type_store.get(.Complex, c_ty).elem;
                if (c_elem.eq(s_ty)) return c_ty;

                if (s_lit and try self.updateCoercedLiteral(ast_unit, s_expr, c_elem, &s_ty, &s_kind)) {
                    if (c_elem.eq(s_ty)) return c_ty;
                }
                break :arith_blk;
            }

            // 6. Scalar Numeric Arithmetic
            if (!check_types.isNumericKind(self, l_k) or !check_types.isNumericKind(self, r_k)) {
                if (l_k == .Any) return r;
                if (r_k == .Any) return l;
                break :arith_blk;
            }
            if (l.eq(r)) return l;

            // Coercion Logic for Mixed Types (Int/Float)
            if (l_lit and r_lit) {
                const l_float = (l_k == .F32 or l_k == .F64);
                const r_float = (r_k == .F32 or r_k == .F64);
                if (l_float and !r_float and check_types.isIntegerKind(self, r_k)) {
                    if (try self.updateCoercedLiteral(ast_unit, bin.right, l, &r, &r_k)) return l;
                } else if (r_float and !l_float and check_types.isIntegerKind(self, l_k)) {
                    if (try self.updateCoercedLiteral(ast_unit, bin.left, r, &l, &l_k)) return r;
                }
            } else if (l_lit) {
                if (try self.updateCoercedLiteral(ast_unit, bin.left, r, &l, &l_k)) return r;
            } else if (r_lit) {
                if (try self.updateCoercedLiteral(ast_unit, bin.right, l, &r, &r_k)) return l;
            } else {
                // Comptime Constant mixing
                const l_const = self.constNumericKind(ast_unit, bin.left) != .none;
                const r_const = self.constNumericKind(ast_unit, bin.right) != .none;
                const l_float = (l_k == .F32 or l_k == .F64);
                const r_float = (r_k == .F32 or r_k == .F64);

                if (l_const and r_float and check_types.isIntegerKind(self, l_k)) return r;
                if (r_const and l_float and check_types.isIntegerKind(self, r_k)) return l;
                if (l_const and r_const) {
                    if (l_float and !r_float and check_types.isIntegerKind(self, r_k)) return l;
                    if (r_float and !l_float and check_types.isIntegerKind(self, l_k)) return r;
                }
            }
        },

        // --- Comparison ---
        .eq, .neq, .lt, .lte, .gt, .gte => cmp_blk: {
            // 1. Tensor Comparison
            if (l_k == .Tensor or r_k == .Tensor) {
                if (l_k == .Tensor and r_k == .Tensor) {
                    if (!l.eq(r)) break :cmp_blk;
                } else {
                    const t_ty = if (l_k == .Tensor) l else r;
                    const t_info = self.context.type_store.get(.Tensor, t_ty);
                    var s_kind = if (l_k == .Tensor) r_k else l_k;

                    if (!check_types.isNumericKind(self, s_kind)) break :cmp_blk;

                    var s_ty = if (l_k == .Tensor) r else l;
                    if (l_k == .Tensor and r_lit) {
                        _ = try self.updateCoercedLiteral(ast_unit, bin.right, t_info.elem, &r, &s_kind);
                    } else if (r_k == .Tensor and l_lit) _ = try self.updateCoercedLiteral(ast_unit, bin.left, t_info.elem, &l, &s_kind);

                    // Re-fetch scalar type after potential coercion update
                    s_ty = if (l_k == .Tensor) r else l;
                    if (self.assignable(s_ty, t_info.elem) != .success) break :cmp_blk;
                }
                const t_info = self.context.type_store.get(.Tensor, if (l_k == .Tensor) l else r);
                return self.context.type_store.mkTensor(self.context.type_store.tBool(), t_info.dims[0..t_info.rank]);
            }

            if (l_k == .Any or r_k == .Any) return self.context.type_store.tBool();

            // 2. Optional Comparison (eq/neq only)
            const is_eq = bin.op == .eq or bin.op == .neq;
            if (is_eq) {
                if (l_k == .String and r_k == .String) {
                    return self.context.type_store.tBool();
                }
                if ((l_k == .Optional) != (r_k == .Optional)) {
                    const opt = if (l_k == .Optional) l else r;
                    const other = if (l_k == .Optional) r else l;
                    const elem = self.context.type_store.get(.Optional, opt).elem;

                    if (self.typeKind(elem) == .Any) break :cmp_blk;
                    if (self.assignable(other, elem) != .success) break :cmp_blk;
                    return self.context.type_store.tBool();
                }
                // Optional(T) vs Optional(T) with Any
                if (l_k == .Optional and r_k == .Optional) {
                    const l_elem = self.context.type_store.get(.Optional, l).elem;
                    const r_elem = self.context.type_store.get(.Optional, r).elem;
                    if (self.typeKind(l_elem) == .Any and self.typeKind(r_elem) != .Any) {
                        ast_unit.type_info.setExprType(bin.left, r);
                    } else if (self.typeKind(r_elem) == .Any and self.typeKind(l_elem) != .Any) {
                        ast_unit.type_info.setExprType(bin.right, l);
                    }
                    return self.context.type_store.tBool();
                }
            }

            // 3. Scalar Comparison
            var match = false;
            // Strict types
            if (l.eq(r)) {
                if (l_k == .Enum or l_k == .Error or l_k == .Bool or l_k == .TypeType) match = true;
                if (is_eq and l_k == .Error) return self.context.type_store.tBool();
            }

            // Numeric mixing
            if (!match) {
                const ints = check_types.isIntegerKind(self, l_k) and check_types.isIntegerKind(self, r_k);
                const floats = (l_k == .F32 or l_k == .F64) and (r_k == .F32 or r_k == .F64);
                const complex = (l_k == .Complex and r_k == .Complex) and self.context.type_store.get(.Complex, l).elem.eq(self.context.type_store.get(.Complex, r).elem);

                if (ints or floats or complex) {
                    match = true;
                } else if (l_lit and r_lit) {
                    // Literal mixing
                    if ((l_k == .F32 or l_k == .F64) and check_types.isIntegerKind(self, r_k)) {
                        if (try self.updateCoercedLiteral(ast_unit, bin.right, l, &r, &r_k)) match = true;
                    } else if ((r_k == .F32 or r_k == .F64) and check_types.isIntegerKind(self, l_k)) {
                        if (try self.updateCoercedLiteral(ast_unit, bin.left, r, &l, &l_k)) match = true;
                    }
                } else if (l_lit and !r_lit and check_types.isNumericKind(self, r_k)) {
                    if (try self.updateCoercedLiteral(ast_unit, bin.left, r, &l, &l_k)) match = true;
                } else if (r_lit and !l_lit and check_types.isNumericKind(self, l_k)) {
                    if (try self.updateCoercedLiteral(ast_unit, bin.right, l, &r, &r_k)) match = true;
                }
            }

            if (!match) break :cmp_blk;
            return self.context.type_store.tBool();
        },

        // --- Logical ---
        .logical_and, .logical_or => {
            if (l.eq(self.context.type_store.tBool()) and r.eq(self.context.type_store.tBool())) {
                return self.context.type_store.tBool();
            }
        },

        // --- Control Flow ---
        .@"orelse" => orelse_blk: {
            if (check_types.isOptional(self, l)) |elem| {
                if (self.typeKind(elem) == .ErrorSet) {
                    const es = self.context.type_store.get(.ErrorSet, elem);
                    if (self.assignable(es.value_ty, r) == .success) {
                        return self.context.type_store.mkErrorSet(es.value_ty, es.error_ty);
                    }
                } else {
                    const r_k_op = self.typeKind(r);
                    if (self.assignable(elem, r) == .success or r_k_op == .Void or r_k_op == .Noreturn) return elem;
                }
                break :orelse_blk;
            }
            try self.context.diags.addError(loc, .invalid_use_of_orelse_on_non_optional, .{l});
            return self.context.type_store.tTypeError();
        },

        .contains => try self.context.diags.addError(loc, .in_operator_not_supported, .{}),
    }

    // Common error path
    try self.context.diags.addError(loc, .invalid_binary_op_operands, .{ bin.op, l_k, r_k });
    return self.context.type_store.tTypeError();
}

/// Validate the unary expression `id`, ensuring operand types and operators align.
fn checkUnary(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const unary_expr = getExpr(ast_unit, .Unary, id);
    const expr_ty = try self.checkExpr(ctx, ast_unit, unary_expr.expr);
    const type_kind = self.typeKind(expr_ty);

    if (type_kind == .TypeError) return self.context.type_store.tTypeError();

    switch (unary_expr.op) {
        .pos, .neg => {
            if (check_types.isNumericKind(self, type_kind)) return expr_ty;
        },
        .logical_not => {
            if (expr_ty.eq(self.context.type_store.tBool()) or expr_ty.eq(self.context.type_store.tAny())) {
                return self.context.type_store.tBool();
            }
        },
        .address_of => return self.context.type_store.mkPtr(expr_ty, false),
    }

    try self.context.diags.addError(exprLoc(ast_unit, unary_expr), .invalid_unary_op_operand, .{ unary_expr.op, type_kind });
    return self.context.type_store.tTypeError();
}
/// Type-check function literal `id`, handling parameters, defaults, body, and purity.
fn checkFunctionLit(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const fn_expr = getExpr(ast_unit, .FunctionLit, id);

    // 1. Nested Function Validation
    if (self.inFunction(ctx) and !self.isNestedFnAllowed(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, fn_expr), .nested_function_not_allowed, .{});
        return self.context.type_store.tTypeError();
    }

    // 2. Attributes & Setup
    try self.checkAttributes(ctx, ast_unit, fn_expr.attrs);

    const params = ast_unit.exprs.param_pool.slice(fn_expr.params);
    var pbuf = try self.gpa.alloc(types.TypeId, params.len);
    defer self.gpa.free(pbuf);

    _ = try ctx.symtab.push(ctx.symtab.currentId());
    defer ctx.symtab.pop();

    // 3. Prepare Comptime Context
    var value_bindings = List(check_types.Binding){};
    defer {
        self.destroyComptimeBindings(value_bindings.items);
        value_bindings.deinit(self.gpa);
    }
    {
        var iter = ast_unit.type_info.comptime_bindings.iterator();
        while (iter.next()) |entry| {
            try value_bindings.append(self.gpa, .{ .Value = .{ .name = entry.key_ptr.*, .value = entry.value_ptr.value, .ty = entry.value_ptr.ty } });
        }
    }

    var is_generic_template = false;
    var unspecialized_comptime_names = std.DynamicBitSetUnmanaged{};
    defer unspecialized_comptime_names.deinit(self.gpa);

    // 4. Process Parameters
    for (params, 0..) |pid, i| {
        pbuf[i] = try self.checkParam(ctx, ast_unit, pid, &value_bindings, &unspecialized_comptime_names, &is_generic_template);
    }

    // 5. Resolve Return Type
    const res = if (!fn_expr.result_ty.isNone()) blk: {
        const ty_expr = fn_expr.result_ty.unwrap();
        if (try check_types.findAnyTypeExpr(self.gpa, ast_unit, ty_expr)) |any_id| {
            try self.context.diags.addError(exprLocFromId(ast_unit, any_id), .invalid_any_type_annotation, .{});
            return self.context.type_store.tTypeError();
        }
        const defer_check = is_generic_template and (try check_types.exprMentionsAnyNameBitset(self.gpa, ast_unit, ty_expr, &unspecialized_comptime_names));

        if (defer_check) break :blk self.context.type_store.tAny();

        const r = try check_types.typeFromTypeExprWithBindings(self, ctx, ast_unit, ty_expr, value_bindings.items);
        if (!r[0]) return self.context.type_store.tTypeError();
        break :blk r[1];
    } else self.context.type_store.tVoid();

    // 6. Body Analysis & Finalization
    const is_variadic = fn_expr.flags.is_variadic and fn_expr.flags.is_extern;
    const initial_res = if (fn_expr.flags.is_async) self.context.type_store.mkFuture(res) else res;

    // Register temp type for recursive calls
    ast_unit.type_info.expr_types.items[id.toRaw()] = self.context.type_store.mkFunction(pbuf, initial_res, is_variadic, true, fn_expr.flags.is_extern);

    const result_kind = self.typeKind(res);
    try self.pushFunc(ctx, res, (result_kind != .Void and result_kind != .Noreturn), !fn_expr.flags.is_proc);
    defer self.popFunc(ctx);

    if (!fn_expr.body.isNone() and !is_generic_template) {
        try self.pushValueReq(ctx, false);
        defer self.popValueReq(ctx);
        _ = try self.checkExpr(ctx, ast_unit, fn_expr.body.unwrap());
    }

    // Finalize Purity & Async
    const refined_res = ctx.func_stack.items[ctx.func_stack.items.len - 1].inferred_result orelse res;
    const actual_res = if (fn_expr.flags.is_async) self.context.type_store.mkFuture(refined_res) else refined_res;
    const final_ty = self.context.type_store.mkFunction(pbuf, actual_res, is_variadic, !fn_expr.flags.is_proc, fn_expr.flags.is_extern);

    ast_unit.type_info.expr_types.items[id.toRaw()] = final_ty;
    return final_ty;
}

/// Helper: Process a single function parameter.
fn checkParam(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    pid: ast.ParamId,
    value_bindings: *List(check_types.Binding),
    unspecialized: *std.DynamicBitSetUnmanaged,
    is_generic: *bool,
) !types.TypeId {
    const p = ast_unit.exprs.Param.get(pid);
    const pat_id = if (!p.pat.isNone()) p.pat.unwrap() else null;
    const pname = if (pat_id) |pidx| bindingNameOfPattern(ast_unit, pidx) else null;

    // 1. Resolve Specialization & Generic Status
    var override_ty: ?types.TypeId = null;
    if (pname) |name| override_ty = self.lookupParamSpecialization(ctx, name);

    if (p.is_comptime) {
        const specialized = !p.value.isNone() or override_ty != null or (pname != null and ast_unit.type_info.lookupComptimeBindingType(pname.?) != null);
        if (!specialized) {
            is_generic.* = true;
            if (pname) |name| {
                if (name.toRaw() >= unspecialized.capacity()) try unspecialized.resize(self.gpa, name.toRaw() + 1, false);
                unspecialized.set(name.toRaw());
            }
        }
    }

    // 2. Resolve Parameter Type
    var pt = self.context.type_store.tAny();
    if (!p.ty.isNone()) {
        const ty_expr = p.ty.unwrap();
        if (ast_unit.kind(ty_expr) == .AnyType) {
            pt = self.context.type_store.tAny();
        } else if (try check_types.findAnyTypeExpr(self.gpa, ast_unit, ty_expr)) |any_id| {
            try self.context.diags.addError(exprLocFromId(ast_unit, any_id), .invalid_any_type_annotation, .{});
            return self.context.type_store.tTypeError();
        } else {
            const defer_check = is_generic.* and (try check_types.exprMentionsAnyNameBitset(self.gpa, ast_unit, ty_expr, unspecialized));

            if (!defer_check) {
                const res = try check_types.typeFromTypeExprWithBindings(self, ctx, ast_unit, ty_expr, value_bindings.items);
                if (!res[0]) return self.context.type_store.tTypeError();
                pt = res[1];

                if (override_ty) |oty| {
                    const pk = self.typeKind(pt);
                    if (pk == .Any or (pk == .TypeType and self.typeKind(self.context.type_store.get(.TypeType, pt).of) == .Any)) {
                        pt = oty;
                    }
                }

                if (pat_id) |pidx| {
                    var pattern_ok = true;
                    switch (pattern_matching.checkPatternShapeForDecl(self, ast_unit, pidx, pt)) {
                        .ok => {},
                        .tuple_arity_mismatch => {
                            try self.context.diags.addError(exprLocFromId(ast_unit, ty_expr), .tuple_arity_mismatch, .{ @as(i64, @intCast(tuplePatternLength(ast_unit, pidx))), @as(i64, @intCast(tupleTypeLength(self, pt))) });
                            pattern_ok = false;
                        },
                        .struct_pattern_field_mismatch => {
                            const fstr = if (structPatternFieldName(ast_unit, pidx)) |n| getStr(ast_unit, n) else "pattern field";
                            try self.context.diags.addError(exprLocFromId(ast_unit, ty_expr), .struct_pattern_field_mismatch, StringPayload{ .value = fstr });
                            pattern_ok = false;
                        },
                        .pattern_shape_mismatch => {
                            try self.context.diags.addError(exprLocFromId(ast_unit, ty_expr), .pattern_shape_mismatch, StringPayload{ .value = "pattern shape mismatch" });
                            pattern_ok = false;
                        },
                    }
                    if (!pattern_ok) pt = self.context.type_store.tTypeError();
                }
            }
        }
    } else if (override_ty) |oty| {
        pt = oty;
    } else if (p.is_comptime) {
        pt = self.context.type_store.mkTypeType(self.context.type_store.tAny());
    }

    try self.bindParamPattern(ctx, ast_unit, pid, p);

    // 3. Process Default Value
    if (!p.value.isNone()) {
        try self.checkParamDefault(ctx, ast_unit, p.value.unwrap(), pt, pname, p.is_comptime, value_bindings);
    }
    return pt;
}

/// Helper: Check parameter default value and seed comptime bindings.
fn checkParamDefault(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    val_expr: ast.ExprId,
    param_ty: types.TypeId,
    param_name: ?ast.StrId,
    is_comptime: bool,
    value_bindings: *List(check_types.Binding),
) !void {
    var def_ty = try self.checkExpr(ctx, ast_unit, val_expr);
    var def_kind = self.typeKind(def_ty);

    if (def_kind == .TypeError) return;

    if (!param_ty.eq(self.context.type_store.tAny())) {
        var compatible = self.assignable(def_ty, param_ty) == .success;
        if (!compatible and check_types.isNumericKind(self, self.typeKind(param_ty))) {
            if (try self.updateCoercedLiteral(ast_unit, val_expr, param_ty, &def_ty, &def_kind)) {
                compatible = self.assignable(def_ty, param_ty) == .success;
            }
        }

        if (!compatible) {
            try self.context.diags.addError(exprLocFromId(ast_unit, val_expr), .argument_type_mismatch, .{ param_ty, def_ty });
            try self.attachTryCastNote(self.context.diags.count() - 1, param_ty);
            return;
        }
    }

    if (is_comptime and param_name != null) {
        const def_val = self.evalComptimeExpr(ctx, ast_unit, val_expr, &[_]Pipeline.ComptimeBinding{}) catch {
            try self.context.diags.addError(exprLocFromId(ast_unit, val_expr), .checker_comptime_not_executed, .{});
            return;
        };

        try ast_unit.type_info.setComptimeBinding(param_name.?, param_ty, def_val);
        try value_bindings.append(self.gpa, .{ .Value = .{ .name = param_name.?, .value = def_val, .ty = param_ty } });

        if (ctx.interp) |*interp| {
            try interp.setBinding(param_name.?, def_val);
        }
    }
}
/// Type-check tuple literal `id` and produce a tuple type of element types.
fn checkTupleLit(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const tuple_lit = getExpr(ast_unit, .TupleLit, id);
    const elems = ast_unit.exprs.expr_pool.slice(tuple_lit.elems);

    if (elems.len == 0) return self.context.type_store.mkTuple(&.{});

    var tbuf = try self.gpa.alloc(types.TypeId, elems.len);
    defer self.gpa.free(tbuf);

    for (elems, 0..) |expr, i| {
        const ety = try self.checkExpr(ctx, ast_unit, expr);
        if (self.typeKind(ety) == .TypeError) return self.context.type_store.tTypeError();
        tbuf[i] = ety;
    }
    return self.context.type_store.mkTuple(tbuf);
}

/// Type-check array literal `id`, ensuring homogenous element types.
fn checkArrayLit(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    id: ast.ExprId,
) !types.TypeId {
    const array_lit = getExpr(ast_unit, .ArrayLit, id);
    const elems = ast_unit.exprs.expr_pool.slice(array_lit.elems);
    const loc = exprLoc(ast_unit, array_lit);

    if (elems.len == 0) {
        return self.context.type_store.mkArray(self.context.type_store.tAny(), 0);
    }

    // Infer type from the first element
    const first_ty = try self.checkExpr(ctx, ast_unit, elems[0]);
    if (self.typeKind(first_ty) == .TypeError) return self.context.type_store.tTypeError();

    // Verify homogeneity
    for (elems[1..]) |expr| {
        const ety = try self.checkExpr(ctx, ast_unit, expr);
        if (self.typeKind(ety) == .TypeError) return self.context.type_store.tTypeError();

        if (!ety.eq(first_ty)) {
            try self.context.diags.addError(loc, .heterogeneous_array_elements, .{ first_ty, ety });
            return self.context.type_store.tTypeError();
        }
    }

    return self.context.type_store.mkArray(first_ty, elems.len);
}

/// Type-check map literal `id`, enforcing consistent key/value types.
fn checkMapLit(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const row = getExpr(ast_unit, .MapLit, id);
    const kvs = ast_unit.exprs.kv_pool.slice(row.entries);

    if (kvs.len == 0) {
        return self.context.type_store.mkMap(self.context.type_store.tAny(), self.context.type_store.tAny());
    }

    // Infer types from the first entry
    const first = ast_unit.exprs.KeyValue.get(kvs[0]);
    const key_ty = try self.checkExpr(ctx, ast_unit, first.key);
    const val_ty = try self.checkExpr(ctx, ast_unit, first.value);

    if (self.typeKind(key_ty) == .TypeError or self.typeKind(val_ty) == .TypeError) {
        return self.context.type_store.tTypeError();
    }

    // Verify homogeneity
    const loc = exprLoc(ast_unit, row);
    for (kvs[1..]) |kvid| {
        const kv = ast_unit.exprs.KeyValue.get(kvid);
        const kt = try self.checkExpr(ctx, ast_unit, kv.key);
        const vt = try self.checkExpr(ctx, ast_unit, kv.value);

        if (self.typeKind(kt) == .TypeError or self.typeKind(vt) == .TypeError) return self.context.type_store.tTypeError();

        if (!kt.eq(key_ty)) {
            try self.context.diags.addError(loc, .map_mixed_key_types, .{ key_ty, kt });
            return self.context.type_store.tTypeError();
        }
        if (!vt.eq(val_ty)) {
            try self.context.diags.addError(loc, .map_mixed_value_types, .{ val_ty, vt });
            return self.context.type_store.tTypeError();
        }
    }

    return self.context.type_store.mkMap(key_ty, val_ty);
}
/// Resolve the index access expression `id` and compute the fetched element type.
fn checkIndexAccess(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const index_expr = getExpr(ast_unit, .IndexAccess, id);
    const loc = exprLoc(ast_unit, index_expr);
    const col_ty = try self.checkExpr(ctx, ast_unit, index_expr.collection);

    const col_kind = self.typeKind(col_ty);
    if (col_kind == .TypeError) return self.context.type_store.tTypeError();

    // 1. Handle Range Indexing (Slicing)
    if (ast_unit.kind(index_expr.index) == .Range) {
        _ = self.checkExpr(ctx, ast_unit, index_expr.index) catch return self.context.type_store.tTypeError();

        return switch (col_kind) {
            .Array => self.context.type_store.mkSlice(self.context.type_store.get(.Array, col_ty).elem, false),
            .Slice => {
                const r = self.context.type_store.get(.Slice, col_ty);
                return self.context.type_store.mkSlice(r.elem, r.is_const);
            },
            .DynArray => self.context.type_store.mkSlice(self.context.type_store.get(.DynArray, col_ty).elem, false),
            .String => self.context.type_store.tString(),
            .Ptr => {
                const ptr = self.context.type_store.get(.Ptr, col_ty);
                return self.context.type_store.mkSlice(ptr.elem, ptr.is_const);
            },
            .Simd, .Tensor => {
                try self.context.diags.addError(loc, .non_integer_index, StringPayload{ .value = "range" });
                return self.context.type_store.tTypeError();
            },
            else => {
                try self.context.diags.addError(loc, .not_indexable, .{col_ty});
                return self.context.type_store.tTypeError();
            },
        };
    }

    // 2. Resolve Index Expression Type
    const idx_ty = try self.checkExpr(ctx, ast_unit, index_expr.index);
    if (self.typeKind(idx_ty) == .TypeError) return self.context.type_store.tTypeError();

    // 3. Handle Map Indexing (Key Matching)
    if (col_kind == .Map) {
        const m = self.context.type_store.get(.Map, col_ty);
        if (!idx_ty.eq(m.key)) {
            try self.context.diags.addError(loc, .map_wrong_key_type, .{ m.key, idx_ty });
            return self.context.type_store.tTypeError();
        }
        return m.value;
    }

    // 4. Handle Integer Indexing (Array, Slice, Ptr, Simd, Tensor)
    if (!check_types.isIntegerKind(self, self.typeKind(idx_ty))) {
        try self.context.diags.addError(loc, .non_integer_index, .{idx_ty});
        return self.context.type_store.tTypeError();
    }

    return switch (col_kind) {
        .Array => self.context.type_store.get(.Array, col_ty).elem,
        .Slice => self.context.type_store.get(.Slice, col_ty).elem,
        .DynArray => self.context.type_store.get(.DynArray, col_ty).elem,
        .String => self.context.type_store.tU8(),
        .Ptr => self.context.type_store.get(.Ptr, col_ty).elem,
        .Simd => self.context.type_store.get(.Simd, col_ty).elem,
        .Tensor => {
            const tensor = self.context.type_store.get(.Tensor, col_ty);
            const rank: usize = @intCast(tensor.rank);
            if (rank == 0) {
                try self.context.diags.addError(loc, .not_indexable, .{col_ty});
                return self.context.type_store.tTypeError();
            }
            if (rank == 1) return tensor.elem;

            var dims = [_]usize{0} ** types.max_tensor_rank;
            var i: usize = 1;
            while (i < rank) : (i += 1) dims[i - 1] = tensor.dims[i];
            return self.context.type_store.mkTensor(tensor.elem, dims[0 .. rank - 1]);
        },
        else => {
            try self.context.diags.addError(loc, .not_indexable, .{col_ty});
            return self.context.type_store.tTypeError();
        },
    };
}

/// Offer builtin `dynarray` methods (e.g., `append`) when resolving `owner_ty.field_name`.
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

    const name = getStr(ast_unit, field_name);
    // Optimization: Check length first
    if (name.len == 6 and std.mem.eql(u8, name, "append")) {
        // Validate Receiver
        if (parent_kind == .Ptr) {
            const ptr_row = self.context.type_store.get(.Ptr, receiver_ty);
            if (!ptr_row.elem.eq(owner_ty) or ptr_row.is_const) {
                try self.context.diags.addError(loc, .method_receiver_requires_pointer, .{name});
                return error.MethodResolutionFailed;
            }
        }

        const dyn_info = self.context.type_store.get(.DynArray, owner_ty);
        const ptr_owner_ty = self.context.type_store.mkPtr(owner_ty, false);
        const params = [_]types.TypeId{ ptr_owner_ty, dyn_info.elem };
        const fn_ty = self.context.type_store.mkFunction(&params, self.context.type_store.tVoid(), false, false, false);

        try ast_unit.type_info.setMethodBinding(expr_id, .{
            .owner_type = owner_ty,
            .method_name = field_name,
            .decl_id = ast.DeclId.fromRaw(0),
            .decl_ast = ast_unit,
            .func_type = fn_ty,
            .self_param_type = ptr_owner_ty,
            .receiver_kind = .pointer,
            .requires_implicit_receiver = parent_kind != .TypeType,
            .needs_addr_of = parent_kind != .Ptr,
            .builtin = .dynarray_append,
        });
        return fn_ty;
    }

    return self.context.type_store.tTypeError();
}

/// Resolve a field access that might refer to a method on `owner_ty`.
fn resolveMethodFieldAccess(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    owner_ty: types.TypeId,
    receiver_ty: types.TypeId,
    field_name: ast.StrId,
    loc: Loc,
) !types.TypeId {
    const parent_kind = self.typeKind(receiver_ty);
    const entry = self.context.type_store.getMethod(owner_ty, field_name) orelse {
        return try self.tryRegisterDynArrayBuiltin(ast_unit, expr_id, owner_ty, receiver_ty, field_name, parent_kind, loc);
    };

    const implicit_receiver = entry.receiver_kind != .none and parent_kind != .TypeType;
    var needs_addr_of = false;

    if (implicit_receiver) {
        switch (entry.receiver_kind) {
            .value => {
                if (!receiver_ty.eq(owner_ty)) {
                    try self.context.diags.addError(loc, .method_receiver_requires_value, .{getStr(ast_unit, field_name)});
                    return error.MethodResolutionFailed;
                }
            },
            .pointer, .pointer_const => {
                if (parent_kind == .Ptr) {
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
            else => {},
        }
    }

    const fn_row = self.context.type_store.get(.Function, entry.func_type);

    // Create trimmed function type for implicit receiver calls
    const result_fn_ty = if (implicit_receiver) blk: {
        const params = self.context.type_store.type_pool.slice(fn_row.params);
        const rest = if (params.len <= 1) params[0..0] else params[1..];
        break :blk self.context.type_store.mkFunction(rest, fn_row.result, fn_row.is_variadic, fn_row.is_pure, false);
    } else entry.func_type;

    try ast_unit.type_info.setMethodBinding(expr_id, .{
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
    });

    return result_fn_ty;
}
/// Determine the type denoted by the field access expression `id`.
fn checkFieldAccess(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const field_expr = getExpr(ast_unit, .FieldAccess, id);
    const field_loc = exprLoc(ast_unit, field_expr);

    const parent_ty = try self.checkExpr(ctx, ast_unit, field_expr.parent);
    if (self.typeKind(parent_ty) == .TypeError) return self.context.type_store.tTypeError();

    const ty = parent_ty;
    const kind = self.typeKind(ty);
    if (kind == .Any) return self.context.type_store.tAny();

    const field_name = getStr(ast_unit, field_expr.field);

    // 1. Check Magic Fields (len, ptr, capacity)
    switch (field_name.len) {
        3 => {
            if (std.mem.eql(u8, field_name, "len")) {
                switch (kind) {
                    .Array, .Slice, .DynArray, .String => {
                        try ast_unit.type_info.setFieldIndex(id, 1);
                        return self.context.type_store.tUsize();
                    },
                    else => {},
                }
            } else if (std.mem.eql(u8, field_name, "ptr")) {
                const ptr_elem: ?types.TypeId = switch (kind) {
                    .Array => self.context.type_store.get(.Array, ty).elem,
                    .Slice => self.context.type_store.get(.Slice, ty).elem,
                    .DynArray => self.context.type_store.get(.DynArray, ty).elem,
                    .String => self.context.type_store.tU8(),
                    else => null,
                };
                if (ptr_elem) |elem| {
                    try ast_unit.type_info.setFieldIndex(id, 0);
                    return self.context.type_store.mkPtr(elem, kind == .String);
                }
            }
        },
        8 => if (kind == .DynArray and std.mem.eql(u8, field_name, "capacity")) {
            try ast_unit.type_info.setFieldIndex(id, 2);
            return self.context.type_store.tUsize();
        },
        else => {},
    }

    // 2. Check Complex Fields (real, imag)
    if (kind == .Complex) {
        if (std.mem.eql(u8, field_name, "real") or std.mem.eql(u8, field_name, "re")) {
            try ast_unit.type_info.setFieldIndex(id, 0);
            return self.context.type_store.get(.Complex, ty).elem;
        }
        if (std.mem.eql(u8, field_name, "imag") or std.mem.eql(u8, field_name, "im")) {
            try ast_unit.type_info.setFieldIndex(id, 1);
            return self.context.type_store.get(.Complex, ty).elem;
        }
        try self.context.diags.addError(field_loc, .unknown_struct_field, .{field_name});
        return self.context.type_store.tTypeError();
    }

    // 3. Main Type Switch
    switch (kind) {
        .Ast => {
            const ast_ty = self.context.type_store.get(.Ast, ty);
            const pkg_name = self.context.interner.get(ast_ty.pkg_name);
            const filepath = self.context.interner.get(ast_ty.filepath);

            const pkg = self.context.compilation_unit.packages.getPtr(pkg_name) orelse
                return self.context.type_store.tTypeError();
            const parent_unit = pkg.sources.getPtr(filepath) orelse
                return self.context.type_store.tTypeError();

            if (parent_unit.ast) |a| {
                if (a.type_info.getExport(a.exprs.strs.intern(field_name))) |ex| {
                    return ex.ty;
                }

                const last_diag_idx = self.context.diags.count();
                try self.context.diags.addError(field_loc, .unknown_module_field, .{field_name});

                var all_exports = List([]const u8){};
                defer all_exports.deinit(self.gpa);
                var it = a.type_info.exports.iterator();
                while (it.next()) |entry| {
                    try all_exports.append(self.gpa, a.exprs.strs.get(entry.key_ptr.*));
                }
                try self.attachSuggestionListNotes(last_diag_idx, field_name, all_exports.items, .did_you_mean_field, .available_fields);
                return self.context.type_store.tTypeError();
            }

            try self.context.diags.addError(field_loc, .unknown_module_field, .{field_name});
            return self.context.type_store.tTypeError();
        },
        .Struct, .Union => {
            const fields = self.context.type_store.field_pool.slice(if (kind == .Struct) self.context.type_store.get(.Struct, ty).fields else self.context.type_store.get(.Union, ty).fields);

            for (fields, 0..) |fid, i| {
                const f = self.context.type_store.Field.get(fid);
                if (f.name.eq(field_expr.field)) {
                    try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                    return f.ty;
                }
            }

            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, ty, field_expr.field, field_loc) catch |err| switch (err) {
                else => return self.context.type_store.tTypeError(),
            };
            if (self.typeKind(method_ty) != .TypeError) return method_ty;

            const last_diag_idx = self.context.diags.count();
            try self.context.diags.addError(field_loc, .unknown_struct_field, .{field_name});

            var all_fields = List([]const u8){};
            defer all_fields.deinit(self.gpa);
            for (fields) |fid| {
                try all_fields.append(self.gpa, self.context.interner.get(self.context.type_store.Field.get(fid).name));
            }
            try self.attachSuggestionListNotes(last_diag_idx, field_name, all_fields.items, .did_you_mean_field, .available_fields);
            return self.context.type_store.tTypeError();
        },
        .Tuple => {
            const elems = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, ty).elems);
            if (std.mem.eql(u8, field_name, "len")) {
                return self.context.type_store.tUsize();
            }
            const index = std.fmt.parseInt(usize, field_name, 10) catch {
                try self.context.diags.addError(field_loc, .expected_field_name_or_index, StringPayload{ .value = field_name });
                return self.context.type_store.tTypeError();
            };
            if (index >= elems.len) {
                try self.context.diags.addError(field_loc, .tuple_index_out_of_bounds, .{ @as(i64, @intCast(index)), if (elems.len == 0) 0 else @as(i64, @intCast(elems.len - 1)) });
                return self.context.type_store.tTypeError();
            }
            try ast_unit.type_info.setFieldIndex(id, @intCast(index));
            return elems[index];
        },
        .DynArray, .Enum, .Error => {
            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, ty, field_expr.field, field_loc) catch return self.context.type_store.tTypeError();
            if (self.typeKind(method_ty) != .TypeError) return method_ty;

            try self.context.diags.addError(field_loc, .field_access_on_non_aggregate, .{kind});
            return self.context.type_store.tTypeError();
        },
        .Ptr => {
            const ptr_inner = self.context.type_store.get(.Ptr, ty).elem;
            const inner_kind = self.typeKind(ptr_inner);

            if (inner_kind == .Complex) {
                if (std.mem.eql(u8, field_name, "real") or std.mem.eql(u8, field_name, "re")) {
                    try ast_unit.type_info.setFieldIndex(id, 0);
                    return self.context.type_store.get(.Complex, ptr_inner).elem;
                }
                if (std.mem.eql(u8, field_name, "imag") or std.mem.eql(u8, field_name, "im")) {
                    try ast_unit.type_info.setFieldIndex(id, 1);
                    return self.context.type_store.get(.Complex, ptr_inner).elem;
                }
            } else if (inner_kind == .Struct) {
                const fields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, ptr_inner).fields);
                for (fields, 0..) |fid, i| {
                    const f = self.context.type_store.Field.get(fid);
                    if (f.name.eq(field_expr.field)) {
                        try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                        return f.ty;
                    }
                }
            }

            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ptr_inner, parent_ty, field_expr.field, field_loc) catch return self.context.type_store.tTypeError();
            if (self.typeKind(method_ty) != .TypeError) return method_ty;

            if (inner_kind == .Struct) {
                try self.context.diags.addError(field_loc, .unknown_struct_field, StringPayload{ .value = field_name });
            } else {
                try self.context.diags.addError(field_loc, .field_access_on_non_aggregate, .{kind});
            }
            return self.context.type_store.tTypeError();
        },
        .TypeType => {
            const inner_ty = self.context.type_store.get(.TypeType, ty).of;
            const inner_kind = self.typeKind(inner_ty);

            if (inner_kind == .Enum) {
                const en = self.context.type_store.get(.Enum, inner_ty);
                const members = self.context.type_store.enum_member_pool.slice(en.members);
                for (members, 0..) |mid, i| {
                    if (self.context.type_store.EnumMember.get(mid).name.eq(field_expr.field)) {
                        try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                        return inner_ty;
                    }
                }

                try self.context.diags.addError(field_loc, .unknown_enum_tag, .{field_name});
                var all_tags = List([]const u8){};
                defer all_tags.deinit(self.gpa);
                try self.appendEnumMemberNames(&all_tags, members);
                try self.attachSuggestionListNotes(self.context.diags.count() - 1, field_name, all_tags.items, .did_you_mean_tag, .available_tags);
                return self.context.type_store.tTypeError();
            } else if (inner_kind == .Ast) {
                return self.checkFieldAccess(ctx, ast_unit, id);
            }

            // Shared logic for Struct, Variant, Error (all use Field pool)
            if (inner_kind == .Struct or inner_kind == .Variant or inner_kind == .Error) {
                const fields = switch (inner_kind) {
                    .Struct => self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, inner_ty).fields),
                    .Variant => self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, inner_ty).variants),
                    .Error => self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, inner_ty).variants),
                    else => unreachable,
                };

                for (fields, 0..) |fid, i| {
                    const f = self.context.type_store.Field.get(fid);
                    if (f.name.eq(field_expr.field)) {
                        if (inner_kind == .Variant) {
                            const pk = self.typeKind(f.ty);
                            if (pk != .Void) {
                                // Variant Arity Error
                                const found: i64 = if (pk == .Tuple) @intCast(self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, f.ty).elems).len) else 1;
                                try self.context.diags.addError(field_loc, .variant_payload_arity_mismatch, .{ 0, found });
                                return self.context.type_store.tTypeError();
                            }
                        }
                        try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                        return inner_ty;
                    }
                }

                // Fallback to Method Lookup
                const method_ty = self.resolveMethodFieldAccess(ast_unit, id, inner_ty, parent_ty, field_expr.field, field_loc) catch return self.context.type_store.tTypeError();
                if (self.typeKind(method_ty) != .TypeError) return method_ty;

                // Error Reporting
                switch (inner_kind) {
                    .Struct => try self.context.diags.addError(field_loc, .unknown_struct_field, StringPayload{ .value = field_name }),
                    .Variant => try self.context.diags.addError(field_loc, .unknown_variant_tag, StringPayload{ .value = field_name }),
                    .Error => try self.context.diags.addError(field_loc, .unknown_error_tag, .{field_name}),
                    else => unreachable,
                }

                var all_tags = List([]const u8){};
                defer all_tags.deinit(self.gpa);
                try self.appendFieldNames(&all_tags, fields);
                if (inner_kind == .Struct) {
                    try self.attachSuggestionListNotes(self.context.diags.count() - 1, field_name, all_tags.items, .did_you_mean_field, .available_fields);
                } else {
                    try self.attachSuggestionListNotes(self.context.diags.count() - 1, field_name, all_tags.items, .did_you_mean_tag, .available_tags);
                }
                return self.context.type_store.tTypeError();
            }

            try self.context.diags.addError(field_loc, .field_access_on_non_aggregate, .{inner_kind});
            return self.context.type_store.tTypeError();
        },
        .Variant => {
            const vty = self.context.type_store.get(.Variant, ty);
            const variants = self.context.type_store.field_pool.slice(vty.variants);

            if (field_expr.is_tuple) {
                const index = std.fmt.parseInt(usize, field_name, 10) catch {
                    try self.context.diags.addError(field_loc, .expected_field_name_or_index, StringPayload{ .value = field_name });
                    return self.context.type_store.tTypeError();
                };
                const runtime_fields: usize = if (variants.len == 0) 1 else 2;
                if (index >= runtime_fields) {
                    try self.context.diags.addError(field_loc, .tuple_index_out_of_bounds, .{ @as(i64, @intCast(index)), if (runtime_fields == 0) 0 else @as(i64, @intCast(runtime_fields - 1)) });
                    return self.context.type_store.tTypeError();
                }
                try ast_unit.type_info.setFieldIndex(id, @intCast(index));

                if (index == 0) return self.context.type_store.tI32();

                var union_fields_args = try self.gpa.alloc(types.TypeStore.StructFieldArg, variants.len);
                defer self.gpa.free(union_fields_args);
                for (variants, 0..) |fid, i| {
                    const fld = self.context.type_store.Field.get(fid);
                    union_fields_args[i] = .{ .name = fld.name, .ty = fld.ty };
                }
                return self.context.type_store.mkUnion(union_fields_args);
            }

            for (variants, 0..) |fid, i| {
                const variant = self.context.type_store.Field.get(fid);
                if (variant.name.eq(field_expr.field)) {
                    try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                    return if (self.typeKind(variant.ty) == .Void) self.context.type_store.tI32() else variant.ty;
                }
            }

            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, ty, field_expr.field, field_loc) catch return self.context.type_store.tTypeError();
            if (self.typeKind(method_ty) != .TypeError) return method_ty;

            const last_diag_idx = self.context.diags.count();
            try self.context.diags.addError(field_loc, .unknown_variant_tag, StringPayload{ .value = field_name });

            var all_tags = List([]const u8){};
            defer all_tags.deinit(self.gpa);
            try self.appendFieldNames(&all_tags, variants);
            try self.attachSuggestionListNotes(last_diag_idx, field_name, all_tags.items, .did_you_mean_tag, .available_tags);
            return self.context.type_store.tTypeError();
        },
        else => {
            try self.context.diags.addError(field_loc, .field_access_on_non_aggregate, .{kind});
            return self.context.type_store.tTypeError();
        },
    }
}

/// Type-check range literal `id`, ensuring bounds share compatible numeric types.
fn checkRange(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const range = getExpr(ast_unit, .Range, id);
    var start_ty = if (!range.start.isNone()) try self.checkExpr(ctx, ast_unit, range.start.unwrap()) else null;
    var end_ty = if (!range.end.isNone()) try self.checkExpr(ctx, ast_unit, range.end.unwrap()) else null;

    if (start_ty == null and end_ty != null) {
        const k = self.typeKind(end_ty.?);
        if (k == .Tuple or k == .Any) {
            if (k == .Any) try ast_unit.type_info.markRangeSpread(self.gpa, id);
            return end_ty.?;
        }
    } else if (start_ty == null and end_ty == null) {
        try self.context.diags.addError(exprLoc(ast_unit, range), .cannot_infer_range_type, .{});
        return self.context.type_store.tTypeError();
    }

    if (start_ty != null and end_ty != null and !start_ty.?.eq(end_ty.?)) {
        var l = start_ty.?;
        var r = end_ty.?;
        var l_k = self.typeKind(l);
        var r_k = self.typeKind(r);

        const l_is_lit = !range.start.isNone() and ast_unit.kind(range.start.unwrap()) == .Literal;
        const r_is_lit = !range.end.isNone() and ast_unit.kind(range.end.unwrap()) == .Literal;

        if (l_is_lit and check_types.isIntegerKind(self, r_k)) {
            if (try self.updateCoercedLiteral(ast_unit, range.start.unwrap(), r, &l, &l_k)) start_ty = l;
        } else if (r_is_lit and check_types.isIntegerKind(self, l_k)) {
            if (try self.updateCoercedLiteral(ast_unit, range.end.unwrap(), l, &r, &r_k)) end_ty = r;
        }
    }

    const final_ty = start_ty orelse end_ty.?;

    if (start_ty != null and end_ty != null and !start_ty.?.eq(end_ty.?)) {
        try self.context.diags.addError(exprLoc(ast_unit, range), .range_type_mismatch, .{ start_ty.?, end_ty.? });
        return self.context.type_store.tTypeError();
    }

    const k = self.typeKind(final_ty);
    if (!check_types.isIntegerKind(self, k) and k != .Any) {
        if (range.start.isNone()) {
            try ast_unit.type_info.markRangeSpread(self.gpa, id);
            return final_ty;
        }
        const hint = self.context.type_store.tAny();
        try self.context.diags.addError(exprLoc(ast_unit, range), .range_requires_integer_operands, .{ start_ty orelse hint, end_ty orelse hint });
        return self.context.type_store.tTypeError();
    }

    return self.context.type_store.mkSlice(self.context.type_store.tUsize(), false);
}

/// Extract an identifier token or field name from a type expression for diagnostics.
fn typeExprNameForDiag(ast_unit: *ast.Ast, expr: ast.ExprId) ?ast.StrId {
    return switch (ast_unit.kind(expr)) {
        .Ident => ast_unit.exprs.get(.Ident, expr).name,
        .FieldAccess => ast_unit.exprs.get(.FieldAccess, expr).field,
        .Call => typeExprNameForDiag(ast_unit, ast_unit.exprs.get(.Call, expr).callee),
        else => null,
    };
}

fn resolveStructLitExpectedType(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, lit_ty: ast.ExprId) !types.TypeId {
    const resolved = try check_types.typeFromTypeExpr(self, ctx, ast_unit, lit_ty);
    if (resolved[0]) return resolved[1];

    const loc = exprLocFromId(ast_unit, lit_ty);
    if (typeExprNameForDiag(ast_unit, lit_ty)) |name| {
        try self.context.diags.addError(loc, .undefined_identifier, .{ast_unit.exprs.strs.get(name)});
    } else {
        try self.context.diags.addError(loc, .could_not_resolve_type, StringPayload{ .value = "type expression" });
    }
    return self.context.type_store.tTypeError();
}

fn coerceStructLitFields(self: *Checker, ast_unit: *ast.Ast, lit_fields: []const ast.StructFieldValueId, expect_ty: types.TypeId) !bool {
    const ts = self.context.type_store;
    const diags = self.context.diags;
    if (self.typeKind(expect_ty) != .Struct) return true;

    const expect_fields = ts.field_pool.slice(ts.get(.Struct, expect_ty).fields);
    for (lit_fields) |fid| {
        const f = ast_unit.exprs.StructFieldValue.get(fid);
        if (f.name.isNone()) continue;

        var expected_field_ty: ?types.TypeId = null;
        for (expect_fields) |efid| {
            const ef = ts.Field.get(efid);
            if (ef.name.eq(f.name.unwrap())) {
                expected_field_ty = ef.ty;
                break;
            }
        }

        if (expected_field_ty) |ety| {
            const got_ty = ast_unit.type_info.expr_types.items[f.value.toRaw()] orelse continue;
            if (!got_ty.eq(ety)) {
                if (self.tryCoerceNullLiteral(ast_unit, f.value, ety)) {
                    ast_unit.type_info.expr_types.items[f.value.toRaw()] = ety;
                    continue;
                }

                if (ast_unit.kind(f.value) == .NullLit) {
                    try diags.addError(exprLocFromId(ast_unit, f.value), .struct_field_type_mismatch, .{ ety, got_ty });
                    return false;
                }

                if (check_types.isNumericKind(self, self.typeKind(ety))) {
                    var coerced = got_ty;
                    var k = self.typeKind(coerced);
                    _ = try self.updateCoercedLiteral(ast_unit, f.value, ety, &coerced, &k);
                }
            }
        }
    }
    return true;
}

fn checkStructLit(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const diags = self.context.diags;
    const struct_lit = getExpr(ast_unit, .StructLit, id);
    const lit_fields = ast_unit.exprs.sfv_pool.slice(struct_lit.fields);

    // Phase 1: Scan fields for spread syntax and validate names
    var spread_expr: ?ast.ExprId = null;
    for (lit_fields) |fid| {
        if (ast.structFieldSpreadExpr(ast_unit, fid)) |s| {
            if (spread_expr != null) {
                try diags.addError(exprLoc(ast_unit, struct_lit), .struct_field_name_mismatch, .{});
                return ts.tTypeError();
            }
            spread_expr = s;
        } else if (ast_unit.exprs.StructFieldValue.get(fid).name.isNone()) {
            try diags.addError(exprLoc(ast_unit, struct_lit), .struct_field_name_mismatch, .{});
            return ts.tTypeError();
        }
    }

    // Phase 2: Resolve expected type and variant parent early
    var explicit_ty: ?types.TypeId = null;
    var variant_parent_ty: ?types.TypeId = null;

    if (!struct_lit.ty.isNone()) {
        const raw_ty = struct_lit.ty.unwrap();
        explicit_ty = try resolveStructLitExpectedType(self, ctx, ast_unit, raw_ty);
        if (self.typeKind(explicit_ty.?) == .TypeError) return ts.tTypeError();

        if (ast_unit.kind(raw_ty) == .FieldAccess) {
            const fr = getExpr(ast_unit, .FieldAccess, raw_ty);
            const parent_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, fr.parent);
            if (parent_res[0]) {
                const k = self.typeKind(parent_res[1]);
                if (k == .Variant or k == .Error) {
                    const pt = self.getPayloadTypeForCase(parent_res[1], fr.field);
                    if (pt != null and self.typeKind(pt.?) == .Struct) variant_parent_ty = parent_res[1];
                }
            }
        }
    }

    // Phase 3: Spread Validation Path
    if (spread_expr) |spread_id| {
        const spread_ty = try self.checkExpr(ctx, ast_unit, spread_id);
        if (self.typeKind(spread_ty) == .TypeError) return ts.tTypeError();

        const base_ty = explicit_ty orelse spread_ty;
        if (self.typeKind(base_ty) != .Struct) {
            try diags.addError(exprLocFromId(ast_unit, spread_id), .expected_struct_type, .{base_ty});
            return ts.tTypeError();
        }

        if (!spread_ty.eq(base_ty) and self.assignable(spread_ty, base_ty) != .success) {
            try diags.addError(exprLocFromId(ast_unit, spread_id), .struct_field_type_mismatch, .{ base_ty, spread_ty });
            return ts.tTypeError();
        }

        const base_fields = ts.field_pool.slice(ts.get(.Struct, base_ty).fields);
        for (lit_fields) |fid| {
            if (ast.structFieldSpreadExpr(ast_unit, fid) != null) continue;

            const f = ast_unit.exprs.StructFieldValue.get(fid);
            const ft = try self.checkExpr(ctx, ast_unit, f.value);
            if (self.typeKind(ft) == .TypeError) return ts.tTypeError();

            const match = self.findFieldByName(base_fields, f.name.unwrap()) orelse {
                try diags.addError(exprLoc(ast_unit, struct_lit), .unknown_struct_field, StringPayload{ .value = getStr(ast_unit, f.name.unwrap()) });
                return ts.tTypeError();
            };

            if (self.assignable(ft, match.field.ty) != .success) {
                try diags.addError(ast_unit.exprs.locs.get(f.loc), .struct_field_type_mismatch, .{ match.field.ty, ft });
                return ts.tTypeError();
            }
        }

        if (!try self.coerceStructLitFields(ast_unit, lit_fields, base_ty)) return ts.tTypeError();
        return variant_parent_ty orelse base_ty;
    }

    // Phase 4: Standard Validation Path (No Spread)
    const buf = try ts.gpa.alloc(types.TypeStore.StructFieldArg, lit_fields.len);
    defer ts.gpa.free(buf);

    for (lit_fields, 0..) |fid, i| {
        const f = ast_unit.exprs.StructFieldValue.get(fid);
        const ft = try self.checkExpr(ctx, ast_unit, f.value);
        if (self.typeKind(ft) == .TypeError) return ts.tTypeError();
        buf[i] = .{ .name = f.name.unwrap(), .ty = ft };
    }

    const struct_ty = ts.mkStruct(buf, 0);
    if (explicit_ty == null) return struct_ty;

    const expect_ty = explicit_ty.?;
    switch (self.assignable(struct_ty, expect_ty)) {
        .success => {},
        .struct_field_count_mismatch => {
            if (!try self.checkMissingFields(ctx, ast_unit, struct_lit, buf, expect_ty)) return ts.tTypeError();
        },
        .unknown_struct_field => {
            const expect_fields = switch (self.typeKind(expect_ty)) {
                .Struct => ts.field_pool.slice(ts.get(.Struct, expect_ty).fields),
                .Union => ts.field_pool.slice(ts.get(.Union, expect_ty).fields),
                else => &[_]types.FieldId{},
            };
            for (buf) |provided| {
                if (self.findFieldByName(expect_fields, provided.name) == null) {
                    try diags.addError(exprLoc(ast_unit, struct_lit), .unknown_struct_field, StringPayload{ .value = getStr(ast_unit, provided.name) });
                    return ts.tTypeError();
                }
            }
        },
        .struct_field_type_mismatch => |err| {
            const f = ast_unit.exprs.StructFieldValue.get(lit_fields[err.index]);
            const expect_fields = ts.field_pool.slice(ts.get(.Struct, expect_ty).fields);
            const match = self.findFieldByName(expect_fields, f.name.unwrap()).?;
            try diags.addError(ast_unit.exprs.locs.get(f.loc), .struct_field_type_mismatch, .{ match.field.ty, ast_unit.type_info.expr_types.items[f.value.toRaw()].? });
            return ts.tTypeError();
        },
        .union_literal_multiple_fields => {
            try diags.addError(exprLoc(ast_unit, struct_lit), .union_literal_multiple_fields, .{});
            return ts.tTypeError();
        },
        .union_empty_literal => {
            try diags.addError(exprLoc(ast_unit, struct_lit), .union_empty_literal, .{});
            return ts.tTypeError();
        },
        else => {
            try diags.addError(exprLoc(ast_unit, struct_lit), .struct_field_type_mismatch, .{ expect_ty, struct_ty });
            return ts.tTypeError();
        },
    }

    if (!try self.coerceStructLitFields(ast_unit, lit_fields, expect_ty)) return ts.tTypeError();
    return variant_parent_ty orelse expect_ty;
}
/// Checks if missing fields have defaults. Returns true if valid, false (and emits diag) if invalid.
fn checkMissingFields(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, struct_lit: ast.Rows.StructLit, provided: []const types.TypeStore.StructFieldArg, expect_ty: types.TypeId) !bool {
    const ts = self.context.type_store;
    const ty_expr = struct_lit.ty.unwrap();
    const expect_fields = ts.field_pool.slice(ts.get(.Struct, expect_ty).fields);

    var missing = List([]const u8){};
    defer missing.deinit(self.gpa);

    for (expect_fields) |efid| {
        const ef = ts.Field.get(efid);
        var present = false;
        for (provided) |p| {
            if (p.name.eq(ef.name)) {
                present = true;
                break;
            }
        }

        if (!present) {
            if (!self.structFieldHasDefault(ctx, ast_unit, ty_expr, ef.name)) {
                try missing.append(self.gpa, self.context.interner.get(ef.name));
            }
        }
    }

    if (missing.items.len > 0) {
        const joined = try diag.joinStrings(self.gpa, ", ", missing.items);
        defer self.gpa.free(joined);

        const idx = self.context.diags.count();
        try self.context.diags.addError(exprLoc(ast_unit, struct_lit), .struct_missing_field, StringPayload{ .value = joined });
        const joined_id = self.context.interner.intern(joined);
        try self.context.diags.attachNoteArgs(idx, null, .missing_fields_list, StringNotePayload{ .value = joined_id });
        return false;
    }
    return true;
}

/// Return true if `field_name` has a default value within `ty_expr`.
fn structFieldHasDefault(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, ty_expr: ast.ExprId, field_name: ast.StrId) bool {
    switch (ast_unit.kind(ty_expr)) {
        .StructType => return structFieldHasDefaultInStructExpr(ast_unit, ty_expr, field_name),
        .Ident => {
            const idr = getExpr(ast_unit, .Ident, ty_expr);
            if (self.lookup(ctx, idr.name)) |sid| {
                const sym = ctx.symtab.syms.get(sid);
                if (!sym.origin_decl.isNone()) {
                    const decl = ast_unit.exprs.Decl.get(sym.origin_decl.unwrap());
                    return self.structFieldHasDefault(ctx, ast_unit, decl.value, field_name);
                }
            }
        },
        .FieldAccess => {
            const fr = getExpr(ast_unit, .FieldAccess, ty_expr);
            const parent_ty = self.checkExpr(ctx, ast_unit, fr.parent) catch return false;

            if (self.typeKind(parent_ty) == .Ast) {
                const ast_ty = self.context.type_store.get(.Ast, parent_ty);
                const pkg_name = self.context.interner.get(ast_ty.pkg_name);
                const filepath = self.context.interner.get(ast_ty.filepath);

                if (self.context.compilation_unit.packages.getPtr(pkg_name)) |pkg| {
                    if (pkg.sources.getPtr(filepath)) |unit| {
                        if (unit.ast) |mod_ast| {
                            if (mod_ast.type_info.getExport(fr.field)) |ex| {
                                const decl = mod_ast.exprs.Decl.get(ex.decl_id);
                                if (mod_ast.kind(decl.value) == .StructType) {
                                    return structFieldHasDefaultInStructExpr(mod_ast, decl.value, field_name);
                                }
                            }
                        }
                    }
                }
            }
        },
        else => {},
    }
    return false;
}

/// Helper checking for defaults inside a direct struct type expression.
fn structFieldHasDefaultInStructExpr(ast_unit: *ast.Ast, struct_expr: ast.ExprId, field_name: ast.StrId) bool {
    const fields = ast_unit.exprs.sfield_pool.slice(ast_unit.exprs.get(.StructType, struct_expr).fields);
    for (fields) |sfid| {
        const sf = ast_unit.exprs.StructField.get(sfid);
        if (sf.name.eq(field_name)) return !sf.value.isNone();
    }
    return false;
}
/// Type-check dereference expression `id`, ensuring pointer operand.
fn checkDeref(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const row = getExpr(ast_unit, .Deref, id);
    const ptr_ty = try self.checkExpr(ctx, ast_unit, row.expr);

    if (self.typeKind(ptr_ty) == .TypeError) return ts.tTypeError();
    if (self.typeKind(ptr_ty) != .Ptr) {
        try self.context.diags.addError(exprLoc(ast_unit, row), .deref_non_pointer, .{ptr_ty});
        return ts.tTypeError();
    }
    return ts.get(.Ptr, ptr_ty).elem;
}

// =========================
// Calls & related helpers
// =========================

/// Resolve the payload type associated with tag `tag` in variant/error type `parent_ty`.
fn resolveTagPayloadType(self: *Checker, parent_ty: types.TypeId, tag: ast.StrId) ?types.TypeId {
    const ts = &self.context.type_store;
    const pk = self.trow(parent_ty);

    const variants_list = switch (pk) {
        .Variant => ts.get(.Variant, parent_ty).variants,
        .Error => ts.get(.Error, parent_ty).variants,
        else => return ts.tTypeError(),
    };

    const cases = ts.field_pool.slice(variants_list);
    for (cases) |fid| {
        const f = ts.Field.get(fid.toRaw());
        if (f.name.eq(tag)) return f.ty;
    }
    return ts.tTypeError();
}

/// Handle `(Type).Tag(...)` calls that construct variant/error cases.
fn checkTagConstructorCall(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    parent_ty: types.TypeId,
    tag: ast.StrId,
    args: []const ast.ExprId,
    loc: Loc,
) !types.TypeId {
    const ts = self.context.type_store;
    const diags = self.context.diags;
    const pk = self.typeKind(parent_ty);

    const variants_list = switch (pk) {
        .Variant => ts.get(.Variant, parent_ty).variants,
        .Error => ts.get(.Error, parent_ty).variants,
        else => return ts.tTypeError(),
    };

    // Find Payload Type
    var payload_ty: types.TypeId = ts.tTypeError();
    const cases = ts.field_pool.slice(variants_list);
    var found = false;

    for (cases) |cid| {
        const c = ts.Field.get(cid);
        if (c.name.eq(tag)) {
            payload_ty = c.ty;
            found = true;
            break;
        }
    }

    if (!found) {
        const tag_name = self.context.interner.get(tag);
        if (pk == .Variant) {
            try diags.addError(loc, .unknown_variant_tag, StringPayload{ .value = tag_name });
        } else try diags.addError(loc, .unknown_error_tag, StringPayload{ .value = tag_name });
        return ts.tTypeError();
    }

    const payload_kind = self.typeKind(payload_ty);
    switch (payload_kind) {
        .Void => {
            if (args.len != 0) {
                try diags.addError(loc, .argument_count_mismatch, .{ 0, @as(i64, @intCast(args.len)) });
                return ts.tTypeError();
            }
            return parent_ty;
        },
        .Tuple => {
            const tup = ts.get(.Tuple, payload_ty);
            const params = ts.type_pool.slice(tup.elems);

            if (args.len != params.len) {
                try diags.addError(loc, .argument_count_mismatch, .{ @as(i64, @intCast(params.len)), @as(i64, @intCast(args.len)) });
                return ts.tTypeError();
            }

            for (args, 0..) |arg, i| {
                var at = try self.checkExpr(ctx, ast_unit, arg);
                if (self.typeKind(at) == .TypeError) return ts.tTypeError();

                var at_kind = self.typeKind(at);
                const pt = params[i];

                if (self.assignable(at, pt) != .success) {
                    const is_num = check_types.isNumericKind(self, self.typeKind(pt));
                    if (!is_num or !(try self.updateCoercedLiteral(ast_unit, arg, pt, &at, &at_kind) and self.assignable(at, pt) == .success)) {
                        try diags.addError(loc, .argument_type_mismatch, .{ pt, at });
                        return ts.tTypeError();
                    }
                }
            }
            return parent_ty;
        },
        else => {
            try diags.addError(loc, .call_non_callable, .{payload_ty});
            return ts.tTypeError();
        },
    }
}

/// Validate the call expression `id` using a multi-stage pipeline.
fn checkCall(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const call_expr = getExpr(ast_unit, .Call, id);

    // Phase 1: Special Forms (Constructors, Builtins)
    if (try self.checkSpecialForms(ctx, ast_unit, id, call_expr)) |ty| return ty;

    // Phase 2: Resolve Callee Type & Handle Methods
    const func_ty = try self.resolveCalleeForCall(ctx, ast_unit, call_expr);
    if (self.typeKind(func_ty) == .TypeError) return ts.tTypeError();

    // If resolution identified a method binding, redirect immediately.
    if (ast_unit.type_info.getMethodBinding(call_expr.callee)) |binding| {
        const args = ast_unit.exprs.expr_pool.slice(call_expr.args);
        return try self.checkMethodCall(ctx, ast_unit, id, &call_expr, binding, args);
    }

    const func_kind = self.typeKind(func_ty);
    if (func_kind == .Any) return ts.tTypeError();

    // Phase 3: Tuple Constructors
    if (func_kind == .Tuple) return self.checkTupleCall(ctx, ast_unit, call_expr, func_ty);

    if (func_kind != .Function) {
        try self.context.diags.addError(exprLoc(ast_unit, call_expr), .call_non_callable, .{func_ty});
        return ts.tTypeError();
    }

    // Phase 4: Standard Function Checks (Purity, Arity, Arguments)
    const fnrow = ts.get(.Function, func_ty);
    try self.checkPurity(ctx, ast_unit, call_expr, fnrow);

    if (try self.checkCallArguments(ctx, ast_unit, call_expr, func_ty, fnrow)) |arg_ctx| {
        var mutable_arg_ctx = arg_ctx;
        defer mutable_arg_ctx.types.deinit(self.gpa);

        // Phase 5: Specialization & Finalization
        return self.finalizeCallSpecialization(ctx, ast_unit, id, call_expr, func_ty, fnrow, &mutable_arg_ctx);
    } else {
        return ts.tTypeError();
    }
}

/// Helper: Handles `(Type).Tag(...)` and `sizeof(...)`.
fn checkSpecialForms(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId, call_expr: ast.Rows.Call) !?types.TypeId {
    const ts = self.context.type_store;
    const callee_kind = ast_unit.kind(call_expr.callee);
    const args = ast_unit.exprs.expr_pool.slice(call_expr.args);

    // (Type).Tag(...)
    if (callee_kind == .FieldAccess) {
        const fr = getExpr(ast_unit, .FieldAccess, call_expr.callee);
        const parent_ty = try self.checkExpr(ctx, ast_unit, fr.parent);
        if (self.typeKind(parent_ty) == .TypeType) {
            const inner_ty = ts.get(.TypeType, parent_ty).of;
            const inner_pk = self.typeKind(inner_ty);
            if (inner_pk == .Variant or inner_pk == .Error) {
                const res = try self.checkTagConstructorCall(ctx, ast_unit, inner_ty, fr.field, args, exprLoc(ast_unit, call_expr));
                if (self.typeKind(res) != .TypeError) {
                    if (self.getPayloadTypeForCase(inner_ty, fr.field)) |pty| {
                        const pk = self.typeKind(pty);
                        const params: []const types.TypeId = switch (pk) {
                            .Void => &.{},
                            .Tuple => ts.type_pool.slice(ts.get(.Tuple, pty).elems),
                            else => &.{pty},
                        };
                        const fn_ty = ts.mkFunction(params, inner_ty, false, false, false);
                        ast_unit.type_info.expr_types.items[call_expr.callee.toRaw()] = fn_ty;
                    }
                }
                return res;
            }
        }
    }

    // sizeof(T)
    if (callee_kind == .Ident) {
        const idr = getExpr(ast_unit, .Ident, call_expr.callee);
        if (std.mem.eql(u8, getStr(ast_unit, idr.name), "sizeof")) {
            if (args.len != 1) {
                try self.context.diags.addError(exprLoc(ast_unit, call_expr), .argument_count_mismatch, .{ 1, @as(i64, @intCast(args.len)) });
                return ts.tTypeError();
            }
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, args[0]);
            ast_unit.type_info.expr_types.items[args[0].toRaw()] = ts.mkTypeType(res[1]);

            if (!res[0]) return ts.tTypeError();

            try ast_unit.type_info.ensureExpr(self.gpa, id);
            ast_unit.type_info.expr_types.items[id.toRaw()] = ts.tU64();

            const any_type_ty = ts.mkTypeType(ts.tAny());
            const fn_ty = ts.mkFunction(&.{any_type_ty}, ts.tU64(), false, true, false);
            try ast_unit.type_info.ensureExpr(self.gpa, call_expr.callee);
            ast_unit.type_info.expr_types.items[call_expr.callee.toRaw()] = fn_ty;

            return ts.tU64();
        }
        if (std.mem.eql(u8, getStr(ast_unit, idr.name), "codeinfo")) {
            if (args.len != 1) {
                try self.context.diags.addError(exprLoc(ast_unit, call_expr), .argument_count_mismatch, .{ 1, @as(i64, @intCast(args.len)) });
                return ts.tTypeError();
            }
            try self.pushValueReq(ctx, true);
            const arg_ty = try self.checkExpr(ctx, ast_unit, args[0]);
            self.popValueReq(ctx);
            if (self.typeKind(arg_ty) == .TypeError) return ts.tTypeError();

            try ast_unit.type_info.ensureExpr(self.gpa, id);
            const info_ty = self.codeInfoResultType();
            ast_unit.type_info.expr_types.items[id.toRaw()] = info_ty;

            const code_ty = ts.tCode();
            const fn_ty = ts.mkFunction(&.{code_ty}, info_ty, false, true, false);
            try ast_unit.type_info.ensureExpr(self.gpa, call_expr.callee);
            ast_unit.type_info.expr_types.items[call_expr.callee.toRaw()] = fn_ty;

            _ = self.evalComptimeExprBorrowed(ctx, ast_unit, id, &.{}) catch {};
            return info_ty;
        }
        if (std.mem.eql(u8, getStr(ast_unit, idr.name), "codeFromInfo")) {
            if (args.len != 1) {
                try self.context.diags.addError(exprLoc(ast_unit, call_expr), .argument_count_mismatch, .{ 1, @as(i64, @intCast(args.len)) });
                return ts.tTypeError();
            }
            try self.pushValueReq(ctx, true);
            const arg_ty = try self.checkExpr(ctx, ast_unit, args[0]);
            self.popValueReq(ctx);
            if (self.typeKind(arg_ty) == .TypeError) return ts.tTypeError();

            // Should verify arg_ty is CodeInfo?
            // CodeInfo is the variant type generated by codeInfoResultType().
            // Ideally we check compatibility. For now, assume correct usage.

            try ast_unit.type_info.ensureExpr(self.gpa, id);
            const code_ty = ts.tCode();
            ast_unit.type_info.expr_types.items[id.toRaw()] = code_ty;

            const info_ty = self.codeInfoResultType();
            const fn_ty = ts.mkFunction(&.{info_ty}, code_ty, false, true, false);
            try ast_unit.type_info.ensureExpr(self.gpa, call_expr.callee);
            ast_unit.type_info.expr_types.items[call_expr.callee.toRaw()] = fn_ty;

            _ = self.evalComptimeExprBorrowed(ctx, ast_unit, id, &.{}) catch {};
            return code_ty;
        }
        if (std.mem.eql(u8, getStr(ast_unit, idr.name), "typeinfo")) {
            if (args.len != 1) {
                try self.context.diags.addError(exprLoc(ast_unit, call_expr), .argument_count_mismatch, .{ 1, @as(i64, @intCast(args.len)) });
                return ts.tTypeError();
            }
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, args[0]);
            ast_unit.type_info.expr_types.items[args[0].toRaw()] = ts.mkTypeType(res[1]);
            if (!res[0]) return ts.tTypeError();
            try ast_unit.type_info.ensureExpr(self.gpa, id);
            const info_ty = self.typeInfoResultType();
            ast_unit.type_info.expr_types.items[id.toRaw()] = info_ty;

            const any_type_ty = ts.mkTypeType(ts.tAny());
            const fn_ty = ts.mkFunction(&.{any_type_ty}, info_ty, false, true, false);
            try ast_unit.type_info.ensureExpr(self.gpa, call_expr.callee);
            ast_unit.type_info.expr_types.items[call_expr.callee.toRaw()] = fn_ty;

            _ = self.evalComptimeExprBorrowed(ctx, ast_unit, id, &.{}) catch {};
            return info_ty;
        }
    }
    return null;
}

fn typeInfoResultType(self: *Checker) types.TypeId {
    if (self.cached_typeinfo_ty) |ty| return ty;
    const ts = self.context.type_store;
    const keys = ts.typeInfoKeys();

    const field_info_ty = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.name, .ty = ts.tString() },
        .{ .name = keys.ty, .ty = ts.tU32() },
    }, 0);
    const enum_member_ty = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.name, .ty = ts.tString() },
        .{ .name = keys.value, .ty = ts.tI64() },
    }, 0);
    const u32_slice = ts.mkSlice(ts.tU32(), false);
    const usize_slice = ts.mkSlice(ts.tUsize(), false);
    const field_slice = ts.mkSlice(field_info_ty, false);
    const enum_member_slice = ts.mkSlice(enum_member_ty, false);

    const ptr_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.elem, .ty = ts.tU32() },
        .{ .name = keys.is_const, .ty = ts.tBool() },
    }, 0);
    const array_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.elem, .ty = ts.tU32() },
        .{ .name = keys.len, .ty = ts.tUsize() },
    }, 0);
    const elem_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.elem, .ty = ts.tU32() },
    }, 0);
    const map_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.key, .ty = ts.tU32() },
        .{ .name = keys.value, .ty = ts.tU32() },
    }, 0);
    const tuple_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.elems, .ty = u32_slice },
    }, 0);
    const fn_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.params, .ty = u32_slice },
        .{ .name = keys.result, .ty = ts.tU32() },
        .{ .name = keys.is_variadic, .ty = ts.tBool() },
        .{ .name = keys.is_pure, .ty = ts.tBool() },
        .{ .name = keys.is_extern, .ty = ts.tBool() },
    }, 0);
    const struct_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.fields, .ty = field_slice },
        .{ .name = keys.provenance, .ty = ts.tU64() },
    }, 0);
    const fields_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.fields, .ty = field_slice },
    }, 0);
    const cases_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.cases, .ty = field_slice },
    }, 0);
    const enum_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.members, .ty = enum_member_slice },
        .{ .name = keys.tag, .ty = ts.tU32() },
    }, 0);
    const errorset_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.value, .ty = ts.tU32() },
        .{ .name = keys.err, .ty = ts.tU32() },
    }, 0);
    const type_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.of, .ty = ts.tU32() },
    }, 0);
    const tensor_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.elem, .ty = ts.tU32() },
        .{ .name = keys.rank, .ty = ts.tU8() },
        .{ .name = keys.dims, .ty = usize_slice },
    }, 0);
    const simd_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.elem, .ty = ts.tU32() },
        .{ .name = keys.lanes, .ty = ts.tU16() },
    }, 0);
    const mlir_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.src, .ty = ts.tString() },
    }, 0);
    const ast_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = keys.pkg, .ty = ts.tString() },
        .{ .name = keys.filepath, .ty = ts.tString() },
    }, 0);

    const void_payload = ts.tVoid();
    const case_count: usize = 42;
    const cases = ts.arena.allocator().alloc(types.TypeStore.StructFieldArg, case_count) catch @panic("OOM");
    var idx: usize = 0;
    const addCase = struct {
        fn add(cases_buf: []types.TypeStore.StructFieldArg, i: *usize, name: []const u8, ty: types.TypeId, strs: *types.StringInterner) void {
            cases_buf[i.*] = .{ .name = strs.intern(name), .ty = ty };
            i.* += 1;
        }
    }.add;

    addCase(cases, &idx, "Void", void_payload, ts.strs);
    addCase(cases, &idx, "Bool", void_payload, ts.strs);
    addCase(cases, &idx, "I8", void_payload, ts.strs);
    addCase(cases, &idx, "I16", void_payload, ts.strs);
    addCase(cases, &idx, "I32", void_payload, ts.strs);
    addCase(cases, &idx, "I64", void_payload, ts.strs);
    addCase(cases, &idx, "U8", void_payload, ts.strs);
    addCase(cases, &idx, "U16", void_payload, ts.strs);
    addCase(cases, &idx, "U32", void_payload, ts.strs);
    addCase(cases, &idx, "U64", void_payload, ts.strs);
    addCase(cases, &idx, "F32", void_payload, ts.strs);
    addCase(cases, &idx, "F64", void_payload, ts.strs);
    addCase(cases, &idx, "Usize", void_payload, ts.strs);
    addCase(cases, &idx, "Complex", elem_payload, ts.strs);
    addCase(cases, &idx, "Tensor", tensor_payload, ts.strs);
    addCase(cases, &idx, "Simd", simd_payload, ts.strs);
    addCase(cases, &idx, "String", void_payload, ts.strs);
    addCase(cases, &idx, "Any", void_payload, ts.strs);
    addCase(cases, &idx, "Code", void_payload, ts.strs);
    addCase(cases, &idx, "Undef", void_payload, ts.strs);
    addCase(cases, &idx, "Ptr", ptr_payload, ts.strs);
    addCase(cases, &idx, "Slice", ptr_payload, ts.strs);
    addCase(cases, &idx, "Array", array_payload, ts.strs);
    addCase(cases, &idx, "DynArray", elem_payload, ts.strs);
    addCase(cases, &idx, "Map", map_payload, ts.strs);
    addCase(cases, &idx, "Optional", elem_payload, ts.strs);
    addCase(cases, &idx, "Tuple", tuple_payload, ts.strs);
    addCase(cases, &idx, "Function", fn_payload, ts.strs);
    addCase(cases, &idx, "Struct", struct_payload, ts.strs);
    addCase(cases, &idx, "Union", fields_payload, ts.strs);
    addCase(cases, &idx, "Enum", enum_payload, ts.strs);
    addCase(cases, &idx, "Variant", cases_payload, ts.strs);
    addCase(cases, &idx, "Error", cases_payload, ts.strs);
    addCase(cases, &idx, "ErrorSet", errorset_payload, ts.strs);
    addCase(cases, &idx, "MlirModule", void_payload, ts.strs);
    addCase(cases, &idx, "MlirAttribute", mlir_payload, ts.strs);
    addCase(cases, &idx, "MlirType", mlir_payload, ts.strs);
    addCase(cases, &idx, "TypeType", type_payload, ts.strs);
    addCase(cases, &idx, "Future", elem_payload, ts.strs);
    addCase(cases, &idx, "Noreturn", void_payload, ts.strs);
    addCase(cases, &idx, "Ast", ast_payload, ts.strs);
    addCase(cases, &idx, "TypeError", void_payload, ts.strs);
    std.debug.assert(idx == case_count);

    const info_ty = ts.mkVariant(cases);
    self.cached_typeinfo_ty = info_ty;
    return info_ty;
}

fn codeInfoResultType(self: *Checker) types.TypeId {
    if (self.cached_codeinfo_ty) |ty| return ty;
    const ts = self.context.type_store;
    const strs = ts.strs;

    const void_payload = ts.tVoid();
    const any_ty = ts.tAny();
    // Recursive fields use Any for now
    const code_info_ref = any_ty;
    const code_info_slice = ts.mkSlice(code_info_ref, false);
    const opt_code_info = ts.mkOptional(code_info_ref);

    const bool_ty = ts.tBool();
    const string_ty = ts.tString();

    const literal_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("value"), .ty = any_ty },
    }, 0);

    const ident_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("name"), .ty = string_ty },
    }, 0);

    const block_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("stmts"), .ty = code_info_slice },
    }, 0);

    const decl_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("name"), .ty = string_ty },
        .{ .name = strs.intern("value"), .ty = opt_code_info },
        .{ .name = strs.intern("ty"), .ty = opt_code_info },
        .{ .name = strs.intern("is_const"), .ty = bool_ty },
    }, 0);

    const binary_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("op"), .ty = string_ty },
        .{ .name = strs.intern("left"), .ty = code_info_ref },
        .{ .name = strs.intern("right"), .ty = code_info_ref },
    }, 0);

    const unary_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("op"), .ty = string_ty },
        .{ .name = strs.intern("expr"), .ty = code_info_ref },
    }, 0);

    const if_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("cond"), .ty = code_info_ref },
        .{ .name = strs.intern("then_block"), .ty = code_info_ref },
        .{ .name = strs.intern("else_block"), .ty = opt_code_info },
    }, 0);

    const return_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("value"), .ty = opt_code_info },
    }, 0);

    const call_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("callee"), .ty = code_info_ref },
        .{ .name = strs.intern("args"), .ty = code_info_slice },
    }, 0);

    const splice_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("name"), .ty = string_ty },
    }, 0);

    const insert_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("expr"), .ty = code_info_ref },
    }, 0);

    const field_access_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("parent"), .ty = code_info_ref },
        .{ .name = strs.intern("field"), .ty = string_ty },
    }, 0);

    const index_access_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("collection"), .ty = code_info_ref },
        .{ .name = strs.intern("index"), .ty = code_info_ref },
    }, 0);

    const array_lit_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("elems"), .ty = code_info_slice },
    }, 0);

    const struct_field_val_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("name"), .ty = string_ty },
        .{ .name = strs.intern("value"), .ty = code_info_ref },
    }, 0);

    const struct_field_val_union = ts.mkVariant(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("Field"), .ty = struct_field_val_payload },
        .{ .name = strs.intern("Spread"), .ty = code_info_ref }, // For spreads
    });

    const struct_lit_payload = ts.mkStruct(&[_]types.TypeStore.StructFieldArg{
        .{ .name = strs.intern("fields"), .ty = ts.mkSlice(struct_field_val_union, false) },
        .{ .name = strs.intern("ty"), .ty = opt_code_info },
    }, 0);

    var cases = std.ArrayList(types.TypeStore.StructFieldArg){ .items = &.{}, .capacity = 0 };

    defer cases.deinit(self.gpa);

    const addCase = struct {
        fn add(list: *std.ArrayList(types.TypeStore.StructFieldArg), s: *types.StringInterner, name: []const u8, ty: types.TypeId, gpa: std.mem.Allocator) void {
            list.append(gpa, .{ .name = s.intern(name), .ty = ty }) catch @panic("OOM");
        }
    }.add;

    addCase(&cases, strs, "None", void_payload, self.gpa);

    addCase(&cases, strs, "Literal", literal_payload, self.gpa);

    addCase(&cases, strs, "Ident", ident_payload, self.gpa);

    addCase(&cases, strs, "Block", block_payload, self.gpa);

    addCase(&cases, strs, "Decl", decl_payload, self.gpa);

    addCase(&cases, strs, "Binary", binary_payload, self.gpa);

    addCase(&cases, strs, "Unary", unary_payload, self.gpa);

    addCase(&cases, strs, "If", if_payload, self.gpa);

    addCase(&cases, strs, "Return", return_payload, self.gpa);

    addCase(&cases, strs, "Call", call_payload, self.gpa);
    addCase(&cases, strs, "Splice", splice_payload, self.gpa);
    addCase(&cases, strs, "Insert", insert_payload, self.gpa);
    addCase(&cases, strs, "FieldAccess", field_access_payload, self.gpa);
    addCase(&cases, strs, "IndexAccess", index_access_payload, self.gpa);
    addCase(&cases, strs, "ArrayLit", array_lit_payload, self.gpa);
    addCase(&cases, strs, "StructLit", struct_lit_payload, self.gpa);

    const info_ty = ts.mkVariant(cases.items);
    self.cached_codeinfo_ty = info_ty;
    return info_ty;
}

/// Helper: Resolves callee type and attempts method lookup for FieldAccess.
fn resolveCalleeForCall(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, call_expr: ast.Rows.Call) !types.TypeId {
    const ts = self.context.type_store;
    const func_ty = try self.checkExpr(ctx, ast_unit, call_expr.callee);

    if (self.typeKind(func_ty) == .TypeError) {
        if (ast_unit.kind(call_expr.callee) == .Ident) {
            const idr = getExpr(ast_unit, .Ident, call_expr.callee);
            if (self.lookup(ctx, idr.name) == null) {
                self.context.diags.messages.items[self.context.diags.messages.items.len - 1].code = .unknown_function;
            }
        }
        return ts.tTypeError();
    }

    if (ast_unit.kind(call_expr.callee) == .FieldAccess) {
        // If already bound (e.g. from previous pass), return.
        if (ast_unit.type_info.getMethodBinding(call_expr.callee) != null) return func_ty;

        const field_expr = getExpr(ast_unit, .FieldAccess, call_expr.callee);
        const parent_ty = try self.checkExpr(ctx, ast_unit, field_expr.parent);
        if (self.typeKind(parent_ty) == .TypeError) return ts.tTypeError();

        const parent_kind = self.typeKind(parent_ty);
        const owner_ty = if (parent_kind == .Ptr) ts.get(.Ptr, parent_ty).elem else if (parent_kind == .TypeType) ts.get(.TypeType, parent_ty).of else parent_ty;
        const receiver_ty = if (parent_kind == .TypeType) owner_ty else parent_ty;

        const method_ty = self.resolveMethodFieldAccess(ast_unit, call_expr.callee, owner_ty, receiver_ty, field_expr.field, exprLoc(ast_unit, field_expr)) catch |err| switch (err) {
            else => return ts.tTypeError(),
        };

        if (self.typeKind(method_ty) != .TypeError) {
            try ast_unit.type_info.clearFieldIndex(call_expr.callee);
            return method_ty;
        }
    }
    return func_ty;
}

/// Helper: Handles `Tuple(...)` constructor calls.
fn checkTupleCall(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, call_expr: ast.Rows.Call, tuple_ty: types.TypeId) !types.TypeId {
    const ts = self.context.type_store;
    const tup = ts.get(.Tuple, tuple_ty);
    const params = ts.type_pool.slice(tup.elems);
    const args = ast_unit.exprs.expr_pool.slice(call_expr.args);

    if (args.len != params.len) {
        try self.context.diags.addError(exprLoc(ast_unit, call_expr), .argument_count_mismatch, .{ @as(i64, @intCast(params.len)), @as(i64, @intCast(args.len)) });
        return ts.tTypeError();
    }

    for (args, 0..) |arg, i| {
        try self.pushValueReq(ctx, true);
        var at = try self.checkExpr(ctx, ast_unit, arg);
        self.popValueReq(ctx);
        if (self.typeKind(at) == .TypeError) return ts.tTypeError();

        var at_kind = self.typeKind(at);
        if (self.assignable(at, params[i]) != .success) {
            const is_num = check_types.isNumericKind(self, self.typeKind(params[i]));
            if (!is_num or !(try self.updateCoercedLiteral(ast_unit, arg, params[i], &at, &at_kind) and self.assignable(at, params[i]) == .success)) {
                try self.context.diags.addError(exprLocFromId(ast_unit, arg), .argument_type_mismatch, .{ params[i], at });
                return ts.tTypeError();
            }
        }
    }
    return tuple_ty;
}

/// Helper: Checks function purity.
fn checkPurity(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, call_expr: ast.Rows.Call, fnrow: types.Rows.Function) !void {
    if (self.inFunction(ctx)) {
        const fctx = self.currentFunc(ctx).?;
        if (fctx.require_pure and !fnrow.is_pure) {
            try self.context.diags.addError(exprLoc(ast_unit, call_expr), .purity_violation, StringPayload{ .value = "call to impure function" });
        }
        if (!fnrow.is_pure) ctx.func_stack.items[ctx.func_stack.items.len - 1].pure = false;
    }
}

const CallArgContext = struct {
    types: List(types.TypeId),
    saw_spread: bool,
    pack_args: bool,
    pack_start: usize,
};

/// Helper: Validates arity and argument types. Returns context needed for specialization.
fn checkCallArguments(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, call_expr: ast.Rows.Call, func_ty: types.TypeId, fnrow: types.Rows.Function) !?CallArgContext {
    const ts = self.context.type_store;
    const diags = self.context.diags;
    const params = ts.type_pool.slice(fnrow.params);
    const args = ast_unit.exprs.expr_pool.slice(call_expr.args);
    const is_internal_variadic = check_types.isInternalVariadic(ts, func_ty);
    const is_any_variadic = is_internal_variadic;

    var min_required = if (params.len == 0) 0 else params.len;

    // Arity Check
    if (!fnrow.is_variadic) {
        if (self.resolveCalleeDecl(ctx, ast_unit, call_expr.callee)) |did| {
            if (self.countTrailingDefaultParams(ast_unit, did)) |defaults| {
                if (defaults <= params.len) min_required -= defaults;
            }
        }
        if (is_any_variadic) {
            min_required = params.len - 1;
            if (args.len < min_required) {
                try diags.addError(exprLoc(ast_unit, call_expr), .argument_count_mismatch, .{ @as(i64, @intCast(min_required)), @as(i64, @intCast(args.len)) });
                return null;
            }
        } else if (args.len < min_required or args.len > params.len) {
            const expected = if (args.len < min_required) min_required else params.len;
            try diags.addError(exprLoc(ast_unit, call_expr), .argument_count_mismatch, .{ @as(i64, @intCast(expected)), @as(i64, @intCast(args.len)) });
            return null;
        }
    } else {
        min_required = if (params.len > 0) params.len - 1 else 0;
        if (args.len < min_required) {
            try diags.addError(exprLoc(ast_unit, call_expr), .argument_count_mismatch, .{ @as(i64, @intCast(min_required)), @as(i64, @intCast(args.len)) });
            return null;
        }
    }

    // Argument Verification
    var arg_types = try List(types.TypeId).initCapacity(self.gpa, args.len);
    var saw_spread = false;
    var pack_args = false;
    var pack_start: usize = 0;

    if (is_any_variadic) {
        pack_start = params.len - 1;
        if (args.len > params.len) pack_args = true;
    }

    for (args, 0..) |arg, i| {
        const pt = if (is_any_variadic and i >= params.len - 1)
            params[params.len - 1]
        else if (!fnrow.is_variadic)
            (if (i < params.len) params[i] else params[params.len - 1])
        else blk: {
            const fixed = if (params.len == 0) 0 else params.len - 1;
            break :blk if (i < fixed) params[i] else params[params.len - 1];
        };

        try self.pushValueReq(ctx, true);
        try self.pushExpectedType(ctx, pt);
        var at = try self.checkExpr(ctx, ast_unit, arg);
        self.popExpectedType(ctx);
        self.popValueReq(ctx);

        if (self.typeKind(at) == .TypeError) {
            arg_types.deinit(self.gpa);
            return null;
        }
        if (self.isSpreadRangeExprChecker(ast_unit, arg)) saw_spread = true;

        var at_kind = self.typeKind(at);
        if (self.tryCoerceNullLiteral(ast_unit, arg, pt)) {
            ast_unit.type_info.expr_types.items[arg.toRaw()] = pt;
            at = pt;
            at_kind = self.typeKind(at);
        }

        if (is_any_variadic and i >= params.len - 1) {
            arg_types.appendAssumeCapacity(at);
            continue;
        }

        if (self.typeKind(pt) == .TypeType and at_kind != .TypeType) {
            const type_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, arg);
            if (type_res[0]) {
                at = ts.mkTypeType(type_res[1]);
                at_kind = .TypeType;
                try ast_unit.type_info.ensureExpr(self.gpa, arg);
                ast_unit.type_info.expr_types.items[arg.toRaw()] = at;
            }
        }

        if (self.assignable(at, pt) != .success) {
            const is_num = check_types.isNumericKind(self, self.typeKind(pt));
            if (!is_num or !(try self.updateCoercedLiteral(ast_unit, arg, pt, &at, &at_kind) and self.assignable(at, pt) == .success)) {
                const idx = diags.count();
                try diags.addError(exprLocFromId(ast_unit, arg), .argument_type_mismatch, .{ pt, at });
                try self.attachTryCastNote(idx, pt);
                arg_types.deinit(self.gpa);
                return null;
            }
        }
        arg_types.appendAssumeCapacity(at);
    }

    return CallArgContext{ .types = arg_types, .saw_spread = saw_spread, .pack_args = pack_args, .pack_start = pack_start };
}

/// Helper: Handles logic for Runtime and Comptime Specialization.
fn finalizeCallSpecialization(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId, call_expr: ast.Rows.Call, func_ty: types.TypeId, fnrow: types.Rows.Function, arg_ctx: *const CallArgContext) !types.TypeId {
    const ts = self.context.type_store;
    const args = ast_unit.exprs.expr_pool.slice(call_expr.args);

    if (calleeNameForCall(ast_unit, call_expr.callee)) |name| {
        try self.maybeRecordRuntimeSpecialization(ctx, ast_unit, id, call_expr.callee, name, args, func_ty);
    }

    // Determine if comptime specialization is needed
    const params = ts.type_pool.slice(fnrow.params);
    const result_is_type = self.typeKind(fnrow.result) == .TypeType;
    var has_comptime_param = false;
    var resolved_ctx_opt: ?call_resolution.FunctionDeclContext = null;

    // Check for comptime params in declaration
    if (calleeNameForCall(ast_unit, call_expr.callee)) |name| {
        if (call_resolution.findFunctionDeclForCall(self.context, ast_unit, call_expr.callee, name)) |d| {
            resolved_ctx_opt = d;
            const decl = d.ast.exprs.Decl.get(d.decl_id);
            if (d.ast.kind(decl.value) == .FunctionLit) {
                const lit = d.ast.exprs.get(.FunctionLit, decl.value);
                const ps = d.ast.exprs.param_pool.slice(lit.params);
                for (ps) |pid| {
                    if (d.ast.exprs.Param.get(pid).is_comptime) {
                        has_comptime_param = true;
                        break;
                    }
                }
            }
        }
    }

    const has_any_param = blk: {
        for (params) |p| {
            if (self.typeKind(p) == .Any) break :blk true;
            if (self.typeKind(p) == .TypeType and self.typeKind(ts.get(.TypeType, p).of) == .Any) break :blk true;
        }
        break :blk false;
    };

    if (fnrow.is_extern) {
        if (arg_ctx.saw_spread) {
            try ast_unit.type_info.setCallSpecialization(self.gpa, id, .{
                .target_decl = 0,
                .target_file_id = std.math.maxInt(u32),
                .pack_args = false,
                .pack_start_index = 0,
                .is_spread = true,
            });
        }
        return fnrow.result;
    }

    if ((!has_any_param and !check_types.isInternalVariadic(ts, func_ty) and !has_comptime_param) or result_is_type) {
        return fnrow.result;
    }

    // Prepare Specialization Data
    var concrete_param_types = try List(types.TypeId).initCapacity(self.gpa, arg_ctx.types.items.len + 1);
    defer concrete_param_types.deinit(self.gpa);

    if (check_types.isInternalVariadic(ts, func_ty)) {
        const fixed = if (params.len == 0) 0 else params.len - 1;
        const limit = if (fixed < arg_ctx.types.items.len) fixed else arg_ctx.types.items.len;
        concrete_param_types.appendSliceAssumeCapacity(arg_ctx.types.items[0..limit]);
        const tuple_ty = try self.computeTrailingAnyTupleTypeChecker(ast_unit, args, fixed);
        concrete_param_types.appendAssumeCapacity(tuple_ty);
    } else {
        for (params, 0..) |p, idx| {
            concrete_param_types.appendAssumeCapacity(if (idx < arg_ctx.types.items.len) arg_ctx.types.items[idx] else p);
        }
    }

    if (resolved_ctx_opt == null) {
        if (calleeNameForCall(ast_unit, call_expr.callee)) |name| {
            resolved_ctx_opt = call_resolution.findFunctionDeclForCall(self.context, ast_unit, call_expr.callee, name);
        }
    }

    if (resolved_ctx_opt) |decl_ctx| {
        const resolved_ctx = resolveFunctionDeclAlias(self, decl_ctx) orelse decl_ctx;
        const target_ctx_opt = if (resolved_ctx.ast.file_id < self.checker_ctx.items.len) self.checker_ctx.items[resolved_ctx.ast.file_id] else null;

        if (target_ctx_opt) |target_ctx| {
            const fn_decl = resolved_ctx.ast.exprs.Decl.get(resolved_ctx.decl_id);
            if (resolved_ctx.ast.kind(fn_decl.value) == .FunctionLit) {
                const fn_lit = resolved_ctx.ast.exprs.get(.FunctionLit, fn_decl.value);
                const fn_params = resolved_ctx.ast.exprs.param_pool.slice(fn_lit.params);

                var comptime_hashes = try List(u64).initCapacity(self.gpa, fn_params.len);
                defer comptime_hashes.deinit(self.gpa);
                var comptime_bindings = List(ComptimeParamBinding){};
                defer comptime_bindings.deinit(self.gpa);

                for (fn_params, 0..) |pid, param_idx| {
                    const p = resolved_ctx.ast.exprs.Param.get(pid);
                    if (!p.is_comptime) {
                        comptime_hashes.appendAssumeCapacity(0);
                        continue;
                    }

                    const arg_expr = if (param_idx < args.len) args[param_idx] else ast.ExprId.fromRaw(std.math.maxInt(u32));
                    if (arg_expr.toRaw() == std.math.maxInt(u32)) {
                        comptime_hashes.appendAssumeCapacity(0);
                        continue;
                    }

                    const cval = self.evalComptimeExpr(ctx, ast_unit, arg_expr, &[_]Pipeline.ComptimeBinding{}) catch {
                        try self.context.diags.addError(exprLoc(ast_unit, call_expr), .checker_comptime_not_executed, .{});
                        return ts.tTypeError();
                    };
                    comptime_hashes.appendAssumeCapacity(ast_unit.type_info.val_store.hashValue(cval));

                    if (!p.pat.isNone()) {
                        if (bindingNameOfPattern(resolved_ctx.ast, p.pat.unwrap())) |pname| {
                            const cloned = try resolved_ctx.ast.type_info.val_store.cloneValue(&ast_unit.type_info.val_store, cval);
                            try comptime_bindings.append(self.gpa, .{ .name = pname, .ty = concrete_param_types.items[param_idx], .value = cloned });
                        }
                    }
                }

                if (comptime_hashes.items.len < concrete_param_types.items.len) {
                    try comptime_hashes.appendNTimes(self.gpa, 0, concrete_param_types.items.len - comptime_hashes.items.len);
                } else {
                    comptime_hashes.items.len = concrete_param_types.items.len;
                }

                const spec_decl_id = try self.getOrInstantiateSpecialization(target_ctx, resolved_ctx.ast, resolved_ctx.decl_id, concrete_param_types.items, comptime_bindings.items, comptime_hashes.items);
                const spec_sig = resolved_ctx.ast.type_info.decl_types.items[spec_decl_id.toRaw()] orelse func_ty;

                try ast_unit.type_info.setCallSpecialization(self.gpa, id, .{
                    .target_decl = spec_decl_id.toRaw(),
                    .target_file_id = @intCast(resolved_ctx.ast.file_id),
                    .pack_args = arg_ctx.pack_args,
                    .pack_start_index = arg_ctx.pack_start,
                    .is_spread = arg_ctx.saw_spread and fnrow.is_variadic,
                });
                return ts.get(.Function, spec_sig).result;
            }
        }
    }
    return fnrow.result;
}
/// Helper to resolve the defining declaration of a callee for default parameter counting.
fn resolveCalleeDecl(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, callee: ast.ExprId) ?ast.DeclId {
    switch (ast_unit.kind(callee)) {
        .Ident => {
            const idr = getExpr(ast_unit, .Ident, callee);
            const sid = self.lookup(ctx, idr.name) orelse return null;
            const sym = ctx.symtab.syms.get(sid);
            if (!sym.origin_decl.isNone()) return sym.origin_decl.unwrap();
        },
        .FieldAccess => {
            const fr = getExpr(ast_unit, .FieldAccess, callee);
            const pk = ast_unit.kind(fr.parent);
            var path_sid: ?ast.StrId = null;

            if (pk == .Import) {
                path_sid = getExpr(ast_unit, .Import, fr.parent).path;
            } else if (pk == .Ident) {
                // Indirect import via ident? Hard to resolve without context.
                return null;
            }

            if (path_sid) |path| {
                const pstr = getStr(ast_unit, path);
                var pkg_iter = self.context.compilation_unit.packages.iterator();
                while (pkg_iter.next()) |pkg| {
                    if (pkg.value_ptr.sources.get(pstr)) |unit| {
                        if (unit.ast) |a| {
                            if (a.type_info.getExport(fr.field)) |ex| return ex.decl_id;
                        }
                        break;
                    }
                }
            }
        },
        else => {},
    }
    return null;
}

/// Count how many trailing parameters of `did` have default values (runtime ones only).
fn countTrailingDefaultParams(_: *Checker, ast_unit: *ast.Ast, did: ast.DeclId) ?usize {
    const decl = ast_unit.exprs.Decl.get(did);
    if (ast_unit.kind(decl.value) != .FunctionLit) return null;
    const fnr = ast_unit.exprs.get(.FunctionLit, decl.value);
    const params = ast_unit.exprs.param_pool.slice(fnr.params);
    if (params.len == 0) return 0;

    var count: usize = 0;
    var i: usize = params.len;
    while (i > 0) {
        i -= 1;
        const p = ast_unit.exprs.Param.get(params[i]);
        if (p.is_comptime or p.value.isNone()) break;
        count += 1;
    }
    return count;
}

/// Validate a method call using the resolved `binding` info.
fn checkMethodCall(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, call_id: ast.ExprId, call_ptr: *const ast.Rows.Call, binding: types.MethodBinding, args: []const ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const diags = self.context.diags;
    const field_expr = getExpr(ast_unit, .FieldAccess, call_ptr.callee);
    const receiver_ty = try self.checkExpr(ctx, ast_unit, field_expr.parent);
    if (self.typeKind(receiver_ty) == .TypeError) return ts.tTypeError();

    // Receiver Addressability Check
    if ((binding.receiver_kind == .pointer or binding.receiver_kind == .pointer_const) and !binding.needs_addr_of) {
        if (self.lvalueRootKind(ctx, ast_unit, field_expr.parent) == .Unknown and self.typeKind(receiver_ty) != .Ptr) {
            try diags.addError(exprLocFromId(ast_unit, field_expr.parent), .method_receiver_not_addressable, StringPayload{ .value = getStr(ast_unit, binding.method_name) });
            return ts.tTypeError();
        }
    }

    const fn_row = ts.get(.Function, binding.func_type);
    const params = ts.type_pool.slice(fn_row.params);
    const implicit_count: usize = if (binding.requires_implicit_receiver) 1 else 0;
    const total_args = args.len + implicit_count;
    var min_required = if (params.len == 0) 0 else params.len;

    if (!fn_row.is_variadic) {
        // Method Default Params
        if (self.countTrailingDefaultParams(binding.decl_ast, binding.decl_id)) |defaults| {
            if (defaults <= params.len) min_required -= defaults;
        }

        if (total_args < min_required or total_args > params.len) {
            const idx = diags.count();
            const expected = if (total_args < min_required) min_required else params.len;
            try diags.addError(exprLoc(ast_unit, call_ptr.*), .argument_count_mismatch, .{ @as(i64, @intCast(expected)), @as(i64, @intCast(total_args)) });
            try self.attachFunctionSignatureNote(idx, binding.func_type);
            return ts.tTypeError();
        }
    } else {
        min_required = if (params.len > 0) params.len - 1 else 0;
        if (total_args < min_required) {
            const idx = diags.count();
            try diags.addError(exprLoc(ast_unit, call_ptr.*), .argument_count_mismatch, .{ @as(i64, @intCast(min_required)), @as(i64, @intCast(total_args)) });
            try self.attachFunctionSignatureNote(idx, binding.func_type);
            return ts.tTypeError();
        }
    }

    // Implicit Receiver Check
    if (binding.requires_implicit_receiver) {
        if (params.len == 0) return ts.tTypeError();
        const self_ty = params[0];
        if (!binding.needs_addr_of) {
            if (self.assignable(receiver_ty, self_ty) != .success) {
                try diags.addError(exprLoc(ast_unit, field_expr), .argument_type_mismatch, .{ self_ty, receiver_ty });
                return ts.tTypeError();
            }
        } else if (!receiver_ty.eq(binding.owner_type)) {
            try diags.addError(exprLoc(ast_unit, field_expr), .method_receiver_requires_pointer, .{getStr(ast_unit, binding.method_name)});
            return ts.tTypeError();
        }
    }

    // Arguments
    var method_args = try List(ast.ExprId).initCapacity(self.gpa, total_args);
    defer method_args.deinit(self.gpa);
    if (binding.requires_implicit_receiver) method_args.appendAssumeCapacity(field_expr.parent);
    method_args.appendSliceAssumeCapacity(args);

    for (args, 0..) |arg, i| {
        try self.pushValueReq(ctx, true);
        var at = try self.checkExpr(ctx, ast_unit, arg);
        self.popValueReq(ctx);
        if (self.typeKind(at) == .TypeError) return ts.tTypeError();

        const p_idx = i + implicit_count;
        const pt = if (!fn_row.is_variadic)
            (if (p_idx < params.len) params[p_idx] else params[params.len - 1])
        else blk: {
            const fixed = if (params.len == 0) 0 else params.len - 1;
            break :blk if (p_idx < fixed) params[p_idx] else params[params.len - 1];
        };

        var at_kind = self.typeKind(at);
        if (self.tryCoerceNullLiteral(ast_unit, arg, pt)) {
            ast_unit.type_info.expr_types.items[arg.toRaw()] = pt;
            at = pt;
            at_kind = self.typeKind(at);
        }

        if (self.typeKind(pt) == .TypeType and at_kind != .TypeType) {
            const type_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, arg);
            if (type_res[0]) {
                at = ts.mkTypeType(type_res[1]);
                try ast_unit.type_info.ensureExpr(self.gpa, arg);
                ast_unit.type_info.expr_types.items[arg.toRaw()] = at;
            }
        }

        if (self.assignable(at, pt) != .success) {
            const is_num = check_types.isNumericKind(self, self.typeKind(pt));
            if (!is_num or !(try self.updateCoercedLiteral(ast_unit, arg, pt, &at, &at_kind) and self.assignable(at, pt) == .success)) {
                const idx = diags.count();
                try diags.addError(exprLocFromId(ast_unit, arg), .argument_type_mismatch, .{ pt, at });
                try self.attachTryCastNote(idx, pt);
                return ts.tTypeError();
            }
        }
    }

    try self.maybeRecordRuntimeSpecialization(ctx, ast_unit, call_id, call_ptr.callee, binding.method_name, method_args.items, binding.func_type);
    return fn_row.result;
}

/// Extract the identifier name used by the callee expression if applicable.
fn calleeNameForCall(ast_unit: *ast.Ast, callee_expr: ast.ExprId) ?ast.StrId {
    return switch (ast_unit.kind(callee_expr)) {
        .Ident => ast_unit.exprs.get(.Ident, callee_expr).name,
        .FieldAccess => ast_unit.exprs.get(.FieldAccess, callee_expr).field,
        else => null,
    };
}
/// Map a triton pointer MLIR token like "!tt.ptr<i32>" to its element SR type.
fn tritonPointeeFromMlir(self: *Checker, tok: []const u8) ?types.TypeId {
    const prefix = "!tt.ptr<";
    if (!std.mem.startsWith(u8, tok, prefix) or !std.mem.endsWith(u8, tok, ">")) return null;

    const inner = tok[prefix.len .. tok.len - 1];
    if (inner.len < 2) return null;

    const ts = self.context.type_store;
    switch (inner[0]) {
        'i' => {
            if (std.mem.eql(u8, inner, "i32")) return ts.tI32();
            if (std.mem.eql(u8, inner, "i64")) return ts.tI64();
            if (std.mem.eql(u8, inner, "i8")) return ts.tI8();
            if (std.mem.eql(u8, inner, "i16")) return ts.tI16();
        },
        'f' => {
            if (std.mem.eql(u8, inner, "f32")) return ts.tF32();
            if (std.mem.eql(u8, inner, "f64")) return ts.tF64();
        },
        else => {},
    }
    return null;
}

/// Return the cached type for `expr_id`, defaulting to `any` if unknown.
fn exprTypeFromInfo(self: *Checker, ast_unit: *ast.Ast, expr_id: ast.ExprId) types.TypeId {
    const raw = expr_id.toRaw();
    const items = ast_unit.type_info.expr_types.items;
    if (raw < items.len) {
        if (items[raw]) |ty| return ty;
    }
    return self.context.type_store.tCode();
}

/// Recognize range expressions used as spreads in trailing `any` tuples.
fn isSpreadRangeExprChecker(self: *Checker, ast_unit: *ast.Ast, expr: ast.ExprId) bool {
    if (ast_unit.kind(expr) != .Range) return false;
    const row = ast_unit.exprs.get(.Range, expr);
    if (!row.start.isNone() or row.end.isNone()) return false;

    const end_ty = self.exprTypeFromInfo(ast_unit, row.end.unwrap());
    const end_kind = self.typeKind(end_ty);
    return end_kind == .Tuple or end_kind == .Any;
}

/// Compute the tuple type for trailing `any` arguments starting at `start_index`.
fn computeTrailingAnyTupleTypeChecker(
    self: *Checker,
    ast_unit: *ast.Ast,
    args: []const ast.ExprId,
    start_index: usize,
) anyerror!types.TypeId {
    if (start_index >= args.len) return self.context.type_store.mkTuple(&.{});

    const trailing_len = args.len - start_index;
    if (trailing_len == 1 and !self.isSpreadRangeExprChecker(ast_unit, args[start_index])) {
        return self.exprTypeFromInfo(ast_unit, args[start_index]);
    }

    var elem_types = try List(types.TypeId).initCapacity(self.gpa, trailing_len);
    defer elem_types.deinit(self.gpa);

    for (args[start_index..]) |arg| {
        elem_types.appendAssumeCapacity(self.exprTypeFromInfo(ast_unit, arg));
    }

    return self.context.type_store.mkTuple(elem_types.items);
}

/// Record runtime specializations when generic/defaulted parameters are passed concrete types.
fn maybeRecordRuntimeSpecialization(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    call_id: ast.ExprId,
    callee_expr: ast.ExprId,
    callee_name: ast.StrId,
    args: []const ast.ExprId,
    fn_ty: types.TypeId,
) !void {
    _ = ctx;
    if (ast_unit.type_info.getSpecializedCall(call_id)) |_| return;

    var decl_ctx = call_resolution.findFunctionDeclForCall(self.context, ast_unit, callee_expr, callee_name) orelse return;
    decl_ctx = resolveFunctionDeclAlias(self, decl_ctx) orelse decl_ctx;

    const d_ast = decl_ctx.ast;
    const decl = d_ast.exprs.Decl.get(decl_ctx.decl_id);
    if (d_ast.kind(decl.value) != .FunctionLit) return;

    const fn_lit = d_ast.exprs.get(.FunctionLit, decl.value);
    const params = d_ast.exprs.param_pool.slice(fn_lit.params);

    var skip_params: usize = 0;
    while (skip_params < params.len and d_ast.exprs.Param.get(params[skip_params]).is_comptime) : (skip_params += 1) {}

    const ts = self.context.type_store;
    const fnrow = ts.get(.Function, fn_ty);
    const param_tys = ts.type_pool.slice(fnrow.params);
    const treat_trailing_any = !fnrow.is_extern and param_tys.len > 0 and self.typeKind(param_tys[param_tys.len - 1]) == .Any;

    var runtime_specs: List(ParamSpecialization) = .empty;
    defer runtime_specs.deinit(self.gpa);

    // Main param loop
    const limit = if (params.len < args.len) params.len else args.len;
    var i = skip_params;
    while (i < limit) : (i += 1) {
        // Optimization: check types before expensive binding/pattern lookups
        const param_ty = if (i < param_tys.len) param_tys[i] else ts.tAny();
        if (self.typeKind(param_ty) != .Any) continue;

        const arg_ty = self.exprTypeFromInfo(ast_unit, args[i]);
        if (self.typeKind(arg_ty) == .Any) continue;

        const param = d_ast.exprs.Param.get(params[i]);
        if (param.pat.isNone()) continue;

        if (bindingNameOfPattern(d_ast, param.pat.unwrap())) |pname| {
            try runtime_specs.append(self.gpa, .{ .name = pname, .ty = arg_ty });
        }
    }

    // Trailing any tuple logic
    if (treat_trailing_any and params.len > 0) {
        const tuple_start = params.len - 1;
        // Only compute tuple if necessary
        const last_param = d_ast.exprs.Param.get(params[tuple_start]);
        if (!last_param.pat.isNone()) {
            if (bindingNameOfPattern(d_ast, last_param.pat.unwrap())) |pname| {
                const tuple_ty = try self.computeTrailingAnyTupleTypeChecker(ast_unit, args, tuple_start);
                // Check if tuple is actually empty/valid
                const tuple_empty = blk: {
                    if (self.typeKind(tuple_ty) != .Tuple) break :blk false;
                    break :blk ts.get(.Tuple, tuple_ty).elems.len == 0;
                };

                if (!tuple_empty) {
                    try runtime_specs.append(self.gpa, .{ .name = pname, .ty = tuple_ty });
                }
            }
        }
    }

    if (runtime_specs.items.len == 0) return;
    if (d_ast.file_id >= self.checker_ctx.items.len) return;

    const target_ctx = self.checker_ctx.items[d_ast.file_id] orelse return;
    _ = try self.checkSpecializedFunction(target_ctx, d_ast, decl_ctx.decl_id, runtime_specs.items, null, &.{});
    try ast_unit.type_info.markSpecializedCall(self.gpa, call_id, decl_ctx);
}

/// Extract identifier name for alias resolution when `expr` represents a dotted path.
fn aliasTargetName(ast_unit: *ast.Ast, expr: ast.ExprId) ?ast.StrId {
    return switch (ast_unit.kind(expr)) {
        .Ident => ast_unit.exprs.get(.Ident, expr).name,
        .FieldAccess => ast_unit.exprs.get(.FieldAccess, expr).field,
        else => null,
    };
}

/// Walk through alias declarations to find the actual source function definition.
fn resolveFunctionDeclAlias(
    self: *Checker,
    start: call_resolution.FunctionDeclContext,
) ?call_resolution.FunctionDeclContext {
    var current = start;
    var depth: usize = 0;
    while (depth < 16) : (depth += 1) {
        const decl = current.ast.exprs.Decl.get(current.decl_id);
        const kind = current.ast.kind(decl.value);

        switch (kind) {
            .FunctionLit => return current,
            .Import => return null,
            .FieldAccess => {
                const fr = current.ast.exprs.get(.FieldAccess, decl.value);
                if (call_resolution.findFunctionDeclFromFieldAccess(self.context, current.ast, fr, fr.field)) |resolved| {
                    if (resolved.ast != current.ast or !resolved.decl_id.eq(current.decl_id)) {
                        return resolved;
                    }
                }
                return current;
            },
            else => {
                const alias_name = aliasTargetName(current.ast, decl.value) orelse return current;
                const next = call_resolution.findFunctionDeclForCall(self.context, current.ast, decl.value, alias_name) orelse return current;
                if (next.ast == current.ast and next.decl_id.eq(current.decl_id)) return current;
                current = next;
            },
        }
    }
    return current;
}

// =========================
// Blocks, Return & Control
// =========================

/// Type-check a `code { ... }` block and warn once that it is not executed regularly.
fn checkCodeBlock(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const cb = getExpr(ast_unit, .CodeBlock, id);
    if (!ctx.warned_code) {
        try self.context.diags.addNote(exprLoc(ast_unit, cb), .checker_code_block_not_executed, .{});
        ctx.warned_code = true;
    }
    // Do not type-check code block bodies; they are intended for splicing/insert.
    return self.context.type_store.tCode();
}

fn expandInsertValue(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, value: comp.ValueId, loc: Loc) !void {
    const s = &ast_unit.type_info.val_store;
    switch (s.kind(value)) {
        .Code => try self.expandInsertBlock(ctx, ast_unit, s.get(.Code, value), loc),
        else => try self.context.diags.addError(loc, .insert_requires_code, .{}),
    }
}

fn codeBlockStmts(self: *Checker, _: *CheckerContext, ast_unit: *ast.Ast, code: comp.CodeValue, loc: Loc) ?[]const ast.StmtId {
    if (ast_unit.kind(code.block) != .Block) {
        self.context.diags.addError(loc, .insert_requires_code, .{}) catch {};
        return null;
    }
    const block = ast_unit.exprs.get(.Block, code.block);
    return ast_unit.stmts.stmt_pool.slice(block.items);
}

fn expandInsertBlock(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, code: comp.CodeValue, loc: Loc) anyerror!void {
    var expanded = List(ast.StmtId){};
    defer expanded.deinit(self.gpa);
    try self.expandCodeBlockStmts(ctx, ast_unit, code, &expanded, loc);
    if (expanded.items.len == 0) return;

    switch (self.currentInsertTarget(ctx)) {
        .unit => {
            var new_decls = List(ast.DeclId){};
            defer new_decls.deinit(self.gpa);
            for (expanded.items) |sid| {
                if (ast_unit.kind(sid) != .Decl) {
                    try self.context.diags.addError(stmtLoc(ast_unit, sid), .insert_requires_decl, .{});
                    continue;
                }
                try new_decls.append(self.gpa, getStmt(ast_unit, .Decl, sid).decl);
            }
            if (new_decls.items.len == 0) return;

            const old = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
            const combined = try ast_unit.gpa.alloc(ast.DeclId, old.len + new_decls.items.len);
            @memcpy(combined[0..old.len], old);
            @memcpy(combined[old.len..], new_decls.items);
            ast_unit.unit.decls = ast_unit.exprs.decl_pool.pushMany(ast_unit.gpa, combined);

            const root_scope = rootScopeId(ctx) orelse return;
            for (new_decls.items) |did| {
                try self.bindDeclPatternInScope(ctx, ast_unit, did, root_scope);
                try self.checkDecl(ctx, ast_unit, did);
            }
        },
        .block => |target| {
            var block_row = ast_unit.exprs.get(.Block, target.block_id);
            const old_items = ast_unit.stmts.stmt_pool.slice(block_row.items);
            var insert_index: usize = old_items.len;
            if (self.currentInsertSite(ctx)) |site| {
                if (site.block_id.eq(target.block_id)) {
                    insert_index = @intCast(site.index);
                    site.index += @intCast(expanded.items.len);
                }
            }
            if (insert_index > old_items.len) insert_index = old_items.len;

            const combined = try ast_unit.gpa.alloc(ast.StmtId, old_items.len + expanded.items.len);
            @memcpy(combined[0..insert_index], old_items[0..insert_index]);
            @memcpy(combined[insert_index .. insert_index + expanded.items.len], expanded.items);
            @memcpy(combined[insert_index + expanded.items.len ..], old_items[insert_index..]);
            block_row.items = ast_unit.stmts.stmt_pool.pushMany(ast_unit.gpa, combined);
            const row_idx = ast_unit.exprs.index.rows.items[target.block_id.toRaw()];
            ast_unit.exprs.Block.list.set(row_idx, block_row);

            for (expanded.items) |sid| {
                switch (ast_unit.kind(sid)) {
                    .Decl => {
                        const did = getStmt(ast_unit, .Decl, sid).decl;
                        try self.bindDeclPatternInScope(ctx, ast_unit, did, target.scope_id);
                        try self.checkDecl(ctx, ast_unit, did);
                        if (self.inFunction(ctx)) {
                            const idx = ctx.func_stack.items.len - 1;
                            var locals = &ctx.func_stack.items[idx].locals;
                            const raw = did.toRaw();
                            if (raw >= locals.capacity()) locals.resize(self.gpa, raw + 1, false) catch {};
                            locals.set(raw);
                        }
                    },
                    else => {
                        _ = try self.checkStmt(ctx, ast_unit, sid);
                    },
                }
            }
        },
    }
}

fn expandCodeBlockStmts(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    code: comp.CodeValue,
    out: *List(ast.StmtId),
    loc: Loc,
) !void {
    var local_code = code;
    if (local_code.ast != ast_unit) {
        if (ctx.interp) |*interp| {
            local_code = interp.cloneCodeToAst(local_code, ast_unit) catch {
                self.context.diags.addError(loc, .insert_requires_code, .{}) catch {};
                return;
            };
            // Ensure type info capacity for new expressions
            if (ast_unit.exprs.index.kinds.items.len > 0) {
                const last_expr = ast.ExprId.fromRaw(@intCast(ast_unit.exprs.index.kinds.items.len - 1));
                ast_unit.type_info.ensureExpr(self.context.gpa, last_expr) catch {};
            }
            // Ensure type info capacity for new declarations
            if (ast_unit.exprs.Decl.list.len > 0) {
                const last_decl = ast.DeclId.fromRaw(@intCast(ast_unit.exprs.Decl.list.len - 1));
                ast_unit.type_info.ensureDecl(self.context.gpa, last_decl) catch {};
            }
        } else {
            self.context.diags.addError(loc, .insert_requires_code, .{}) catch {};
            return;
        }
    }

    const stmts = self.codeBlockStmts(ctx, ast_unit, local_code, loc) orelse return;
    if (stmts.len == 0) return;

    for (stmts) |sid| {
        if (ast_unit.kind(sid) == .Expr) {
            const expr_id = getStmt(ast_unit, .Expr, sid).expr;
            if (ast_unit.kind(expr_id) == .Splice) {
                const sp = getExpr(ast_unit, .Splice, expr_id);
                if (try self.resolveSpliceValue(ctx, ast_unit, local_code, expr_id, sp.name, exprLoc(ast_unit, sp))) |val| {
                    const s = &ast_unit.type_info.val_store;
                    if (s.kind(val.*) == .Code) {
                        try self.expandCodeBlockStmts(ctx, ast_unit, s.get(.Code, val.*), out, loc);
                    } else {
                        const name_str = getStr(ast_unit, sp.name);
                        try self.context.diags.addError(exprLoc(ast_unit, sp), .code_splice_requires_code, .{name_str});
                    }
                }
                continue;
            }
        }
        try self.applySpliceBindingsInStmt(ctx, ast_unit, local_code, sid);
        try out.append(self.gpa, sid);
    }
}

fn resolveSpliceValue(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    code: comp.CodeValue,
    expr_id: ast.ExprId,
    name: ast.StrId,
    loc: Loc,
) !?*comp.ValueId {
    if (ast_unit.type_info.getComptimeValue(expr_id)) |cached| return cached;
    const s = &ast_unit.type_info.val_store;
    const caps = s.code_binding_pool.slice(code.captures);
    for (caps) |cid| {
        const binding = s.CodeBinding.get(cid);
        if (!binding.name.eq(name)) continue;
        var value_id = binding.value;
        if (s.kind(value_id) == .Code) {
            var code_val = s.get(.Code, value_id);
            if (code_val.ast != ast_unit) {
                if (ctx.interp) |*interp| {
                    code_val = interp.cloneCodeToAst(code_val, ast_unit) catch {
                        try self.context.diags.addError(loc, .code_splice_requires_expr, .{});
                        return null;
                    };
                    const code_caps = s.code_binding_pool.slice(code_val.captures);
                    var new_captures = std.ArrayList(comp.ValueRows.CodeBinding){};
                    defer new_captures.deinit(self.gpa);
                    for (code_caps) |cap_id| {
                        const b = s.CodeBinding.get(cap_id);
                        const name_str = code_val.ast.exprs.strs.get(b.name);
                        const new_name = ast_unit.exprs.strs.intern(name_str);
                        const cloned_val = try s.cloneValue(&code_val.ast.type_info.val_store, b.value);
                        try new_captures.append(self.gpa, .{ .name = new_name, .value = cloned_val });
                    }
                    code_val.captures = s.addCodeBindings(new_captures.items);
                    value_id = s.add(.Code, code_val);
                } else {
                    try self.context.diags.addError(loc, .code_splice_requires_expr, .{});
                    return null;
                }
                // Ensure type info capacity
                if (ast_unit.exprs.index.kinds.items.len > 0) {
                    const last_expr = ast.ExprId.fromRaw(@intCast(ast_unit.exprs.index.kinds.items.len - 1));
                    try ast_unit.type_info.ensureExpr(self.context.gpa, last_expr);
                }
                // Ensure type info capacity for new declarations
                if (ast_unit.exprs.Decl.list.len > 0) {
                    const last_decl = ast.DeclId.fromRaw(@intCast(ast_unit.exprs.Decl.list.len - 1));
                    try ast_unit.type_info.ensureDecl(self.context.gpa, last_decl);
                }
            }
        }
        try ast_unit.type_info.setComptimeValue(expr_id, value_id);
        return ast_unit.type_info.getComptimeValue(expr_id);
    }
    if (ast_unit.type_info.cloneComptimeBindingValue(&ast_unit.type_info.val_store, name) catch null) |val| {
        try ast_unit.type_info.setComptimeValue(expr_id, val);
        return ast_unit.type_info.getComptimeValue(expr_id);
    }

    const name_str = getStr(ast_unit, name);
    try self.context.diags.addError(loc, .code_splice_unknown_identifier, .{name_str});
    return null;
}

fn applySpliceBindingsInStmt(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, code: comp.CodeValue, sid: ast.StmtId) anyerror!void {
    switch (ast_unit.kind(sid)) {
        .Expr => try self.applySpliceBindingsInExpr(ctx, ast_unit, code, getStmt(ast_unit, .Expr, sid).expr),
        .Decl => {
            const decl = ast_unit.exprs.Decl.get(getStmt(ast_unit, .Decl, sid).decl);
            if (!decl.ty.isNone()) try self.applySpliceBindingsInExpr(ctx, ast_unit, code, decl.ty.unwrap());
            try self.applySpliceBindingsInExpr(ctx, ast_unit, code, decl.value);
        },
        .Assign => {
            const row = getStmt(ast_unit, .Assign, sid);
            if (row.left == .expr) try self.applySpliceBindingsInExpr(ctx, ast_unit, code, row.left.expr);
            try self.applySpliceBindingsInExpr(ctx, ast_unit, code, row.right);
        },
        .Insert => try self.applySpliceBindingsInExpr(ctx, ast_unit, code, getStmt(ast_unit, .Insert, sid).expr),
        .Return => {
            const row = getStmt(ast_unit, .Return, sid);
            if (!row.value.isNone()) try self.applySpliceBindingsInExpr(ctx, ast_unit, code, row.value.unwrap());
        },
        .Break => {
            const row = getStmt(ast_unit, .Break, sid);
            if (!row.value.isNone()) try self.applySpliceBindingsInExpr(ctx, ast_unit, code, row.value.unwrap());
        },
        .Defer => try self.applySpliceBindingsInExpr(ctx, ast_unit, code, getStmt(ast_unit, .Defer, sid).expr),
        .ErrDefer => try self.applySpliceBindingsInExpr(ctx, ast_unit, code, getStmt(ast_unit, .ErrDefer, sid).expr),
        else => {},
    }
}

fn applySpliceBindingsInExpr(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, code: comp.CodeValue, expr_id: ast.ExprId) !void {
    const kind = ast_unit.kind(expr_id);
    if (kind == .Splice) {
        const row = getExpr(ast_unit, .Splice, expr_id);
        _ = try self.resolveSpliceValue(ctx, ast_unit, code, expr_id, row.name, exprLoc(ast_unit, row));
        return;
    }
    if (kind == .CodeBlock) return;
    switch (kind) {
        inline else => |k| {
            const row = ast_unit.exprs.get(k, expr_id);
            inline for (@typeInfo(@TypeOf(row)).@"struct".fields) |f| {
                if (comptime std.mem.eql(u8, f.name, "loc")) continue;
                if (f.type == ast.ExprId) {
                    try self.applySpliceBindingsInExpr(ctx, ast_unit, code, @field(row, f.name));
                } else if (f.type == ast.OptExprId) {
                    const opt = @field(row, f.name);
                    if (!opt.isNone()) try self.applySpliceBindingsInExpr(ctx, ast_unit, code, opt.unwrap());
                } else if (f.type == ast.RangeExpr) {
                    for (ast_unit.exprs.expr_pool.slice(@field(row, f.name))) |child| {
                        try self.applySpliceBindingsInExpr(ctx, ast_unit, code, child);
                    }
                } else if (f.type == ast.RangeStmt) {
                    for (ast_unit.stmts.stmt_pool.slice(@field(row, f.name))) |sid| {
                        try self.applySpliceBindingsInStmt(ctx, ast_unit, code, sid);
                    }
                } else if (f.type == ast.RangeMatchArm) {
                    for (ast_unit.exprs.arm_pool.slice(@field(row, f.name))) |arm_id| {
                        const arm = ast_unit.exprs.MatchArm.get(arm_id);
                        if (!arm.guard.isNone()) try self.applySpliceBindingsInExpr(ctx, ast_unit, code, arm.guard.unwrap());
                        try self.applySpliceBindingsInExpr(ctx, ast_unit, code, arm.body);
                    }
                }
            }
        },
    }
}

fn typeFromSpliceValue(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, value: comp.ValueId, loc: Loc, opt_splice_id: ?ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const s = &ast_unit.type_info.val_store;
    return switch (s.kind(value)) {
        .Int => ts.tI64(), // Or infer from context? For now use default types for literals
        .Float => ts.tF64(),
        .Bool => ts.tBool(),
        .Void => ts.tVoid(),
        .String => ts.tString(),
        // TODO: Handle Sequence, Struct, Map if they can be lowered to runtime values
        // For now, these are the basics required.
        .Sequence => blk: {
            const seq = s.get(.Sequence, value);
            const items = s.val_pool.slice(seq.elems);
            // Unpack single-element sequences (e.g. from blocks)
            if (items.len == 1) {
                break :blk try self.typeFromSpliceValue(ctx, ast_unit, items[0], loc, null);
            }
            // Create a tuple type
            var elem_types = std.ArrayList(types.TypeId){};
            defer elem_types.deinit(self.gpa);
            for (items) |v| {
                const t = try self.typeFromSpliceValue(ctx, ast_unit, v, loc, null);
                try elem_types.append(self.gpa, t);
            }
            break :blk ts.mkTuple(elem_types.items);
        },
        .Struct => blk: {
            const sv = s.get(.Struct, value);
            const fields = s.struct_field_pool.slice(sv.fields);
            // Create a struct type
            // Note: This creates an anonymous struct type. Named structs might need different handling if they have an original declaration.
            var struct_fields = std.ArrayList(types.TypeStore.StructFieldArg){};
            defer struct_fields.deinit(self.gpa);
            for (fields) |fid| {
                const f = s.StructField.get(fid);
                const name_str = ast_unit.exprs.strs.get(f.name);
                const field_name = ast_unit.exprs.strs.intern(name_str); // Ensure interned in current unit
                const t = try self.typeFromSpliceValue(ctx, ast_unit, f.value, loc, null);
                try struct_fields.append(self.gpa, .{ .name = field_name, .ty = t });
            }
            break :blk ts.mkStruct(struct_fields.items, 0);
        },
        .Type => ts.mkTypeType(s.get(.Type, value).ty),
        .Code => blk: {
            var code = s.get(.Code, value);
            var code_id = value;
            if (code.ast != ast_unit) {
                if (ctx.interp) |*interp| {
                    code = interp.cloneCodeToAst(code, ast_unit) catch {
                        try self.context.diags.addError(loc, .code_splice_requires_expr, .{});
                        break :blk ts.tTypeError();
                    };
                    const caps = ast_unit.type_info.val_store.code_binding_pool.slice(code.captures);
                    var new_captures = std.ArrayList(comp.ValueRows.CodeBinding){};
                    defer new_captures.deinit(self.gpa);
                    for (caps) |cid| {
                        const b = ast_unit.type_info.val_store.CodeBinding.get(cid);
                        const name_str = code.ast.exprs.strs.get(b.name);
                        const new_name = ast_unit.exprs.strs.intern(name_str);
                        const cloned_val = try ast_unit.type_info.val_store.cloneValue(&code.ast.type_info.val_store, b.value);
                        try new_captures.append(self.gpa, .{ .name = new_name, .value = cloned_val });
                    }
                    code.captures = ast_unit.type_info.val_store.addCodeBindings(new_captures.items);
                    code_id = ast_unit.type_info.val_store.add(.Code, code);
                    // Ensure type info capacity for cloned expressions/declarations.
                    if (ast_unit.exprs.index.kinds.items.len > 0) {
                        const last_expr = ast.ExprId.fromRaw(@intCast(ast_unit.exprs.index.kinds.items.len - 1));
                        try ast_unit.type_info.ensureExpr(self.context.gpa, last_expr);
                    }
                    if (ast_unit.exprs.Decl.list.len > 0) {
                        const last_decl = ast.DeclId.fromRaw(@intCast(ast_unit.exprs.Decl.list.len - 1));
                        try ast_unit.type_info.ensureDecl(self.context.gpa, last_decl);
                    }
                } else {
                    try self.context.diags.addError(loc, .code_splice_requires_expr, .{});
                    break :blk ts.tTypeError();
                }
            }

            if (opt_splice_id) |sid| {
                try ast_unit.type_info.ensureExpr(self.gpa, sid);
                try ast_unit.type_info.setComptimeValue(sid, code_id);
            } else {
                break :blk ts.tCode();
            }

            // Try single expression extraction first
            if (comp.codeExprFromCodeValue(ast_unit, code)) |expr_id| {
                try self.applySpliceBindingsInExpr(ctx, ast_unit, code, expr_id);
                break :blk try self.checkExpr(ctx, ast_unit, expr_id);
            }
            try self.context.diags.addError(loc, .code_splice_requires_expr, .{});
            break :blk ts.tTypeError();
        },
        else => {
            try self.context.diags.addError(loc, .code_splice_requires_expr, .{});
            return ts.tTypeError();
        },
    };
}

fn rootScopeId(ctx: *CheckerContext) ?symbols.ScopeId {
    return if (ctx.symtab.stack.items.len > 0) ctx.symtab.stack.items[0].id else null;
}

fn declareSymbolInScope(ctx: *CheckerContext, scope_id: symbols.ScopeId, sym: symbols.SymbolRow) !symbols.SymbolId {
    const id = ctx.symtab.syms.add(ctx.symtab.gpa, sym);
    for (ctx.symtab.stack.items) |*frame| {
        if (frame.id.eq(scope_id)) {
            try frame.list.append(ctx.symtab.gpa, id);
            return id;
        }
    }
    try ctx.symtab.stack.items[ctx.symtab.stack.items.len - 1].list.append(ctx.symtab.gpa, id);
    return id;
}

fn declIsComptimeValue(ast_unit: *ast.Ast, did: ast.DeclId) bool {
    const decl = ast_unit.exprs.Decl.get(did);
    return switch (ast_unit.kind(decl.value)) {
        .Literal, .MlirBlock, .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType, .MapType, .ComptimeBlock, .TypeOf => true,
        else => false,
    };
}

fn bindDeclPatternInScope(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, did: ast.DeclId, scope_id: symbols.ScopeId) !void {
    const decl = ast_unit.exprs.Decl.get(did);
    if (decl.pattern.isNone()) return;

    var names = std.ArrayList(ast.StrId){};
    defer names.deinit(self.gpa);
    try pattern_matching.collectPatternBindings(self, ast_unit, decl.pattern.unwrap(), &names);
    if (names.items.len == 0) return;

    const is_comptime = declIsComptimeValue(ast_unit, did);
    if (ctx.symtab.stack.items.len == 0) return;
    for (names.items) |name| {
        _ = try declareSymbolInScope(ctx, scope_id, .{
            .name = name,
            .kind = .Var,
            .is_comptime = is_comptime,
            .loc = decl.loc,
            .origin_decl = .some(did),
            .origin_param = .none(),
        });
    }
}

/// Check async block: validates body and returns Future<BodyType>.
fn checkAsyncBlock(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ab = ast_unit.exprs.get(.AsyncBlock, id);
    const body_ty = try self.checkExpr(ctx, ast_unit, ab.body);
    if (self.typeKind(body_ty) == .TypeError) return self.context.type_store.tTypeError();
    return self.context.type_store.mkFuture(body_ty);
}

/// Validate an `mlir` block: check args, enforce comptime splices, and stamp the resulting type.
fn checkMlirBlock(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const diags = self.context.diags;
    const row = ast_unit.exprs.get(.MlirBlock, id);

    const args = ast_unit.exprs.expr_pool.slice(row.args);
    for (args) |arg_id| _ = try self.checkExpr(ctx, ast_unit, arg_id);

    var has_splices = false;
    const pieces = ast_unit.exprs.mlir_piece_pool.slice(row.pieces);

    for (pieces) |pid| {
        const piece = ast_unit.exprs.MlirPiece.get(pid);
        if (piece.kind != .splice) continue;
        has_splices = true;

        const name = piece.text;
        const loc = exprLoc(ast_unit, row);
        const name_str = getStr(ast_unit, name);

        const sym_id = self.lookup(ctx, name) orelse {
            try diags.addError(loc, .mlir_splice_unknown_identifier, .{name_str});
            return ts.tTypeError();
        };
        const sym = ctx.symtab.syms.get(sym_id);

        if (!sym.is_comptime) {
            try diags.addError(loc, .mlir_splice_not_comptime, .{name_str});
            return ts.tTypeError();
        }

        // Handle Declarations
        if (!sym.origin_decl.isNone()) {
            const did = sym.origin_decl.unwrap();
            const decl_expr = ast_unit.exprs.Decl.get(did).value;
            const is_cached = ast_unit.type_info.getComptimeValue(decl_expr) != null or ast_unit.type_info.lookupComptimeBindingType(name) != null;

            if (sym.is_comptime or is_cached) {
                try ast_unit.type_info.setMlirSpliceInfo(pid, .{ .decl = .{ .decl_id = did, .name = name } });
                const computed = try self.evalComptimeExpr(ctx, ast_unit, decl_expr, &[_]Pipeline.ComptimeBinding{});
                try ast_unit.type_info.setMlirSpliceValue(pid, computed);
                continue;
            }
        }

        // Handle Params
        if (sym.kind == .Param) {
            if (sym.origin_param.isNone()) {
                try diags.addError(loc, .mlir_splice_not_comptime, .{name_str});
                return ts.tTypeError();
            }
            const pid_param = sym.origin_param.unwrap();
            const param_row = ast_unit.exprs.Param.get(pid_param);

            var param_ty = ts.tAny();
            if (!param_row.ty.isNone()) {
                const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, param_row.ty.unwrap());
                if (res[0]) param_ty = res[1];
            }

            if (ts.getKind(param_ty) == .TypeType) {
                try ast_unit.type_info.setMlirSpliceInfo(pid, .{ .type_param = .{ .param_id = pid_param, .name = name, .ty = param_ty } });
            } else {
                try ast_unit.type_info.setMlirSpliceInfo(pid, .{ .value_param = .{ .param_id = pid_param, .name = name, .ty = param_ty } });
            }
        } else {
            try diags.addError(loc, .mlir_splice_not_comptime, .{name_str});
            return ts.tTypeError();
        }
    }

    if (row.kind != .Operation and !ast_unit.type_info.hasComptimeValue(id) and !has_splices) {
        const mlir_ctx = self.pipeline.ensureMlirContext().*;
        const text_ref = mlir.StringRef.from(getStr(ast_unit, row.text));
        const loc = exprLoc(ast_unit, row);
        const s = &ast_unit.type_info.val_store;

        switch (row.kind) {
            .Module => {
                var mod = mlir.Module.createParse(mlir_ctx, text_ref);
                if (mod.isNull()) {
                    try diags.addError(loc, .mlir_parse_error, .{getStr(ast_unit, row.text)});
                    return ts.tTypeError();
                }
                try ast_unit.type_info.setComptimeValue(id, s.add(.MlirModule, .{ .module = mod }));
            },
            .Type => {
                const ty = mlir.Type.parseGet(mlir_ctx, text_ref);
                if (ty.isNull()) {
                    try diags.addError(loc, .mlir_parse_error, .{getStr(ast_unit, row.text)});
                    return ts.tTypeError();
                }
                try ast_unit.type_info.setComptimeValue(id, s.add(.MlirType, .{ .ty = ty }));
            },
            .Attribute => {
                const attr = mlir.Attribute.parseGet(mlir_ctx, text_ref);
                if (attr.isNull()) {
                    try diags.addError(loc, .mlir_parse_error, .{getStr(ast_unit, row.text)});
                    return ts.tTypeError();
                }
                try ast_unit.type_info.setComptimeValue(id, s.add(.MlirAttribute, .{ .attr = attr }));
            },
            .Operation => {}, // Handled by result_ty logic below
        }
    }

    var result_ty = switch (row.kind) {
        .Module => ts.tMlirModule(),
        .Attribute => ts.mkMlirAttribute(row.text),
        .Type => ts.mkTypeType(ts.mkMlirType(row.text)),
        .Operation => ts.tAny(),
    };

    if (row.kind == .Operation) {
        if (!row.result_ty.isNone()) {
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, row.result_ty.unwrap());
            if (res[0]) result_ty = res[1];
        } else if (self.typeKind(result_ty) == .Any) {
            if (self.getExpectedType(ctx)) |hint| {
                result_ty = hint;
            } else {
                try diags.addError(exprLoc(ast_unit, row), .mlir_operation_missing_result_type, .{});
                result_ty = ts.tTypeError();
            }
        }
    }
    ast_unit.type_info.setExprType(id, result_ty);
    return result_ty;
}

/// Type-check the `.insert` expression by checking its operand (returns `Any`).
fn checkInsert(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const r = getExpr(ast_unit, .Insert, id);
    _ = try self.checkExpr(ctx, ast_unit, r.expr);
    const computed = try self.evalComptimeExpr(ctx, ast_unit, r.expr, &.{});
    try self.expandInsertValue(ctx, ast_unit, computed, exprLoc(ast_unit, r));
    return self.context.type_store.tAny();
}

fn checkSplice(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const row = getExpr(ast_unit, .Splice, id);
    const loc = exprLoc(ast_unit, row);

    if (ast_unit.type_info.getComptimeValue(id)) |cached| {
        return try self.typeFromSpliceValue(ctx, ast_unit, cached.*, loc, id);
    }

    const name_str = getStr(ast_unit, row.name);
    try self.context.diags.addError(loc, .code_splice_unknown_identifier, .{name_str});
    return self.context.type_store.tTypeError();
}

/// Ensure a `return` statement matches enclosing function requirements and emit diagnostics.
fn checkReturn(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, rr: ast.Rows.Return) !types.TypeId {
    const ts = self.context.type_store;
    if (ctx.func_stack.items.len == 0) {
        try self.context.diags.addError(exprLoc(ast_unit, rr), .return_outside_function, .{});
        return ts.tTypeError();
    }

    var func_ctx = &ctx.func_stack.items[ctx.func_stack.items.len - 1];
    const expect_ty = func_ctx.result;
    const has_value = !rr.value.isNone();

    var ret_ty = if (!has_value) ts.tVoid() else blk: {
        try self.pushValueReq(ctx, true);
        if (func_ctx.has_result) try self.pushExpectedType(ctx, expect_ty);

        const t = try self.checkExpr(ctx, ast_unit, rr.value.unwrap());

        if (func_ctx.has_result) self.popExpectedType(ctx);
        self.popValueReq(ctx);
        break :blk t;
    };

    if (self.typeKind(ret_ty) == .TypeError) return ts.tTypeError();

    if (func_ctx.has_result and !has_value) {
        try self.context.diags.addError(exprLoc(ast_unit, rr), .missing_return_value, .{expect_ty});
        return ts.tTypeError();
    }
    if (!func_ctx.has_result and has_value) {
        try self.context.diags.addError(exprLoc(ast_unit, rr), .return_value_in_void_function, .{ret_ty});
        return ts.tTypeError();
    }

    // Attempt null literal coercion
    if (has_value) {
        if (self.tryCoerceNullLiteral(ast_unit, rr.value.unwrap(), expect_ty)) {
            ast_unit.type_info.expr_types.items[rr.value.unwrap().toRaw()] = expect_ty;
            ret_ty = expect_ty;
        }
    }

    // Opportunistic Result Inference for `any` or `type`
    if (func_ctx.inferred_result == null) {
        const expect_kind = self.typeKind(expect_ty);
        const ret_kind = self.typeKind(ret_ty);

        if (ret_kind != .Any and ret_kind != .TypeError) {
            if (expect_kind == .Any) {
                func_ctx.inferred_result = ret_ty;
            } else if (expect_kind == .TypeType) {
                const expect_of = ts.get(.TypeType, expect_ty).of;
                if (self.typeKind(expect_of) == .Any) {
                    if (ret_kind == .TypeType) {
                        const ret_of = ts.get(.TypeType, ret_ty).of;
                        if (self.typeKind(ret_of) != .Any and self.typeKind(ret_of) != .TypeError)
                            func_ctx.inferred_result = ret_ty;
                    } else {
                        const wrapped = ts.mkTypeType(ret_ty);
                        func_ctx.inferred_result = wrapped;
                        ret_ty = wrapped;
                    }
                }
            }
        }
    }

    if (self.assignable(ret_ty, expect_ty) != .success) {
        if (check_types.isNumericKind(self, self.typeKind(expect_ty)) and has_value) {
            var coerced = ret_ty;
            var coerced_kind = self.typeKind(coerced);
            if (try self.updateCoercedLiteral(ast_unit, rr.value.unwrap(), expect_ty, &coerced, &coerced_kind) and
                self.assignable(coerced, expect_ty) == .success)
            {
                return coerced;
            }
        }
        try self.context.diags.addError(exprLoc(ast_unit, rr), .return_type_mismatch, .{ expect_ty, ret_ty });
        return ts.tTypeError();
    }
    return ret_ty;
}

/// Type-check an `if` expression or statement, ensuring both branches agree on types.
fn checkIf(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const diags = self.context.diags;
    const if_expr = getExpr(ast_unit, .If, id);

    // Condition expects bool
    try self.pushExpectedType(ctx, ts.tBool());
    const cond = try self.checkExpr(ctx, ast_unit, if_expr.cond);
    self.popExpectedType(ctx);

    if (!cond.eq(ts.tBool())) {
        try diags.addError(exprLoc(ast_unit, if_expr), .non_boolean_condition, .{self.typeKind(cond)});
        return ts.tTypeError();
    }

    const value_required = self.isValueReq(ctx);
    if (!value_required) {
        try self.pushExpectedType(ctx, null);
        defer self.popExpectedType(ctx);
        _ = try self.checkExpr(ctx, ast_unit, if_expr.then_block);
        if (!if_expr.else_block.isNone()) _ = try self.checkExpr(ctx, ast_unit, if_expr.else_block.unwrap());
        return ts.tVoid();
    }

    const expected_ty = self.getExpectedType(ctx);
    try self.pushExpectedType(ctx, expected_ty);
    const then_ty = try self.checkExpr(ctx, ast_unit, if_expr.then_block);
    self.popExpectedType(ctx);

    if (self.typeKind(then_ty) == .TypeError) return ts.tTypeError();

    if (if_expr.else_block.isNone()) {
        if (self.typeKind(then_ty) == .Noreturn) return ts.tNoreturn();
        try diags.addError(exprLoc(ast_unit, if_expr), .if_expression_requires_else, .{});
        return ts.tTypeError();
    }

    try self.pushExpectedType(ctx, expected_ty);
    const else_ty = try self.checkExpr(ctx, ast_unit, if_expr.else_block.unwrap());
    self.popExpectedType(ctx);

    if (self.typeKind(else_ty) == .TypeError) return ts.tTypeError();

    const then_nr = self.typeKind(then_ty) == .Noreturn;
    const else_nr = self.typeKind(else_ty) == .Noreturn;

    if (then_nr and else_nr) return ts.tNoreturn();
    if (then_nr) return else_ty;
    if (else_nr) return then_ty;
    if (then_ty.eq(else_ty)) return then_ty;

    if (expected_ty) |expect| {
        if (self.assignable(then_ty, expect) == .success and self.assignable(else_ty, expect) == .success) return expect;
    } else {
        const then_const = self.constNumericKindForValue(ast_unit, if_expr.then_block);
        const else_const = self.constNumericKindForValue(ast_unit, if_expr.else_block.unwrap());
        if (then_const != .none and else_const != .none and then_const != else_const) {
            try diags.addError(exprLoc(ast_unit, if_expr), .if_branch_type_mismatch, .{ then_ty, else_ty });
            return ts.tTypeError();
        }
    }

    if (self.unifyTypes(then_ty, else_ty)) |u| return u;

    try diags.addError(exprLoc(ast_unit, if_expr), .if_branch_type_mismatch, .{ then_ty, else_ty });
    return ts.tTypeError();
}

/// Type-check `while` loops, including pattern matching and loop result tracking.
fn checkWhile(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const wr = getExpr(ast_unit, .While, id);
    var loop_binding = false;

    if (!wr.cond.isNone()) {
        const cond_expr = wr.cond.unwrap();
        const ty = try self.checkExpr(ctx, ast_unit, cond_expr);
        if (self.typeKind(ty) == .TypeError) return ts.tTypeError();

        if (!wr.pattern.isNone()) {
            if (!(try pattern_matching.checkPattern(self, ctx, ast_unit, wr.pattern.unwrap(), ty, true))) return ts.tTypeError();
            try pattern_matching.declareBindingsInPattern(self, ctx, ast_unit, wr.pattern.unwrap(), wr.loc, .anonymous);
            try self.pushLoopBinding(ctx, wr.pattern, ty);
            loop_binding = true;
        } else {
            const ck = self.typeKind(ty);
            if (ck != .Bool and ck != .Any) {
                try self.context.diags.addError(exprLoc(ast_unit, wr), .non_boolean_condition, .{ck});
                return ts.tTypeError();
            }
        }
    }

    try self.pushLoop(ctx, wr.label);
    defer self.popLoop(ctx);
    defer if (loop_binding) self.popLoopBinding(ctx);

    const body_ty = try self.checkExpr(ctx, ast_unit, wr.body);
    if (self.isValueReq(ctx)) {
        if (self.loopCtxForLabel(ctx, wr.label)) |lctx| {
            if (lctx.result_ty) |ty| return ty;
            return ts.tTypeError();
        }
    }
    return body_ty;
}

/// Handle `unreachable` expressions (no-op besides returning `any`).
fn checkUnreachable(self: *Checker, _: ast.ExprId) !types.TypeId {
    return self.context.type_store.tAny();
}

/// Validate `for` loops over iterable collections and establish loop bindings.
fn checkFor(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const fr = getExpr(ast_unit, .For, id);
    const it = try self.checkExpr(ctx, ast_unit, fr.iterable);
    const kind = self.typeKind(it);

    const subject_ty: types.TypeId = switch (kind) {
        .Array, .DynArray => blk: {
            if (ast_unit.kind(fr.pattern) == .Slice) break :blk it;
            break :blk if (kind == .Array) ts.get(.Array, it).elem else ts.get(.DynArray, it).elem;
        },
        .Slice => it, // Slice iter always yields slice or element? Original logic implies slice->slice pattern or element
        else => {
            try self.context.diags.addError(exprLoc(ast_unit, fr), .non_iterable_in_for, .{it});
            return ts.tTypeError();
        },
    };

    // Correct slice element logic if pattern isn't slice
    const final_ty = if (kind == .Slice and ast_unit.kind(fr.pattern) != .Slice) ts.get(.Slice, it).elem else subject_ty;

    if (!(try pattern_matching.checkPattern(self, ctx, ast_unit, fr.pattern, final_ty, true))) {
        return ts.tTypeError();
    }

    try self.pushLoopBinding(ctx, .some(fr.pattern), final_ty);
    try self.pushLoop(ctx, fr.label);
    defer self.popLoop(ctx);
    defer self.popLoopBinding(ctx);

    const body_ty = try self.checkExpr(ctx, ast_unit, fr.body);
    if (self.isValueReq(ctx)) {
        if (self.loopCtxForLabel(ctx, fr.label)) |lctx| {
            if (lctx.result_ty) |ty| return ty;
            return ts.tTypeError();
        }
    }
    return body_ty;
}

// =========================
// Casts, Catch, Optionals
// =========================

/// Try to reconcile `a` and `b` by picking a castable/superset type when possible.
fn unifyTypes(self: *Checker, a: types.TypeId, b: types.TypeId) ?types.TypeId {
    if (a.eq(b)) return a;
    const ts = self.context.type_store;
    const ak = self.typeKind(a);
    const bk = self.typeKind(b);

    if (ak == .Any or bk == .Any) return null;

    if (ak == .Optional and bk == .Optional) {
        const ao = ts.get(.Optional, a);
        const bo = ts.get(.Optional, b);
        if (self.unifyTypes(ao.elem, bo.elem)) |elem| return ts.mkOptional(elem);
        return null;
    }

    if (self.assignable(b, a) == .success or self.castable(b, a)) return a;
    if (self.assignable(a, b) == .success or self.castable(a, b)) return b;

    if (check_types.isNumericKind(self, ak) and check_types.isNumericKind(self, bk)) return self.unifyNumeric(a, b);

    return null;
}

/// Normalize the numeric types `a` and `b` to a common type for comparison purposes.
fn unifyNumeric(self: *Checker, a: types.TypeId, b: types.TypeId) types.TypeId {
    const ak = self.typeKind(a);
    const bk = self.typeKind(b);
    const ts = self.context.type_store;

    if (ak == .F64 or bk == .F64) return ts.tF64();
    if (ak == .F32 or bk == .F32) return ts.tF32();
    if (ak == .Usize or bk == .Usize) return ts.tUsize();

    const asz = check_types.typeSize(self.context, a);
    const bsz = check_types.typeSize(self.context, b);
    if (asz != bsz) return if (asz > bsz) a else b;

    // Same width: prefer unsigned
    if (check_types.isUnsignedInt(ak)) return a;
    if (check_types.isUnsignedInt(bk)) return b;
    return a;
}

/// Return true when `got` is allowed to be cast to `expect` (even if not assignable).
fn castable(self: *Checker, got: types.TypeId, expect: types.TypeId) bool {
    if (got.eq(expect)) return true;
    const gk = self.typeKind(got);
    const ek = self.typeKind(expect);
    const ts = self.context.type_store;

    if (self.isSliceOfU8(got) and ek == .String) return true;
    if (gk == .String and self.isSliceOfU8(expect)) return true;

    if (ek == .Optional) {
        const opt = ts.get(.Optional, expect);
        if (self.assignable(got, opt.elem) == .success or self.castable(got, opt.elem)) return true;
    }

    if (gk == .Simd and ek == .Simd) {
        const vsimd = ts.get(.Simd, got);
        const tsimd = ts.get(.Simd, expect);
        return vsimd.lanes == tsimd.lanes and
            check_types.isNumericKind(self, self.typeKind(vsimd.elem)) and
            check_types.isNumericKind(self, self.typeKind(tsimd.elem));
    }

    // Numeric checks
    const g_num = check_types.isNumericKind(self, gk);
    const e_num = check_types.isNumericKind(self, ek);
    if (g_num and e_num) return true;

    if ((gk == .Enum and check_types.isIntegerKind(self, ek)) or (ek == .Enum and check_types.isIntegerKind(self, gk))) return true;
    if (gk == .Ptr and ek == .Ptr) return true;

    return false;
}

fn isSliceOfU8(self: *Checker, ty: types.TypeId) bool {
    if (self.typeKind(ty) != .Slice) return false;
    return self.context.type_store.get(.Slice, ty).elem.eq(self.context.type_store.tU8());
}

/// Validate a `break` statement, ensuring loop contexts/values align.
fn checkBreak(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, br: ast.Rows.Break) !types.TypeId {
    const ts = self.context.type_store;
    if (!self.inLoop(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, br), .break_outside_loop, .{});
        return ts.tTypeError();
    }

    var val_ty: types.TypeId = undefined;
    const has_val = !br.value.isNone();
    if (has_val) {
        val_ty = try self.checkExpr(ctx, ast_unit, br.value.unwrap());
        if (self.typeKind(val_ty) == .TypeError) return ts.tTypeError();
    }

    if (self.loopCtxForLabel(ctx, br.label)) |lctx| {
        if (has_val) {
            if (lctx.result_ty) |rt| {
                if (!val_ty.eq(rt)) {
                    try self.context.diags.addError(exprLoc(ast_unit, br), .loop_break_value_type_conflict, .{ rt, val_ty });
                    return ts.tTypeError();
                }
            } else lctx.result_ty = val_ty;
            return val_ty;
        }
        return ts.tVoid();
    }
    return ts.tTypeError();
}
/// Handle `continue` expressions (no type, but ensures location is tracked).
fn checkContinue(self: *Checker, id: ast.ExprId) !types.TypeId {
    _ = id;
    return self.context.type_store.tVoid();
}

/// Validate `defer` expressions inside functions only.
fn checkDefer(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, defer_expr: ast.Rows.Defer) !types.TypeId {
    const ts = self.context.type_store;
    if (!self.inFunction(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, defer_expr), .defer_outside_function, .{});
    }
    _ = try self.checkExpr(ctx, ast_unit, defer_expr.expr);
    return ts.tVoid();
}

/// Validate `err defer` expressions, requiring enclosing error functions.
fn checkErrDefer(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, errdefer_expr: ast.Rows.ErrDefer) !types.TypeId {
    const ts = self.context.type_store;
    if (!self.inFunction(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, errdefer_expr), .errdefer_outside_function, .{});
        return ts.tTypeError();
    }
    const current_func = self.currentFunc(ctx).?;
    if (!current_func.has_result or self.typeKind(current_func.result) != .ErrorSet) {
        try self.context.diags.addError(exprLoc(ast_unit, errdefer_expr), .errdefer_in_non_error_function, .{});
        return ts.tTypeError();
    }
    const ty = try self.checkExpr(ctx, ast_unit, errdefer_expr.expr);
    if (self.typeKind(ty) == .TypeError) return ts.tTypeError();
    return ts.tVoid();
}

/// Type-check `err.unwrap` ensuring the enclosing function returns an `ErrorSet`.
fn checkErrUnwrap(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const diags = self.context.diags;
    const eur = getExpr(ast_unit, .ErrUnwrap, id);
    const et = try self.checkExpr(ctx, ast_unit, eur.expr);

    if (self.typeKind(et) == .TypeError) return ts.tTypeError();
    if (self.typeKind(et) != .ErrorSet) {
        try diags.addError(exprLoc(ast_unit, eur), .error_propagation_on_non_error, .{et});
        return ts.tTypeError();
    }

    const er = ts.get(.ErrorSet, et);
    if (!self.inFunction(ctx)) {
        try diags.addError(exprLoc(ast_unit, eur), .error_propagation_mismatched_function_result, StringPayload{ .value = "unknown context" });
        return ts.tTypeError();
    }

    const fctx = self.currentFunc(ctx).?;
    if (self.typeKind(fctx.result) != .ErrorSet) {
        try diags.addError(exprLoc(ast_unit, eur), .error_propagation_mismatched_function_result, .{fctx.result});
        return ts.tTypeError();
    }

    // Ensure the error/value halves align with the function result type
    const fr = ts.get(.ErrorSet, fctx.result);
    if (self.assignable(er.error_ty, fr.error_ty) != .success or self.assignable(er.value_ty, fr.value_ty) != .success) {
        try diags.addError(exprLoc(ast_unit, eur), .error_propagation_mismatched_function_result, .{fctx.result});
        return ts.tTypeError();
    }
    return er.value_ty;
}

/// Validate optional unwrap (`?`) operations.
fn checkOptionalUnwrap(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const our = getExpr(ast_unit, .OptionalUnwrap, id);
    const ot = try self.checkExpr(ctx, ast_unit, our.expr);

    if (self.typeKind(ot) == .TypeError) return ts.tTypeError();
    if (self.typeKind(ot) != .Optional) {
        try self.context.diags.addError(exprLoc(ast_unit, our), .invalid_optional_unwrap_target, .{ot});
        return ts.tTypeError();
    }
    return ts.get(.Optional, ot).elem;
}

/// Check await expression: operand must be Future<T>, result is T.
fn checkAwait(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const aw = ast_unit.exprs.get(.Await, id);
    const op_ty = try self.checkExpr(ctx, ast_unit, aw.expr);
    const kind = self.typeKind(op_ty);

    if (kind == .TypeError) return ts.tTypeError();
    if (kind == .Any) return ts.tAny();
    if (kind == .Future) return ts.get(.Future, op_ty).elem;

    try self.context.diags.addError(exprLoc(ast_unit, aw), .await_on_non_future, .{op_ty});
    return ts.tTypeError();
}

/// Type-check closure literals, requiring explicit parameter annotations.
fn checkClosure(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const cr = getExpr(ast_unit, .Closure, id);
    const params = ast_unit.exprs.param_pool.slice(cr.params);

    const param_tys = try ts.gpa.alloc(types.TypeId, params.len);
    defer ts.gpa.free(param_tys);

    for (params, 0..) |p_idx, i| {
        const p = ast_unit.exprs.Param.get(p_idx);
        if (p.ty.isNone()) {
            try self.context.diags.addError(exprLoc(ast_unit, p), .type_annotation_mismatch, .{});
            return ts.tTypeError();
        }
        const ty_expr = p.ty.unwrap();
        if (ast_unit.kind(ty_expr) == .AnyType) {
            param_tys[i] = ts.tAny();
        } else if (try check_types.findAnyTypeExpr(self.gpa, ast_unit, ty_expr)) |any_id| {
            try self.context.diags.addError(exprLocFromId(ast_unit, any_id), .invalid_any_type_annotation, .{});
            return ts.tTypeError();
        } else {
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, ty_expr);
            if (!res[0]) return ts.tTypeError();
            param_tys[i] = res[1];
        }
    }

    const body_ty = try self.checkExpr(ctx, ast_unit, cr.body);
    if (self.typeKind(body_ty) == .TypeError) return ts.tTypeError();

    // Closures are always pure function *types* (no side-effect tracking here).
    return ts.mkFunction(param_tys, body_ty, false, true, false);
}

/// Handle different cast/kind modifiers, validating safety and recording results.
fn checkCast(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const diags = self.context.diags;
    const cr = getExpr(ast_unit, .Cast, id);

    if (try check_types.findAnyTypeExpr(self.gpa, ast_unit, cr.ty)) |any_id| {
        try diags.addError(exprLocFromId(ast_unit, any_id), .invalid_any_type_annotation, .{});
        return ts.tTypeError();
    }
    const et_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, cr.ty);
    if (!et_res[0]) {
        try diags.addError(exprLoc(ast_unit, cr), .cast_target_not_type, .{});
        return ts.tTypeError();
    }
    const et = et_res[1];
    const vt = try self.checkExpr(ctx, ast_unit, cr.expr);
    if (self.typeKind(vt) == .TypeError) return ts.tTypeError();

    const vk = self.typeKind(vt);
    const ek = self.typeKind(et);

    switch (cr.kind) {
        .normal => {
            if (self.assignable(vt, et) != .success and !self.castable(vt, et)) {
                try diags.addError(exprLoc(ast_unit, cr), .invalid_cast, .{ vk, ek });
                return ts.tTypeError();
            }
        },
        .bitcast => {
            const gsize = check_types.typeSize(self.context, vt);
            const tsize = check_types.typeSize(self.context, et);
            // Combined logic for clearer optimization
            const allowed = (vk == .Any or ek == .Any) or (gsize == tsize) or
                ((vk == .Ptr and ek == .Optional) or (vk == .Optional and ek == .Ptr));

            if (!allowed) {
                try diags.addError(exprLoc(ast_unit, cr), .invalid_bitcast, .{ vk, ek });
            }
        },
        .saturate, .wrap => {
            if (!check_types.isNumericKind(self, vk) or !check_types.isNumericKind(self, ek)) {
                try diags.addError(exprLoc(ast_unit, cr), .numeric_cast_on_non_numeric, .{vk});
                return ts.tTypeError();
            }
        },
        .checked => {
            if (self.assignable(vt, et) != .success and !self.castable(vt, et)) {
                try diags.addError(exprLoc(ast_unit, cr), .invalid_checked_cast, .{ vk, ek });
                return ts.tTypeError();
            }
            return ts.mkOptional(et);
        },
    }
    return et;
}

/// Type-check `catch` expressions, ensuring handler types match automations.
fn checkCatch(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const row = getExpr(ast_unit, .Catch, id);
    const lhs_ty = try self.checkExpr(ctx, ast_unit, row.expr);

    if (self.typeKind(lhs_ty) == .TypeError) return ts.tTypeError();

    if (self.typeKind(lhs_ty) != .ErrorSet) {
        try self.context.diags.addError(exprLoc(ast_unit, row), .catch_on_non_error, .{lhs_ty});
        return ts.tTypeError();
    }

    const es_info = ts.get(.ErrorSet, lhs_ty);
    var handler_ty: ?types.TypeId = null;

    if (!row.binding_name.isNone()) {
        const name = row.binding_name.unwrap();
        try self.pushCatchBinding(ctx, name, es_info.error_ty);
        handler_ty = try self.checkExpr(ctx, ast_unit, row.handler);
        self.popCatchBinding(ctx);
    } else {
        handler_ty = try self.checkExpr(ctx, ast_unit, row.handler);
    }

    if (handler_ty == null) return ts.tTypeError();

    // Side-effects only path
    if (!self.isValueReq(ctx)) {
        if (self.typeKind(handler_ty.?) == .Noreturn) return ts.tNoreturn();
        return ts.tVoid();
    }

    // Noreturn handler allows success path type propagation
    if (self.typeKind(handler_ty.?) == .Noreturn) return es_info.value_ty;

    const want_ok_ty = es_info.value_ty;
    if (self.assignable(handler_ty.?, want_ok_ty) != .success and !self.castable(handler_ty.?, want_ok_ty)) {
        try self.context.diags.addError(exprLoc(ast_unit, row), .catch_handler_type_mismatch, .{ want_ok_ty, handler_ty.? });
        return ts.tTypeError();
    }

    return es_info.value_ty;
}

/// Resolve import expressions to module-type proxies used during checking.
fn checkImport(self: *Checker, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const ts = self.context.type_store;
    const ir = getExpr(ast_unit, .Import, id);
    const filepath = getStr(ast_unit, ir.path);

    // Optimization: Interner and packages hoisted
    const interner = self.context.interner;
    const packages = self.context.compilation_unit.packages;

    for (packages.values()) |pkg| {
        if (pkg.sources.get(filepath) == null) continue;
        const pkg_name = interner.intern(pkg.name);
        const ast_ty = ts.mkAst(pkg_name, ir.path);
        ast_unit.type_info.expr_types.items[id.toRaw()] = ast_ty;
        return ast_ty;
    }

    try self.context.diags.addError(ast_unit.exprs.locs.get(ir.loc), .import_not_found, StringPayload{ .value = filepath });
    return ts.tTypeError();
}
