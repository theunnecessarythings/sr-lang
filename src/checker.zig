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

/// Allocator that backs all checker-internal data structures.
gpa: std.mem.Allocator,
/// Shared compilation context.
context: *Context,
/// Pipeline that drives the compilation phases.
pipeline: *Pipeline,
/// Stack of per-file checker contexts currently active.
checker_ctx: List(CheckerContext),
/// Scratch buffer reused for expression collection.
expr_id_scratch: std.ArrayList(ast.ExprId) = .{},
/// Additional scratch buffers for nested requests.
expr_id_scratch_extra: std.ArrayList(std.ArrayList(ast.ExprId)) = .{},
/// How many scratch buffers are currently checked-out.
expr_id_scratch_depth: usize = 0,

/// Per-AST context that tracks symbol tables, loops, matches, and diagnostic state.
pub const CheckerContext = struct {
    /// Symbol table used for name lookup inside the current AST unit.
    symtab: symbols.SymbolStore,

    /// Persistent interpreter instance for this AST unit.
    interp: ?*interpreter.Interpreter = null,

    /// Stack of function contexts currently being type-checked.
    func_stack: List(FunctionCtx) = .{},
    /// Stack of loop contexts for break/continue resolution.
    loop_stack: List(LoopCtx) = .{},
    /// Stack tracking whether the current block expects values.
    value_ctx: List(bool) = .{},
    /// Stack of expected types for the current expression (if known).
    expected_ty_stack: List(?types.TypeId) = .{},
    /// Records whether nested function literals are allowed at each depth.
    allow_nested_fn: List(bool) = .{},
    /// Whether metadata diagnostics have already been emitted.
    warned_meta: bool = false,
    /// Whether code diagnostics have already been emitted.
    warned_code: bool = false,

    /// Loop bindings currently in scope (for labelled breaks).
    loop_binding_stack: List(LoopBindingCtx) = .{},
    /// Exception/catch bindings currently in scope.
    catch_binding_stack: List(CatchBindingCtx) = .{},
    /// Match-binding contexts currently in scope.
    match_binding_stack: List(MatchBindingCtx) = .{},

    /// Declarations whose types are currently being resolved to prevent recursion.
    resolving_type_decls: Map(ast.DeclId, void) = .{},
    /// Expressions whose types are currently being resolved.
    resolving_type_exprs: Map(ast.ExprId, void) = .{},
    /// Pending parameter specializations for generics.
    param_specializations: List(ParamSpecialization) = .{},
    /// Cache to map a (Function + Concrete Args) -> Synthetic DeclId
    specialization_cache: SpecializationCache = .{},

    /// Release all lists and the symbol table managed by this context.
    pub fn deinit(self: *CheckerContext, gpa: std.mem.Allocator) void {
        self.symtab.deinit();
        self.func_stack.deinit(gpa);
        self.loop_stack.deinit(gpa);
        self.value_ctx.deinit(gpa);
        self.expected_ty_stack.deinit(gpa);
        self.allow_nested_fn.deinit(gpa);
        self.loop_binding_stack.deinit(gpa);
        self.catch_binding_stack.deinit(gpa);
        self.match_binding_stack.deinit(gpa);
        self.resolving_type_decls.deinit(gpa);
        self.resolving_type_exprs.deinit(gpa);
        self.param_specializations.deinit(gpa);
        var spec_it = self.specialization_cache.iterator();
        while (spec_it.next()) |entry| {
            gpa.free(entry.key_ptr.param_types);
        }
        self.specialization_cache.deinit(gpa);

        if (self.interp) |interp| {
            interp.deinit();
            gpa.destroy(interp);
        }
    }
};

/// Tracks a loop-specific binding introduced by `for`/`while` constructs.
const LoopBindingCtx = struct {
    /// Pattern bound by the loop (if any) for `for`/`while` binding checks.
    pat: ast.OptPatternId,
    /// Type of the loop subject that the pattern must match.
    subject_ty: types.TypeId,
};

/// Records the active pattern and type information for a match arm.
const MatchBindingCtx = struct {
    /// Pattern used by the current match arm.
    pat: ast.PatternId,
    /// Type of the value being matched against.
    subject_ty: types.TypeId,
};

/// Captures the name and type produced by a `catch` clause.
const CatchBindingCtx = struct {
    /// Name bound inside the catch handler.
    name: ast.StrId,
    /// Type assigned to the caught exception.
    ty: types.TypeId,
};

/// Simple string payload used when diagnostics only need raw text.
const StringPayload = struct {
    value: []const u8,
};

/// Associates a generic parameter name with the concrete type chosen for a specialization.
pub const ParamSpecialization = struct {
    /// Parameter name being specialized.
    name: ast.StrId,
    /// Concrete type chosen for the specialization.
    ty: types.TypeId,
};

/// Tracks the currently-checked function’s type expectations and local captures.
const FunctionCtx = struct {
    /// Function return type (possibly inferred).
    result: types.TypeId,
    /// True when the function declares a return value.
    has_result: bool,
    /// Whether the function has been proven pure so far.
    pure: bool,
    /// Whether purity is required by the declaration/context.
    require_pure: bool,
    /// Locally-defined entities tracked for resolution.
    locals: std.AutoArrayHashMapUnmanaged(u32, void) = .{},
    /// Optional refined result type discovered during return checking.
    inferred_result: ?types.TypeId = null,
};

/// Tracks the innermost loop label and result type for break/continue resolution.
const LoopCtx = struct {
    /// Optional label attached to the loop.
    label: ast.OptStrId,
    /// Inferred result type for loops that return expressions.
    result_ty: ?types.TypeId = null,
};

/// Construct a new `Checker` wired to `pipeline`, `context`, and allocator `gpa`.
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
        .expr_id_scratch = std.ArrayList(ast.ExprId){},
        .expr_id_scratch_extra = std.ArrayList(std.ArrayList(ast.ExprId)){},
        .expr_id_scratch_depth = 0,
    };
}

/// Deinitialize the checker, releasing all per-file contexts.
pub fn deinit(self: *Checker) void {
    for (self.checker_ctx.items) |*ctx| {
        ctx.deinit(self.gpa);
    }
    self.checker_ctx.deinit(self.gpa);
    for (self.expr_id_scratch_extra.items) |*scratch| {
        scratch.deinit(self.gpa);
    }
    self.expr_id_scratch_extra.deinit(self.gpa);
    self.expr_id_scratch.deinit(self.gpa);
}

/// Execute the checker across all AST units ordered by `levels`.
pub fn run(self: *Checker, levels: *const compile.DependencyLevels) !void {
    var ast_by_file_id: std.AutoArrayHashMap(u32, *ast.Ast) = .init(self.gpa);
    defer ast_by_file_id.deinit();

    var pkg_iter = self.context.compilation_unit.packages.iterator();
    while (pkg_iter.next()) |pkg| {
        var source_iter = pkg.value_ptr.sources.iterator();
        while (source_iter.next()) |unit| {
            if (unit.value_ptr.ast) |ast_unit| {
                try ast_by_file_id.put(unit.value_ptr.file_id, ast_unit);
            }
        }
    }

    // Size the per-file checker context table by max file_id + 1 to allow
    // direct indexing via ast_unit.file_id used during lowering.
    const max_file_id = std.mem.max(u32, ast_by_file_id.keys());
    try self.checker_ctx.resize(self.gpa, max_file_id + 1);

    for (levels.levels.items) |level| {
        if (level.items.len == 0) continue;

        for (level.items) |file_id| {
            const ast_unit = ast_by_file_id.get(file_id) orelse continue;
            self.checker_ctx.items[file_id] = CheckerContext{ .symtab = .init(self.gpa) };
            const ctx = &self.checker_ctx.items[file_id];
            ctx.symtab = .init(self.gpa);

            try self.ensureInterpreter(ast_unit, ctx);
            try predeclare(self, ast_unit, ctx);
        }
    }

    for (levels.levels.items) |level| {
        if (level.items.len == 0) continue;
        for (level.items) |file_id| {
            const ast_unit = ast_by_file_id.get(file_id) orelse continue;
            const ctx = &self.checker_ctx.items[file_id];
            const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
            for (decl_ids) |did|
                try self.checkDecl(ctx, ast_unit, did);
        }
    }
}

pub fn ensureInterpreter(self: *Checker, ast_unit: *ast.Ast, ctx: *CheckerContext) anyerror!void {
    if (ctx.interp) |_| return;
    const interp_ptr = try self.gpa.create(interpreter.Interpreter);
    var interp_ready = false;
    defer if (!interp_ready) self.gpa.destroy(interp_ptr);
    interp_ptr.* = try interpreter.Interpreter.init(self.gpa, ast_unit, &ctx.symtab, &self.context.compilation_unit);
    interp_ready = true;
    ctx.interp = interp_ptr;
}

/// Walk the AST for `ast_unit`, binding top-level declarations and checking each node.
pub fn runAst(self: *Checker, ast_unit: *ast.Ast, ctx: *CheckerContext) !void {
    try self.ensureInterpreter(ast_unit, ctx);
    try self.predeclare(ast_unit, ctx);

    const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
    for (decl_ids) |did|
        try self.checkDecl(ctx, ast_unit, did);
}

fn predeclare(self: *Checker, ast_unit: *ast.Ast, ctx: *CheckerContext) !void {
    // pre-allocate type slots
    const expr_len: usize = ast_unit.exprs.index.kinds.items.len;
    const decl_len: usize = ast_unit.exprs.Decl.list.len;
    try ast_unit.type_info.expr_types.appendNTimes(self.gpa, null, expr_len);
    try ast_unit.type_info.decl_types.appendNTimes(self.gpa, null, decl_len);

    // Add builtin symbols to the global scope
    _ = try ctx.symtab.push(null);

    const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);

    // (1) Bind all top-level names so forward refs resolve
    for (decl_ids) |did|
        try self.bindDeclPattern(ctx, ast_unit, did);

    // (2) Predeclare signatures for all top-level functions
    for (decl_ids) |did| {
        const decl = ast_unit.exprs.Decl.get(did);
        if (ast_unit.kind(decl.value) == .FunctionLit) {
            try self.predeclareFunction(ctx, ast_unit, did);
        }
    }

    // (2b) Pre-register all methods using their predeclared signatures so that
    // method calls can resolve across declarations and ordering.
    for (decl_ids) |did| {
        const decl = ast_unit.exprs.Decl.get(did);
        if (decl.method_path.isNone()) continue;
        if (ast_unit.kind(decl.value) != .FunctionLit) continue;
        const sig_ty = ast_unit.type_info.decl_types.items[did.toRaw()] orelse self.context.type_store.tAny();
        _ = try self.registerMethodDecl(ctx, ast_unit, did, decl, sig_ty);
    }
}

/// Return the `TypeKind` of `t` using the checker's type store.
pub inline fn typeKind(self: *const Checker, t: types.TypeId) types.TypeKind {
    return self.context.type_store.getKind(t);
}

/// Determine the source location for expression `eid`.
inline fn exprLocFromId(ast_unit: *ast.Ast, eid: ast.ExprId) Loc {
    return switch (ast_unit.kind(eid)) {
        inline else => |x| exprLoc(ast_unit, getExpr(ast_unit, x, eid)),
    };
}

/// Fetch the location stored in `expr` (literal struct/row) within `ast_unit`.
inline fn exprLoc(ast_unit: *ast.Ast, expr: anytype) Loc {
    return ast_unit.exprs.locs.get(expr.loc);
}

/// Retrieve the `StmtRow` of kind `K` for statement `id`.
inline fn getStmt(ast_unit: *ast.Ast, comptime K: ast.StmtKind, id: ast.StmtId) ast.StmtRowT(K) {
    return ast_unit.stmts.get(K, id);
}

/// Resolve an interned string `sid` within `ast_unit`.
pub inline fn getStr(ast_unit: *const ast.Ast, sid: ast.StrId) []const u8 {
    return ast_unit.exprs.strs.get(sid);
}

/// Fetch the expression row of kind `K` identified by `id`.
inline fn getExpr(ast_unit: *ast.Ast, comptime K: ast.ExprKind, id: ast.ExprId) ast.RowT(K) {
    return ast_unit.exprs.get(K, id);
}

pub fn acquireExprIdsScratch(self: *Checker) !*std.ArrayList(ast.ExprId) {
    const idx = self.expr_id_scratch_depth;
    self.expr_id_scratch_depth += 1;
    if (idx == 0) {
        self.expr_id_scratch.clearRetainingCapacity();
        return &self.expr_id_scratch;
    }
    const extra_index = idx - 1;
    if (extra_index >= self.expr_id_scratch_extra.items.len) {
        try self.expr_id_scratch_extra.append(self.gpa, std.ArrayList(ast.ExprId){});
    }
    const scratch = &self.expr_id_scratch_extra.items[extra_index];
    scratch.clearRetainingCapacity();
    return scratch;
}

pub fn releaseExprIdsScratch(self: *Checker) void {
    std.debug.assert(self.expr_id_scratch_depth > 0);
    self.expr_id_scratch_depth -= 1;
}

/// Push a new nested-function permission `v` onto the current context.
fn pushAllowNestedFn(self: *Checker, ctx: *CheckerContext, v: bool) !void {
    try ctx.allow_nested_fn.append(self.gpa, v);
}

/// Pop the most-recent nested-function permission flag.
fn popAllowNestedFn(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.allow_nested_fn.items.len > 0) _ = ctx.allow_nested_fn.pop();
}

/// Test whether nested function literals are currently permitted.
fn isNestedFnAllowed(_: *const Checker, ctx: *CheckerContext) bool {
    if (ctx.allow_nested_fn.items.len == 0) return false;
    return ctx.allow_nested_fn.items[ctx.allow_nested_fn.items.len - 1];
}

/// Evaluate expression `expr` at compile time, caching the result in `ast_unit`.
pub fn evalComptimeExpr(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    expr: ast.ExprId,
    bindings: []const Pipeline.ComptimeBinding,
) anyerror!comp.ComptimeValue {
    // Ensure the interpreter is available for this AST.
    try self.ensureInterpreter(ast_unit, ctx);

    if (ast_unit.type_info.getComptimeValue(expr)) |cached| {
        return comp.cloneComptimeValue(self.gpa, cached.*);
    }

    const interp = ctx.interp.?;

    var alias_bindings: std.ArrayList(interpreter.Binding) = undefined;
    var alias_bindings_init = false;
    defer if (alias_bindings_init) alias_bindings.deinit(self.gpa);

    var has_binding_scope = false;
    var binding_scope: interpreter.Interpreter.BindingScope = undefined;
    defer if (has_binding_scope) binding_scope.deinit();

    if (bindings.len > 0) {
        alias_bindings = std.ArrayList(interpreter.Binding).empty;
        alias_bindings_init = true;
        var alias_success = false;
        defer if (!alias_success) {
            for (alias_bindings.items) |*binding| binding.value.destroy(self.gpa);
        };

        for (bindings) |binding| {
            const binding_value = switch (binding) {
                .type_param => interpreter.Binding{ .name = binding.type_param.name, .value = .{ .Type = binding.type_param.ty } },
                .value_param => blk: {
                    const cloned = try comp.cloneComptimeValue(self.gpa, binding.value_param.value);
                    break :blk interpreter.Binding{ .name = binding.value_param.name, .value = cloned };
                },
            };
            try alias_bindings.append(self.gpa, binding_value);
        }

        binding_scope = try interp.pushBindings(&alias_bindings);
        alias_success = true;
        has_binding_scope = true;
        alias_bindings.clearRetainingCapacity();
    }

    const computed = try interp.evalExpr(expr);
    const stored = try comp.cloneComptimeValue(self.gpa, computed);
    try ast_unit.type_info.setComptimeValue(expr, stored);
    return computed;
}

/// Declare bindings introduced by `d.pattern` (if any) in the current symbol scope.
pub fn bindDeclPattern(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    did: ast.DeclId,
) !void {
    const decl = ast_unit.exprs.Decl.get(did);
    if (decl.pattern.isNone()) return;
    try pattern_matching.declareBindingsInPattern(
        self,
        ctx,
        ast_unit,
        decl.pattern.unwrap(),
        decl.loc,
        .{ .decl = did },
    );
}

/// Register bindings created by a parameter pattern prior to its use.
fn bindParamPattern(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, pid: ast.ParamId, p: ast.Rows.Param) !void {
    if (p.pat.isNone()) return;
    try pattern_matching.declareBindingsInPattern(
        self,
        ctx,
        ast_unit,
        p.pat.unwrap(),
        p.loc,
        .{ .param = pid },
    );
}

/// Push a new function context with the declared result type and purity requirements.
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
        .inferred_result = null,
    });
}
/// Pop the current function context, releasing any locals map.
fn popFunc(self: *Checker, ctx: *CheckerContext) void {
    if (ctx.func_stack.items.len > 0) {
        var context = &ctx.func_stack.items[ctx.func_stack.items.len - 1];
        context.locals.deinit(self.gpa);
        _ = ctx.func_stack.pop();
    }
}
/// Return true when the checker is currently inside a function literal.
fn inFunction(_: *const Checker, ctx: *CheckerContext) bool {
    return ctx.func_stack.items.len > 0;
}
/// Fetch the active function context, if any.
fn currentFunc(_: *const Checker, ctx: *CheckerContext) ?FunctionCtx {
    if (ctx.func_stack.items.len == 0) return null;
    return ctx.func_stack.items[ctx.func_stack.items.len - 1];
}

/// Push loop metadata (label) on entry to a loop.
fn pushLoop(self: *Checker, ctx: *CheckerContext, label: ast.OptStrId) !void {
    try ctx.loop_stack.append(self.gpa, .{ .label = label, .result_ty = null });
}
/// Pop the current loop metadata on exit.
fn popLoop(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.loop_stack.items.len > 0) _ = ctx.loop_stack.pop();
}
/// Return true while inside a loop construct.
fn inLoop(_: *const Checker, ctx: *CheckerContext) bool {
    return ctx.loop_stack.items.len > 0;
}
/// Track the binding created by a loop pattern matched against `subj`.
inline fn pushLoopBinding(self: *Checker, ctx: *CheckerContext, pat: ast.OptPatternId, subj: types.TypeId) !void {
    try ctx.loop_binding_stack.append(self.gpa, .{ .pat = pat, .subject_ty = subj });
}
/// Remove the loop binding once the loop scope ends.
inline fn popLoopBinding(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.loop_binding_stack.items.len > 0) _ = ctx.loop_binding_stack.pop();
}

/// Return the identifier bound by `pid` when it is a simple binding pattern.
fn bindingNameOfPattern(ast_unit: *ast.Ast, pid: ast.PatternId) ?ast.StrId {
    return switch (ast_unit.kind(pid)) {
        .Binding => ast_unit.pats.get(.Binding, pid).name,
        else => null,
    };
}

/// Predeclare the signature of function literal `did` so later calls can resolve against it.
fn predeclareFunction(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    did: ast.DeclId,
) !void {
    const decl = ast_unit.exprs.Decl.get(did);
    std.debug.assert(ast_unit.kind(decl.value) == .FunctionLit);

    const func_id = decl.value;
    const func = getExpr(ast_unit, .FunctionLit, func_id);
    const params = ast_unit.exprs.param_pool.slice(func.params);

    var param_types = try self.gpa.alloc(types.TypeId, params.len);
    defer self.gpa.free(param_types);

    var bindings = List(check_types.Binding){};
    defer bindings.deinit(self.gpa);

    // Parameter types (no pattern checks, no default-value checks here)
    var i: usize = 0;
    while (i < params.len) : (i += 1) {
        const param = ast_unit.exprs.Param.get(params[i]);
        if (!param.ty.isNone()) {
            const res = try check_types.typeFromTypeExprWithBindings(self, ctx, ast_unit, param.ty.unwrap(), bindings.items);
            const pt_or_err = res[1];
            param_types[i] = if (self.typeKind(pt_or_err) == .TypeError)
                self.context.type_store.tAny()
            else
                pt_or_err;

            if (!param.is_comptime) continue;
            if (param.pat.isNone()) continue;

            const pat_id = param.pat.unwrap();
            if (ast_unit.kind(pat_id) == .Binding) {
                const pname = ast_unit.pats.get(.Binding, pat_id).name;
                if (self.typeKind(param_types[i]) == .TypeType) {
                    try bindings.append(self.gpa, .{ .Type = .{
                        .name = pname,
                        .ty = self.context.type_store.tAny(),
                    } });
                }
            }
        } else if (param.is_comptime) {
            param_types[i] = self.context.type_store.mkTypeType(self.context.type_store.tAny());
        } else {
            // Unannotated runtime param – unknown until body checking
            param_types[i] = self.context.type_store.tAny();
        }
    }

    const res_or_err = if (!func.result_ty.isNone())
        (try check_types.typeFromTypeExprWithBindings(self, ctx, ast_unit, func.result_ty.unwrap(), bindings.items))[1]
    else
        self.context.type_store.tVoid();
    if (self.typeKind(res_or_err) == .TypeError) return; // diagnostics already emitted
    const res = res_or_err;

    // Be optimistic about purity here; we’ll finalize after body checking.
    const sig_ty = self.context.type_store.mkFunction(param_types, res, func.flags.is_variadic, true, func.flags.is_extern);

    // Stamp both the decl type and the function literal expr type.
    ast_unit.type_info.decl_types.items[did.toRaw()] = sig_ty;
}

/// Search for the most recent specialization for generic parameter `name`.
pub fn lookupParamSpecialization(_: *const Checker, ctx: *CheckerContext, name: ast.StrId) ?types.TypeId {
    var i: usize = ctx.param_specializations.items.len;
    while (i > 0) {
        i -= 1;
        const spec = ctx.param_specializations.items[i];
        if (spec.name.eq(name)) return spec.ty;
    }
    return null;
}

/// Type check the specialized function literal `id` using parameter overrides `specs`.
pub fn checkSpecializedFunction(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    decl_id: ast.DeclId,
    specs: []const ParamSpecialization,
    snapshot_decl: ?ast.DeclId,
) !types.TypeId {
    const decl = ast_unit.exprs.Decl.get(decl_id);
    std.debug.assert(ast_unit.kind(decl.value) == .FunctionLit);
    const id = decl.value;
    const need_scope = ctx.symtab.stack.items.len == 0;
    if (need_scope) {
        _ = try ctx.symtab.push(null);
        const decl_ids = ast_unit.exprs.decl_pool.slice(ast_unit.unit.decls);
        for (decl_ids) |did| {
            try self.bindDeclPattern(ctx, ast_unit, did);
        }
    }
    defer if (need_scope) ctx.symtab.pop();

    const base_len = ctx.param_specializations.items.len;
    defer ctx.param_specializations.items.len = base_len;
    if (specs.len > 0) try ctx.param_specializations.appendSlice(self.gpa, specs);

    const backup_len = ast_unit.type_info.expr_types.items.len;
    // Clear cached expression types for this function so specializations re-check bodies.
    var expr_ids = try self.acquireExprIdsScratch();
    defer self.releaseExprIdsScratch();
    try check_types.collectDeclExprs(self.gpa, ast_unit, decl_id, expr_ids);
    const ExprTypeEntry = struct {
        index: u32,
        ty: ?types.TypeId,
    };

    var entry_buf = try self.gpa.alloc(ExprTypeEntry, expr_ids.items.len);
    defer self.gpa.free(entry_buf);
    var entry_count: usize = 0;
    for (expr_ids.items) |eid| {
        const raw = eid.toRaw();
        if (raw >= backup_len) continue;
        entry_buf[entry_count] = ExprTypeEntry{ .index = raw, .ty = ast_unit.type_info.expr_types.items[raw] };
        entry_count += 1;
        ast_unit.type_info.expr_types.items[raw] = null;
    }
    defer {
        ast_unit.type_info.expr_types.items.len = backup_len;
        for (entry_buf[0..entry_count]) |entry| {
            ast_unit.type_info.expr_types.items[entry.index] = entry.ty;
        }
    }

    try self.pushAllowNestedFn(ctx, true);
    defer self.popAllowNestedFn(ctx);
    const result_ty = try self.checkFunctionLit(ctx, ast_unit, id);
    if (snapshot_decl) |target_decl| {
        try check_types.storeSpecializationExprTypes(
            self,
            ast_unit,
            expr_ids.items[0..expr_ids.items.len],
            target_decl,
        );
        var call_expr_ids = std.ArrayList(u32){};
        var call_specs = std.ArrayList(types.CallSpecialization){};
        defer {
            call_expr_ids.deinit(self.gpa);
            call_specs.deinit(self.gpa);
        }
        for (expr_ids.items) |eid| {
            const raw = eid.toRaw();
            if (ast_unit.type_info.call_specializations.get(raw)) |spec| {
                try call_expr_ids.append(self.gpa, raw);
                try call_specs.append(self.gpa, spec);
            }
        }
        if (call_expr_ids.items.len != 0) {
            try ast_unit.type_info.storeSpecializationCallSnapshot(target_decl, call_expr_ids.items, call_specs.items);
        }
    }
    return result_ty;
}

/// Retrieve or create a synthetic specialization of `original_decl_id` using `concrete_param_types`.
fn getOrInstantiateSpecialization(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    original_decl_id: ast.DeclId,
    concrete_param_types: []const types.TypeId,
) !ast.DeclId {
    var synthetic_decl_id: ast.DeclId = undefined;
    const lookup_key = types.SpecializationKey{
        .original_decl_id = original_decl_id.toRaw(),
        .param_types = concrete_param_types,
    };

    if (ctx.specialization_cache.get(lookup_key)) |existing| {
        const sig_opt = if (existing.toRaw() < ast_unit.type_info.decl_types.items.len)
            ast_unit.type_info.decl_types.items[existing.toRaw()]
        else
            null;
        const needs_refresh = blk: {
            if (sig_opt) |sig| {
                if (self.context.type_store.getKind(sig) == .Function) {
                    const fr = self.context.type_store.get(.Function, sig);
                    const rk = self.typeKind(fr.result);
                    if (rk == .Any) break :blk true;
                    if (rk == .TypeType) {
                        const of = self.context.type_store.get(.TypeType, fr.result).of;
                        if (self.typeKind(of) == .Any) break :blk true;
                    }
                }
            } else break :blk true;
            break :blk false;
        };
        if (!needs_refresh) return existing;
        synthetic_decl_id = existing;
    } else {
        const new_slot_index = ast_unit.type_info.decl_types.items.len;
        try ast_unit.type_info.decl_types.append(self.gpa, null);
        synthetic_decl_id = ast.DeclId.fromRaw(@intCast(new_slot_index));

        const params_dup = try self.gpa.dupe(types.TypeId, concrete_param_types);
        var params_owned = true;
        errdefer if (params_owned) self.gpa.free(params_dup);

        const key = types.SpecializationKey{
            .original_decl_id = original_decl_id.toRaw(),
            .param_types = params_dup,
        };
        errdefer if (!params_owned) {
            if (ctx.specialization_cache.fetchRemove(key)) |kv| {
                self.gpa.free(kv.key.param_types);
            }
        };

        const gop = try ctx.specialization_cache.getOrPut(self.gpa, key);
        if (gop.found_existing) {
            self.gpa.free(params_dup);
            return gop.value_ptr.*;
        }
        params_owned = false;
        gop.value_ptr.* = synthetic_decl_id;

        try ast_unit.type_info.synthetic_decls.append(self.gpa, synthetic_decl_id.toRaw());
    }

    const original_decl = ast_unit.exprs.Decl.get(original_decl_id);
    if (ast_unit.kind(original_decl.value) != .FunctionLit) return synthetic_decl_id;

    var specs = std.ArrayList(ParamSpecialization){};
    defer specs.deinit(self.gpa);
    const fn_lit = ast_unit.exprs.get(.FunctionLit, original_decl.value);
    const params = ast_unit.exprs.param_pool.slice(fn_lit.params);
    var i: usize = 0;
    while (i < params.len and i < concrete_param_types.len) : (i += 1) {
        const p = ast_unit.exprs.Param.get(params[i]);
        if (p.pat.isNone()) continue;
        if (bindingNameOfPattern(ast_unit, p.pat.unwrap())) |name| {
            try specs.append(self.gpa, .{ .name = name, .ty = concrete_param_types[i] });
        }
    }

    const fn_type = try self.checkSpecializedFunction(ctx, ast_unit, original_decl_id, specs.items, synthetic_decl_id);
    const fn_row_checked = self.context.type_store.get(.Function, fn_type);
    const new_sig = self.context.type_store.mkFunction(
        concrete_param_types,
        fn_row_checked.result,
        fn_row_checked.is_variadic,
        fn_row_checked.is_pure,
        fn_row_checked.is_extern,
    );
    ast_unit.type_info.decl_types.items[synthetic_decl_id.toRaw()] = new_sig;

    return synthetic_decl_id;
}

/// Track a match binding introduced by `pat` for the current subject type.
pub inline fn pushMatchBinding(self: *Checker, ctx: *CheckerContext, pat: ast.PatternId, subj: types.TypeId) !void {
    try ctx.match_binding_stack.append(self.gpa, .{ .pat = pat, .subject_ty = subj });
}
/// Remove the most-recent match binding when leaving the match scope.
pub inline fn popMatchBinding(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.match_binding_stack.items.len > 0) _ = ctx.match_binding_stack.pop();
}

/// Push a catch handler binding named `name` with type `ty`.
inline fn pushCatchBinding(self: *Checker, ctx: *CheckerContext, name: ast.StrId, ty: types.TypeId) !void {
    try ctx.catch_binding_stack.append(self.gpa, .{ .name = name, .ty = ty });
}
/// Drop the latest catch binding on scope exit.
inline fn popCatchBinding(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.catch_binding_stack.items.len > 0) _ = ctx.catch_binding_stack.pop();
}

/// Lookup the type previously bound to `name` by an active catch context.
inline fn bindingTypeFromActiveCatches(_: *Checker, ctx: *CheckerContext, name: ast.StrId) ?types.TypeId {
    var i: isize = @as(isize, @intCast(ctx.catch_binding_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const context = ctx.catch_binding_stack.items[@intCast(i)];
        if (context.name.eq(name)) return context.ty;
    }
    return null;
}

/// Walk active match bindings to find the type bound to `name`.
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

/// Walk the loop binding stack to find a binding for `name`.
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

/// Record whether the next expressions must produce a value (true => value required).
fn pushValueReq(self: *Checker, ctx: *CheckerContext, v: bool) !void {
    try ctx.value_ctx.append(self.gpa, v);
}
/// Restore the previous value requirement flag.
fn popValueReq(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.value_ctx.items.len > 0) _ = ctx.value_ctx.pop();
}
/// Test whether values are required in the current checking context.
pub fn isValueReq(_: *const Checker, ctx: *CheckerContext) bool {
    if (ctx.value_ctx.items.len == 0) return true; // default: value required
    return ctx.value_ctx.items[ctx.value_ctx.items.len - 1];
}

/// Push an expected type onto the stack.
fn pushExpectedType(self: *Checker, ctx: *CheckerContext, ty: ?types.TypeId) !void {
    try ctx.expected_ty_stack.append(self.gpa, ty);
}
/// Pop the expected type from the stack.
fn popExpectedType(_: *Checker, ctx: *CheckerContext) void {
    if (ctx.expected_ty_stack.items.len > 0) _ = ctx.expected_ty_stack.pop();
}
/// Get the current expected type, if any.
pub fn getExpectedType(_: *const Checker, ctx: *CheckerContext) ?types.TypeId {
    if (ctx.expected_ty_stack.items.len == 0) return null;
    return ctx.expected_ty_stack.items[ctx.expected_ty_stack.items.len - 1];
}

/// Lookup symbol `name` in the current scope.
pub fn lookup(_: *Checker, ctx: *CheckerContext, name: ast.StrId) ?symbols.SymbolId {
    return ctx.symtab.lookup(ctx.symtab.currentId(), name);
}

/// Return the `LoopCtx` matching `opt_label`, defaulting to the innermost loop.
fn loopCtxForLabel(_: *Checker, ctx: *CheckerContext, opt_label: ast.OptStrId) ?*LoopCtx {
    if (ctx.loop_stack.items.len == 0) return null;
    const want: ?u32 = if (!opt_label.isNone()) opt_label.unwrap().toRaw() else null;
    var i: isize = @as(isize, @intCast(ctx.loop_stack.items.len)) - 1;
    while (i >= 0) : (i -= 1) {
        const idx: usize = @intCast(i);
        const lc = &ctx.loop_stack.items[idx];
        if (want == null) return lc;
        if (!lc.label.isNone() and lc.label.unwrap().eq(ast.StrId.fromRaw(want.?))) return lc;
    }
    return null;
}

// =========================================================
// Declarations & Statements
// =========================================================
/// Type-check the declaration `decl_id`, including its initializer and patterns.
pub fn checkDecl(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, decl_id: ast.DeclId) !void {
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

    // Method registration happens in runAst() pre-pass for top-level methods.

    // Initializers must be evaluated in value context even inside statement blocks
    try self.pushValueReq(ctx, true);
    var pushed_nested = false;
    if (self.inFunction(ctx) and !decl.method_path.isNone() and ast_unit.kind(decl.value) == .FunctionLit) {
        try self.pushAllowNestedFn(ctx, true);
        pushed_nested = true;
    }
    try self.pushExpectedType(ctx, expect_ty);
    var rhs_ty = try self.checkExpr(ctx, ast_unit, decl.value);
    self.popExpectedType(ctx);
    if (pushed_nested) self.popAllowNestedFn(ctx);
    self.popValueReq(ctx);

    if (self.typeKind(rhs_ty) == .TypeError) return;

    if (self.inFunction(ctx) and !decl.method_path.isNone() and ast_unit.kind(decl.value) == .FunctionLit) {
        _ = try self.registerMethodDecl(ctx, ast_unit, decl_id, decl, rhs_ty);
    }

    // Try to coerce value type to expected type (if any)
    try self.tryTypeCoercion(ctx, ast_unit, decl_id, rhs_ty, expect_ty);

    // If LHS is a pattern, ensure the RHS type matches the pattern's shape.
    if (!decl.pattern.isNone()) {
        const shape_ok = pattern_matching.checkPatternShapeForDecl(self, ast_unit, decl.pattern.unwrap(), rhs_ty);
        switch (shape_ok) {
            .ok => {},
            .tuple_arity_mismatch => {
                const pat_len = tuplePatternLength(ast_unit, decl.pattern.unwrap());
                const val_len = tupleTypeLength(self, rhs_ty);
                try self.context.diags.addError(
                    exprLoc(ast_unit, decl),
                    .tuple_arity_mismatch,
                    .{ @as(i64, @intCast(pat_len)), @as(i64, @intCast(val_len)) },
                );
                return;
            },
            .struct_pattern_field_mismatch => {
                const field_name = structPatternFieldName(ast_unit, decl.pattern.unwrap());
                const field_str = if (field_name) |name| ast_unit.exprs.strs.get(name) else "struct field";
                try self.context.diags.addError(
                    exprLoc(ast_unit, decl),
                    .struct_pattern_field_mismatch,
                    StringPayload{ .value = field_str },
                );
                return;
            },
            .pattern_shape_mismatch => {
                try self.context.diags.addError(
                    exprLoc(ast_unit, decl),
                    .pattern_shape_mismatch,
                    StringPayload{ .value = "pattern shape mismatch" },
                );
                return;
            },
        }
    }

    if (!decl.pattern.isNone()) {
        const pat_id = decl.pattern.unwrap();
        if (ast_unit.kind(pat_id) == .Binding) {
            const binding = ast_unit.pats.get(.Binding, pat_id);
            var binding_ty = if (expect_ty) |et| et else rhs_ty;
            var stored = self.evalComptimeExpr(ctx, ast_unit, decl.value, &[_]Pipeline.ComptimeBinding{}) catch null;
            if (stored) |*value| {
                // If this binding represents `type` and we evaluated a concrete type, refine away `any`.
                if (self.typeKind(binding_ty) == .TypeType) {
                    const tt = self.context.type_store.get(.TypeType, binding_ty);
                    if (self.typeKind(tt.of) == .Any and value.* == .Type) {
                        binding_ty = self.context.type_store.mkTypeType(value.Type);
                        rhs_ty = binding_ty;
                        ast_unit.type_info.decl_types.items[decl_id.toRaw()] = binding_ty;
                        ast_unit.type_info.expr_types.items[decl.value.toRaw()] = binding_ty;
                    }
                }

                const binding_clone = try comp.cloneComptimeValue(self.gpa, stored.?);
                try ast_unit.type_info.setComptimeBinding(binding.name, binding_ty, binding_clone);
                if (ctx.interp) |interp| {
                    var interp_clone = try comp.cloneComptimeValue(self.gpa, stored.?);
                    interp.setBinding(binding.name, interp_clone) catch |err| {
                        interp_clone.destroy(self.gpa);
                        value.destroy(self.gpa);
                        return err;
                    };
                }
                value.destroy(self.gpa);
            }
        }
    }

    // Method registration happens in runAst pre-pass; avoid re-registering here.

    // Record exports for top-level bindings only (not inside functions).
    if (!self.inFunction(ctx)) {
        // Prefer finalized decl type if present (post-coercion), otherwise use rhs type.
        const final_rhs_ty =
            if (ast_unit.type_info.decl_types.items[decl_id.toRaw()]) |t| t else rhs_ty;
        try self.recordExportsForDecl(ctx, ast_unit, decl_id, final_rhs_ty);
    }
}

fn tuplePatternLength(ast_unit: *ast.Ast, pat_id: ast.PatternId) usize {
    if (ast_unit.kind(pat_id) != .Tuple) return 0;
    const tp = ast_unit.pats.get(.Tuple, pat_id);
    return ast_unit.pats.pat_pool.slice(tp.elems).len;
}

fn tupleTypeLength(self: *Checker, ty: types.TypeId) usize {
    if (self.typeKind(ty) != .Tuple) return 0;
    const tup = self.context.type_store.get(.Tuple, ty);
    return self.context.type_store.type_pool.slice(tup.elems).len;
}

fn structPatternFieldName(ast_unit: *ast.Ast, pat_id: ast.PatternId) ?ast.StrId {
    if (ast_unit.kind(pat_id) != .Struct) return null;
    const sp = ast_unit.pats.get(.Struct, pat_id);
    const fields = ast_unit.pats.field_pool.slice(sp.fields);
    if (fields.len == 0) return null;
    return ast_unit.pats.StructField.get(fields[0]).name;
}

/// Record exported bindings produced by `decl_id` with runtime type `value_ty`.
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
                try ast_unit.type_info.addExport(nm, bty, decl_id);
            }
        }
        break;
    }
}

fn ensureMethodIsFunction(
    self: *Checker,
    ast_unit: *ast.Ast,
    decl: ast.Rows.Decl,
    func_ty_id: types.TypeId,
) !bool {
    const loc = exprLoc(ast_unit, decl);

    if (self.typeKind(func_ty_id) != .Function or ast_unit.kind(decl.value) != .FunctionLit) {
        try self.context.diags.addError(loc, .method_requires_function_value, .{});
        return false;
    }

    return true;
}

fn resolveOwnerType(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    owner_seg: ast.Rows.MethodPathSeg,
    out_owner_ty: *types.TypeId,
) !bool {
    const owner_loc = ast_unit.exprs.locs.get(owner_seg.loc);

    const owner_sym_id = self.lookup(ctx, owner_seg.name) orelse {
        const owner_name = ast_unit.exprs.strs.get(owner_seg.name);
        try self.context.diags.addError(
            owner_loc,
            .undefined_identifier,
            .{owner_name},
        );
        return false;
    };

    const owner_sym = ctx.symtab.syms.get(owner_sym_id);
    if (owner_sym.origin_decl.isNone()) {
        const owner_name = ast_unit.exprs.strs.get(owner_seg.name);
        try self.context.diags.addError(
            owner_loc,
            .method_owner_not_struct,
            StringPayload{ .value = owner_name },
        );
        return false;
    }

    const owner_decl_id = owner_sym.origin_decl.unwrap();

    var owner_ty: types.TypeId = if (ast_unit.type_info.decl_types.items[owner_decl_id.toRaw()]) |t|
        t
    else blk: {
        const owner_decl = ast_unit.exprs.Decl.get(owner_decl_id);
        const ty = try self.checkExpr(ctx, ast_unit, owner_decl.value);
        if (self.typeKind(ty) == .TypeError) return false;
        ast_unit.type_info.decl_types.items[owner_decl_id.toRaw()] = ty;
        break :blk ty;
    };

    // If we got a `TypeType`, use its underlying `of` type.
    if (self.typeKind(owner_ty) == .TypeType) {
        owner_ty = self.context.type_store.get(.TypeType, owner_ty).of;
    }

    switch (self.typeKind(owner_ty)) {
        .Struct, .Union, .Enum, .Variant, .Error => {},
        else => {
            try self.context.diags.addError(
                owner_loc,
                .method_owner_not_struct,
                .{owner_ty},
            );
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
    std.debug.assert(params.len == func_params.len);

    if (params.len == 0) {
        // No parameters -> no implicit receiver. This is allowed.
        return true;
    }

    const first_param = ast_unit.exprs.Param.get(params[0]);
    const param_loc = ast_unit.exprs.locs.get(first_param.loc);

    // Detect `self` binding in the first parameter pattern.
    var is_self_binding = false;
    if (!first_param.pat.isNone()) {
        const pat_id = first_param.pat.unwrap();
        if (ast_unit.kind(pat_id) == .Binding) {
            const binding = ast_unit.pats.get(.Binding, pat_id);
            if (std.mem.eql(u8, getStr(ast_unit, binding.name), "self")) {
                is_self_binding = true;
            }
        }
    }

    if (!is_self_binding) {
        // No `self` -> leave receiver_kind = .none, self_param_type = null.
        return true;
    }

    if (first_param.ty.isNone()) {
        try self.context.diags.addError(
            param_loc,
            .method_self_requires_type,
            .{},
        );
        return false;
    }

    const self_param_ty = func_params[0];
    const self_param_kind = self.typeKind(self_param_ty);

    switch (self_param_kind) {
        .Ptr => {
            const ptr_row = self.context.type_store.get(.Ptr, self_param_ty);
            if (!ptr_row.elem.eq(owner_ty)) {
                try self.context.diags.addError(
                    param_loc,
                    .method_self_type_mismatch,
                    .{ self_param_ty, owner_ty },
                );
                return false;
            }

            receiver_kind_out.* = if (ptr_row.is_const)
                .pointer_const
            else
                .pointer;
        },
        else => {
            if (!self_param_ty.eq(owner_ty)) {
                try self.context.diags.addError(
                    param_loc,
                    .method_self_type_mismatch,
                    .{ self_param_ty, owner_ty },
                );
                return false;
            }

            receiver_kind_out.* = .value;
        },
    }

    self_param_type_out.* = self_param_ty;
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
    const seg_range = decl.method_path.asRange();
    const seg_ids = ast_unit.exprs.method_path_pool.slice(seg_range);
    if (seg_ids.len < 2) return false;

    const owner_seg = ast_unit.exprs.MethodPathSeg.get(seg_ids[0]);

    // For now we only allow `Owner.method`.
    if (seg_ids.len != 2) {
        try self.context.diags.addError(
            ast_unit.exprs.locs.get(owner_seg.loc),
            .method_invalid_owner_path,
            .{},
        );
        return false;
    }

    const method_seg = ast_unit.exprs.MethodPathSeg.get(seg_ids[seg_ids.len - 1]);

    // Resolve owner type.
    var owner_ty: types.TypeId = undefined;
    if (!try self.resolveOwnerType(ctx, ast_unit, owner_seg, &owner_ty)) {
        return false;
    }

    // Check value is a function and expression is a function literal.
    if (!try self.ensureMethodIsFunction(ast_unit, decl, func_ty_id)) {
        return false;
    }

    // Extract function literal + parameter types.
    const fn_lit = getExpr(ast_unit, .FunctionLit, decl.value);
    const func_ty = self.context.type_store.get(.Function, func_ty_id);
    const func_params = self.context.type_store.type_pool.slice(func_ty.params);

    // Analyze optional `self` parameter.
    var receiver_kind: types.MethodReceiverKind = .none;
    var self_param_type_opt: ?types.TypeId = null;

    if (!try self.analyzeSelfParam(
        ast_unit,
        owner_ty,
        fn_lit,
        func_params,
        &receiver_kind,
        &self_param_type_opt,
    )) {
        return false;
    }

    // Build the method entry.
    const entry: types.MethodEntry = .{
        .owner_type = owner_ty,
        .method_name = method_seg.name,
        .decl_id = decl_id,
        .decl_ast = ast_unit,
        .func_expr = decl.value,
        .func_type = func_ty_id,
        .self_param_type = self_param_type_opt,
        .receiver_kind = receiver_kind,
        .builtin = null,
    };

    // Check for duplicate methods on this type.
    if (self.context.type_store.getMethod(owner_ty, method_seg.name)) |existing| {
        if (!existing.decl_id.eq(decl_id)) {
            try self.context.diags.addError(
                ast_unit.exprs.locs.get(method_seg.loc),
                .duplicate_method_on_type,
                .{getStr(ast_unit, method_seg.name)},
            );
            return false;
        }
    }

    // Store the method and its expression types.
    try self.context.type_store.putMethod(entry);
    try check_types.storeMethodExprTypes(self, ast_unit, owner_ty, method_seg.name, decl.value);

    return true;
}

/// Diagnostics representing why `got` cannot be assigned to `expect`.
const AssignErrors = union(enum) {
    /// Source array has the wrong length for target array.
    array_length_mismatch,
    /// Tuple arity differs from expected target arity.
    tuple_arity_mismatch,
    /// `null` assigned to non-optional target.
    assign_null_to_non_optional,
    /// Pointer element types differ.
    pointer_type_mismatch,
    /// Pointer const-correctness violated.
    pointer_constness_violation,
    /// Slice loses const qualifier during assignment.
    slice_constness_violation,
    /// Expected an array type but got something else.
    expected_array_type,
    /// Expected a tuple type but got something else.
    expected_tuple_type,
    /// Expected a map type but got something else.
    expected_map_type,
    /// Expected a pointer type but got something else.
    expected_pointer_type,
    /// Expected integer kind but didn't find one.
    expected_integer_type,
    /// Expected float kind but got another type.
    expected_float_type,
    /// Expected enum type mismatch.
    expected_enum_type,
    /// Map key type mismatch.
    map_wrong_key_type,
    /// Expected a literal type but got a value.
    type_value_mismatch,
    /// Null assigned where `noreturn` expected.
    noreturn_not_storable,
    /// Expected struct target but type differs.
    expected_struct_type,
    /// Struct declared fewer fields than provided.
    struct_field_count_mismatch,
    /// Struct literal refers to an unknown field.
    unknown_struct_field,
    /// Struct field names don't align.
    struct_field_name_mismatch,
    /// Union literal sets more than one field.
    union_literal_multiple_fields,
    /// Union literal leaves no field set.
    union_empty_literal,
    /// Expected a tensor type but got different kind.
    expected_tensor_type,
    /// Tensor ranks differ.
    tensor_rank_mismatch,
    /// Tensor dimensions mismatch.
    tensor_dimension_mismatch,
    /// Tensor element type mismatch.
    tensor_element_type_mismatch,
    /// Struct field type mismatch with indexes for diagnostics.
    struct_field_type_mismatch: struct { index: usize, tag_index: usize },
    /// General failure when no other case matched.
    failure,
    /// Assignment succeeded.
    success,
};

fn assignableSlice(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const expected_ty = self.context.type_store.get(.Slice, expect);
    const got_kind = self.typeKind(got);

    switch (got_kind) {
        .Slice => {
            const got_ty = self.context.type_store.get(.Slice, got);
            if (!expected_ty.is_const and got_ty.is_const) {
                return .slice_constness_violation;
            }
            return self.assignable(got_ty.elem, expected_ty.elem);
        },
        .Array => {
            const got_ty = self.context.type_store.get(.Array, got);
            return self.assignable(got_ty.elem, expected_ty.elem);
        },
        .DynArray => {
            const got_ty = self.context.type_store.get(.DynArray, got);
            return self.assignable(got_ty.elem, expected_ty.elem);
        },
        else => return .failure,
    }
}

fn assignableArray(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const got_kind = self.typeKind(got);
    if (got_kind != .Array) return .expected_array_type;

    const expected_ty = self.context.type_store.get(.Array, expect);
    const got_ty = self.context.type_store.get(.Array, got);
    const elem_ok = self.assignable(got_ty.elem, expected_ty.elem);
    if (got_ty.len != expected_ty.len) return .array_length_mismatch;
    return elem_ok;
}

fn assignableDynArray(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    // BUGFIX: allow assigning from DynArray itself AND from Array/Slice (element-compatible).
    const expected_ty = self.context.type_store.get(.DynArray, expect);
    const got_kind = self.typeKind(got);

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
}

fn assignableTuple(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const got_kind = self.typeKind(got);
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
}

fn assignableMap(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const got_kind = self.typeKind(got);

    // Allow "empty array" sugar to coerce to any map type.
    if (got_kind == .Array) {
        const got_ty = self.context.type_store.get(.Array, got);
        if (got_ty.len != 0) return .expected_map_type;
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
}

fn assignableSimd(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const expected_ty = self.context.type_store.get(.Simd, expect);
    const got_kind = self.typeKind(got);

    switch (got_kind) {
        .Simd => {
            const got_ty = self.context.type_store.get(.Simd, got);
            if (got_ty.lanes != expected_ty.lanes) return .array_length_mismatch;
            return self.assignable(got_ty.elem, expected_ty.elem);
        },
        .Array => {
            const got_ty = self.context.type_store.get(.Array, got);
            if (got_ty.len != expected_ty.lanes) return .array_length_mismatch;
            return self.assignable(got_ty.elem, expected_ty.elem);
        },
        else => return .failure,
    }
}

fn assignableTensor(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const expected_ty = self.context.type_store.get(.Tensor, expect);
    const expected_rank: usize = @intCast(expected_ty.rank);
    const got_kind = self.typeKind(got);

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
                dims_buf[rank] = arr.len;
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
    const got_kind = self.typeKind(got);
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
    const got_kind = self.typeKind(got);
    if (got_kind != .Struct) return .expected_struct_type;

    const expected_ty = self.context.type_store.get(.Union, expect);
    const got_ty = self.context.type_store.get(.Struct, got);

    const expected_fields = self.context.type_store.field_pool.slice(expected_ty.fields);
    const got_fields = self.context.type_store.field_pool.slice(got_ty.fields);

    // Should only have one field set in union
    if (got_fields.len == 0) return .union_empty_literal;
    if (got_fields.len != 1) return .union_literal_multiple_fields;

    const gf = self.context.type_store.Field.get(got_fields[0]);

    const match = self.findFieldByName(expected_fields, gf.name) orelse {
        return .unknown_struct_field;
    };

    const res = self.assignable(gf.ty, match.field.ty);
    if (res != .success) return res;

    return .success;
}

fn assignableStruct(self: *Checker, got: types.TypeId, expect: types.TypeId) AssignErrors {
    const got_kind = self.typeKind(got);
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

        const match = self.findFieldByName(got_fields, ef.name) orelse
            return .struct_field_name_mismatch;

        const res = self.assignable(match.field.ty, ef.ty);
        if (res != .success) {
            return .{ .struct_field_type_mismatch = .{
                .index = match.index,
                .tag_index = @intFromEnum(res),
            } };
        }
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
        .Slice => return self.assignableSlice(got, expect),
        .Array => return self.assignableArray(got, expect),
        .DynArray => return self.assignableDynArray(got, expect),
        .Tuple => return self.assignableTuple(got, expect),
        .Map => return self.assignableMap(got, expect),
        .Simd => return self.assignableSimd(got, expect),
        .Tensor => return self.assignableTensor(got, expect),
        .Optional => return self.assignableOptional(got, expect),
        .Ptr => return self.assignablePtr(got, expect),
        .TypeType => {
            if (got_kind != .TypeType) return .type_value_mismatch;
            return .success;
        },
        .Noreturn => return .noreturn_not_storable,
        .Union => return self.assignableUnion(got, expect),
        .Struct => return self.assignableStruct(got, expect),
        .Enum => {
            if (got_kind != .Enum) return .expected_enum_type;
            if (!got.eq(expect)) return .failure;
            return .success;
        },
        .Function => {
            if (got_kind != .Function) return .failure;
            // Keeping existing behavior: functions are assignable if both are .Function.
            // (Detailed param/result checking is commented out in original.)
            return .success;
        },
        .ErrorSet => return self.assignableErrorSet(got, expect),
        .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .Usize => return self.assignableInteger(got),
        .F32, .F64 => return self.assignableFloat(got),
        else => {},
    }
    return .failure;
}

/// Infer the declaration type using `rhs_ty` when no annotation is provided.
fn typeInferFromRHS(self: *Checker, ast_unit: *ast.Ast, decl_id: ast.DeclId, rhs_ty: types.TypeId) !void {
    const decl = ast_unit.exprs.Decl.get(decl_id);
    // Degenerate cases where we don't infer from RHS
    const rhs_kind = self.typeKind(rhs_ty);
    switch (rhs_kind) {
        .Array => {
            const arr = self.context.type_store.get(.Array, rhs_ty);
            if (arr.len == 0)
                try self.context.diags.addError(
                    exprLoc(ast_unit, ast_unit.exprs.Decl.get(decl_id)),
                    .cannot_infer_type_from_empty_array,
                    .{},
                );
        },
        .Optional => {
            const opt = self.context.type_store.get(.Optional, rhs_ty);
            if (self.typeKind(opt.elem) == .Any) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, ast_unit.exprs.Decl.get(decl_id)),
                    .cannot_infer_type_from_null,
                    .{},
                );
            } else {
                ast_unit.type_info.decl_types.items[decl_id.toRaw()] = rhs_ty;
                ast_unit.type_info.expr_types.items[decl.value.toRaw()] = rhs_ty;
            }
        },
        else => {
            ast_unit.type_info.decl_types.items[decl_id.toRaw()] = rhs_ty;
            ast_unit.type_info.expr_types.items[decl.value.toRaw()] = rhs_ty;
        },
    }
}

/// Update literal `expr_id` to `target_ty` when numeric coercion succeeds.
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
/// Kind of compile-time numeric expression (int or float).
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
fn tryCoerceVariantOrErrorLiteral(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    expr_id: ast.ExprId,
    expect_ty: types.TypeId,
) !bool {
    return switch (ast_unit.kind(expr_id)) {
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

/// Try to coerce call-like expressions that target a variant/error case payload.
fn tryCoerceCallLike(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    call_like: *const ast.Rows.Call,
    expect_ty: types.TypeId,
) !bool {
    var cur = call_like.callee;
    var last: ?ast.StrId = null;
    while (ast_unit.kind(cur) == .FieldAccess) {
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

/// Try to coerce struct literal `sl` to the payload type of `expect_ty`.
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
    while (ast_unit.kind(cur) == .FieldAccess) {
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

/// Look up the payload type for case `lname` inside the variant/error `expect_ty`.
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

/// Verify that call arguments match the payload `pay_ty`.
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

/// Verify that struct literal `sl` matches the payload struct type `pay_ty`.
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

/// Attempt to coerce the RHS type `rhs_ty` to `expect_ty` for declaration `decl_id`.
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

    // If that failed, see if we're assigning null to an optional
    if (is_assignable == .failure) {
        if (self.tryCoerceNullLiteral(ast_unit, decl.value, expect_ty.?)) {
            is_assignable = .success;
        }
    }

    // Apply result (and corresponding diagnostics).
    switch (is_assignable) {
        .success => {
            // Use expected type and also update RHS expr type for consistency.
            ast_unit.type_info.decl_types.items[decl_id.toRaw()] = expect_ty.?;
            ast_unit.type_info.expr_types.items[decl.value.toRaw()] = expect_ty.?;
        },
        .failure => try self.context.diags.addError(
            exprLoc(ast_unit, decl),
            .type_annotation_mismatch,
            .{ expect_ty.?, current_rhs_ty },
        ),
        inline else => |_, x| {
            const diag_code = @field(diag.DiagnosticCode, @tagName(x));
            try self.context.diags.addError(exprLoc(ast_unit, decl), diag_code, .{});
        },
    }
}

/// Validate the assignment statement `stmt`, handling destructuring and coercions.
fn checkAssign(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    stmt: *const ast.StmtRows.Assign,
) !void {
    // Handle `_ = rhs` as a special discard operation.
    if (ast_unit.kind(stmt.left) == .Ident) {
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
    const lkind = ast_unit.kind(stmt.left);
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
        var rt = try self.checkExpr(ctx, ast_unit, stmt.right);
        self.popValueReq(ctx);

        if (self.tryCoerceNullLiteral(ast_unit, stmt.right, lt)) {
            ast_unit.type_info.expr_types.items[stmt.right.toRaw()] = lt;
            rt = lt;
        }

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
                    try self.context.diags.addError(
                        exprLoc(ast_unit, stmt),
                        .type_annotation_mismatch,
                        .{ expected, value_ty },
                    );
                }
            }
        }
    }
    // Purity: assignment writes inside pure functions are allowed only to locals
    if (self.inFunction(ctx) and self.currentFunc(ctx).?.require_pure) {
        switch (self.lvalueRootKind(ctx, ast_unit, stmt.left)) {
            .LocalDecl => {},
            .Param, .NonLocalDecl, .Unknown => {
                try self.context.diags.addError(
                    exprLoc(ast_unit, stmt),
                    .purity_violation,
                    StringPayload{ .value = "assignment touches non-local" },
                );
                ctx.func_stack.items[ctx.func_stack.items.len - 1].pure = false;
            },
        }
    }
}

/// Type-check statement `sid`, returning the resulting type (usually void).
fn checkStmt(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, sid: ast.StmtId) !types.TypeId {
    switch (ast_unit.kind(sid)) {
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
/// Type-check expression `id` while caching the result in `ast_unit.type_info`.
pub fn checkExpr(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) anyerror!types.TypeId {
    if (ast_unit.type_info.expr_types.items[id.toRaw()]) |cached| return cached;

    const tid: types.TypeId = switch (ast_unit.kind(id)) {
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
            const result_ty = try self.checkExpr(ctx, ast_unit, cb.block);
            var computed = try self.evalComptimeExpr(ctx, ast_unit, cb.block, &[_]Pipeline.ComptimeBinding{});
            computed.destroy(self.gpa);
            return result_ty;
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
        .NullLit => blk: {
            if (self.getExpectedType(ctx)) |expect| {
                if (self.typeKind(expect) == .Optional) break :blk expect;
            }
            break :blk self.context.type_store.mkOptional(self.context.type_store.tAny());
        },

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

/// Determine the declared type for literal expression `id`.
fn checkLiteral(self: *Checker, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const lit = getExpr(ast_unit, .Literal, id);
    return switch (lit.kind) {
        .int => blk: {
            const info = switch (lit.data) {
                .int => |int_info| int_info,
                else => return self.context.type_store.tTypeError(),
            };
            const literal_text = self.context.interner.get(info.text);
            if (!info.valid) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, lit),
                    .invalid_integer_literal,
                    StringPayload{ .value = literal_text },
                );
                return self.context.type_store.tTypeError();
            }
            const max_i64: u128 = @intCast(std.math.maxInt(i64));
            if (info.value > max_i64) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, lit),
                    .invalid_integer_literal,
                    StringPayload{ .value = literal_text },
                );
                return self.context.type_store.tTypeError();
            }
            break :blk self.context.type_store.tI64();
        },
        .imaginary => blk: {
            const info = switch (lit.data) {
                .imaginary => |imag| imag,
                else => return self.context.type_store.tTypeError(),
            };
            const literal_text = getStr(ast_unit, info.text);
            if (!info.valid) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, lit),
                    .invalid_imaginary_literal,
                    StringPayload{ .value = literal_text },
                );
                return self.context.type_store.tTypeError();
            }
            const text = literal_text;
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
            const literal_text = self.context.interner.get(info.text);
            if (!info.valid) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, lit),
                    .invalid_float_literal,
                    StringPayload{ .value = literal_text },
                );
                return self.context.type_store.tTypeError();
            }
            break :blk self.context.type_store.tF64();
        },
        .bool => self.context.type_store.tBool(),
        .string => self.context.type_store.tString(),
        .char => self.context.type_store.tU32(),
    };
}
/// Resolve identifier `id` to its type by looking up scopes/patterns.
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
                var rhs_ty = blk: {
                    if (ast_unit.type_info.expr_types.items[drow.value.toRaw()]) |t| break :blk t;
                    if (ast_unit.type_info.decl_types.items[did.toRaw()]) |t| break :blk t;
                    // Fallback: check rhs now
                    break :blk try self.checkExpr(ctx, ast_unit, drow.value);
                };
                if (ast_unit.kind(drow.pattern.unwrap()) == .Binding) {
                    if (self.typeKind(rhs_ty) == .TypeType) {
                        const tt = self.context.type_store.get(.TypeType, rhs_ty);
                        if (self.typeKind(tt.of) == .Any) {
                            const type_res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, drow.value);
                            if (type_res[0] and self.typeKind(type_res[1]) != .TypeError) {
                                rhs_ty = self.context.type_store.mkTypeType(type_res[1]);
                                ast_unit.type_info.decl_types.items[did.toRaw()] = rhs_ty;
                                ast_unit.type_info.expr_types.items[drow.value.toRaw()] = rhs_ty;
                            }
                        }
                    }
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
                var pt = res[1];
                if (self.typeKind(pt) == .Any) {
                    if (self.lookupParamSpecialization(ctx, row.name)) |override_ty| {
                        pt = override_ty;
                    }
                }
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

    const ident_name = ast_unit.exprs.strs.get(row.name);
    const last_diag_idx = self.context.diags.count();
    try self.context.diags.addError(exprLoc(ast_unit, row), .undefined_identifier, .{ident_name});

    // --- "Did you mean?" suggestion logic ---
    var best_suggestion: ?[]const u8 = null;
    var min_dist: usize = 3; // Keep threshold low to avoid bad suggestions

    var seen_names = std.ArrayList(ast.StrId){};
    defer seen_names.deinit(self.gpa);

    var current_scope_id: ?symbols.ScopeId = ctx.symtab.currentId();
    while (current_scope_id) |scope_id| {
        const scope = ctx.symtab.scopes.get(scope_id);

        const pool_ids = ctx.symtab.sym_pool.slice(scope.symbols);
        for (pool_ids) |sid| {
            try considerSymbolSuggestion(self, ctx, ast_unit, ident_name, &seen_names, &best_suggestion, &min_dist, sid);
        }

        for (ctx.symtab.stack.items) |frame| {
            if (frame.id.eq(scope_id)) {
                for (frame.list.items) |sym_id| {
                    try considerSymbolSuggestion(self, ctx, ast_unit, ident_name, &seen_names, &best_suggestion, &min_dist, sym_id);
                }
                break;
            }
        }

        current_scope_id = if (scope.parent.isNone()) null else scope.parent.unwrap();
    }

    if (best_suggestion) |suggestion| {
        try self.context.diags.attachNoteArgs(last_diag_idx, null, .did_you_mean, .{suggestion});
    }

    return self.context.type_store.tTypeError();
}

/// Type-check block expression `id` while respecting value vs statement context.
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
            const sk = ast_unit.kind(stmts[i]);
            if (sk == .Break) after_break = true else if (sk == .Expr) {
                const se = getStmt(ast_unit, .Expr, stmts[i]).expr;
                if (ast_unit.kind(se) == .Break) after_break = true;
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
        const sk = ast_unit.kind(stmts[i]);
        if (sk == .Break) after_break = true else if (sk == .Expr) {
            const se = getStmt(ast_unit, .Expr, stmts[i]).expr;
            if (ast_unit.kind(se) == .Break) after_break = true;
        }
    }
    // If last is an expression, evaluate it in value context directly
    const last = stmts[stmts.len - 1];
    const last_kind = ast_unit.kind(last);
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

/// Fetch the source location for the statement `sid`.
fn stmtLoc(ast_unit: *ast.Ast, sid: ast.StmtId) Loc {
    return switch (ast_unit.kind(sid)) {
        .Expr => exprLocFromId(ast_unit, getStmt(ast_unit, .Expr, sid).expr),
        .Decl => blk: {
            const row = getStmt(ast_unit, .Decl, sid);
            const d = ast_unit.exprs.Decl.get(row.decl);
            break :blk exprLoc(ast_unit, d);
        },
        inline else => |x| exprLoc(ast_unit, getStmt(ast_unit, x, sid)),
    };
}

/// Validate binary operation `id`, ensuring operand types/coercion rules hold.
fn checkBinary(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const bin: ast.Rows.Binary = getExpr(ast_unit, .Binary, id);
    var l = try self.checkExpr(ctx, ast_unit, bin.left);
    var r = try self.checkExpr(ctx, ast_unit, bin.right);
    var lhs_kind = self.typeKind(l);
    var rhs_kind = self.typeKind(r);

    if (lhs_kind == .TypeError or rhs_kind == .TypeError) return self.context.type_store.tTypeError();

    const left_is_literal = ast_unit.kind(bin.left) == .Literal;
    const right_is_literal = ast_unit.kind(bin.right) == .Literal;

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
                    if (lc.elem.eq(rc.elem)) return l;
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
                both_complex = lc.elem.eq(rc.elem);
            }
            var both_same_enum = lhs_kind == .Enum and rhs_kind == .Enum and l.eq(r);
            var both_same_error = lhs_kind == .Error and rhs_kind == .Error and l.eq(r);

            // Handle Optional(T) == null or Optional(T) != null
            if ((bin.op == .eq or bin.op == .neq) and lhs_kind == .Optional and rhs_kind == .Optional) {
                const l_opt_elem_ty = self.context.type_store.get(.Optional, l).elem;
                const r_opt_elem_ty = self.context.type_store.get(.Optional, r).elem;

                if (self.typeKind(l_opt_elem_ty) == .Any or self.typeKind(r_opt_elem_ty) == .Any) {
                    if (self.typeKind(l_opt_elem_ty) == .Any and self.typeKind(r_opt_elem_ty) != .Any) {
                        ast_unit.type_info.setExprType(bin.left, r);
                    } else if (self.typeKind(r_opt_elem_ty) == .Any and self.typeKind(l_opt_elem_ty) != .Any) {
                        ast_unit.type_info.setExprType(bin.right, l);
                    }
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
                            both_complex = lc.elem.eq(rc.elem);
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
                            both_complex = lc.elem.eq(rc.elem);
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
                            both_complex = lc.elem.eq(rc.elem);
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
            if (l.eq(self.context.type_store.tBool()) and
                r.eq(self.context.type_store.tBool()))
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
                // Plain optional: require R assignable to T unless RHS is void/noreturn
                const rhs_operand_kind = self.typeKind(r);
                if (self.assignable(elem, r) == .success or rhs_operand_kind == .Void or rhs_operand_kind == .Noreturn) return elem;
                try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_binary_op_operands, .{ bin.op, lhs_kind, rhs_kind });
                return self.context.type_store.tTypeError();
            }
            try self.context.diags.addError(exprLoc(ast_unit, bin), .invalid_use_of_orelse_on_non_optional, .{l});
            return self.context.type_store.tTypeError();
        },
        else => unreachable,
    }
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
            if (!check_types.isNumericKind(self, type_kind)) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, unary_expr),
                    .invalid_unary_op_operand,
                    .{ unary_expr.op, type_kind },
                );
                return self.context.type_store.tTypeError();
            }
            return expr_ty;
        },
        .logical_not => {
            // Accept bool or any
            if (!expr_ty.eq(self.context.type_store.tBool()) and !expr_ty.eq(self.context.type_store.tAny())) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, unary_expr),
                    .invalid_unary_op_operand,
                    .{ unary_expr.op, type_kind },
                );
                return self.context.type_store.tTypeError();
            }
            return self.context.type_store.tBool();
        },
        .address_of => return self.context.type_store.mkPtr(expr_ty, false),
    }
}

/// Type-check function literal `id`, handling parameters, defaults, body, and purity.
fn checkFunctionLit(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    // Disallow nested function definitions unless explicitly allowed by the current context
    // (e.g., when defining methods inside functions before hoisting at lowering).
    if (self.inFunction(ctx) and !self.isNestedFnAllowed(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, getExpr(ast_unit, .FunctionLit, id)), .nested_function_not_allowed, .{});
        return self.context.type_store.tTypeError();
    }
    const fnr = getExpr(ast_unit, .FunctionLit, id);
    const params = ast_unit.exprs.param_pool.slice(fnr.params);
    var pbuf = try self.gpa.alloc(types.TypeId, params.len);
    defer self.gpa.free(pbuf);
    _ = try ctx.symtab.push(ctx.symtab.currentId());
    defer ctx.symtab.pop();

    var is_generic_template = false;
    var i: usize = 0;
    while (i < params.len) : (i += 1) {
        const p = ast_unit.exprs.Param.get(params[i]);

        if (p.is_comptime) {
            var specialized = false;
            if (!p.pat.isNone()) {
                if (bindingNameOfPattern(ast_unit, p.pat.unwrap())) |pname| {
                    if (self.lookupParamSpecialization(ctx, pname)) |_| {
                        specialized = true;
                    }
                }
            }
            if (!specialized) is_generic_template = true;
        }

        if (!p.ty.isNone()) {
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, p.ty.unwrap());
            if (!res[0]) return self.context.type_store.tTypeError();
            var pt = res[1];
            if (!p.pat.isNone()) {
                if (bindingNameOfPattern(ast_unit, p.pat.unwrap())) |pname| {
                    if (self.lookupParamSpecialization(ctx, pname)) |override_ty| {
                        const pk = self.typeKind(pt);
                        if (pk == .Any) {
                            pt = override_ty;
                        } else if (pk == .TypeType) {
                            const tt = self.context.type_store.get(.TypeType, pt);
                            if (self.typeKind(tt.of) == .Any) {
                                pt = override_ty;
                            }
                        }
                    }
                }
            }
            // If parameter uses a pattern, ensure its shape matches the annotated type
            if (!p.pat.isNone()) {
                const pat_id = p.pat.unwrap();
                const shape_ok = pattern_matching.checkPatternShapeForDecl(self, ast_unit, pat_id, pt);
                switch (shape_ok) {
                    .ok => {},
                    .tuple_arity_mismatch => {
                        const pat_len: i64 = @intCast(tuplePatternLength(ast_unit, pat_id));
                        const val_len: i64 = @intCast(tupleTypeLength(self, pt));
                        try self.context.diags.addError(
                            exprLoc(ast_unit, fnr),
                            .tuple_arity_mismatch,
                            .{ pat_len, val_len },
                        );
                        return self.context.type_store.tTypeError();
                    },
                    .struct_pattern_field_mismatch => {
                        const field_name = structPatternFieldName(ast_unit, pat_id);
                        const field_str = if (field_name) |name| getStr(ast_unit, name) else "pattern field";
                        try self.context.diags.addError(
                            exprLoc(ast_unit, fnr),
                            .struct_pattern_field_mismatch,
                            StringPayload{ .value = field_str },
                        );
                        return self.context.type_store.tTypeError();
                    },
                    .pattern_shape_mismatch => {
                        try self.context.diags.addError(
                            exprLoc(ast_unit, fnr),
                            .pattern_shape_mismatch,
                            StringPayload{ .value = "pattern shape mismatch" },
                        );
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
                            const expected_ty = pt;
                            const actual_ty = def_ty;
                            const diag_idx = self.context.diags.count();
                            try self.context.diags.addError(exprLocFromId(ast_unit, def_expr), .argument_type_mismatch, .{ expected_ty, actual_ty });
                            try self.attachTryCastNote(diag_idx, pt);
                            return self.context.type_store.tTypeError();
                        }
                    } else {
                        const expected_ty = pt;
                        const actual_ty = def_ty;
                        const diag_idx = self.context.diags.count();
                        try self.context.diags.addError(exprLocFromId(ast_unit, def_expr), .argument_type_mismatch, .{ expected_ty, actual_ty });
                        try self.attachTryCastNote(diag_idx, pt);
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

    const is_variadic = fnr.flags.is_variadic and fnr.flags.is_extern;

    // Temporarily record a function type (purity will be finalized after body analysis)
    const temp_ty = self.context.type_store.mkFunction(pbuf, res, is_variadic, true, fnr.flags.is_extern);
    ast_unit.type_info.expr_types.items[id.toRaw()] = temp_ty;

    const result_kind = self.typeKind(res);
    const returns_value = result_kind != .Void and result_kind != .Noreturn;
    try self.pushFunc(ctx, res, returns_value, !fnr.flags.is_proc);
    defer self.popFunc(ctx);
    if (!fnr.body.isNone() and !is_generic_template) {
        // Function bodies are in statement context: no value required from the block
        try self.pushValueReq(ctx, false);
        defer self.popValueReq(ctx);
        _ = try self.checkExpr(ctx, ast_unit, fnr.body.unwrap());
    }
    // Extern procs are considered impure; otherwise proc purity comes from body analysis.
    const func_ctx = ctx.func_stack.items[ctx.func_stack.items.len - 1];
    const refined_res = func_ctx.inferred_result orelse res;
    const is_pure = if (fnr.flags.is_proc) false else true;
    const final_ty = self.context.type_store.mkFunction(pbuf, refined_res, is_variadic, is_pure, fnr.flags.is_extern);
    ast_unit.type_info.expr_types.items[id.toRaw()] = final_ty;
    return final_ty;
}

/// Type-check tuple literal `id` and produce a tuple type of element types.
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

/// Type-check array literal `id`, ensuring homogenous element types.
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
        return self.context.type_store.mkArray(self.context.type_store.tAny(), 0);
    }
    const first_ty = try self.checkExpr(ctx, ast_unit, elems[0]);
    if (self.typeKind(first_ty) == .TypeError) return self.context.type_store.tTypeError();
    var i: usize = 1;
    while (i < elems.len) : (i += 1) {
        const ety = try self.checkExpr(ctx, ast_unit, elems[i]);
        if (!ety.eq(first_ty)) {
            try self.context.diags.addError(
                exprLoc(ast_unit, array_lit),
                .heterogeneous_array_elements,
                .{ first_ty, ety },
            );
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
        if (!kt.eq(key_ty)) {
            try self.context.diags.addError(
                exprLoc(ast_unit, row),
                .map_mixed_key_types,
                .{ key_ty, kt },
            );
            return self.context.type_store.tTypeError();
        }
        if (!vt.eq(val_ty)) {
            try self.context.diags.addError(
                exprLoc(ast_unit, row),
                .map_mixed_value_types,
                .{ val_ty, vt },
            );
            return self.context.type_store.tTypeError();
        }
    }
    return self.context.type_store.mkMap(key_ty, val_ty);
}

/// Resolve the index access expression `id` and compute the fetched element type.
fn checkIndexAccess(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const index_expr = getExpr(ast_unit, .IndexAccess, id);
    const col_ty = try self.checkExpr(ctx, ast_unit, index_expr.collection);
    const col_kind = self.typeKind(col_ty);
    if (col_kind == .TypeError) return self.context.type_store.tTypeError();
    switch (col_kind) {
        .Array, .Slice, .DynArray, .String => return self.indexElemTypeFromArrayLike(ctx, ast_unit, col_ty, index_expr.index, exprLoc(ast_unit, index_expr)),
        .Ptr => return self.indexElemTypeFromPointer(ctx, ast_unit, col_ty, index_expr.index, exprLoc(ast_unit, index_expr)),
        .Tensor => return self.indexElemTypeFromTensor(ctx, ast_unit, col_ty, index_expr.index, exprLoc(ast_unit, index_expr)),
        .Simd => {
            if (ast_unit.kind(index_expr.index) == .Range) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, index_expr),
                    .non_integer_index,
                    StringPayload{ .value = "range" },
                );
                return self.context.type_store.tTypeError();
            }
            const it = try self.checkExpr(ctx, ast_unit, index_expr.index);
            if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
            if (!check_types.isIntegerKind(self, self.typeKind(it))) {
                try self.context.diags.addError(exprLoc(ast_unit, index_expr), .non_integer_index, .{it});
                return self.context.type_store.tTypeError();
            }
            const simd = self.context.type_store.get(.Simd, col_ty);
            return simd.elem;
        },
        .Map => {
            const m = self.context.type_store.get(.Map, col_ty);
            const it = try self.checkExpr(ctx, ast_unit, index_expr.index);
            if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
            if (!it.eq(m.key)) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, index_expr),
                    .map_wrong_key_type,
                    .{ m.key, it },
                );
                return self.context.type_store.tTypeError();
            }
            return m.value;
        },
        else => {
            try self.context.diags.addError(exprLoc(ast_unit, index_expr), .not_indexable, .{col_ty});
        },
    }
    return self.context.type_store.tTypeError();
}

/// Compute the element or slice type for array-like `col_ty` indexed by `idx_expr`.
fn indexElemTypeFromArrayLike(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, col_ty: types.TypeId, idx_expr: ast.ExprId, loc: Loc) !types.TypeId {
    const col_kind = self.typeKind(col_ty);
    if (!(col_kind == .Array or col_kind == .Slice or col_kind == .String or col_kind == .DynArray)) {
        // Defensive: caller promised an array-like, but was not. Avoid panic.
        try self.context.diags.addError(loc, .not_indexable, .{col_ty});
        return self.context.type_store.tTypeError();
    }
    if (ast_unit.kind(idx_expr) == .Range) {
        _ = self.checkExpr(ctx, ast_unit, idx_expr) catch return self.context.type_store.tTypeError(); // validate range endpoints
        return switch (col_kind) {
            .Array => blk: {
                const r = self.context.type_store.get(.Array, col_ty);
                break :blk self.context.type_store.mkSlice(r.elem, false);
            },
            .Slice => blk2: {
                const r = self.context.type_store.get(.Slice, col_ty);
                break :blk2 self.context.type_store.mkSlice(r.elem, r.is_const);
            },
            .DynArray => blk3: {
                const r = self.context.type_store.get(.DynArray, col_ty);
                break :blk3 self.context.type_store.mkSlice(r.elem, false);
            },
            .String => self.context.type_store.tString(),
            else => return self.context.type_store.tTypeError(),
        };
    }
    const it = try self.checkExpr(ctx, ast_unit, idx_expr);
    if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
    if (!check_types.isIntegerKind(self, self.typeKind(it))) {
        try self.context.diags.addError(loc, .non_integer_index, .{it});
        return self.context.type_store.tTypeError();
    }
    return switch (col_kind) {
        .Array => self.context.type_store.get(.Array, col_ty).elem,
        .Slice => self.context.type_store.get(.Slice, col_ty).elem,
        .DynArray => self.context.type_store.get(.DynArray, col_ty).elem,
        .String => self.context.type_store.tU8(),
        else => self.context.type_store.tTypeError(),
    };
}

/// Compute the type referenced by pointer `col_ty` when indexed by `idx_expr`.
fn indexElemTypeFromPointer(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, col_ty: types.TypeId, idx_expr: ast.ExprId, loc: Loc) !types.TypeId {
    const ptr_row = self.context.type_store.get(.Ptr, col_ty);
    if (ast_unit.kind(idx_expr) == .Range) {
        _ = self.checkExpr(ctx, ast_unit, idx_expr) catch return self.context.type_store.tTypeError();
        return self.context.type_store.mkSlice(ptr_row.elem, ptr_row.is_const);
    }

    const it = try self.checkExpr(ctx, ast_unit, idx_expr);
    if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
    if (!check_types.isIntegerKind(self, self.typeKind(it))) {
        try self.context.diags.addError(loc, .non_integer_index, .{it});
        return self.context.type_store.tTypeError();
    }
    return ptr_row.elem;
}

/// Determine the element type after indexing tensor `col_ty`.
fn indexElemTypeFromTensor(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, col_ty: types.TypeId, idx_expr: ast.ExprId, loc: Loc) !types.TypeId {
    const tensor = self.context.type_store.get(.Tensor, col_ty);
    const rank: usize = @intCast(tensor.rank);
    if (rank == 0) {
        try self.context.diags.addError(loc, .not_indexable, .{col_ty});
        return self.context.type_store.tTypeError();
    }

    if (ast_unit.kind(idx_expr) == .Range) {
        // Tensor slicing is not yet supported.
        try self.context.diags.addError(
            loc,
            .non_integer_index,
            StringPayload{ .value = "range" },
        );
        return self.context.type_store.tTypeError();
    }

    const it = try self.checkExpr(ctx, ast_unit, idx_expr);
    if (self.typeKind(it) == .TypeError) return self.context.type_store.tTypeError();
    if (!check_types.isIntegerKind(self, self.typeKind(it))) {
        try self.context.diags.addError(loc, .non_integer_index, .{it});
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
    const method_name = getStr(ast_unit, field_name);

    if (std.mem.eql(u8, method_name, "append")) {
        const dyn_info = self.context.type_store.get(.DynArray, owner_ty);
        const elem_ty = dyn_info.elem;
        const ptr_owner_ty = self.context.type_store.mkPtr(owner_ty, false);
        const params = [_]types.TypeId{ ptr_owner_ty, elem_ty };
        const fn_ty = self.context.type_store.mkFunction(&params, self.context.type_store.tVoid(), false, false, false);

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
    const entry_opt = self.context.type_store.getMethod(owner_ty, field_name);
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
            break :blk self.context.type_store.mkFunction(rest, fn_row.result, fn_row.is_variadic, fn_row.is_pure, false);
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

/// Determine the type denoted by the field access expression `id`.
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

        const field_name_str = getStr(ast_unit, field_expr.field);

        if (parent_unit.ast) |a| {
            const target_sid = a.exprs.strs.intern(field_name_str);
            if (a.type_info.getExport(target_sid)) |ex| {
                return ex.ty;
            }

            const last_diag_idx = self.context.diags.count();
            try self.context.diags.addError(field_loc, .unknown_module_field, .{field_name_str});

            var all_exports = std.ArrayList([]const u8){};
            defer all_exports.deinit(self.gpa);

            var it = a.type_info.exports.iterator();
            while (it.next()) |entry| {
                const export_name = a.exprs.strs.get(entry.key_ptr.*);
                _ = all_exports.append(self.gpa, export_name) catch {};
            }

            try self.attachSuggestionListNotes(last_diag_idx, field_name_str, all_exports.items, .did_you_mean_field, .available_fields);

            return self.context.type_store.tTypeError();
        }

        try self.context.diags.addError(field_loc, .unknown_module_field, .{field_name_str});
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
    } else if (std.mem.eql(u8, field_name, "ptr")) {
        const ptr_ty: ?types.TypeId = switch (kind) {
            .Array => self.context.type_store.mkPtr(self.context.type_store.get(.Array, ty).elem, false),
            .Slice => self.context.type_store.mkPtr(self.context.type_store.get(.Slice, ty).elem, false),
            .DynArray => self.context.type_store.mkPtr(self.context.type_store.get(.DynArray, ty).elem, false),
            .String => self.context.type_store.mkPtr(self.context.type_store.tU8(), true),
            else => null,
        };
        if (ptr_ty) |pty| {
            try ast_unit.type_info.setFieldIndex(id, 0);
            return pty;
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
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_struct_field, .{field_name});
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

            const last_diag_idx = self.context.diags.count();
            try self.context.diags.addError(field_loc, .unknown_struct_field, .{field_name});

            var all_fields = std.ArrayList([]const u8){};
            defer all_fields.deinit(self.gpa);

            for (fields) |fid| {
                const f = self.context.type_store.Field.get(fid);
                const field_name_str = self.context.interner.get(f.name);
                try all_fields.append(self.gpa, field_name_str);
            }
            try self.attachSuggestionListNotes(last_diag_idx, field_name, all_fields.items, .did_you_mean_field, .available_fields);

            return self.context.type_store.tTypeError();
        },
        .Tuple => {
            const tuple_row = self.context.type_store.get(.Tuple, ty);
            const elems = self.context.type_store.type_pool.slice(tuple_row.elems);
            const field_token = getStr(ast_unit, field_expr.field);
            const index = std.fmt.parseInt(usize, field_token, 10) catch {
                try self.context.diags.addError(
                    exprLoc(ast_unit, field_expr),
                    .expected_field_name_or_index,
                    StringPayload{ .value = field_token },
                );
                return self.context.type_store.tTypeError();
            };
            if (index >= elems.len) {
                const max_index: i64 = if (elems.len == 0) 0 else @intCast(elems.len - 1);
                try self.context.diags.addError(
                    exprLoc(ast_unit, field_expr),
                    .tuple_index_out_of_bounds,
                    .{ @as(i64, @intCast(index)), max_index },
                );
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
                try self.context.diags.addError(
                    field_loc,
                    .unknown_struct_field,
                    StringPayload{ .value = field_name },
                );
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
                for (members, 0..) |member_id, i| {
                    const m = self.context.type_store.EnumMember.get(member_id);
                    if (m.name.eq(field_expr.field)) {
                        try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                        return ty;
                    }
                }
                const field_name_str = getStr(ast_unit, field_expr.field);
                const last_diag_idx = self.context.diags.count();
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_enum_tag, .{field_name_str});
                var all_tags = std.ArrayList([]const u8){};
                defer all_tags.deinit(self.gpa);
                try self.appendEnumMemberNames(&all_tags, members);
                try self.attachSuggestionListNotes(last_diag_idx, field_name_str, all_tags.items, .did_you_mean_tag, .available_tags);
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
                const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, parent_ty, field_expr.field, field_loc) catch |err| switch (err) {
                    else => return self.context.type_store.tTypeError(),
                };
                if (self.typeKind(method_ty) != .TypeError) return method_ty;
                try self.context.diags.addError(
                    exprLoc(ast_unit, field_expr),
                    .unknown_struct_field,
                    StringPayload{ .value = field_name },
                );
                return self.context.type_store.tTypeError();
            } else if (inner_kind == .Variant) {
                const vr = self.context.type_store.get(.Variant, ty);
                const variants = self.context.type_store.field_pool.slice(vr.variants);
                for (variants, 0..) |variant_id, i| {
                    const v = self.context.type_store.Field.get(variant_id);
                    if (v.name.eq(field_expr.field)) {
                        const pk = self.typeKind(v.ty);
                        if (pk == .Void) {
                            try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                            return ty;
                        }
                        const found: i64 = if (pk == .Tuple) blk: {
                            const tup = self.context.type_store.get(.Tuple, v.ty);
                            break :blk @intCast(self.context.type_store.type_pool.slice(tup.elems).len);
                        } else 1;
                        try self.context.diags.addError(
                            exprLoc(ast_unit, field_expr),
                            .variant_payload_arity_mismatch,
                            .{ 0, found },
                        );
                        return self.context.type_store.tTypeError();
                    }
                }
                const field_name_str = getStr(ast_unit, field_expr.field);
                const last_diag_idx = self.context.diags.count();
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_variant_tag, .{field_name_str});
                var all_tags = std.ArrayList([]const u8){};
                defer all_tags.deinit(self.gpa);
                try self.appendFieldNames(&all_tags, variants);
                try self.attachSuggestionListNotes(last_diag_idx, field_name_str, all_tags.items, .did_you_mean_tag, .available_tags);
                return self.context.type_store.tTypeError();
            } else if (inner_kind == .Error) {
                const er = self.context.type_store.get(.Error, ty);
                const tags = self.context.type_store.field_pool.slice(er.variants);
                for (tags, 0..) |tag_id, i| {
                    const t = self.context.type_store.Field.get(tag_id);
                    if (t.name.eq(field_expr.field)) {
                        try ast_unit.type_info.setFieldIndex(id, @intCast(i));
                        return ty;
                    }
                }
                const field_name_str = getStr(ast_unit, field_expr.field);
                const last_diag_idx = self.context.diags.count();
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .unknown_error_tag, .{field_name_str});
                var all_tags = std.ArrayList([]const u8){};
                defer all_tags.deinit(self.gpa);
                try self.appendFieldNames(&all_tags, tags);
                try self.attachSuggestionListNotes(last_diag_idx, field_name_str, all_tags.items, .did_you_mean_tag, .available_tags);
                return self.context.type_store.tTypeError();
            } else if (inner_kind == .Ast) {
                const ast_ty = self.context.type_store.get(.Ast, ty);
                const pkg_name = self.context.interner.get(ast_ty.pkg_name);
                const filepath = self.context.interner.get(ast_ty.filepath);
                const pkg = self.context.compilation_unit.packages.getPtr(pkg_name) orelse
                    return self.context.type_store.tTypeError();
                const parent_unit = pkg.sources.getPtr(filepath) orelse
                    return self.context.type_store.tTypeError();

                if (parent_unit.ast) |a| {
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
                const field_token = getStr(ast_unit, field_expr.field);
                const index = std.fmt.parseInt(usize, field_token, 10) catch {
                    try self.context.diags.addError(
                        exprLoc(ast_unit, field_expr),
                        .expected_field_name_or_index,
                        StringPayload{ .value = field_token },
                    );
                    return self.context.type_store.tTypeError();
                };
                const runtime_fields: usize = if (variants.len == 0) 1 else 2;
                if (index >= runtime_fields) {
                    const max_index: i64 = if (runtime_fields == 0) 0 else @intCast(runtime_fields - 1);
                    try self.context.diags.addError(
                        exprLoc(ast_unit, field_expr),
                        .tuple_index_out_of_bounds,
                        .{ @as(i64, @intCast(index)), max_index },
                    );
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
                    const ty_kind = self.typeKind(variant.ty);
                    if (ty_kind == .Void) return self.context.type_store.tI32();
                    return variant.ty;
                }
            }
            const method_ty = self.resolveMethodFieldAccess(ast_unit, id, ty, ty, field_expr.field, field_loc) catch |err| switch (err) {
                else => return self.context.type_store.tTypeError(),
            };
            if (self.typeKind(method_ty) != .TypeError) return method_ty;
            try self.context.diags.addError(
                exprLoc(ast_unit, field_expr),
                .unknown_variant_tag,
                StringPayload{ .value = field_name },
            );
            return self.context.type_store.tTypeError();
        },
        else => {
            try self.context.diags.addError(exprLoc(ast_unit, field_expr), .field_access_on_non_aggregate, .{kind});
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
        const end_t = end_ty.?;
        const end_kind = self.typeKind(end_t);
        if (end_kind == .Tuple) {
            return end_t;
        }
        if (end_kind == .Any) {
            try ast_unit.type_info.markRangeSpread(self.gpa, id);
            return end_t;
        }
    }

    if (start_ty == null and end_ty == null) {
        try self.context.diags.addError(exprLoc(ast_unit, range), .cannot_infer_range_type, .{});
        return self.context.type_store.tTypeError();
    }

    if (start_ty != null and end_ty != null and !start_ty.?.eq(end_ty.?)) {
        var l = start_ty.?;
        var r = end_ty.?;
        var lkind = self.typeKind(l);
        var rkind = self.typeKind(r);
        const l_is_lit = if (!range.start.isNone()) ast_unit.kind(range.start.unwrap()) == .Literal else false;
        const r_is_lit = if (!range.end.isNone()) ast_unit.kind(range.end.unwrap()) == .Literal else false;

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
        try self.context.diags.addError(
            exprLoc(ast_unit, range),
            .range_type_mismatch,
            .{ start_ty.?, end_ty.? },
        );
        return self.context.type_store.tTypeError();
    }

    const k = self.typeKind(final_ty);
    if (!check_types.isIntegerKind(self, k) and k != .Any) {
        // Allow `..expr` spread forms even after specialization narrows `expr` to a concrete type.
        if (range.start.isNone()) {
            try ast_unit.type_info.markRangeSpread(self.gpa, id);
            return final_ty;
        }
        const integer_hint = self.context.type_store.tAny();
        const start_report = if (start_ty) |ty| ty else integer_hint;
        const end_report = if (end_ty) |ty| ty else integer_hint;
        try self.context.diags.addError(
            exprLoc(ast_unit, range),
            .range_requires_integer_operands,
            .{ start_report, end_report },
        );
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

/// Validate struct literal `id` against its optional type annotation, generating diagnostics on mismatch.
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
            try self.context.diags.addError(
                exprLoc(ast_unit, struct_lit),
                .struct_field_name_mismatch,
                .{},
            );
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
        if (typeExprNameForDiag(ast_unit, lit_ty)) |name| {
            const ident_name = ast_unit.exprs.strs.get(name);
            try self.context.diags.addError(exprLocFromId(ast_unit, lit_ty), .undefined_identifier, .{ident_name});
        } else {
            try self.context.diags.addError(exprLocFromId(ast_unit, lit_ty), .could_not_resolve_type, StringPayload{ .value = "type expression" });
        }
        return self.context.type_store.tTypeError();
    };
    const is_assignable = self.assignable(struct_ty, expect_ty);
    switch (is_assignable) {
        .success => {},
        .struct_field_count_mismatch => {
            if (self.structMissingFieldsCoveredByDefaults(ctx, ast_unit, struct_lit, struct_ty, expect_ty)) {
                return expect_ty;
            }
            const diag_idx = self.context.diags.count();
            const missing = try self.collectMissingStructFields(ctx, ast_unit, struct_lit, struct_ty, expect_ty);
            try self.context.diags.addError(
                exprLoc(ast_unit, struct_lit),
                .struct_missing_field,
                if (missing) |str| StringPayload{ .value = self.context.interner.get(str) } else StringPayload{ .value = "missing field" },
            );
            if (missing) |str| {
                try self.context.diags.attachNoteArgs(diag_idx, null, .missing_fields_list, StringNotePayload{ .value = str });
            }
            return self.context.type_store.tTypeError();
        },
        .unknown_struct_field => {
            const expected_struct = self.context.type_store.get(.Struct, expect_ty);
            const expected_fields = self.context.type_store.field_pool.slice(expected_struct.fields);
            var missing_name: ?[]const u8 = null;
            var j: usize = 0;
            while (j < lit_fields.len) : (j += 1) {
                const field_value = ast_unit.exprs.StructFieldValue.get(lit_fields[j]);
                if (field_value.name.isNone()) continue;
                if (self.findFieldByName(expected_fields, field_value.name.unwrap()) == null) {
                    missing_name = getStr(ast_unit, field_value.name.unwrap());
                    break;
                }
            }
            const field_name = missing_name orelse "unknown field";
            try self.context.diags.addError(
                exprLoc(ast_unit, struct_lit),
                .unknown_struct_field,
                StringPayload{ .value = field_name },
            );
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
        .struct_field_type_mismatch => |err| {
            const f = ast_unit.exprs.StructFieldValue.get(lit_fields[err.index]);
            const loc = ast_unit.exprs.locs.get(f.loc);
            const expected_struct = self.context.type_store.get(.Struct, expect_ty);
            const expected_fields = self.context.type_store.field_pool.slice(expected_struct.fields);
            const match = self.findFieldByName(expected_fields, f.name.unwrap()) orelse return self.context.type_store.tTypeError();
            const expected_field_ty = match.field.ty;
            const actual_ty = ast_unit.type_info.expr_types.items[f.value.toRaw()];
            try self.context.diags.addError(
                loc,
                .struct_field_type_mismatch,
                .{ expected_field_ty, actual_ty.? },
            );
            return self.context.type_store.tTypeError();
        },
        else => {
            try self.context.diags.addError(
                exprLoc(ast_unit, struct_lit),
                .struct_field_type_mismatch,
                .{ expect_ty, struct_ty },
            );
            return self.context.type_store.tTypeError();
        },
    }

    // If the literal was annotated with a struct type, refine the field literal
    // types to match the expected field types (e.g., coerce int literals down).
    if (self.typeKind(expect_ty) == .Struct) {
        const expect_struct = self.context.type_store.get(.Struct, expect_ty);
        const expect_fields = self.context.type_store.field_pool.slice(expect_struct.fields);
        var j: usize = 0;
        while (j < lit_fields.len) : (j += 1) {
            const f = ast_unit.exprs.StructFieldValue.get(lit_fields[j]);
            if (f.name.isNone()) continue;
            const fname = f.name.unwrap();

            // Locate the corresponding expected field type.
            var expected_field_ty: ?types.TypeId = null;
            for (expect_fields) |efid| {
                const ef = self.context.type_store.Field.get(efid);
                if (ef.name.eq(fname)) {
                    expected_field_ty = ef.ty;
                    break;
                }
            }
            if (expected_field_ty == null) continue;

            const ety = expected_field_ty.?;
            const got_ty = buf[j].ty;
            if (got_ty.eq(ety)) continue;

            if (self.tryCoerceNullLiteral(ast_unit, f.value, ety)) {
                ast_unit.type_info.expr_types.items[f.value.toRaw()] = ety;
                buf[j].ty = ety;
                continue;
            }

            if (check_types.isNumericKind(self, self.typeKind(ety))) {
                var coerced_ty = got_ty;
                var coerced_kind = self.typeKind(coerced_ty);
                _ = try self.updateCoercedLiteral(ast_unit, f.value, ety, &coerced_ty, &coerced_kind);
            }
        }
    }
    return expect_ty;
}

/// Return true when missing struct literal fields have defaults within `expect_ty`.
fn structMissingFieldsCoveredByDefaults(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    struct_lit: ast.Rows.StructLit,
    provided_ty: types.TypeId,
    expect_ty: types.TypeId,
) bool {
    if (struct_lit.ty.isNone()) return false;
    if (self.typeKind(provided_ty) != .Struct or self.typeKind(expect_ty) != .Struct) return false;

    const ty_expr = struct_lit.ty.unwrap();
    const got_struct = self.context.type_store.get(.Struct, provided_ty);
    const expect_struct = self.context.type_store.get(.Struct, expect_ty);
    const got_fields = self.context.type_store.field_pool.slice(got_struct.fields);
    const expect_fields = self.context.type_store.field_pool.slice(expect_struct.fields);

    for (expect_fields) |efid| {
        const expected_field = self.context.type_store.Field.get(efid);
        var present = false;
        for (got_fields) |gfid| {
            const provided_field = self.context.type_store.Field.get(gfid);
            if (provided_field.name.eq(expected_field.name)) {
                present = true;
                break;
            }
        }
        if (present) continue;
        if (!self.structFieldHasDefault(ctx, ast_unit, ty_expr, expected_field.name)) {
            return false;
        }
    }
    return true;
}

/// Collect missing struct field names that lack defaults for diagnostics.
fn collectMissingStructFields(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    struct_lit: ast.Rows.StructLit,
    provided_ty: types.TypeId,
    expect_ty: types.TypeId,
) !?ast.StrId {
    if (struct_lit.ty.isNone()) return null;
    if (self.typeKind(provided_ty) != .Struct or self.typeKind(expect_ty) != .Struct) return null;

    const ty_expr = struct_lit.ty.unwrap();
    const provided_struct = self.context.type_store.get(.Struct, provided_ty);
    const expect_struct = self.context.type_store.get(.Struct, expect_ty);
    const provided_fields = self.context.type_store.field_pool.slice(provided_struct.fields);
    const expect_fields = self.context.type_store.field_pool.slice(expect_struct.fields);

    var missing = std.ArrayList([]const u8){};
    defer missing.deinit(self.gpa);

    for (expect_fields) |efid| {
        const expected_field = self.context.type_store.Field.get(efid);
        var present = false;
        for (provided_fields) |pfid| {
            const provided_field = self.context.type_store.Field.get(pfid);
            if (provided_field.name.eq(expected_field.name)) {
                present = true;
                break;
            }
        }
        if (present) continue;
        if (self.structFieldHasDefault(ctx, ast_unit, ty_expr, expected_field.name)) continue;
        const field_name = self.context.interner.get(expected_field.name);
        try missing.append(self.gpa, field_name);
    }

    if (missing.items.len == 0) return null;
    const joined = try diag.joinStrings(self.gpa, ", ", missing.items);
    const joined_id = self.context.interner.intern(joined);
    self.gpa.free(joined);
    return joined_id;
}

/// Return true if `field_name` has a default value within `ty_expr`.
fn structFieldHasDefault(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    ty_expr: ast.ExprId,
    field_name: ast.StrId,
) bool {
    return switch (ast_unit.kind(ty_expr)) {
        .StructType => structFieldHasDefaultInStructExpr(ast_unit, ty_expr, field_name),
        .Ident => blk: {
            const idr = getExpr(ast_unit, .Ident, ty_expr);
            if (self.lookup(ctx, idr.name)) |sid| {
                const sym = ctx.symtab.syms.get(sid);
                if (!sym.origin_decl.isNone()) {
                    const decl = ast_unit.exprs.Decl.get(sym.origin_decl.unwrap());
                    if (ast_unit.kind(decl.value) == .StructType) {
                        break :blk structFieldHasDefaultInStructExpr(ast_unit, decl.value, field_name);
                    }
                }
            }
            break :blk false;
        },
        .FieldAccess => {
            const field_expr = getExpr(ast_unit, .FieldAccess, ty_expr);
            const parent_ty = self.checkExpr(ctx, ast_unit, field_expr.parent) catch return false;
            if (self.typeKind(parent_ty) != .Ast) return false;

            const ast_ty = self.context.type_store.get(.Ast, parent_ty);
            const pkg_name = self.context.interner.get(ast_ty.pkg_name);
            const filepath = self.context.interner.get(ast_ty.filepath);
            const pkg = self.context.compilation_unit.packages.getPtr(pkg_name) orelse return false;
            const parent_unit = pkg.sources.getPtr(filepath) orelse return false;
            if (parent_unit.ast) |module_ast| {
                if (module_ast.type_info.getExport(field_expr.field)) |export_entry| {
                    const decl = module_ast.exprs.Decl.get(export_entry.decl_id);
                    if (module_ast.kind(decl.value) == .StructType) {
                        return structFieldHasDefaultInStructExpr(module_ast, decl.value, field_name);
                    }
                }
            }
            return false;
        },
        else => false,
    };
}

/// Helper checking for defaults inside a direct struct type expression.
fn structFieldHasDefaultInStructExpr(
    ast_unit: *ast.Ast,
    struct_expr: ast.ExprId,
    field_name: ast.StrId,
) bool {
    const struct_row = ast_unit.exprs.get(.StructType, struct_expr);
    const sfield_ids = ast_unit.exprs.sfield_pool.slice(struct_row.fields);
    for (sfield_ids) |sfid| {
        const sf = ast_unit.exprs.StructField.get(sfid);
        if (sf.name.eq(field_name)) {
            return !sf.value.isNone();
        }
    }
    return false;
}

/// Type-check dereference expression `id`, ensuring pointer operand.
fn checkDeref(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const row = getExpr(ast_unit, .Deref, id);
    const ptr_ty = try self.checkExpr(ctx, ast_unit, row.expr);
    if (self.typeKind(ptr_ty) == .TypeError) return self.context.type_store.tTypeError();
    const kind = self.typeKind(ptr_ty);
    if (kind != .Ptr) {
        try self.context.diags.addError(exprLoc(ast_unit, row), .deref_non_pointer, .{ptr_ty});
        return self.context.type_store.tTypeError();
    }
    const ptr_row = self.context.type_store.get(.Ptr, ptr_ty);
    return ptr_row.elem;
}

// =========================
// Calls & related helpers
// =========================

/// Resolve the payload type associated with tag `tag` in variant/error type `parent_ty`.
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
        const tag_name = self.context.interner.get(tag);
        if (pk == .Variant) {
            try self.context.diags.addError(
                loc,
                .unknown_variant_tag,
                StringPayload{ .value = tag_name },
            );
        } else {
            try self.context.diags.addError(
                loc,
                .unknown_error_tag,
                StringPayload{ .value = tag_name },
            );
        }
        return self.context.type_store.tTypeError();
    }

    const payload_ty = payload_ty_opt.?;
    const payload_kind = self.typeKind(payload_ty);

    switch (payload_kind) {
        .Void => {
            // Tag-only: must have zero args
            if (args.len != 0) {
                try self.context.diags.addError(
                    loc,
                    .argument_count_mismatch,
                    .{ 0, @as(i64, @intCast(args.len)) },
                );
                return self.context.type_store.tTypeError();
            }
            return parent_ty;
        },
        .Tuple => {
            // Exact arity, per-element type check
            const tup = self.context.type_store.get(.Tuple, payload_ty);
            const params = self.context.type_store.type_pool.slice(tup.elems);

            if (args.len != params.len) {
                const expected_count: i64 = @intCast(params.len);
                const actual_count: i64 = @intCast(args.len);
                // IMPORTANT: only one arity diagnostic
                try self.context.diags.addError(
                    loc,
                    .argument_count_mismatch,
                    .{ expected_count, actual_count },
                );
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
                    const expected_ty = params[i];
                    const actual_ty = at;
                    // IMPORTANT: only one type diagnostic
                    try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_ty, actual_ty });
                    return self.context.type_store.tTypeError();
                }
            }
            return parent_ty;
        },
        else => {
            // Non-void, non-tuple payloads (e.g. struct) are not callable: use literals like Type.Tag{...}
            try self.context.diags.addError(
                loc,
                .call_non_callable,
                .{payload_ty},
            );
            return self.context.type_store.tTypeError();
        },
    }
}

/// Validate the call expression `id`, checking argument arity/types, methods, and builtins.
fn checkCall(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const call_expr = getExpr(ast_unit, .Call, id);
    const call_loc = exprLoc(ast_unit, call_expr);
    const callee_kind = ast_unit.kind(call_expr.callee);
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
                        const fn_ty = self.context.type_store.mkFunction(params, inner_ty, false, false, false);
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
                try self.context.diags.addError(
                    call_loc,
                    .argument_count_mismatch,
                    .{ 1, @as(i64, @intCast(args.len)) },
                );
                return self.context.type_store.tTypeError();
            }
            const res = try check_types.typeFromTypeExpr(self, ctx, ast_unit, args[0]);
            ast_unit.type_info.expr_types.items[args[0].toRaw()] = self.context.type_store.mkTypeType(res[1]);
            if (!res[0]) return self.context.type_store.tTypeError();
            // Record a comptime value for potential constant folding (optional)
            try ast_unit.type_info.ensureExpr(self.gpa, id);
            ast_unit.type_info.expr_types.items[id.toRaw()] = self.context.type_store.tU64();
            // Stamp callee type so lower_tir can query it
            const any_type_ty = self.context.type_store.mkTypeType(self.context.type_store.tAny());
            const fn_ty = self.context.type_store.mkFunction(&.{any_type_ty}, self.context.type_store.tU64(), false, true, false);
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
        return try self.checkMethodCall(ctx, ast_unit, id, &call_expr, binding, args);
    }
    if (calleeNameForCall(ast_unit, call_expr.callee)) |name| {
        try self.maybeRecordRuntimeSpecialization(ctx, ast_unit, id, call_expr.callee, name, args, func_ty);
    }
    func_kind = self.typeKind(func_ty);
    if (func_kind == .Any) return self.context.type_store.tTypeError();

    // Tuple-as-constructor: `(T0,T1,..)(a0,a1,..)` -> construct the tuple type.
    if (func_kind == .Tuple) {
        const tup = self.context.type_store.get(.Tuple, func_ty);
        const params = self.context.type_store.type_pool.slice(tup.elems);
        if (args.len != params.len) {
            try self.context.diags.addError(
                call_loc,
                .argument_count_mismatch,
                .{ @as(i64, @intCast(params.len)), @as(i64, @intCast(args.len)) },
            );
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
                const expected_ty = params[i];
                const actual_ty = at;
                const loc = exprLocFromId(ast_unit, args[i]);
                try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_ty, actual_ty });
                return self.context.type_store.tTypeError();
            }
        }
        return func_ty;
    }

    if (func_kind != .Function) {
        try self.context.diags.addError(
            call_loc,
            .call_non_callable,
            .{func_ty},
        );
        return self.context.type_store.tTypeError();
    }

    // Purity bookkeeping / enforcement
    const fnrow = self.context.type_store.get(.Function, func_ty);
    if (self.inFunction(ctx)) {
        const fctx = self.currentFunc(ctx).?;
        if (fctx.require_pure and !fnrow.is_pure) {
            try self.context.diags.addError(
                call_loc,
                .purity_violation,
                StringPayload{ .value = "call to impure function" },
            );
            return self.context.type_store.tTypeError();
        }
        if (!fnrow.is_pure) {
            const idx = ctx.func_stack.items.len - 1;
            ctx.func_stack.items[idx].pure = false;
        }
    }

    // Arity & argument type checks
    const params = self.context.type_store.type_pool.slice(fnrow.params);
    const is_internal_variadic = check_types.isInternalVariadic(self.context.type_store, func_ty);
    const is_non_extern_any_variadic_candidate = is_internal_variadic;
    var pack_args = false;
    var pack_start_index: usize = 0;

    if (!fnrow.is_variadic) { // This branch is taken for non-extern functions
        var min_required = params.len;
        // If callee is a direct identifier to a function declaration with defaulted trailing params,
        // allow omitting those arguments.
        if (callee_kind == .Ident) {
            const idr = getExpr(ast_unit, .Ident, call_expr.callee);
            if (self.lookup(ctx, idr.name)) |sid| {
                const srow = ctx.symtab.syms.get(sid);
                if (!srow.origin_decl.isNone()) {
                    const did = srow.origin_decl.unwrap();
                    if (ast_unit.kind(ast_unit.exprs.Decl.get(did).value) == .FunctionLit) {
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
            const pk = ast_unit.kind(fr.parent);
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
                        if (ast_unit.kind(drow2.value) == .Import) {
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

        if (is_non_extern_any_variadic_candidate) {
            // For non-extern functions with a final 'any' parameter,
            // allow any number of arguments >= (params.len - 1).
            // The 'any' parameter will consume all arguments from params.len - 1 onwards.
            min_required = params.len - 1; // All but the last 'any' param are fixed
            if (args.len < min_required) {
                const diag_idx = self.context.diags.count();
                try self.context.diags.addError(
                    call_loc,
                    .argument_count_mismatch,
                    .{ @as(i64, @intCast(min_required)), @as(i64, @intCast(args.len)) },
                );
                try self.attachFunctionSignatureNote(diag_idx, func_ty);
                return self.context.type_store.tTypeError();
            }
            // No upper bound on args.len here, as 'any' consumes the rest.
        } else {
            // Original arity check for non-variadic, non-any-last-param functions
            if (!(args.len >= min_required and args.len <= params.len)) {
                const diag_idx = self.context.diags.count();
                const expected_count = if (args.len < min_required) min_required else params.len;
                try self.context.diags.addError(
                    call_loc,
                    .argument_count_mismatch,
                    .{ @as(i64, @intCast(expected_count)), @as(i64, @intCast(args.len)) },
                );
                try self.attachFunctionSignatureNote(diag_idx, func_ty);
                return self.context.type_store.tTypeError();
            }
        }
    } else { // fnrow.is_variadic is true (only for extern functions now)
        const min_required = if (params.len == 0) 0 else params.len - 1;
        if (args.len < min_required) {
            const diag_idx = self.context.diags.count();
            try self.context.diags.addError(
                call_loc,
                .argument_count_mismatch,
                .{ @as(i64, @intCast(min_required)), @as(i64, @intCast(args.len)) },
            );
            try self.attachFunctionSignatureNote(diag_idx, func_ty);
            return self.context.type_store.tTypeError();
        }
    }

    var arg_types = std.ArrayList(types.TypeId){};
    defer arg_types.deinit(self.gpa);

    var saw_spread = false;

    if (is_non_extern_any_variadic_candidate) {
        pack_start_index = params.len - 1;
        if (args.len > params.len) {
            pack_args = true;
        }
    }

    var i: usize = 0;
    while (i < args.len) : (i += 1) {
        const pt = if (is_non_extern_any_variadic_candidate and i >= params.len - 1)
            params[params.len - 1]
        else if (!fnrow.is_variadic)
            (if (i < params.len) params[i] else params[params.len - 1])
        else blk: {
            const fixed = if (params.len == 0) 0 else params.len - 1;
            break :blk if (i < fixed) params[i] else params[params.len - 1];
        };

        // Arguments must be evaluated in value context by default
        try self.pushValueReq(ctx, true);
        try self.pushExpectedType(ctx, pt);
        var at = try self.checkExpr(ctx, ast_unit, args[i]);
        self.popExpectedType(ctx);
        self.popValueReq(ctx);
        if (self.typeKind(at) == .TypeError) return self.context.type_store.tTypeError();
        var at_kind = self.typeKind(at);

        if (self.isSpreadRangeExprChecker(ast_unit, args[i])) saw_spread = true;

        if (self.tryCoerceNullLiteral(ast_unit, args[i], pt)) {
            ast_unit.type_info.expr_types.items[args[i].toRaw()] = pt;
            at = pt;
            at_kind = self.typeKind(at);
        }

        // If this argument is part of the 'any' packing, we don't need to check
        // its individual type against 'any' because 'any' accepts anything.
        // The packing logic in lower_tir will handle creating the tuple.
        if (is_non_extern_any_variadic_candidate and i >= params.len - 1) {
            // No individual type check needed here, as 'any' accepts anything.
            // The 'at' (type of args[i]) is already checked for TypeError.
            try arg_types.append(self.gpa, at);
            continue; // Move to the next argument
        }

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
                    try arg_types.append(self.gpa, at);
                    continue;
                }
            }
            const expected_ty = pt;
            const actual_ty = at;
            const loc = exprLocFromId(ast_unit, args[i]);
            const diag_idx = self.context.diags.count();
            try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_ty, actual_ty });
            try self.attachTryCastNote(diag_idx, pt);
            return self.context.type_store.tTypeError();
        }
        try arg_types.append(self.gpa, at);
    }

    const has_any_param = blk: {
        var idx: usize = 0;
        while (idx < params.len) : (idx += 1) {
            const pk = self.typeKind(params[idx]);
            if (pk == .Any) break :blk true;
            if (pk == .TypeType) {
                const tt = self.context.type_store.get(.TypeType, params[idx]);
                if (self.typeKind(tt.of) == .Any) break :blk true;
            }
        }
        break :blk false;
    };

    const result_is_type = blk_res: {
        const k = self.typeKind(fnrow.result);
        break :blk_res k == .TypeType;
    };

    if (!fnrow.is_extern and (has_any_param or is_internal_variadic) and !result_is_type) {
        var concrete_param_types = std.ArrayList(types.TypeId){};
        defer concrete_param_types.deinit(self.gpa);

        if (is_internal_variadic) {
            const fixed_params_count = if (params.len == 0) 0 else params.len - 1;
            var idx: usize = 0;
            while (idx < fixed_params_count and idx < arg_types.items.len) : (idx += 1) {
                try concrete_param_types.append(self.gpa, arg_types.items[idx]);
            }
            const tuple_ty = try self.computeTrailingAnyTupleTypeChecker(ast_unit, args, fixed_params_count);
            try concrete_param_types.append(self.gpa, tuple_ty);
        } else {
            var idx: usize = 0;
            while (idx < params.len) : (idx += 1) {
                const arg_ty = if (idx < arg_types.items.len) arg_types.items[idx] else params[idx];
                try concrete_param_types.append(self.gpa, arg_ty);
            }
        }

        if (calleeNameForCall(ast_unit, call_expr.callee)) |callee_name| {
            if (call_resolution.findFunctionDeclForCall(self.context, ast_unit, call_expr.callee, callee_name)) |decl_ctx| {
                var target_ctx_opt: ?*CheckerContext = null;
                var resolved_ctx = decl_ctx;
                if (resolveFunctionDeclAlias(self, resolved_ctx)) |resolved| {
                    resolved_ctx = resolved;
                }
                if (resolved_ctx.ast.file_id < self.checker_ctx.items.len) {
                    target_ctx_opt = &self.checker_ctx.items[resolved_ctx.ast.file_id];
                }
                if (target_ctx_opt) |target_ctx| {
                    const spec_decl_id = try self.getOrInstantiateSpecialization(
                        target_ctx,
                        resolved_ctx.ast,
                        resolved_ctx.decl_id,
                        concrete_param_types.items,
                    );
                    const spec_sig = resolved_ctx.ast.type_info.decl_types.items[spec_decl_id.toRaw()] orelse func_ty;
                    try ast_unit.type_info.setCallSpecialization(self.gpa, id, .{
                        .target_decl = spec_decl_id.toRaw(),
                        .target_file_id = @intCast(resolved_ctx.ast.file_id),
                        .pack_args = pack_args,
                        .pack_start_index = pack_start_index,
                        .is_spread = saw_spread and fnrow.is_variadic,
                    });
                    return self.context.type_store.get(.Function, spec_sig).result;
                }
            }
        }
    }
    if (fnrow.is_extern and saw_spread) {
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
        // Only consider runtime params; comptime params are always required
        if (p.is_comptime) break;
        if (p.value.isNone()) break;
        count += 1;
    }
    return count;
}

/// Validate a method call using the resolved `binding` info.
fn checkMethodCall(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    call_id: ast.ExprId,
    call_expr: *const ast.Rows.Call,
    binding: types.MethodBinding,
    args: []const ast.ExprId,
) !types.TypeId {
    const field_expr = getExpr(ast_unit, .FieldAccess, call_expr.callee);
    const receiver_ty = try self.checkExpr(ctx, ast_unit, field_expr.parent);
    if (self.typeKind(receiver_ty) == .TypeError) return self.context.type_store.tTypeError();

    if (binding.receiver_kind == .pointer or binding.receiver_kind == .pointer_const) {
        if (!binding.needs_addr_of and self.lvalueRootKind(ctx, ast_unit, field_expr.parent) == .Unknown and self.typeKind(receiver_ty) != .Ptr) {
            try self.context.diags.addError(
                exprLocFromId(ast_unit, field_expr.parent),
                .method_receiver_not_addressable,
                StringPayload{ .value = getStr(ast_unit, binding.method_name) },
            );
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
            const diag_idx = self.context.diags.count();
            const expected_count = if (total_args < min_required) min_required else params.len;
            try self.context.diags.addError(
                exprLoc(ast_unit, call_expr.*),
                .argument_count_mismatch,
                .{ @as(i64, @intCast(expected_count)), @as(i64, @intCast(total_args)) },
            );
            try self.attachFunctionSignatureNote(diag_idx, binding.func_type);
            return self.context.type_store.tTypeError();
        }
    } else {
        const min_required = if (params.len == 0) 0 else params.len - 1;
        if (total_args < min_required) {
            const diag_idx = self.context.diags.count();
            try self.context.diags.addError(
                exprLoc(ast_unit, call_expr.*),
                .argument_count_mismatch,
                .{ @as(i64, @intCast(min_required)), @as(i64, @intCast(total_args)) },
            );
            try self.attachFunctionSignatureNote(diag_idx, binding.func_type);
            return self.context.type_store.tTypeError();
        }
    }

    if (binding.requires_implicit_receiver) {
        if (params.len == 0) {
            try self.context.diags.addError(
                exprLoc(ast_unit, call_expr.*),
                .argument_count_mismatch,
                .{ 1, @as(i64, @intCast(total_args)) },
            );
            return self.context.type_store.tTypeError();
        }
        const self_param_ty = params[0];
        if (!binding.needs_addr_of) {
            if (self.assignable(receiver_ty, self_param_ty) != .success) {
                const expected_ty = self_param_ty;
                const actual_ty = receiver_ty;
                try self.context.diags.addError(exprLoc(ast_unit, field_expr), .argument_type_mismatch, .{ expected_ty, actual_ty });
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

        if (self.tryCoerceNullLiteral(ast_unit, args[i], pt)) {
            ast_unit.type_info.expr_types.items[args[i].toRaw()] = pt;
            at = pt;
            at_kind = self.typeKind(at);
        }

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
            const expected_ty = pt;
            const actual_ty = at;
            const loc = exprLocFromId(ast_unit, args[i]);
            const diag_idx = self.context.diags.count();
            try self.context.diags.addError(loc, .argument_type_mismatch, .{ expected_ty, actual_ty });
            try self.attachTryCastNote(diag_idx, pt);
            return self.context.type_store.tTypeError();
        }
    }

    var method_args: List(ast.ExprId) = .empty;
    defer method_args.deinit(self.gpa);
    if (binding.requires_implicit_receiver) {
        try method_args.append(self.gpa, field_expr.parent);
    }
    for (args) |arg| {
        try method_args.append(self.gpa, arg);
    }
    try self.maybeRecordRuntimeSpecialization(
        ctx,
        ast_unit,
        call_id,
        call_expr.callee,
        binding.method_name,
        method_args.items,
        binding.func_type,
    );

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

/// Return the cached type for `expr_id`, defaulting to `any` if unknown.
fn exprTypeFromInfo(self: *Checker, ast_unit: *ast.Ast, expr_id: ast.ExprId) types.TypeId {
    if (expr_id.toRaw() < ast_unit.type_info.expr_types.items.len) {
        if (ast_unit.type_info.expr_types.items[expr_id.toRaw()]) |ty| {
            return ty;
        }
    }
    return self.context.type_store.tAny();
}

/// Recognize range expressions used as spreads in trailing `any` tuples.
fn isSpreadRangeExprChecker(self: *Checker, ast_unit: *ast.Ast, expr: ast.ExprId) bool {
    if (ast_unit.kind(expr) != .Range) return false;
    const row = ast_unit.exprs.get(.Range, expr);
    if (!row.start.isNone()) return false;
    if (row.end.isNone()) return false;
    const end_expr = row.end.unwrap();
    const end_ty = self.exprTypeFromInfo(ast_unit, end_expr);
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
    if (start_index >= args.len) {
        return self.context.type_store.mkTuple(&.{});
    }
    const trailing_len = args.len - start_index;
    if (trailing_len == 1 and !self.isSpreadRangeExprChecker(ast_unit, args[start_index])) {
        return self.exprTypeFromInfo(ast_unit, args[start_index]);
    }
    var elem_types = std.ArrayList(types.TypeId){};
    defer elem_types.deinit(self.gpa);

    var idx = start_index;
    while (idx < args.len) : (idx += 1) {
        try elem_types.append(self.gpa, self.exprTypeFromInfo(ast_unit, args[idx]));
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
    if (ast_unit.type_info.getSpecializedCall(call_id)) |_| {
        return;
    }
    var decl_ctx = call_resolution.findFunctionDeclForCall(self.context, ast_unit, callee_expr, callee_name) orelse return;
    decl_ctx = resolveFunctionDeclAlias(self, decl_ctx) orelse decl_ctx;
    const decl = decl_ctx.ast.exprs.Decl.get(decl_ctx.decl_id);
    if (decl_ctx.ast.kind(decl.value) != .FunctionLit) return;
    const fn_lit = decl_ctx.ast.exprs.get(.FunctionLit, decl.value);
    const params = decl_ctx.ast.exprs.param_pool.slice(fn_lit.params);

    var skip_params: usize = 0;
    while (skip_params < params.len and decl_ctx.ast.exprs.Param.get(params[skip_params]).is_comptime) : (skip_params += 1) {}

    const fnrow = self.context.type_store.get(.Function, fn_ty);
    const param_tys = self.context.type_store.type_pool.slice(fnrow.params);
    const treat_trailing_any = !fnrow.is_extern and param_tys.len > 0 and self.typeKind(param_tys[param_tys.len - 1]) == .Any;

    var runtime_specs: List(ParamSpecialization) = .empty;
    defer runtime_specs.deinit(self.gpa);

    var runtime_idx: usize = skip_params;
    while (runtime_idx < params.len and runtime_idx < args.len) : (runtime_idx += 1) {
        const param = decl_ctx.ast.exprs.Param.get(params[runtime_idx]);
        if (param.pat.isNone()) continue;
        const pname = bindingNameOfPattern(decl_ctx.ast, param.pat.unwrap()) orelse continue;
        const param_ty = if (runtime_idx < param_tys.len) param_tys[runtime_idx] else self.context.type_store.tAny();
        if (self.typeKind(param_ty) != .Any) continue;
        const arg_ty = self.exprTypeFromInfo(ast_unit, args[runtime_idx]);
        if (self.typeKind(arg_ty) == .Any) continue;
        try runtime_specs.append(self.gpa, .{ .name = pname, .ty = arg_ty });
    }

    if (treat_trailing_any and params.len > 0) {
        const tuple_start = params.len - 1;
        const tuple_ty = try self.computeTrailingAnyTupleTypeChecker(ast_unit, args, tuple_start);
        const tuple_kind = self.typeKind(tuple_ty);
        if (!(tuple_kind == .Tuple and self.context.type_store.get(.Tuple, tuple_ty).elems.len == 0)) {
            const last_param = decl_ctx.ast.exprs.Param.get(params[tuple_start]);
            if (!last_param.pat.isNone()) {
                if (bindingNameOfPattern(decl_ctx.ast, last_param.pat.unwrap())) |pname| {
                    try runtime_specs.append(self.gpa, .{ .name = pname, .ty = tuple_ty });
                }
            }
        }
    }

    if (runtime_specs.items.len == 0)
        return;
    if (decl_ctx.ast.file_id >= self.checker_ctx.items.len)
        return;

    const target_ctx = &self.checker_ctx.items[decl_ctx.ast.file_id];
    _ = try self.checkSpecializedFunction(target_ctx, decl_ctx.ast, decl_ctx.decl_id, runtime_specs.items, null);
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
        if (kind == .FunctionLit) return current;
        if (kind == .Import) return null;
        if (kind == .FieldAccess) {
            const fr = current.ast.exprs.get(.FieldAccess, decl.value);
            if (call_resolution.findFunctionDeclFromFieldAccess(self.context, current.ast, fr, fr.field)) |resolved| {
                if (resolved.ast != current.ast or !resolved.decl_id.eq(current.decl_id)) {
                    return resolved;
                }
            }
            return current;
        }
        const alias_name = aliasTargetName(current.ast, decl.value) orelse return current;
        const next = call_resolution.findFunctionDeclForCall(self.context, current.ast, decl.value, alias_name) orelse return current;
        if (next.ast == current.ast and next.decl_id.eq(current.decl_id)) return current;
        current = next;
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
    return try self.checkExpr(ctx, ast_unit, cb.block);
}

/// Treat async blocks opaquely by always returning `Any`.
fn checkAsyncBlock(self: *Checker, id: ast.ExprId) !types.TypeId {
    _ = id;
    // Treat async blocks as opaque for typing.
    return self.context.type_store.tAny();
}

/// Validate an `mlir` block: check args, enforce comptime splices, and stamp the resulting type.
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
            try self.context.diags.addError(loc, .mlir_splice_not_comptime, .{getStr(ast_unit, name)});
            return self.context.type_store.tTypeError();
        }

        if (!sym.origin_decl.isNone() and sym.is_comptime) {
            const did = sym.origin_decl.unwrap();
            try ast_unit.type_info.setMlirSpliceInfo(pid, .{ .decl = .{ .decl_id = did, .name = name } });
            const decl = ast_unit.exprs.Decl.get(did);
            var computed = try self.evalComptimeExpr(ctx, ast_unit, decl.value, &[_]Pipeline.ComptimeBinding{});
            const value_clone = try comp.cloneComptimeValue(self.gpa, computed);
            try ast_unit.type_info.setMlirSpliceValue(pid, value_clone);
            computed.destroy(self.gpa);
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

/// Type-check the `.insert` expression by checking its operand (returns `Any`).
fn checkInsert(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const r = getExpr(ast_unit, .Insert, id);
    _ = try self.checkExpr(ctx, ast_unit, r.expr);
    return self.context.type_store.tAny();
}

/// Ensure a `return` statement matches enclosing function requirements and emit diagnostics.
fn checkReturn(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, rr: ast.Rows.Return) !types.TypeId {
    if (ctx.func_stack.items.len == 0) {
        try self.context.diags.addError(exprLoc(ast_unit, rr), .return_outside_function, .{});
        return self.context.type_store.tTypeError();
    }
    const current_func = ctx.func_stack.items[ctx.func_stack.items.len - 1];

    const expect_ty = current_func.result;
    const has_value = !rr.value.isNone();
    var ret_ty = if (!has_value) self.context.type_store.tVoid() else blk: {
        try self.pushValueReq(ctx, true);
        const t = try self.checkExpr(ctx, ast_unit, rr.value.unwrap());
        self.popValueReq(ctx);
        break :blk t;
    };
    if (self.typeKind(ret_ty) == .TypeError) return self.context.type_store.tTypeError();

    if (current_func.has_result and !has_value) {
        try self.context.diags.addError(
            exprLoc(ast_unit, rr),
            .missing_return_value,
            .{expect_ty},
        );
        return self.context.type_store.tTypeError();
    }
    if (!current_func.has_result and has_value) {
        try self.context.diags.addError(
            exprLoc(ast_unit, rr),
            .return_value_in_void_function,
            .{ret_ty},
        );
        return self.context.type_store.tTypeError();
    }

    if (!rr.value.isNone()) {
        if (self.tryCoerceNullLiteral(ast_unit, rr.value.unwrap(), expect_ty)) {
            ast_unit.type_info.expr_types.items[rr.value.unwrap().toRaw()] = expect_ty;
            ret_ty = expect_ty;
        }
    }

    // Opportunistically refine the function result when it was declared as `any` or `type` of `any`.
    var func_ctx = &ctx.func_stack.items[ctx.func_stack.items.len - 1];
    if (func_ctx.inferred_result == null) {
        const expect_kind = self.typeKind(expect_ty);
        if (expect_kind == .Any and self.typeKind(ret_ty) != .Any and self.typeKind(ret_ty) != .TypeError) {
            func_ctx.inferred_result = ret_ty;
        } else if (expect_kind == .TypeType) {
            const expect_of = self.context.type_store.get(.TypeType, expect_ty).of;
            if (self.typeKind(expect_of) == .Any) {
                if (self.typeKind(ret_ty) == .TypeType) {
                    const ret_of = self.context.type_store.get(.TypeType, ret_ty).of;
                    if (self.typeKind(ret_of) != .Any and self.typeKind(ret_of) != .TypeError) {
                        func_ctx.inferred_result = ret_ty;
                    }
                } else if (self.typeKind(ret_ty) != .TypeError) {
                    const wrapped = self.context.type_store.mkTypeType(ret_ty);
                    func_ctx.inferred_result = wrapped;
                    ret_ty = wrapped;
                }
            }
        }
    }

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
        try self.context.diags.addError(
            exprLoc(ast_unit, rr),
            .return_type_mismatch,
            .{ expect_ty, ret_ty },
        );
        return self.context.type_store.tTypeError();
    }
    return ret_ty;
}

/// Type-check an `if` expression or statement, ensuring both branches agree on types.
fn checkIf(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const if_expr = getExpr(ast_unit, .If, id);

    // Condition expects bool
    try self.pushExpectedType(ctx, self.context.type_store.tBool());
    const cond = try self.checkExpr(ctx, ast_unit, if_expr.cond);
    self.popExpectedType(ctx);

    if (!cond.eq(self.context.type_store.tBool())) {
        const cond_ty = self.typeKind(cond);
        try self.context.diags.addError(exprLoc(ast_unit, if_expr), .non_boolean_condition, .{cond_ty});
        return self.context.type_store.tTypeError();
    }

    const value_required = self.isValueReq(ctx);
    const expected_ty = self.getExpectedType(ctx);

    if (!value_required) {
        try self.pushExpectedType(ctx, null); // No value expected in sub-blocks
        defer self.popExpectedType(ctx);
        _ = try self.checkExpr(ctx, ast_unit, if_expr.then_block);
        if (!if_expr.else_block.isNone()) _ = try self.checkExpr(ctx, ast_unit, if_expr.else_block.unwrap());
        return self.context.type_store.tVoid();
    }

    // Push expected type for branches so they can use it for inference (e.g. null literals)
    try self.pushExpectedType(ctx, expected_ty);
    const then_ty = try self.checkExpr(ctx, ast_unit, if_expr.then_block);
    self.popExpectedType(ctx);

    if (self.typeKind(then_ty) == .TypeError) return self.context.type_store.tTypeError();
    if (if_expr.else_block.isNone()) {
        if (self.typeKind(then_ty) == .Noreturn) {
            return self.context.type_store.tNoreturn();
        }
        try self.context.diags.addError(exprLoc(ast_unit, if_expr), .if_expression_requires_else, .{});
        return self.context.type_store.tTypeError();
    }

    try self.pushExpectedType(ctx, expected_ty);
    const else_ty = try self.checkExpr(ctx, ast_unit, if_expr.else_block.unwrap());
    self.popExpectedType(ctx);

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

    if (then_ty.eq(else_ty)) return then_ty;

    if (expected_ty) |expect| {
        // If both branches successfully coerced to expected type (via pushExpectedType down to checkExpr),
        // then then_ty and else_ty might already be expect.
        // If not, check if they are assignable.
        const t_ok = self.assignable(then_ty, expect) == .success;
        const e_ok = self.assignable(else_ty, expect) == .success;
        if (t_ok and e_ok) return expect;
    }

    // Fallback: manual coercion of direct null literals (for cases where pushExpectedType didn't catch it?
    // Actually, if pushExpectedType works, checkExpr(NullLit) returns expect.
    // But if checkExpr returned something else (e.g. block returned ?any but we wanted ?i32?),
    // wait, if block returned ?any, it means null inside didn't see expected type?
    // If we push expected type, checkBlock -> checkExpr(last) -> ... -> checkExpr(NullLit) should see it.
    // So we shouldn't need tryCoerceNullLiteral here if the stack works!

    // But let's keep unification as fallback.

    if (self.unifyTypes(then_ty, else_ty)) |u| {
        return u;
    }
    try self.context.diags.addError(
        exprLoc(ast_unit, if_expr),
        .if_branch_type_mismatch,
        .{ then_ty, else_ty },
    );
    return self.context.type_store.tTypeError();
}

/// Try to reconcile `a` and `b` by picking a castable/superset type when possible.
fn unifyTypes(self: *Checker, a: types.TypeId, b: types.TypeId) ?types.TypeId {
    if (a.eq(b)) return a;
    const ak = self.typeKind(a);
    const bk = self.typeKind(b);

    if (ak == .Any) return null;
    if (bk == .Any) return null;

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

/// Normalize the numeric types `a` and `b` to a common type for comparison purposes.
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
    const asz = check_types.typeSize(self.context, a);
    const bsz = check_types.typeSize(self.context, b);
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

/// Type-check `while` loops, including pattern matching and loop result tracking.
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

/// Handle `unreachable` expressions (no-op besides returning `any`).
fn checkUnreachable(self: *Checker, _: ast.ExprId) !types.TypeId {
    return self.context.type_store.tAny();
}

/// Validate `for` loops over iterable collections and establish loop bindings.
fn checkFor(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const fr = getExpr(ast_unit, .For, id);
    const it = try self.checkExpr(ctx, ast_unit, fr.iterable);
    const kind = self.typeKind(it);

    switch (kind) {
        .Array, .Slice, .DynArray => {
            const subject_ty: types.TypeId = switch (ast_unit.kind(fr.pattern)) {
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
            try self.context.diags.addError(exprLoc(ast_unit, fr), .non_iterable_in_for, .{it});
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

/// Return true when `got` is allowed to be cast to `expect` (even if not assignable).
fn castable(self: *Checker, got: types.TypeId, expect: types.TypeId) bool {
    if (got.eq(expect)) return true;
    const gk = self.typeKind(got);
    const ek = self.typeKind(expect);

    if (self.isSliceOfU8(got) and ek == .String) return true;
    if (gk == .String and self.isSliceOfU8(expect)) return true;

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

    if (gk == .Enum and check_types.isIntegerKind(self, ek)) return true;
    if (ek == .Enum and check_types.isIntegerKind(self, gk)) return true;

    // Pointer-to-pointer
    if (gk == .Ptr and ek == .Ptr) return true;

    return false;
}

fn isSliceOfU8(self: *Checker, ty: types.TypeId) bool {
    if (self.typeKind(ty) != .Slice) return false;
    const slice = self.context.type_store.get(.Slice, ty);
    return slice.elem.eq(self.context.type_store.tU8());
}

/// Validate a `break` statement, ensuring loop contexts/values align.
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
                if (!val_ty.?.eq(rt)) {
                    try self.context.diags.addError(
                        exprLoc(ast_unit, br),
                        .loop_break_value_type_conflict,
                        .{ rt, val_ty.? },
                    );
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

/// Handle `continue` expressions (no type, but ensures location is tracked).
fn checkContinue(self: *Checker, id: ast.ExprId) !types.TypeId {
    _ = id;
    return self.context.type_store.tVoid();
}

/// Validate `defer` expressions inside functions only.
fn checkDefer(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, defer_expr: ast.Rows.Defer) !types.TypeId {
    if (!self.inFunction(ctx)) {
        try self.context.diags.addError(exprLoc(ast_unit, defer_expr), .defer_outside_function, .{});
    }
    _ = try self.checkExpr(ctx, ast_unit, defer_expr.expr);
    return self.context.type_store.tVoid();
}

/// Validate `err defer` expressions, requiring enclosing error functions.
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

/// Type-check `err.unwrap` ensuring the enclosing function returns an `ErrorSet`.
fn checkErrUnwrap(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const eur = getExpr(ast_unit, .ErrUnwrap, id);
    const et = try self.checkExpr(ctx, ast_unit, eur.expr);
    if (self.typeKind(et) == .TypeError)
        return self.context.type_store.tTypeError();
    if (self.typeKind(et) != .ErrorSet) {
        try self.context.diags.addError(
            exprLoc(ast_unit, eur),
            .error_propagation_on_non_error,
            .{et},
        );
        return self.context.type_store.tTypeError();
    }
    const er = self.context.type_store.get(.ErrorSet, et);

    if (!self.inFunction(ctx)) {
        try self.context.diags.addError(
            exprLoc(ast_unit, eur),
            .error_propagation_mismatched_function_result,
            StringPayload{ .value = "unknown context" },
        );
        return self.context.type_store.tTypeError();
    }
    const fctx = self.currentFunc(ctx).?;
    const fk = self.typeKind(fctx.result);
    if (fk != .ErrorSet) {
        try self.context.diags.addError(
            exprLoc(ast_unit, eur),
            .error_propagation_mismatched_function_result,
            .{fctx.result},
        );
        return self.context.type_store.tTypeError();
    }

    // Ensure the error/value halves align with the function result type
    const fr = self.context.type_store.get(.ErrorSet, fctx.result);
    if (self.assignable(er.error_ty, fr.error_ty) != .success or self.assignable(er.value_ty, fr.value_ty) != .success) {
        try self.context.diags.addError(
            exprLoc(ast_unit, eur),
            .error_propagation_mismatched_function_result,
            .{fctx.result},
        );
        return self.context.type_store.tTypeError();
    }
    return er.value_ty;
}

/// Validate optional unwrap (`?`) operations.
fn checkOptionalUnwrap(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const our = getExpr(ast_unit, .OptionalUnwrap, id);
    const ot = try self.checkExpr(ctx, ast_unit, our.expr);
    if (self.typeKind(ot) == .TypeError)
        return self.context.type_store.tTypeError();
    if (self.typeKind(ot) != .Optional) {
        try self.context.diags.addError(
            exprLoc(ast_unit, our),
            .invalid_optional_unwrap_target,
            .{ot},
        );
        return self.context.type_store.tTypeError();
    }
    const ore = self.context.type_store.get(.Optional, ot);
    return ore.elem;
}

/// Placeholder handling for `await` expressions (currently permits `any`).
fn checkAwait(self: *Checker, id: ast.ExprId) !types.TypeId {
    _ = id;
    return self.context.type_store.tAny();
}

/// Type-check closure literals, requiring explicit parameter annotations.
fn checkClosure(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const cr = getExpr(ast_unit, .Closure, id);
    const params = ast_unit.exprs.param_pool.slice(cr.params);

    var param_tys = try self.context.type_store.gpa.alloc(types.TypeId, params.len);
    defer self.context.type_store.gpa.free(param_tys);

    var i: usize = 0;
    while (i < params.len) : (i += 1) {
        const p = ast_unit.exprs.Param.get(params[i]);
        if (p.ty.isNone()) {
            try self.context.diags.addError(
                exprLoc(ast_unit, p),
                .type_annotation_mismatch,
                .{},
            );
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
    return self.context.type_store.mkFunction(param_tys, body_ty, false, true, false);
}

/// Handle different cast/kind modifiers, validating safety and recording results.
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
            if (vk == .Any or ek == .Any) {} else if (gsize != tsize) {
                try self.context.diags.addError(exprLoc(ast_unit, cr), .invalid_bitcast, .{ vk, ek });
            }
        },
        .saturate, .wrap => {
            if (!check_types.isNumericKind(self, vk) or !check_types.isNumericKind(self, ek)) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, cr),
                    .numeric_cast_on_non_numeric,
                    .{vk},
                );
                return self.context.type_store.tTypeError();
            }
        },
        .checked => {
            if (self.assignable(vt, et) != .success and !self.castable(vt, et)) {
                try self.context.diags.addError(
                    exprLoc(ast_unit, cr),
                    .invalid_checked_cast,
                    .{ vk, ek },
                );
                return self.context.type_store.tTypeError();
            }
            return self.context.type_store.mkOptional(et);
        },
    }
    return et;
}

/// Type-check `catch` expressions, ensuring handler types match automations.
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
        try self.context.diags.addError(
            exprLoc(ast_unit, row),
            .catch_on_non_error,
            .{lhs_ty},
        );
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
        try self.context.diags.addError(
            exprLoc(ast_unit, row),
            .catch_handler_type_mismatch,
            .{ want_ok_ty, handler_ty.? },
        );
        return self.context.type_store.tTypeError();
    }

    return result_ty;
}

/// Resolve import expressions to module-type proxies used during checking.
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

    try self.context.diags.addError(
        ast_unit.exprs.locs.get(ir.loc),
        .import_not_found,
        StringPayload{ .value = filepath },
    );
    return self.context.type_store.tTypeError();
}

// =========================
// Misc helpers
// =========================

/// Emit diagnostics when literal `rhs` divides by zero.
fn checkDivByZero(self: *Checker, ast_unit: *ast.Ast, rhs: ast.ExprId, loc: Loc) !void {
    if (ast_unit.kind(rhs) != .Literal) return;
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

/// Emit error when integer literal `rhs` is zero in division/mod contexts.
fn checkIntZeroLiteral(self: *Checker, ast_unit: *ast.Ast, rhs: ast.ExprId, loc: Loc) !void {
    if (ast_unit.kind(rhs) != .Literal) return;
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

/// Categories describing where an lvalue ultimately resolves.
const LvalueRootKind = enum {
    /// The lvalue refers to a declaration tied to the current function body.
    LocalDecl,
    /// The lvalue resolves to a formal parameter.
    Param,
    /// The lvalue points to a global or outer declaration.
    NonLocalDecl,
    /// Unable to determine the origin of the lvalue.
    Unknown,
};
/// Determine whether the lvalue rooted at `expr` refers to a local, param, or other decl.
fn lvalueRootKind(self: *Checker, ctx: *CheckerContext, ast_unit: *ast.Ast, expr: ast.ExprId) LvalueRootKind {
    switch (ast_unit.kind(expr)) {
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

/// Payload type used for diagnostics that require a string argument (e.g., missing case lists).
pub const StringNotePayload = struct { value: ast.StrId };

/// Compute the Levenshtein distance between `s1` and `s2`, returning null on allocation failure.
fn levenshteinDistance(allocator: std.mem.Allocator, s1: []const u8, s2: []const u8) ?usize {
    const s1_len = s1.len;
    const s2_len = s2.len;

    if (s1_len == 0) return s2_len;
    if (s2_len == 0) return s1_len;

    var dp = allocator.alloc(usize, s1_len + 1) catch return null;
    defer allocator.free(dp);

    for (0..s1_len + 1) |i| {
        dp[i] = i;
    }

    for (1..s2_len + 1) |j| {
        var prev_dist: usize = dp[0];
        dp[0] = j;
        for (1..s1_len + 1) |i| {
            const temp = dp[i];
            const substitution_cost: usize = if (s1[i - 1] == s2[j - 1]) 0 else 1;
            dp[i] = @min(@min(dp[i - 1] + 1, dp[i] + 1), prev_dist + substitution_cost);
            prev_dist = temp;
        }
    }

    return dp[s1_len];
}

/// Among `candidates`, pick the best string-similarity match for `target`.
fn findBestSuggestion(self: *Checker, target: []const u8, candidates: []const []const u8) ?[]const u8 {
    var best: ?[]const u8 = null;
    var min_dist: usize = 3;
    for (candidates) |candidate| {
        if (levenshteinDistance(self.gpa, target, candidate)) |dist| {
            if (dist < min_dist) {
                min_dist = dist;
                best = candidate;
            }
        }
    }
    return best;
}

/// Append field names from `fields` to `list` (used for diagnostics).
fn appendFieldNames(self: *Checker, list: *std.ArrayList([]const u8), fields: []const types.FieldId) !void {
    for (fields) |fid| {
        const f = self.context.type_store.Field.get(fid);
        try list.append(self.gpa, self.context.interner.get(f.name));
    }
}

/// Append enum member names from `members` into `list`.
fn appendEnumMemberNames(self: *Checker, list: *std.ArrayList([]const u8), members: []const types.EnumMemberId) !void {
    for (members) |mid| {
        const m = self.context.type_store.EnumMember.get(mid);
        try list.append(self.gpa, self.context.interner.get(m.name));
    }
}

/// Attach suggestion notes referencing `candidates` to diagnostic `diag_idx`.
fn attachSuggestionListNotes(
    self: *Checker,
    diag_idx: usize,
    target: []const u8,
    candidates: []const []const u8,
    comptime suggestion_code: diag.NoteCode,
    comptime available_code: ?diag.NoteCode,
) !void {
    if (candidates.len == 0) return;
    if (self.findBestSuggestion(target, candidates)) |suggestion| {
        try self.context.diags.attachNoteArgs(diag_idx, null, suggestion_code, .{suggestion});
    }
    if (available_code) |code| {
        const joined = try diag.joinStrings(self.gpa, ", ", candidates);
        if (joined.len > 0) {
            const joined_id = self.context.interner.intern(joined);
            self.gpa.free(joined);
            try self.context.diags.attachNoteArgs(diag_idx, null, code, StringNotePayload{ .value = joined_id });
        } else {
            self.gpa.free(joined);
        }
    }
}

/// Consider `sym_id` for typo suggestions against `ident_name`.
fn considerSymbolSuggestion(
    self: *Checker,
    ctx: *CheckerContext,
    ast_unit: *ast.Ast,
    ident_name: []const u8,
    seen: *std.ArrayList(ast.StrId),
    best_suggestion: *?[]const u8,
    min_dist: *usize,
    sym_id: symbols.SymbolId,
) !void {
    const sym = ctx.symtab.syms.get(sym_id);
    for (seen.items) |sid| {
        if (sid.eq(sym.name)) return;
    }
    try seen.append(self.gpa, sym.name);

    const sym_name = ast_unit.exprs.strs.get(sym.name);
    if (sym_name.len == 0) return;

    if (levenshteinDistance(self.gpa, ident_name, sym_name)) |dist| {
        if (dist < min_dist.*) {
            min_dist.* = dist;
            best_suggestion.* = sym_name;
        }
    }
}

/// Format `type_id` into a string interner entry for diagnostics.
fn formatTypeForNote(self: *Checker, type_id: types.TypeId) !ast.StrId {
    var buf = std.ArrayList(u8){};
    defer buf.deinit(self.gpa);
    const writer = buf.writer(self.gpa);
    try self.context.type_store.formatTypeForDiagnostic(type_id, .{}, writer);
    const slice = buf.items[0..buf.items.len];
    return self.context.interner.intern(slice);
}

/// Attach a note displaying the signature of `func_ty` to diagnostic `diag_idx`.
fn attachFunctionSignatureNote(self: *Checker, diag_idx: usize, func_ty: types.TypeId) !void {
    const signature = try formatTypeForNote(self, func_ty);
    try self.context.diags.attachNoteArgs(diag_idx, null, .function_signature, StringNotePayload{ .value = signature });
}

/// Add a `try_cast` note suggesting an explicit cast to `expected_ty`.
fn attachTryCastNote(self: *Checker, diag_idx: usize, expected_ty: types.TypeId) !void {
    var buf = std.ArrayList(u8){};
    defer buf.deinit(self.gpa);
    var writer = buf.writer(self.gpa);
    try writer.print("cast to ", .{});
    try self.context.type_store.formatTypeForDiagnostic(expected_ty, .{}, writer);
    const suggestion = buf.items[0..buf.items.len];
    const suggestion_id = self.context.interner.intern(suggestion);
    try self.context.diags.attachNoteArgs(diag_idx, null, .try_cast, StringNotePayload{ .value = suggestion_id });
}
