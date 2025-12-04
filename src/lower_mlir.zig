const std = @import("std");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const comp = @import("comptime.zig");
const compile = @import("compile.zig");
const mlir = @import("mlir_bindings.zig");

const Builder = tir.Builder;

const Stats = struct {
    block_count: usize = 0,
    total_pieces: usize = 0,
    total_args: usize = 0,
    max_pieces: usize = 0,
    max_args: usize = 0,
    global_init_blocks: usize = 0,
    global_init_decls: usize = 0,
};

/// External hooks needed when lowering MLIR fragments.
pub const Hooks = struct {
    /// Host-provided context pointer forwarded to every callback.
    host: *anyopaque,
    /// Callback that lowers expressions inside MLIR fragments.
    lowerExprValue: *const fn (*anyopaque, *ast.Ast, *anyopaque, *Builder.FunctionFrame, *Builder.BlockFrame, ast.ExprId, ?types.TypeId) anyerror!tir.ValueId,
    /// Callback used to evaluate embedded comptime expressions inside MLIR.
    evalComptimeExpr: *const fn (*anyopaque, *ast.Ast, *anyopaque, *Builder.FunctionFrame, *Builder.BlockFrame, ast.ExprId, types.TypeId) anyerror!comp.ComptimeValue,
    /// Callback that coerces MLIR result values into expected types.
    emitCoerce: *const fn (*anyopaque, *Builder.BlockFrame, tir.ValueId, types.TypeId, types.TypeId, tir.OptLocId) anyerror!tir.ValueId,
    /// Callback returning the current type of an AST expression.
    getExprType: *const fn (*anyopaque, *ast.Ast, ast.ExprId) ?types.TypeId,
    /// Callback that fetches the declared type of a declaration.
    getDeclType: *const fn (*anyopaque, *ast.Ast, ast.DeclId) ?types.TypeId,
    /// Indicates whether a type maps to the wildcard `Any` placeholder.
    isAny: *const fn (*anyopaque, types.TypeId) bool,
    /// Lookup a previously bound comptime value for a monomorph parameter.
    lookupMonomorphValue: *const fn (*anyopaque, ast.StrId) anyerror!?comp.ComptimeValue,
    /// Lookup a previously bound type for a monomorph parameter.
    lookupMonomorphType: *const fn (*anyopaque, ast.StrId) ?types.TypeId,
    /// Create a fresh environment used by MLIR lowering hooks.
    createEnv: *const fn (*anyopaque) anyerror!*anyopaque,
    /// Destroy an environment that was created earlier.
    destroyEnv: *const fn (*anyopaque, *anyopaque) void,
};

/// Wrapper managing MLIR context and lowering helpers.
pub const LowerMlir = struct {
    /// Allocator used for temporary structures.
    gpa: std.mem.Allocator,
    /// Compiler context that owns the type store.
    context: *compile.Context,
    /// Tracks whether the MLIR context has been initialized.
    state: State = {},
    /// Tracking/trace state.
    trace_enabled: bool = false,
    stats: Stats = {},

    /// Tracks the lifecycle of the lazily-created MLIR context handle.
    const State = struct {
        /// Indicates whether the MLIR context has already been created.
        initialized: bool = false,
        /// Cached MLIR context handle.
        ctx: mlir.Context = undefined,
    };

    /// Initialize a `LowerMlir` handle with the provided allocator and compiler context.
    pub fn init(gpa: std.mem.Allocator, context: *compile.Context) LowerMlir {
        var trace = false;
        if (std.os.getenv("SR_MLIR_TRACE")) |_| trace = true;
        return .{ .gpa = gpa, .context = context, .trace_enabled = trace };
    }

    /// Destroy any owned MLIR state if it was created.
    pub fn deinit(self: *LowerMlir) void {
        if (self.trace_enabled) self.dumpStats();
        if (self.state.initialized) {
            self.state.ctx.destroy();
            self.state = .{};
        }
    }

    /// Lazily create the MLIR context and return it.
    pub fn ensureContext(self: *LowerMlir) mlir.Context {
        if (!self.state.initialized) {
            self.state.ctx = compile.initMLIR(self.gpa);
            self.state.initialized = true;
        }
        return self.state.ctx;
    }

    fn recordBlock(self: *LowerMlir, piece_count: usize, arg_count: usize) void {
        self.stats.block_count += 1;
        self.stats.total_pieces += piece_count;
        self.stats.total_args += arg_count;
        if (piece_count > self.stats.max_pieces) self.stats.max_pieces = piece_count;
        if (arg_count > self.stats.max_args) self.stats.max_args = arg_count;
    }

    fn noteGlobalInit(self: *LowerMlir, decl_count: usize) void {
        if (decl_count == 0) return;
        self.stats.global_init_blocks += 1;
        self.stats.global_init_decls += decl_count;
    }

    fn dumpStats(self: *LowerMlir) void {
        const s = self.stats;
        std.debug.print(
            "MLIR lowering trace: {d} blocks, {d} pieces (max {d}), {d} args (max {d}), {d} global init funcs covering {d} decls\n",
            .{
                s.block_count,
                s.total_pieces,
                s.max_pieces,
                s.total_args,
                s.max_args,
                s.global_init_blocks,
                s.global_init_decls,
            },
        );
    }

    /// Emit a global initialization function for embedded MLIR fragments collected from `a`.
    pub fn emitGlobalInit(self: *LowerMlir, hooks: Hooks, a: *ast.Ast, b: *Builder) !void {
        var global_mlir_decls = std.ArrayList(ast.DeclId){};
        defer global_mlir_decls.deinit(self.gpa);

        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        try global_mlir_decls.ensureTotalCapacity(self.gpa, decls.len);
        for (decls) |did| {
            const d = a.exprs.Decl.get(did);
            if (a.kind(d.value) == .MlirBlock and d.pattern.isNone()) {
                try global_mlir_decls.append(self.gpa, did);
            }
        }

        if (global_mlir_decls.items.len == 0) return;
        self.noteGlobalInit(global_mlir_decls.items.len);

        const name = b.intern("__sr_global_mlir_init");
        var f = try b.beginFunction(name, self.context.type_store.tVoid(), false, .empty());
        var blk = try b.beginBlock(&f);
        const env_ptr = try hooks.createEnv(hooks.host);
        defer hooks.destroyEnv(hooks.host, env_ptr);

        for (global_mlir_decls.items) |did| {
            const d = a.exprs.Decl.get(did);
            _ = try hooks.lowerExprValue(hooks.host, a, env_ptr, &f, &blk, d.value, null);
        }

        if (blk.term.isNone()) {
            try b.setReturn(&blk, .none(), tir.OptLocId.none());
        }
        try b.endBlock(&f, blk);
        try b.endFunction(f);
    }

    /// Lower the MLIR block expression `id`, handling slices and splices using `hooks`.
    pub fn lowerBlock(
        self: *LowerMlir,
        hooks: Hooks,
        a: *ast.Ast,
        env_ptr: *anyopaque,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        id: ast.ExprId,
        expected_ty: ?types.TypeId,
        loc: tir.OptLocId,
    ) !tir.ValueId {
        const row = a.exprs.get(.MlirBlock, id);
        const expr_ty_opt = hooks.getExprType(hooks.host, a, id);
        var ty0 = expr_ty_opt orelse (expected_ty orelse self.context.type_store.tAny());
        if (hooks.isAny(hooks.host, ty0)) {
            ty0 = switch (row.kind) {
                .Module => self.context.type_store.tMlirModule(),
                .Attribute => self.context.type_store.tMlirAttribute(),
                .Type => self.context.type_store.tMlirType(),
                .Operation => ty0,
            };
        }
        if (expected_ty) |want| {
            if (expr_ty_opt) |expr_ty| {
                if (hooks.isAny(hooks.host, expr_ty) and !hooks.isAny(hooks.host, want)) {
                    ty0 = want;
                }
            } else {
                ty0 = want;
            }
        }

        const ast_piece_ids = a.exprs.mlir_piece_pool.slice(row.pieces);
        var tir_piece_ids = std.ArrayListUnmanaged(tir.MlirPieceId){};
        try tir_piece_ids.ensureTotalCapacity(self.gpa, ast_piece_ids.len);
        defer tir_piece_ids.deinit(self.gpa);
        for (ast_piece_ids) |pid| {
            const piece = a.exprs.MlirPiece.get(pid);
            var splice_value: comp.ComptimeValue = .Void;
            if (piece.kind == .splice) {
                splice_value = try self.resolveSpliceValue(hooks, a, env_ptr, f, blk, pid, piece.text, row.loc);
            }
            const new_id = blk.builder.t.instrs.addMlirPieceRow(
                .{ .kind = piece.kind, .text = piece.text, .value = splice_value },
            );
            tir_piece_ids.append(self.gpa, new_id) catch @panic("OOM");
        }
        const pieces_range = blk.builder.t.instrs.mlir_piece_pool.pushMany(self.gpa, tir_piece_ids.items);

        const arg_ids = a.exprs.expr_pool.slice(row.args);
        self.recordBlock(ast_piece_ids.len, arg_ids.len);
        var arg_vals = try self.gpa.alloc(tir.ValueId, arg_ids.len);
        defer self.gpa.free(arg_vals);
        for (arg_ids, 0..) |arg_id, i| {
            arg_vals[i] = try hooks.lowerExprValue(hooks.host, a, env_ptr, f, blk, arg_id, null);
        }
        const args_range = blk.builder.t.instrs.value_pool.pushMany(self.gpa, arg_vals);

        const result_id = blk.builder.freshValue();
        const iid = blk.builder.t.instrs.add(.MlirBlock, .{
            .result = .some(result_id),
            .ty = ty0,
            .kind = row.kind,
            .expr = id,
            .text = row.text,
            .pieces = pieces_range,
            .args = args_range,
            .loc = loc,
        });
        blk.instrs.append(self.gpa, iid) catch @panic("OOM");
        if (expected_ty) |want| {
            if (!ty0.eq(want)) {
                return hooks.emitCoerce(hooks.host, blk, result_id, ty0, want, loc);
            }
        }
        return result_id;
    }

    /// Resolve the value that should be spliced into MLIR for `piece_id`.
    fn resolveSpliceValue(
        self: *LowerMlir,
        hooks: Hooks,
        a: *ast.Ast,
        env_ptr: *anyopaque,
        f: *Builder.FunctionFrame,
        blk: *Builder.BlockFrame,
        piece_id: ast.MlirPieceId,
        name: ast.StrId,
        loc_id: ast.LocId,
    ) !comp.ComptimeValue {
        const info = a.type_info.getMlirSpliceInfo(piece_id) orelse return error.LoweringBug;
        const diag_loc = a.exprs.locs.get(loc_id);
        const name_str = a.exprs.strs.get(name);
        return switch (info) {
            .decl => |decl_info| blk: {
                const decl = a.exprs.Decl.get(decl_info.decl_id);
                const expect_ty = hooks.getDeclType(hooks.host, a, decl_info.decl_id) orelse
                    (hooks.getExprType(hooks.host, a, decl.value) orelse self.context.type_store.tAny());
                break :blk try hooks.evalComptimeExpr(hooks.host, a, env_ptr, f, blk, decl.value, expect_ty);
            },
            .value_param => |param_info| blk: {
                const maybe_val = try hooks.lookupMonomorphValue(hooks.host, param_info.name);
                if (maybe_val) |val| break :blk val;
                try self.context.diags.addError(diag_loc, .mlir_splice_unbound, .{name_str});
                return error.LoweringBug;
            },
            .type_param => |param_info| blk: {
                if (hooks.lookupMonomorphType(hooks.host, param_info.name)) |ty| {
                    break :blk comp.ComptimeValue{ .Type = ty };
                }
                try self.context.diags.addError(diag_loc, .mlir_splice_unbound, .{name_str});
                return error.LoweringBug;
            },
        };
    }
};
