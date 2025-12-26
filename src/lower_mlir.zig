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
    host: *anyopaque,
    lowerExprValue: *const fn (*anyopaque, *ast.Ast, *anyopaque, *Builder.FunctionFrame, *Builder.BlockFrame, ast.ExprId, ?types.TypeId) anyerror!tir.ValueId,
    evalComptimeExpr: *const fn (*anyopaque, *ast.Ast, *anyopaque, *Builder.FunctionFrame, *Builder.BlockFrame, ast.ExprId, types.TypeId) anyerror!comp.ComptimeValue,
    emitCoerce: *const fn (*anyopaque, *Builder.BlockFrame, tir.ValueId, types.TypeId, types.TypeId, tir.OptLocId) anyerror!tir.ValueId,
    getExprType: *const fn (*anyopaque, *ast.Ast, ast.ExprId) ?types.TypeId,
    getDeclType: *const fn (*anyopaque, *ast.Ast, ast.DeclId) ?types.TypeId,
    isAny: *const fn (*anyopaque, types.TypeId) bool,
    lookupMonomorphValue: *const fn (*anyopaque, ast.StrId) anyerror!?comp.ComptimeValue,
    lookupMonomorphType: *const fn (*anyopaque, ast.StrId) ?types.TypeId,
    createEnv: *const fn (*anyopaque) anyerror!*anyopaque,
    destroyEnv: *const fn (*anyopaque, *anyopaque) void,
};

/// Wrapper managing MLIR context and lowering helpers.
pub const LowerMlir = struct {
    gpa: std.mem.Allocator,
    context: *compile.Context,
    state: State = {},
    trace_enabled: bool = false,
    stats: Stats = {},

    const State = struct {
        initialized: bool = false,
        ctx: mlir.Context = undefined,
    };

    pub fn init(gpa: std.mem.Allocator, context: *compile.Context) LowerMlir {
        return .{
            .gpa = gpa,
            .context = context,
            .trace_enabled = std.os.getenv("SR_MLIR_TRACE") != null,
        };
    }

    pub fn deinit(self: *LowerMlir) void {
        if (self.trace_enabled) self.dumpStats();
        if (self.state.initialized) {
            self.state.ctx.destroy();
            self.state = .{};
        }
    }

    pub fn ensureContext(self: *LowerMlir) mlir.Context {
        if (!self.state.initialized) {
            self.state.ctx = compile.initMLIR(self.gpa);
            self.state.initialized = true;
        }
        return self.state.ctx;
    }

    inline fn recordBlock(self: *LowerMlir, piece_count: usize, arg_count: usize) void {
        if (!self.trace_enabled) return;
        self.stats.block_count += 1;
        self.stats.total_pieces += piece_count;
        self.stats.total_args += arg_count;
        if (piece_count > self.stats.max_pieces) self.stats.max_pieces = piece_count;
        if (arg_count > self.stats.max_args) self.stats.max_args = arg_count;
    }

    inline fn noteGlobalInit(self: *LowerMlir, decl_count: usize) void {
        if (!self.trace_enabled or decl_count == 0) return;
        self.stats.global_init_blocks += 1;
        self.stats.global_init_decls += decl_count;
    }

    fn dumpStats(self: *LowerMlir) void {
        const s = self.stats;
        std.debug.print(
            "MLIR lowering trace: {d} blocks, {d} pieces (max {d}), {d} args (max {d}), {d} global init funcs covering {d} decls\n",
            .{ s.block_count, s.total_pieces, s.max_pieces, s.total_args, s.max_args, s.global_init_blocks, s.global_init_decls },
        );
    }

    pub fn emitGlobalInit(self: *LowerMlir, hooks: Hooks, a: *ast.Ast, b: *Builder) !void {
        var global_mlir_decls = std.ArrayListUnmanaged(ast.DeclId){};
        defer global_mlir_decls.deinit(self.gpa);

        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        // Optimization: Pre-scan to avoid over-allocation, though ensureTotalCapacity is usually sufficient.
        // Given decls are mixed, we stick to dynamic growth but start with a reasonable heuristic or 0.
        // Here we just iterate once.
        for (decls) |did| {
            const d = a.exprs.Decl.get(did);
            if (a.kind(d.value) == .MlirBlock and d.pattern.isNone()) {
                try global_mlir_decls.append(self.gpa, did);
            }
        }

        const items = global_mlir_decls.items;
        if (items.len == 0) return;
        self.noteGlobalInit(items.len);

        const name = b.intern("__sr_global_mlir_init");
        var f = try b.beginFunction(self.context, name, self.context.type_store.tVoid(), false, false, .empty(), false, false, .none());
        var blk = try b.beginBlock(&f);

        const env_ptr = try hooks.createEnv(hooks.host);
        defer hooks.destroyEnv(hooks.host, env_ptr);

        for (items) |did| {
            const d = a.exprs.Decl.get(did);
            _ = try hooks.lowerExprValue(hooks.host, a, env_ptr, &f, &blk, d.value, null);
        }

        if (blk.term.isNone()) try b.setReturn(&blk, .none(), .none());
        try b.endBlock(&f, blk);
        try b.endFunction(f);
    }

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
                .Attribute => self.context.type_store.mkMlirAttribute(row.text),
                .Type => self.context.type_store.mkTypeType(self.context.type_store.mkMlirType(row.text)),
                .Operation => ty0,
            };
            // If we still have Any, but the caller expected a concrete type, use the expected type.
            if (expected_ty) |want| {
                if (!hooks.isAny(hooks.host, want)) ty0 = want;
            }
        }

        // Optimization: Allocate exact size buffers for pieces and args to avoid ArrayList resizing overhead.
        const ast_piece_ids = a.exprs.mlir_piece_pool.slice(row.pieces);
        const tir_pieces = try self.gpa.alloc(tir.MlirPieceId, ast_piece_ids.len);
        defer self.gpa.free(tir_pieces);

        for (ast_piece_ids, 0..) |pid, i| {
            const piece = a.exprs.MlirPiece.get(pid);
            const splice_val = if (piece.kind == .splice)
                try self.resolveSpliceValue(hooks, a, env_ptr, f, blk, pid, piece.text, row.loc)
            else
                comp.ComptimeValue.Void;

            tir_pieces[i] = blk.builder.t.instrs.addMlirPieceRow(.{ .kind = piece.kind, .text = piece.text, .value = splice_val, .ty = null });
        }
        const pieces_range = blk.builder.t.instrs.mlir_piece_pool.pushMany(self.gpa, tir_pieces);

        const arg_ids = a.exprs.expr_pool.slice(row.args);
        self.recordBlock(ast_piece_ids.len, arg_ids.len);

        const arg_vals = try self.gpa.alloc(tir.ValueId, arg_ids.len);
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
        try blk.instrs.append(self.gpa, iid);

        if (expected_ty) |want| {
            if (!ty0.eq(want)) return hooks.emitCoerce(hooks.host, blk, result_id, ty0, want, loc);
        }
        return result_id;
    }

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
        return switch (info) {
            .decl => |d_info| blk: {
                const decl = a.exprs.Decl.get(d_info.decl_id);
                const expect_ty = hooks.getDeclType(hooks.host, a, d_info.decl_id) orelse
                    (hooks.getExprType(hooks.host, a, decl.value) orelse self.context.type_store.tAny());
                break :blk try hooks.evalComptimeExpr(hooks.host, a, env_ptr, f, blk, decl.value, expect_ty);
            },
            .value_param => |p_info| blk: {
                if (try hooks.lookupMonomorphValue(hooks.host, p_info.name)) |val| break :blk val;
                try self.context.diags.addError(a.exprs.locs.get(loc_id), .mlir_splice_unbound, .{a.exprs.strs.get(name)});
                return error.LoweringBug;
            },
            .type_param => |p_info| blk: {
                if (hooks.lookupMonomorphType(hooks.host, p_info.name)) |ty| break :blk comp.ComptimeValue{ .Type = ty };
                try self.context.diags.addError(a.exprs.locs.get(loc_id), .mlir_splice_unbound, .{a.exprs.strs.get(name)});
                return error.LoweringBug;
            },
        };
    }
};

