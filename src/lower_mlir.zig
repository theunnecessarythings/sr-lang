const std = @import("std");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");
const comp = @import("comptime.zig");
const compile = @import("compile.zig");
const mlir = @import("mlir_bindings.zig");

const Builder = tir.Builder;

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

pub const LowerMlir = struct {
    gpa: std.mem.Allocator,
    context: *compile.Context,
    state: State = .{},

    const State = struct {
        initialized: bool = false,
        ctx: mlir.Context = undefined,
    };

    pub fn init(gpa: std.mem.Allocator, context: *compile.Context) LowerMlir {
        return .{ .gpa = gpa, .context = context };
    }

    pub fn deinit(self: *LowerMlir) void {
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

    pub fn emitGlobalInit(self: *LowerMlir, hooks: Hooks, a: *ast.Ast, b: *Builder) !void {
        var global_mlir_decls = std.ArrayList(ast.DeclId){};
        defer global_mlir_decls.deinit(self.gpa);

        const decls = a.exprs.decl_pool.slice(a.unit.decls);
        for (decls) |did| {
            const d = a.exprs.Decl.get(did);
            const kind = a.exprs.index.kinds.items[d.value.toRaw()];
            if (kind == .MlirBlock and d.pattern.isNone()) {
                try global_mlir_decls.append(self.gpa, did);
            }
        }

        if (global_mlir_decls.items.len == 0) return;

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
