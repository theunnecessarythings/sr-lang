const std = @import("std");
const ast = @import("ast.zig");
const tir = @import("tir.zig");
const types = @import("types.zig");

const Allocator = std.mem.Allocator;
const ArrayList = std.array_list.Managed;
const AutoHashMap = std.AutoHashMap;
const StringHashMap = std.StringHashMap;

const LowerError = error{
    UnsupportedAstNode,
    SemanticError, // e.g. variable not found or missing type
    OutOfMemory,
};

var g_lambda_counter: usize = 0;

pub const LowerTir = struct {
    allocator: Allocator,
    type_arena: *types.TypeArena,
    expr_types: *AutoHashMap(*const ast.Expr, types.TypeId),
    decl_types: *AutoHashMap(*const ast.Decl, types.TypeId),
    module: tir.Module,
    builder: tir.Builder,
    void_t: types.TypeId,
    bool_t: types.TypeId,
    usize_t: ?types.TypeId = null,
    string_t: ?types.TypeId = null,

    pub fn init(
        self: *LowerTir,
        allocator: Allocator,
        arena: *types.TypeArena,
        expr_map: *AutoHashMap(*const ast.Expr, types.TypeId),
        decl_map: *AutoHashMap(*const ast.Decl, types.TypeId),
    ) anyerror!void {
        const void_t = try arena.mk(.{ .Void = {} });
        const bool_t = try arena.mk(.{ .Bool = {} });
        self.* = .{
            .allocator = allocator,
            .type_arena = arena,
            .expr_types = expr_map,
            .decl_types = decl_map,
            .module = tir.Module.init(allocator, arena),
            .builder = undefined,
            .void_t = void_t,
            .bool_t = bool_t,
        };
        self.usize_t = self.tryMkUsize();
        self.string_t = self.tryMkString();
        self.builder = tir.Builder.init(allocator, &self.module);
    }

    pub fn deinit(self: *LowerTir) void {
        self.module.deinit();
    }

    pub fn run(self: *LowerTir, unit: *const ast.Unit) anyerror!tir.Module {
        // package decl omitted for now; wire into output module metadata if needed
        for (unit.decls.items) |*decl| {
            try self.lowerTopLevelDecl(decl);
        }
        return self.module;
    }

    //==========================================================================
    // Top level: functions & globals
    //==========================================================================
    fn lowerTopLevelDecl(self: *LowerTir, decl: *const ast.Decl) anyerror!void {
        if (decl.binding) |pat| {
            switch (pat.*) {
                .Binding => |bind| {
                    if (decl.value.* == .FunctionLit) {
                        try self.lowerFunction(bind.name, decl);
                        return;
                    }
                    // Non-function top-level => global (no initializer yet)
                    const ty = self.decl_types.get(decl) orelse return LowerError.SemanticError;
                    try self.module.globals.append(.{
                        .name = bind.name,
                        .ty = ty,
                    });
                },
                // Support destructuring into multiple globals later as needed.
                else => return LowerError.UnsupportedAstNode,
            }
        } else {
            // Unnamed top-level value? Could be a bare call/expr at module init time.
            // Leave unsupported for now.
            return LowerError.UnsupportedAstNode;
        }
    }

    fn lowerFunction(self: *LowerTir, name: []const u8, fun_decl: *const ast.Decl) anyerror!void {
        const fun_expr = fun_decl.value;
        const fun = &fun_expr.FunctionLit;

        // Type from checker
        const fn_ty_id = self.expr_types.get(fun_expr) orelse return LowerError.SemanticError;
        const fn_ty = self.type_arena.get(fn_ty_id).Function;

        // Create TIR function
        const f = try self.builder.addFunction(name, fn_ty.result);
        // Always add formal parameters (even for externs), but do not emit blocks for extern/no-body.
        for (fun.params.items, 0..) |p, i| {
            _ = try self.builder.addFuncParam(f, extractParamName(p), fn_ty.params[i]);
        }

        // Extern or no body: declare only — no blocks/terminator.
        if (fun.is_extern or fun.body == null) {
            return;
        }

        // ====== Lower function body ======
        // Prepare entry block (for allocas etc.)
        const entry = try self.builder.addBlock(f);
        var fn_ctx = FunctionContext.init(self.allocator, &self.builder, f, entry, self.type_arena, self.void_t, self.bool_t);
        try fn_ctx.pushScope();
        defer fn_ctx.deinit();

        // Bind params in the entry block (spill for `mut`/`ref` when needed)
        for (fun.params.items, 0..) |p, i| {
            const p_ty = fn_ty.params[i];
            const param_id = f.params.items[i].id; // already added above            // Bind pattern
            if (p.pat) |pat| {
                switch (pat.*) {
                    .Binding => |bind| {
                        if (bind.is_mut) {
                            const ptr_ty = try self.mkPointer(p_ty);
                            const slot = try self.builder.alloca(entry, ptr_ty, null, 0);
                            _ = try self.builder.store(entry, self.void_t, slot, param_id, 0);
                            try fn_ctx.bindMut(bind.name, slot);
                        } else if (bind.by_ref) {
                            // by_ref: assume parameter is already a pointer or we pass address
                            try fn_ctx.bindMut(bind.name, param_id);
                        } else {
                            try fn_ctx.bindImm(bind.name, param_id);
                        }
                    },
                    .Tuple => |tp| {
                        // Destructure tuple param value into locals (immutable by default)
                        try self.bindTuplePattern(&fn_ctx, .{ .value = param_id, .is_ptr = false }, p_ty, &tp);
                    },
                    else => return LowerError.UnsupportedAstNode,
                }
            }
        }
        const body = fun.body.?;
        try self.lowerBlockStmts(&fn_ctx, &body);
        // fallthrough out of function body: run all defers (normal), then implicit ret if void
        try self.runDefersToDepth(&fn_ctx, 0, false);
        if (f.result == self.void_t and entry.term == null and fn_ctx.current_block.term == null) {
            self.builder.retVoid(fn_ctx.current_block);
        }
    }

    //==========================================================================
    // Statements
    //==========================================================================
    fn lowerBlockStmts(self: *LowerTir, ctx: *FunctionContext, blk: *const ast.Block) anyerror!void {
        // Track if we saw a return to avoid accidental fallthrough.
        var terminated = false;

        for (blk.items.items) |*stmt| {
            if (terminated) break;
            terminated = try self.lowerStmt(ctx, stmt);
        }

        if (!terminated) {
            // Implicit return for void functions is OK; otherwise type checker should have flagged it.
            if (ctx.func.result == self.void_t) {
                self.builder.retVoid(ctx.current_block);
            }
        }
    }

    /// Returns true if this statement ended the current block (return/br/unreachable).
    fn lowerStmt(self: *LowerTir, ctx: *FunctionContext, stmt: *const ast.Statement) anyerror!bool {
        const b = ctx.current_block;
        switch (stmt.*) {
            .Defer => |d| {
                try ctx.addDefer(d.expr, false);
                return false;
            },
            .ErrDefer => |d| {
                try ctx.addDefer(d.expr, true);
                return false;
            },

            .Expr => |*e| {
                _ = try self.lowerExpr(ctx, e);
                return false;
            },
            .Decl => |d| {
                // Lower initializer
                const value_id = try self.lowerExpr(ctx, d.value);
                const value_ty = self.expr_types.get(d.value) orelse return LowerError.SemanticError;

                if (d.binding) |pat| {
                    switch (pat.*) {
                        .Binding => |bind| {
                            if (d.is_const) {
                                try ctx.bindImm(bind.name, value_id);
                            } else {
                                // Mutable local -> stack slot + store
                                const ptr_ty = try self.mkPointer(value_ty);
                                const slot = try self.builder.alloca(b, ptr_ty, null, 0);
                                _ = try self.builder.store(b, self.void_t, slot, value_id, 0);
                                try ctx.bindMut(bind.name, slot);
                            }
                        },
                        .Tuple => |tp| {
                            // Destructure tuple into (possibly) multiple locals – for now immutable
                            try self.bindTuplePattern(ctx, .{ .value = value_id, .is_ptr = false }, value_ty, &tp);
                        },
                        else => return LowerError.UnsupportedAstNode,
                    }
                }
                return false;
            },
            .Assign => |as| {
                // Compute lvalue pointer and rvalue then store
                const lhs_ptr = try self.lowerAddress(ctx, as.left);
                const rhs_val = try self.lowerExpr(ctx, as.right);
                _ = try self.builder.store(b, self.void_t, lhs_ptr, rhs_val, 0);
                return false;
            },
            .Return => |ret| {
                if (ret.value) |ve| {
                    const v = try self.lowerExpr(ctx, ve);
                    // is_err?  -> run errdefers conditionally
                    // const is_err = try self.call1(ctx, "builtin.err.is_err", self.bool_t, v);
                    // try self.runAllDefersBeforeReturn(ctx, is_err);
                    self.builder.ret(ctx.current_block, v);
                } else {
                    // void return: only normal defers run
                    try self.runAllDefersBeforeReturn(ctx, null);
                    self.builder.retVoid(ctx.current_block);
                }
                return true;
            },
            .Break => |brk| {
                // Find loop target and run defers for intervening scopes (normal-only).
                const tgt = ctx.findLoop(brk.label) orelse return LowerError.SemanticError;
                try self.runDefersToDepth(ctx, tgt.scope_depth, false);
                // break value (or undef) to loop join param
                const v = if (brk.value) |ve|
                    try self.lowerExpr(ctx, ve)
                else
                    try self.builder.constUndef(ctx.current_block, tgt.result_ty);
                try self.builder.br(ctx.current_block, tgt.join_block.id, &.{v});
                return true;
            },
            .Continue => |_| {
                const tgt = ctx.findLoop(null) orelse return LowerError.SemanticError;
                try self.runDefersToDepth(ctx, tgt.scope_depth, false);
                try self.builder.br(ctx.current_block, tgt.continue_block.id, &.{});
                return true;
            },
            .Unreachable => |_| {
                self.builder.unreachableOp(b);
                return true;
            },
            .Insert => |_| return LowerError.UnsupportedAstNode,
        }
    }

    //==========================================================================
    // Expressions
    //==========================================================================
    fn lowerExpr(self: *LowerTir, ctx: *FunctionContext, expr: *const ast.Expr) anyerror!tir.ValueId {
        const b = ctx.current_block;
        const ty = self.getExprType(expr) orelse return LowerError.SemanticError;

        switch (expr.*) {
            .Range => |r| {
                // Build a first-class range value
                const start_v = if (r.start) |s| try self.lowerExpr(ctx, s) else try self.builder.constUndef(b, ty);
                const end_v = if (r.end) |e| try self.lowerExpr(ctx, e) else try self.builder.constUndef(b, ty);
                const incl = try self.builder.constBool(b, self.bool_t, r.inclusive_right);
                var args = [_]tir.ValueId{ start_v, end_v, incl };
                return self.builder.call(b, ty, "builtin.range.make", args[0..]);
            },
            // ----- Basic literals -----
            .IntLit => |lit| {
                const v = try std.fmt.parseInt(i64, lit.value, 0);
                return self.builder.constInt(b, ty, v);
            },
            .FloatLit => |lit| {
                const v = try std.fmt.parseFloat(f64, lit.value);
                return self.builder.constFloat(b, ty, v);
            },
            .BoolLit => |lit| return self.builder.constBool(b, ty, lit.value),
            .StringLit => |lit| return self.builder.constString(b, ty, lit.value),
            .CharLit => |lit| {
                // represent char as int
                return self.builder.constInt(b, ty, @as(i64, @intCast(lit.value)));
            },
            .NullLit => |_| return self.builder.constNull(b, ty),
            .UndefLit => |_| return self.builder.constUndef(b, ty),

            // ----- Identifiers -----
            .Identifier => |ident| {
                const vb = ctx.lookup(ident.name) orelse return LowerError.SemanticError;
                return try self.valueOfVar(ctx, vb, ty);
            },

            // ----- Builtin Type literal (meta) -----
            .Type => |_| return LowerError.UnsupportedAstNode,

            // ----- Composite literals -----
            .TupleLit => |tl| {
                var vals = try self.tmpVals(tir.ValueId, tl.elems.items.len);
                defer self.allocator.free(vals);

                for (tl.elems.items, 0..) |e, i|
                    vals[i] = try self.lowerExpr(ctx, e);

                return self.builder.tupleMake(b, ty, vals);
            },
            .ArrayLit => |al| {
                var vals = try self.tmpVals(tir.ValueId, al.elems.items.len);
                defer self.allocator.free(vals);

                for (al.elems.items, 0..) |e, i|
                    vals[i] = try self.lowerExpr(ctx, e);

                return self.builder.arrayMake(b, ty, vals);
            },
            .StructLit => |sl| {
                var fields = try self.tmpVals(tir.Instr.StructFieldInit, sl.fields.items.len);
                defer self.allocator.free(fields);

                for (sl.fields.items, 0..) |f, i| {
                    const fv = try self.lowerExpr(ctx, f.value);
                    fields[i] = .{ .index = @intCast(i), .name = f.name, .value = fv };
                }
                return self.builder.structMake(b, ty, fields);
            },
            .MapLit => |ml| {
                // Build from key/value arrays via builtin.map.from_kv
                var kvs = try self.tmpVals(tir.ValueId, ml.entries.items.len * 2);
                defer self.allocator.free(kvs);
                var j: usize = 0;
                for (ml.entries.items) |kv| {
                    kvs[j] = try self.lowerExpr(ctx, kv.key);
                    j += 1;
                    kvs[j] = try self.lowerExpr(ctx, kv.value);
                    j += 1;
                }
                return self.builder.call(b, ty, "builtin.map.from_kv", kvs);
            },
            .VariantLit => |vl| {
                const tag_s = try self.constStr(ctx, vl.name);
                const payload = if (vl.value) |vex| try self.lowerExpr(ctx, vex) else try self.builder.constUndef(b, self.void_t);
                return self.builder.call(b, ty, "builtin.variant.make", &.{ tag_s, payload });
            },
            .EnumLit => |el| {
                const name_s = try self.constStr(ctx, el.name);
                const payload = if (el.value) |vex| try self.lowerExpr(ctx, vex) else try self.builder.constUndef(b, self.void_t);
                return self.builder.call(b, ty, "builtin.enum.make", &.{ name_s, payload });
            },

            // ----- Prefix -----
            .UnaryPlus => |u| {
                // no-op
                return self.lowerExpr(ctx, u.right);
            },
            .UnaryMinus => |u| {
                const v = try self.lowerExpr(ctx, u.right);
                // 0 - x
                const zero = try self.zeroConst(ctx, ty);
                return self.builder.sub(b, ty, zero, v);
            },
            .AddressOf => |u| {
                const ptr = try self.lowerAddress(ctx, u.right);
                return ptr;
            },
            .LogicalNot => |u| {
                const v = try self.lowerExpr(ctx, u.right);
                return self.builder.lNot(b, ty, v);
            },

            // ----- Infix -----
            .InfixAdd => |op| return self.binOp(ctx, ty, op.left, op.right, .Add),
            .InfixSub => |op| return self.binOp(ctx, ty, op.left, op.right, .Sub),
            .InfixMul => |op| return self.binOp(ctx, ty, op.left, op.right, .Mul),
            .InfixDiv => |op| return self.binOp(ctx, ty, op.left, op.right, .Div),
            .InfixMod => |op| return self.binOp(ctx, ty, op.left, op.right, .Mod),
            .InfixShl => |op| return self.binOp(ctx, ty, op.left, op.right, .Shl),
            .InfixShr => |op| return self.binOp(ctx, ty, op.left, op.right, .Shr),
            .InfixBitAnd => |op| return self.binOp(ctx, ty, op.left, op.right, .BitAnd),
            .InfixBitOr => |op| return self.binOp(ctx, ty, op.left, op.right, .BitOr),
            .InfixBitXor => |op| return self.binOp(ctx, ty, op.left, op.right, .BitXor),

            .InfixEq => |op| return self.cmpOp(ctx, op.left, op.right, .CmpEq),
            .InfixNeq => |op| return self.cmpOp(ctx, op.left, op.right, .CmpNe),
            .InfixLt => |op| return self.cmpOp(ctx, op.left, op.right, .CmpLt),
            .InfixLte => |op| return self.cmpOp(ctx, op.left, op.right, .CmpLe),
            .InfixGt => |op| return self.cmpOp(ctx, op.left, op.right, .CmpGt),
            .InfixGte => |op| return self.cmpOp(ctx, op.left, op.right, .CmpGe),

            // Logical And/Or – emitted as ops (no short-circuit CFG here)
            // Logical And/Or – now lowered with short-circuit CFG and block params
            .InfixLogicalAnd => |op| {
                return self.lowerLogicalAnd(ctx, op.left, op.right);
            },
            .InfixLogicalOr => |op| {
                return self.lowerLogicalOr(ctx, op.left, op.right);
            },

            // Optionals / Errors:
            .InfixOrelse => |op| {
                return self.lowerOrelse(ctx, op.left, op.right, ty);
            },
            .InfixCatch => |op| {
                return self.lowerCatch(ctx, &op, ty);
            },

            // ----- Postfix -----
            .PostfixErrorUnwrap => |pe| {
                const v = try self.lowerExpr(ctx, pe.expr);
                // builtin.err.unwrap : panics (or traps) on error; result type is success payload type `ty`
                return self.call1(ctx, "builtin.err.unwrap", ty, v);
            },
            .PostfixOptionalUnwrap => |po| {
                const v = try self.lowerExpr(ctx, po.expr);
                // builtin.opt.expect : traps if None; returns inner
                return self.call1(ctx, "builtin.opt.expect", ty, v);
            },
            .PostfixDeref => |pd| {
                // *expr : load
                const ptr = try self.lowerExpr(ctx, pd.expr);
                return self.builder.load(b, ty, ptr, 0);
            },
            .PostfixIndex => |ix| {
                // If base is pointer/slice and you want an lvalue, use lowerAddress(); otherwise value load path:
                const base_val = try self.lowerExpr(ctx, ix.collection);
                const idx_val = try self.lowerExpr(ctx, ix.index);
                return self.builder.index(b, ty, base_val, idx_val);
            },
            .PostfixField => |pf| {
                // Extract field from value aggregate
                const base = try self.lowerExpr(ctx, pf.parent);
                var field_index: u32 = 0;
                if (pf.is_tuple) {
                    // Tuple-style ".0", ".1", ...
                    field_index = try self.parseTupleIndex(pf.field);
                } else {
                    const base_ty = self.getExprType(pf.parent) orelse return LowerError.SemanticError;
                    field_index = try self.resolveStructFieldIndex(base_ty, pf.field);
                }
                return self.builder.extractField(b, ty, base, field_index, pf.field);
            },
            .PostfixCall => |call| {
                var callee_name: []const u8 = undefined;
                switch (call.callee.*) {
                    .Identifier => callee_name = call.callee.Identifier.name,
                    .FunctionLit => {
                        callee_name = try self.materializeFunctionLiteral(ctx, &call.callee.FunctionLit);
                    },
                    .Closure => {
                        // capture-less closure becomes a function; if captures exist, we pass them as extra params at the front
                        callee_name = try self.materializeClosure(ctx, &call.callee.Closure);
                    },
                    else => return LowerError.UnsupportedAstNode,
                }
                var args = ArrayList(tir.ValueId).init(self.allocator);
                defer args.deinit();
                for (call.args.items) |arg_expr| try args.append(try self.lowerExpr(ctx, arg_expr));
                return self.builder.call(b, ty, callee_name, args.items);
            },
            .PostfixAwait => |pa| {
                const fut = try self.lowerExpr(ctx, pa.expr);
                return self.call1(ctx, "builtin.async.await", ty, fut);
            },

            // ----- Casts -----
            .CastNormal => |c| {
                const v = try self.lowerExpr(ctx, c.expr);
                return self.builder.castNormal(b, ty, v);
            },
            .CastBit => |c| {
                const v = try self.lowerExpr(ctx, c.expr);
                return self.builder.castBit(b, ty, v);
            },
            .CastSaturate => |c| {
                const v = try self.lowerExpr(ctx, c.expr);
                return self.builder.castSaturate(b, ty, v);
            },
            .CastWrap => |c| {
                const v = try self.lowerExpr(ctx, c.expr);
                return self.builder.castWrap(b, ty, v);
            },
            .CastChecked => |c| {
                const v = try self.lowerExpr(ctx, c.expr);
                return self.builder.castChecked(b, ty, v);
            },

            // ----- Control flow as expressions -----
            .If => |iff| return self.lowerIfExpr(ctx, &iff, ty),
            .While => |w| return self.lowerWhileExpr(ctx, &w, ty),
            .For => |fr| return self.lowerForExpr(ctx, &fr, ty),
            .Match => |mm| {
                return self.lowerMatchExpr(ctx, &mm, ty);
            }, // ----- Blocks / misc -----
            .Block => |bb| return self.lowerBlockExpr(ctx, &bb, ty),
            .ComptimeBlock => |cb| {
                // Treat as normal block at runtime lowering
                return self.lowerBlockExpr(ctx, &cb.block, ty);
            },
            .CodeBlock => |cb| {
                // Same as normal block (user-level meaning already resolved during checking)
                return self.lowerBlockExpr(ctx, &cb.block, ty);
            },
            .MlirBlock => |mb| {
                // Opaque bridge: builtin.mlir.exec(kind, text) -> ty
                const kind_s: []const u8 = switch (mb.kind) {
                    .Module => "module",
                    .Type => "type",
                    .Attribute => "attribute",
                    .Operation => "operation",
                };
                const text_v = try self.builder.constString(b, try self.requireStringType(), mb.text);
                const kind_v = try self.builder.constString(b, try self.requireStringType(), kind_s);
                var args = [_]tir.ValueId{ kind_v, text_v };
                return self.builder.call(b, ty, "builtin.mlir.exec", args[0..]);
            },
            .AsyncBlock => |ab| {
                // Spawn a lambda returning the value of ab.body
                const fn_name = try self.materializeThunkOfExpr(ctx, ab.body, "async.lambda");
                _ = fn_name;
                var args = [_]tir.ValueId{};
                return self.builder.call(b, ty, "builtin.async.spawn", args[0..]); // assumes callee captured by symbol, backend can read it
            },
            .Closure => {
                // Return a function symbol (no direct function values in TIR).
                // We materialize the closure as a named function and return undef of its type (call sites handle it).
                _ = try self.materializeClosure(ctx, &expr.Closure);
                return self.builder.constUndef(b, ty);
            },
            // ----- Function literal as expression -----
            .FunctionLit => |_| {
                // Materialize a named function symbol; TIR has no first-class function values,
                // so we return an undef of the function type and rely on call sites to use the symbol.
                _ = try self.materializeFunctionLiteral(ctx, &expr.FunctionLit);
                return self.builder.constUndef(b, ty);
            },
            .Import => |_| {
                // Lower as opaque import() call returning requested type
                var args = [_]tir.ValueId{};
                return self.builder.call(b, ty, "builtin.import", args[0..]);
            },
            .TypeOf => |to| {
                // Return a compile-time type object via builtin.typeof(expr)
                const v = try self.lowerExpr(ctx, to.expr);
                return self.builder.call(b, ty, "builtin.typeof", &.{v});
            },
        }
    }

    // --- scopes & defers -----------------------------------------------------
    fn runAllDefersBeforeReturn(self: *LowerTir, ctx: *FunctionContext, is_err_opt: ?tir.ValueId) anyerror!void {
        // Run from innermost scope to root
        while (ctx.scopes.items.len > 0) {
            const depth = ctx.scopes.items.len - 1;
            try self.runDefersInScope(ctx, depth, is_err_opt);
            ctx.popScope();
        }
    }

    fn runDefersToDepth(self: *LowerTir, ctx: *FunctionContext, target_depth: usize, is_err: bool) anyerror!void {
        // Pop scopes until we reach target_depth, executing normal defers (and NOT errdefers)
        while (ctx.scopes.items.len > target_depth) {
            const depth = ctx.scopes.items.len - 1;
            try self.runDefersInScope(ctx, depth, if (is_err) null else null);
            ctx.popScope();
        }
    }

    //==========================================================================
    // Helpers (values, addresses, patterns, control)
    //==========================================================================

    fn getExprType(self: *LowerTir, e: *const ast.Expr) ?types.TypeId {
        return self.expr_types.get(e);
    }

    fn tryMkUsize(self: *LowerTir) ?types.TypeId {
        _ = self;
        return null;
    }
    fn tryMkString(self: *LowerTir) ?types.TypeId {
        _ = self;
        // if your arena has a canonical String
        return null;
    }
    fn requireStringType(self: *LowerTir) anyerror!types.TypeId {
        if (self.string_t) |t| return t;
        return try self.type_arena.mk(.{ .String = {} });
    }

    fn guessStringType(self: *LowerTir) anyerror!types.TypeId {
        // Replace with your canonical string type (e.g., slice[u8] const)
        // Fallback to any/opaque pointer if needed.
        // For now we assume TypeArena provides String.
        return try self.type_arena.mk(.{ .String = {} });
    }

    fn call1(self: *LowerTir, ctx: *FunctionContext, callee: []const u8, ty: types.TypeId, a0: tir.ValueId) anyerror!tir.ValueId {
        var args = [_]tir.ValueId{a0};
        return self.builder.call(ctx.current_block, ty, callee, args[0..]);
    }
    fn call2(self: *LowerTir, ctx: *FunctionContext, callee: []const u8, ty: types.TypeId, a0: tir.ValueId, a1: tir.ValueId) anyerror!tir.ValueId {
        var args = [_]tir.ValueId{ a0, a1 };
        return self.builder.call(ctx.current_block, ty, callee, args[0..]);
    }
    fn constStr(self: *LowerTir, ctx: *FunctionContext, s: []const u8) anyerror!tir.ValueId {
        const st = try self.requireStringType();
        return self.builder.constString(ctx.current_block, st, s);
    }

    fn parseTupleIndex(_: *LowerTir, s: []const u8) anyerror!u32 {
        // parse ".0", ".1", etc. Caller guarantees tuple-style
        if (s.len == 0) return LowerError.SemanticError;
        return @intCast(try std.fmt.parseInt(u32, s, 10));
    }

    fn mkPointer(self: *LowerTir, elem: types.TypeId) anyerror!types.TypeId {
        // Adjust to your real pointer constructor in `types.zig`
        return try self.type_arena.mk(.{ .Ptr = .{ .elem = elem, .is_const = false } });
    }

    // Run defers in a given scope depth (0..len-1), honoring err-only via is_err_opt.
    fn runDefersInScope(self: *LowerTir, ctx: *FunctionContext, depth: usize, is_err_opt: ?tir.ValueId) anyerror!void {
        const scope = &ctx.scopes.items[depth];
        if (scope.defers.items.len == 0) return;
        // Execute in LIFO
        var i: isize = @intCast(scope.defers.items.len - 1);
        while (i >= 0) : (i -= 1) {
            const ent = scope.defers.items[@intCast(i)];
            if (!ent.is_err_only) {
                _ = try self.lowerExpr(ctx, ent.expr);
            } else {
                if (is_err_opt) |is_err| {
                    // cond run
                    const then_b = try self.builder.addBlock(ctx.func);
                    const cont_b = try self.builder.addBlock(ctx.func);
                    try self.builder.condBr(ctx.current_block, is_err, then_b.id, &.{}, cont_b.id, &.{});
                    ctx.current_block = then_b;
                    _ = try self.lowerExpr(ctx, ent.expr);
                    try self.builder.br(ctx.current_block, cont_b.id, &.{});
                    ctx.current_block = cont_b;
                } else {
                    // not an error path -> skip
                }
            }
        }
    }

    // ----- Optionals -----
    fn lowerOrelse(self: *LowerTir, ctx: *FunctionContext, lhs_e: *const ast.Expr, rhs_e: *const ast.Expr, result_ty: types.TypeId) anyerror!tir.ValueId {
        const b = ctx.current_block;
        const lhs = try self.lowerExpr(ctx, lhs_e);
        const is_some = try self.call1(ctx, "builtin.opt.is_some", self.bool_t, lhs);

        const then_b = try self.builder.addBlock(ctx.func);
        const else_b = try self.builder.addBlock(ctx.func);
        const join_b = try self.builder.addBlock(ctx.func);
        const res = try self.builder.addBlockParam(join_b, "orelse.res", result_ty);

        try self.builder.condBr(b, is_some, then_b.id, &.{}, else_b.id, &.{});
        // then: unwrap
        ctx.current_block = then_b;
        const unwrapped = try self.call1(ctx, "builtin.opt.unwrap", result_ty, lhs);
        try self.builder.br(ctx.current_block, join_b.id, &.{unwrapped});
        // else: rhs
        ctx.current_block = else_b;
        const rv = try self.lowerExpr(ctx, rhs_e);
        try self.builder.br(ctx.current_block, join_b.id, &.{rv});
        // join
        ctx.current_block = join_b;
        return res;
    }

    // ----- Errors -----
    fn lowerCatch(self: *LowerTir, ctx: *FunctionContext, op: *const ast.InfixCatch, result_ty: types.TypeId) anyerror!tir.ValueId {
        const b = ctx.current_block;
        const lhs = try self.lowerExpr(ctx, op.left);
        const is_ok = try self.call1(ctx, "builtin.err.is_ok", self.bool_t, lhs);

        const then_b = try self.builder.addBlock(ctx.func);
        const else_b = try self.builder.addBlock(ctx.func);
        const join_b = try self.builder.addBlock(ctx.func);
        const res = try self.builder.addBlockParam(join_b, "catch.res", result_ty);

        try self.builder.condBr(b, is_ok, then_b.id, &.{}, else_b.id, &.{});
        // then: unwrap ok
        ctx.current_block = then_b;
        const okv = try self.call1(ctx, "builtin.err.unwrap_ok", result_ty, lhs);
        try self.builder.br(ctx.current_block, join_b.id, &.{okv});
        // else: bind error and eval rhs
        ctx.current_block = else_b;
        var rhs_res: tir.ValueId = undefined;
        if (op.binding) |idn| {
            const errv = try self.call1(ctx, "builtin.err.unwrap_err", try self.type_arena.mk(.{ .Any = {} }), lhs);
            try ctx.bindImm(idn.name, errv);
            rhs_res = try self.lowerExpr(ctx, op.right);
        } else {
            rhs_res = try self.lowerExpr(ctx, op.right);
        }
        try self.builder.br(ctx.current_block, join_b.id, &.{rhs_res});
        // join
        ctx.current_block = join_b;
        return res;
    }

    fn zeroConst(self: *LowerTir, ctx: *FunctionContext, ty: types.TypeId) anyerror!tir.ValueId {
        // naive: use const_undef replaced by cast-saturate? For now int/float/bool best-effort:
        // Prefer a proper "zero" factory from types if you have one.
        const b = ctx.current_block;
        const kind = self.type_arena.get(ty);
        // Simple heuristic
        if (@hasField(@TypeOf(kind), "Int")) return self.builder.constInt(b, ty, 0);
        if (@hasField(@TypeOf(kind), "Float")) return self.builder.constFloat(b, ty, 0.0);
        if (ty == self.bool_t) return self.builder.constBool(b, ty, false);
        return self.builder.constUndef(b, ty);
    }

    fn tmpVals(self: *LowerTir, comptime T: type, n: usize) anyerror![]T {
        return self.allocator.alloc(T, n);
    }

    fn binOp(self: *LowerTir, ctx: *FunctionContext, ty: types.TypeId, l: *const ast.Expr, r: *const ast.Expr, tag: tir.InstrTag) anyerror!tir.ValueId {
        const b = ctx.current_block;
        const lv = try self.lowerExpr(ctx, l);
        const rv = try self.lowerExpr(ctx, r);
        return switch (tag) {
            .Add => self.builder.add(b, ty, lv, rv),
            .Sub => self.builder.sub(b, ty, lv, rv),
            .Mul => self.builder.mul(b, ty, lv, rv),
            .Div => self.builder.div(b, ty, lv, rv),
            .Mod => self.builder.modulo(b, ty, lv, rv),
            .Shl => self.builder.shl(b, ty, lv, rv),
            .Shr => self.builder.shr(b, ty, lv, rv),
            .BitAnd => self.builder.bitAnd(b, ty, lv, rv),
            .BitOr => self.builder.bitOr(b, ty, lv, rv),
            .BitXor => self.builder.bitXor(b, ty, lv, rv),
            else => LowerError.UnsupportedAstNode,
        };
    }

    fn binLogic(self: *LowerTir, ctx: *FunctionContext, l: *const ast.Expr, r: *const ast.Expr, tag: tir.InstrTag) anyerror!tir.ValueId {
        const b = ctx.current_block;
        const lv = try self.lowerExpr(ctx, l);
        const rv = try self.lowerExpr(ctx, r);
        return switch (tag) {
            .LogicalAnd => self.builder.lAnd(b, self.bool_t, lv, rv),
            .LogicalOr => self.builder.lOr(b, self.bool_t, lv, rv),
            else => LowerError.UnsupportedAstNode,
        };
    }

    fn cmpOp(self: *LowerTir, ctx: *FunctionContext, l: *const ast.Expr, r: *const ast.Expr, tag: tir.InstrTag) anyerror!tir.ValueId {
        const b = ctx.current_block;
        const lv = try self.lowerExpr(ctx, l);
        const rv = try self.lowerExpr(ctx, r);
        return switch (tag) {
            .CmpEq => self.builder.cmpEq(b, self.bool_t, lv, rv),
            .CmpNe => self.builder.cmpNe(b, self.bool_t, lv, rv),
            .CmpLt => self.builder.cmpLt(b, self.bool_t, lv, rv),
            .CmpLe => self.builder.cmpLe(b, self.bool_t, lv, rv),
            .CmpGt => self.builder.cmpGt(b, self.bool_t, lv, rv),
            .CmpGe => self.builder.cmpGe(b, self.bool_t, lv, rv),
            else => LowerError.UnsupportedAstNode,
        };
    }

    // ----- Short-circuit logical AND -----
    fn lowerLogicalAnd(self: *LowerTir, ctx: *FunctionContext, left: *const ast.Expr, right: *const ast.Expr) anyerror!tir.ValueId {
        const l = try self.lowerExpr(ctx, left);

        const rhs_b = try self.builder.addBlock(ctx.func);
        const join_b = try self.builder.addBlock(ctx.func);
        const res = try self.builder.addBlockParam(join_b, "land.res", self.bool_t);

        // if (!l) goto join(false) else goto rhs
        const false_v = try self.builder.constBool(ctx.current_block, self.bool_t, false);
        try self.builder.condBr(ctx.current_block, l, rhs_b.id, &.{}, join_b.id, &.{false_v});

        // rhs: compute r, jump join(r)
        ctx.current_block = rhs_b;
        const r = try self.lowerExpr(ctx, right);
        try self.builder.br(ctx.current_block, join_b.id, &.{r});

        ctx.current_block = join_b;
        return res;
    }

    // ----- Short-circuit logical OR -----
    fn lowerLogicalOr(self: *LowerTir, ctx: *FunctionContext, left: *const ast.Expr, right: *const ast.Expr) anyerror!tir.ValueId {
        const l = try self.lowerExpr(ctx, left);

        const rhs_b = try self.builder.addBlock(ctx.func);
        const join_b = try self.builder.addBlock(ctx.func);
        const res = try self.builder.addBlockParam(join_b, "lor.res", self.bool_t);

        // if (l) goto join(true) else goto rhs
        const true_v = try self.builder.constBool(ctx.current_block, self.bool_t, true);
        try self.builder.condBr(ctx.current_block, l, join_b.id, &.{true_v}, rhs_b.id, &.{});

        // rhs: compute r, jump join(r)
        ctx.current_block = rhs_b;
        const r = try self.lowerExpr(ctx, right);
        try self.builder.br(ctx.current_block, join_b.id, &.{r});

        ctx.current_block = join_b;
        return res;
    }

    fn bindPatternToValue(self: *LowerTir, ctx: *FunctionContext, pat: *const ast.Pattern, value: tir.ValueId, value_ty: types.TypeId) anyerror!void {
        const b = ctx.current_block;
        switch (pat.*) {
            .Path => {}, // no binding
            .Binding => |bind| {
                if (bind.is_mut or bind.by_ref) {
                    const ptr_ty = try self.mkPointer(value_ty);
                    const slot = try self.builder.alloca(b, ptr_ty, null, 0);
                    _ = try self.builder.store(b, self.void_t, slot, value, 0);
                    try ctx.bindMut(bind.name, slot);
                } else try ctx.bindImm(bind.name, value);
            },
            .Wildcard => {},
            .Tuple => |tp| {
                for (tp.elems.items, 0..) |subp, i| {
                    const elem_ty = value_ty; // TODO: refine via types
                    const ev = try self.builder.extractElem(b, elem_ty, value, @intCast(i));
                    try self.bindPatternToValue(ctx, subp, ev, elem_ty);
                }
            },
            .Struct => |sp| {
                for (sp.fields.items) |f| {
                    const idx = try self.resolveStructFieldIndex(value_ty, f.name);
                    const fv = try self.builder.extractField(b, value_ty, value, idx, f.name);
                    try self.bindPatternToValue(ctx, f.pattern, fv, value_ty);
                }
            },
            else => return LowerError.UnsupportedAstNode,
        }
    }
    fn bindVariantTuple(self: *LowerTir, ctx: *FunctionContext, vp: *const ast.VariantTuplePattern, scrut: tir.ValueId, scrut_ty: types.TypeId) anyerror!void {
        _ = scrut_ty;
        // tuple payload
        const tup = try self.builder.call(ctx.current_block, self.void_t, "builtin.variant.get_tuple", &.{scrut});
        for (vp.elems.items, 0..) |pe, i| {
            const ev = try self.builder.extractElem(ctx.current_block, self.void_t, tup, @intCast(i));
            try self.bindPatternToValue(ctx, pe, ev, self.void_t);
        }
    }
    fn bindVariantStruct(self: *LowerTir, ctx: *FunctionContext, vp: *const ast.VariantStructPattern, scrut: tir.ValueId, scrut_ty: types.TypeId) anyerror!void {
        _ = scrut_ty;
        for (vp.fields.items) |f| {
            const val = try self.builder.call(ctx.current_block, self.void_t, "builtin.variant.get_field", &.{ scrut, try self.constStr(ctx, f.name) });
            try self.bindPatternToValue(ctx, f.pattern, val, self.void_t);
        }
    }
    const Rvalue = struct { value: tir.ValueId, is_ptr: bool };

    /// Get a pointer (lvalue address) for an expression used on the left of an assignment or for `&`.
    fn lowerAddress(self: *LowerTir, ctx: *FunctionContext, e: *const ast.Expr) anyerror!tir.ValueId {
        const b = ctx.current_block;
        switch (e.*) {
            .Identifier => |id| {
                const vb = ctx.lookup(id.name) orelse return LowerError.SemanticError;
                switch (vb.kind) {
                    // .Imm => return LowerError.SemanticError, // cannot take address of rvalue (unless you choose to spill)
                    .Imm => {
                        // spill to a fresh slot to take address
                        const ety = self.getExprType(e) orelse return LowerError.SemanticError;
                        const ptr_ty = try self.mkPointer(ety);
                        const slot = try self.builder.alloca(b, ptr_ty, null, 0);
                        _ = try self.builder.store(b, self.void_t, slot, vb.v, 0);
                        return slot;
                    },
                    .Ptr => return vb.v,
                }
            },
            .PostfixDeref => |pd| {
                // address-of (*p) == p
                return try self.lowerExpr(ctx, pd.expr);
            },
            .PostfixField => |pf| {
                // address into struct field: gep base_ptr, fieldIndex
                // For simplicity, compute base address first (if we have a pointer), else spill base to a slot and then gep.
                const base_val = try self.lowerExpr(ctx, pf.parent);
                // If we only have a value, spill:
                const base_ty = self.getExprType(pf.parent) orelse return LowerError.SemanticError;
                const ptr_ty = try self.mkPointer(base_ty);
                const slot = try self.builder.alloca(b, ptr_ty, null, 0);
                _ = try self.builder.store(b, self.void_t, slot, base_val, 0);

                // TODO: consult types to compute the actual field index:
                const fld_index: u32 = try self.resolveStructFieldIndex(base_ty, pf.field);

                var idxs = try self.tmpVals(tir.Instr.GepIndex, 1 + 0);
                defer self.allocator.free(idxs);
                idxs[0] = .{ .Const = @intCast(fld_index) };
                const res_ptr_ty = ptr_ty; // same pointer base; real impl refines type
                return self.builder.gep(b, res_ptr_ty, slot, idxs);
            },
            .PostfixIndex => |ix| {
                // address of element: gep base_ptr, index
                const coll_val = try self.lowerExpr(ctx, ix.collection);
                const idx_val = try self.lowerExpr(ctx, ix.index);

                // As above, if collection is not a pointer, spill to slot.
                const coll_ty = self.getExprType(ix.collection) orelse return LowerError.SemanticError;
                const coll_ptr_ty = try self.mkPointer(coll_ty);
                const slot = try self.builder.alloca(b, coll_ptr_ty, null, 0);
                _ = try self.builder.store(b, self.void_t, slot, coll_val, 0);

                var idxs = try self.tmpVals(tir.Instr.GepIndex, 1);
                defer self.allocator.free(idxs);
                idxs[0] = .{ .Value = idx_val };
                const res_ptr_ty = coll_ptr_ty;
                return self.builder.gep(b, res_ptr_ty, slot, idxs);
            },
            else => return LowerError.UnsupportedAstNode,
        }
    }

    fn valueOfVar(self: *LowerTir, ctx: *FunctionContext, v: VarBinding, expected_ty: types.TypeId) anyerror!tir.ValueId {
        const b = ctx.current_block;
        switch (v.kind) {
            .Imm => return v.v,
            .Ptr => return self.builder.load(b, expected_ty, v.v, 0),
        }
    }

    /// Best-effort: fetch element type of a tuple type id.
    fn tupleElemType(self: *LowerTir, tuple_ty: types.TypeId, index: usize) ?types.TypeId {
        const T = self.type_arena.get(tuple_ty);
        // Adjust this to your actual `types.Type` representation.
        if (@hasField(@TypeOf(T), "Tuple")) {
            if (index < T.Tuple.elems.len) return T.Tuple.elems[index];
        }
        return null;
    }

    /// Destructure a tuple pattern from an rvalue (not pointer here).
    fn bindTuplePattern(self: *LowerTir, ctx: *FunctionContext, from: Rvalue, tuple_ty: types.TypeId, tp: *const ast.TuplePattern) anyerror!void {
        const b = ctx.current_block;
        for (tp.elems.items, 0..) |pe, i| {
            const elem_ty = self.tupleElemType(tuple_ty, i) orelse self.void_t; // best-effort
            const v = try self.builder.extractElem(b, elem_ty, from.value, @intCast(i));
            switch (pe.*) {
                .Binding => |bind| {
                    if (bind.is_mut or bind.by_ref) {
                        // Spill into stack slot
                        const ptr_ty = try self.mkPointer(elem_ty);
                        const slot = try self.builder.alloca(b, ptr_ty, null, 0);
                        _ = try self.builder.store(b, self.void_t, slot, v, 0);
                        try ctx.bindMut(bind.name, slot);
                    } else {
                        try ctx.bindImm(bind.name, v);
                    }
                },
                .Wildcard => {}, // ignore
                else => return LowerError.UnsupportedAstNode,
            }
        }
    }

    // ----- Block as expression -----
    fn lowerBlockExpr(self: *LowerTir, ctx: *FunctionContext, blk: *const ast.Block, ty: types.TypeId) anyerror!tir.ValueId {
        // Evaluate statements; if last statement is an expression, return it; otherwise void/undef
        var last_value: ?tir.ValueId = null;
        var terminated = false;

        for (blk.items.items, 0..) |*stmt, idx| {
            if (terminated) break;

            switch (stmt.*) {
                .Expr => |*e| {
                    last_value = try self.lowerExpr(ctx, e);
                },
                else => {
                    terminated = try self.lowerStmt(ctx, stmt);
                    if (terminated) break;
                    // If not an expression stmt, clear last_value unless it's the final position
                    if (idx != blk.items.items.len - 1) last_value = null;
                },
            }
        }

        if (last_value) |v| return v;
        // Fallback
        return self.builder.constUndef(ctx.current_block, ty);
    }

    fn lowerWhileExpr(self: *LowerTir, ctx: *FunctionContext, w: *const ast.While, result_ty: types.TypeId) anyerror!tir.ValueId {
        const entry_b = ctx.current_block;
        const header_b = try self.builder.addBlock(ctx.func);
        const body_b = try self.builder.addBlock(ctx.func);
        const exit_b = try self.builder.addBlock(ctx.func);
        const join_b = try self.builder.addBlock(ctx.func);
        const res_param = try self.builder.addBlockParam(join_b, "while.res", result_ty);
        // Enter loop:
        try self.builder.br(entry_b, header_b.id, &.{});

        // Register loop target (for labeled break/continue with values)
        try ctx.pushLoop(w.label, exit_b, header_b, join_b, res_param, result_ty);

        // header: evaluate cond or pattern
        ctx.current_block = header_b;
        var cond_v: tir.ValueId = undefined;
        if (w.is_pattern and w.pattern != null) {
            // Evaluate expression and test pattern each trip
            if (w.cond == null) return LowerError.SemanticError;
            const sv = try self.lowerExpr(ctx, w.cond.?);
            const test_cond = try self.condFromPattern(ctx, w.pattern.?, sv) orelse return LowerError.UnsupportedAstNode;
            cond_v = test_cond;
            // Stash the scrutinee into a temp slot so body can bind it
            const scrut_ty = self.getExprType(w.cond.?) orelse return LowerError.SemanticError;
            const ptr_ty = try self.mkPointer(scrut_ty);
            const slot = try self.builder.alloca(header_b, ptr_ty, null, 0);
            _ = try self.builder.store(header_b, self.void_t, slot, sv, 0);
            // Jump either to body (will load/bind) or to exit
            try self.builder.condBr(ctx.current_block, cond_v, body_b.id, &.{}, exit_b.id, &.{});
            // body: load and bind pattern then run body block
            ctx.current_block = body_b;
            const sv_loaded = try self.builder.load(body_b, scrut_ty, slot, 0);
            try self.bindPatternToValue(ctx, w.pattern.?, sv_loaded, scrut_ty);
        } else {
            // Regular while(cond)
            if (w.cond) |ce|
                cond_v = try self.lowerExpr(ctx, ce)
            else
                cond_v = try self.builder.constBool(header_b, self.bool_t, true);
            try self.builder.condBr(ctx.current_block, cond_v, body_b.id, &.{}, exit_b.id, &.{});
            ctx.current_block = body_b;
        }
        // body:
        try self.lowerBlockStmts(ctx, &w.body);
        // If body didn't terminate, go back to header
        if (ctx.current_block.term == null) {
            try self.builder.br(ctx.current_block, header_b.id, &.{});
        }

        // exit
        ctx.popLoop();
        // exit -> join with undef result (if not via `break value`)
        ctx.current_block = exit_b;
        const uv = try self.builder.constUndef(exit_b, result_ty);
        try self.builder.br(exit_b, join_b.id, &.{uv});
        // land
        ctx.current_block = join_b;
        return res_param;
    }

    // ----- For expression over integer ranges only -----
    fn lowerForExpr(self: *LowerTir, ctx: *FunctionContext, fr: *const ast.For, result_ty: types.TypeId) anyerror!tir.ValueId {
        const it_ty = self.getExprType(fr.iterable) orelse return LowerError.SemanticError;

        const b_entry = ctx.current_block;
        const header_b = try self.builder.addBlock(ctx.func);
        const body_b = try self.builder.addBlock(ctx.func);
        const exit_b = try self.builder.addBlock(ctx.func);
        const join_b = try self.builder.addBlock(ctx.func);
        const res_param = try self.builder.addBlockParam(join_b, "for.res", result_ty);

        // loop control
        try ctx.pushLoop(fr.label, exit_b, header_b, join_b, res_param, result_ty);

        if (fr.iterable.* == .Range) {
            // ---------------- Range-based for ----------------
            const rg = fr.iterable.Range;
            if (rg.start == null or rg.end == null) return LowerError.SemanticError;
            const start_v = try self.lowerExpr(ctx, rg.start.?);
            const end_v = try self.lowerExpr(ctx, rg.end.?);
            const idx_ty = self.getExprType(rg.start.?) orelse return LowerError.SemanticError;

            const idx_param = try self.builder.addBlockParam(header_b, "i", idx_ty);
            // enter with i = start
            try self.builder.br(b_entry, header_b.id, &.{start_v});
            // header compare
            ctx.current_block = header_b;
            const cond = if (rg.inclusive_right)
                try self.builder.cmpLe(header_b, self.bool_t, idx_param, end_v)
            else
                try self.builder.cmpLt(header_b, self.bool_t, idx_param, end_v);
            try self.builder.condBr(ctx.current_block, cond, body_b.id, &.{}, exit_b.id, &.{});
            // body: bind pattern to i
            ctx.current_block = body_b;
            try self.bindPatternToValue(ctx, fr.pattern, idx_param, idx_ty);
            try self.lowerBlockStmts(ctx, &fr.body);
            if (ctx.current_block.term == null) {
                const one = try self.builder.constInt(ctx.current_block, idx_ty, 1);
                const i_next = try self.builder.add(ctx.current_block, idx_ty, idx_param, one);
                try self.builder.br(ctx.current_block, header_b.id, &.{i_next});
            }
        } else {
            // ---------------- Array/Slice-based for via index ----------------
            const arr = try self.lowerExpr(ctx, fr.iterable);
            // len = builtin.len(arr) : usize
            const idx_ty = self.usize_t orelse (try self.type_arena.mk(.{ .Usize = {} }));
            const len = try self.builder.call(b_entry, idx_ty, "builtin.len", &.{arr});
            const zero = try self.builder.constInt(b_entry, idx_ty, 0);
            // header param i:usize, entry jump i=0
            const idx_param = try self.builder.addBlockParam(header_b, "i", idx_ty);
            try self.builder.br(b_entry, header_b.id, &.{zero});
            // header: i < len ?
            ctx.current_block = header_b;
            const cond = try self.builder.cmpLt(header_b, self.bool_t, idx_param, len);
            try self.builder.condBr(ctx.current_block, cond, body_b.id, &.{}, exit_b.id, &.{});
            // body: elem = arr[i]
            ctx.current_block = body_b;
            const elem_ty = tyElemFromIterable: {
                break :tyElemFromIterable it_ty; // best-effort
            };
            const elem = try self.builder.index(body_b, elem_ty, arr, idx_param);
            try self.bindPatternToValue(ctx, fr.pattern, elem, elem_ty);
            try self.lowerBlockStmts(ctx, &fr.body);
            if (ctx.current_block.term == null) {
                const one = try self.builder.constInt(ctx.current_block, idx_ty, 1);
                const i_next = try self.builder.add(ctx.current_block, idx_ty, idx_param, one);
                try self.builder.br(ctx.current_block, header_b.id, &.{i_next});
            }
        }
        ctx.popLoop();
        // exit -> join undef (unless `break value` already passed a concrete one)
        ctx.current_block = exit_b;
        const uv = try self.builder.constUndef(exit_b, result_ty);
        try self.builder.br(exit_b, join_b.id, &.{uv});
        ctx.current_block = join_b;
        return res_param;
    }

    // ----- Match expression -----
    fn lowerMatchExpr(self: *LowerTir, ctx: *FunctionContext, mm: *const ast.Match, result_ty: types.TypeId) anyerror!tir.ValueId {
        const scrut = try self.lowerExpr(ctx, mm.expr);
        const scrut_ty = self.getExprType(mm.expr) orelse return LowerError.SemanticError;

        // Join with result param
        const join_b = try self.builder.addBlock(ctx.func);
        const res = try self.builder.addBlockParam(join_b, "match.res", result_ty);

        // We'll build a chain of tests (no Switch if guards are present).
        var cur = ctx.current_block;
        var next_b: ?*tir.Block = null;

        // For each arm except last, create test->arm->next chain
        for (mm.arms.items, 0..) |arm, i| {
            const is_last = (i + 1 == mm.arms.items.len);

            if (!is_last) {
                next_b = try self.builder.addBlock(ctx.func);
            } else {
                next_b = null;
            }

            // Build condition from pattern (+ optional guard)
            const pat_cond = try self.condFromPattern(ctx, arm.pattern, scrut);
            if (pat_cond == null) return LowerError.UnsupportedAstNode;
            var cond_v = pat_cond.?;

            if (arm.guard) |gexpr| {
                // cond = cond && guard
                const g = try self.lowerExpr(ctx, gexpr);
                cond_v = try self.builder.lAnd(cur, self.bool_t, cond_v, g);
            }

            const arm_b = try self.builder.addBlock(ctx.func);
            if (next_b) |nb| {
                try self.builder.condBr(cur, cond_v, arm_b.id, &.{}, nb.id, &.{});
            } else {
                // last arm: cond true -> arm; false -> (error)
                // If there's no final wildcard arm, it's a semantic error earlier; we still create a default path returning undef.
                const def_b = try self.builder.addBlock(ctx.func);
                try self.builder.condBr(cur, cond_v, arm_b.id, &.{}, def_b.id, &.{});
                // default: jump join with undef
                ctx.current_block = def_b;
                const uv = try self.builder.constUndef(def_b, result_ty);
                try self.builder.br(def_b, join_b.id, &.{uv});
            }

            // arm body -> value -> join
            ctx.current_block = arm_b;
            // Create an arm-local scope for defers inside the arm
            try ctx.pushScope();
            try self.bindPatternToValue(ctx, arm.pattern, scrut, scrut_ty);
            const v = try self.lowerExpr(ctx, arm.body);
            try self.runDefersToDepth(ctx, ctx.scopes.items.len - 1, false);
            ctx.popScope();
            try self.builder.br(ctx.current_block, join_b.id, &.{v});

            // advance
            if (next_b) |nb| cur = nb;
        }

        // land
        ctx.current_block = join_b;
        return res;
    }

    // Try to infer element type from an iterable type id; best-effort.
    fn tyElemFromIterable(self: *LowerTir, it_ty: types.TypeId) types.TypeId {
        const T = self.type_arena.get(it_ty);
        // Adjust to your real type union names/fields:
        if (@hasField(@TypeOf(T), "Slice")) return T.Slice.elem;
        if (@hasField(@TypeOf(T), "DynArray")) return T.DynArray.elem;
        if (@hasField(@TypeOf(T), "Array")) return T.Array.elem;
        if (@hasField(@TypeOf(T), "MapType")) return T.MapType.value;
        // fallback
        return it_ty;
    }

    /// Build a boolean condition that "scrut matches pattern".
    /// Supports:
    ///  - Literal(int/char/bool/string best-effort via equality)
    ///  - RangePattern (.. / ..=)
    ///  - OrPattern (|) combining supported subpatterns
    ///  - Wildcard (_)
    ///  - Binding (always true)
    ///  - Path (via builtin.path.match)
    ///  - Struct / Tuple / Slice (elementwise)
    ///  - VariantTuple / VariantStruct via builtin.variant.*
    fn condFromPattern(self: *LowerTir, ctx: *FunctionContext, pat: *const ast.Pattern, scrut: tir.ValueId) anyerror!?tir.ValueId {
        const b = ctx.current_block;
        switch (pat.*) {
            .Wildcard => {
                return try self.builder.constBool(b, self.bool_t, true);
            },
            .Binding => {
                // always matches
                return try self.builder.constBool(b, self.bool_t, true);
            },
            .Literal => |pexpr_ptr| {
                const pt = self.getExprType(pexpr_ptr) orelse return null;
                switch (pexpr_ptr.*) {
                    .IntLit => {
                        const iv = try std.fmt.parseInt(i64, pexpr_ptr.IntLit.value, 0);
                        const lit_v = try self.builder.constInt(b, pt, iv);
                        return try self.builder.cmpEq(b, self.bool_t, scrut, lit_v);
                    },
                    .BoolLit => {
                        const lit_v = try self.builder.constBool(b, pt, pexpr_ptr.BoolLit.value);
                        return try self.builder.cmpEq(b, self.bool_t, scrut, lit_v);
                    },
                    .CharLit => {
                        const lit_v = try self.builder.constInt(b, pt, @intCast(pexpr_ptr.CharLit.value));
                        return try self.builder.cmpEq(b, self.bool_t, scrut, lit_v);
                    },
                    .StringLit => {
                        const lit_v = try self.builder.constString(b, try self.requireStringType(), pexpr_ptr.StringLit.value);
                        return try self.call2(ctx, "builtin.eq", self.bool_t, scrut, lit_v);
                    },
                    else => return null,
                }
            },
            .Range => |rp| {
                if (rp.start == null or rp.end == null) return null;
                const st = try self.lowerExpr(ctx, rp.start.?);
                const ed = try self.lowerExpr(ctx, rp.end.?);
                const ge = try self.builder.cmpGe(b, self.bool_t, scrut, st);
                const le_or_lt = if (rp.inclusive_right)
                    try self.builder.cmpLe(b, self.bool_t, scrut, ed)
                else
                    try self.builder.cmpLt(b, self.bool_t, scrut, ed);
                return try self.builder.lAnd(b, self.bool_t, ge, le_or_lt);
            },
            .Or => |alts| {
                if (alts.alts.items.len == 0) return null;
                // If alts introduce bindings, we would need to bind post-branch; unsupported for now.
                var acc: ?tir.ValueId = null;
                for (alts.alts.items) |subp| {
                    const c = try self.condFromPattern(ctx, subp, scrut) orelse return null;
                    acc = if (acc) |a|
                        try self.builder.lOr(b, self.bool_t, a, c)
                    else
                        c;
                }
                return acc;
            },
            .At => |ap| {
                // binder @ pat  -> same condition as inner pattern
                return try self.condFromPattern(ctx, ap.pattern, scrut);
            },
            .Path => |pp| {
                // test symbolic path (e.g., Enum.Tag) equality on scrut
                const path_s = try self.constPathToString(ctx, &pp);
                return try self.builder.call(b, self.bool_t, "builtin.path.match", &.{ scrut, path_s });
            },
            .Struct => |sp| {
                var acc: ?tir.ValueId = null;
                // All fields must match
                for (sp.fields.items) |f| {
                    // extract subvalue and test recursively

                    const whole_ty = self.void_t; // best-effort
                    const idx = try self.resolveStructFieldIndex(whole_ty, f.name);
                    const sub = try self.builder.extractField(b, whole_ty, scrut, idx, f.name);
                    const c = try self.condFromPattern(ctx, f.pattern, sub) orelse return null;
                    acc = if (acc) |a| try self.builder.lAnd(b, self.bool_t, a, c) else c;
                }
                return acc orelse try self.builder.constBool(b, self.bool_t, true);
            },
            .Tuple => |tp| {
                var acc: ?tir.ValueId = null;
                for (tp.elems.items, 0..) |subp, i| {
                    const sub = try self.builder.extractElem(b, self.void_t, scrut, @intCast(i));
                    const c = try self.condFromPattern(ctx, subp, sub) orelse return null;
                    acc = if (acc) |a| try self.builder.lAnd(b, self.bool_t, a, c) else c;
                }
                return acc orelse try self.builder.constBool(b, self.bool_t, true);
            },
            .Slice => |sp| {
                // Match prefix elements (ignoring rest if has_rest)
                if (sp.has_rest) {
                    // Only check provided fixed elements
                }
                var acc: ?tir.ValueId = null;
                for (sp.elems.items, 0..) |subp, i| {
                    const idx_ty = self.usize_t orelse (try self.type_arena.mk(.{ .Usize = {} }));
                    const idxv = try self.builder.constInt(b, idx_ty, @intCast(i));
                    const sub = try self.builder.index(b, self.void_t, scrut, idxv);
                    const c = try self.condFromPattern(ctx, subp, sub) orelse return null;
                    acc = if (acc) |a| try self.builder.lAnd(b, self.bool_t, a, c) else c;
                }
                return acc orelse try self.builder.constBool(b, self.bool_t, true);
            },
            .VariantTuple => |vp| {
                // Check tag matches (via last segment name)
                const tag = vp.path.items[vp.path.items.len - 1].name;
                const tag_s = try self.constStr(ctx, tag);
                const tag_ok = try self.builder.call(b, self.bool_t, "builtin.variant.tag_is", &.{ scrut, tag_s });
                // Then check tuple payload elements
                const tpl = try self.builder.call(b, self.void_t, "builtin.variant.get_tuple", &.{scrut});
                var acc: tir.ValueId = tag_ok;
                for (vp.elems.items, 0..) |pe, i| {
                    const ev = try self.builder.extractElem(b, self.void_t, tpl, @intCast(i));
                    const c = try self.condFromPattern(ctx, pe, ev) orelse return null;
                    acc = try self.builder.lAnd(b, self.bool_t, acc, c);
                }
                return acc;
            },
            .VariantStruct => |vp| {
                const tag = vp.path.items[vp.path.items.len - 1].name;
                const tag_s = try self.constStr(ctx, tag);
                const tag_ok = try self.builder.call(b, self.bool_t, "builtin.variant.tag_is", &.{ scrut, tag_s });
                var acc: tir.ValueId = tag_ok;
                for (vp.fields.items) |f| {
                    const fv = try self.builder.call(b, self.void_t, "builtin.variant.get_field", &.{ scrut, try self.constStr(ctx, f.name) });
                    const c = try self.condFromPattern(ctx, f.pattern, fv) orelse return null;
                    acc = try self.builder.lAnd(b, self.bool_t, acc, c);
                }
                return acc;
            },
        }
    }

    // ----- If as expression with block params (phi) -----
    fn lowerIfExpr(self: *LowerTir, ctx: *FunctionContext, iff: *const ast.If, result_ty: types.TypeId) anyerror!tir.ValueId {
        const cond_v = try self.lowerExpr(ctx, iff.cond);

        const then_b = try self.builder.addBlock(ctx.func);
        const else_b = try self.builder.addBlock(ctx.func);
        const join_b = try self.builder.addBlock(ctx.func);

        // Join block has a param carrying the chosen value
        const join_param = try self.builder.addBlockParam(join_b, "if.res", result_ty);

        // branch
        try self.builder.condBr(ctx.current_block, cond_v, then_b.id, &.{}, else_b.id, &.{});

        // then
        ctx.current_block = then_b;
        const then_v = try self.lowerBlockExpr(ctx, &iff.then_block, result_ty);
        try self.builder.br(ctx.current_block, join_b.id, &.{then_v});

        // else
        ctx.current_block = else_b;
        var else_v: tir.ValueId = undefined;
        if (iff.else_block) |else_expr| {
            else_v = try self.lowerExpr(ctx, else_expr);
        } else {
            else_v = try self.builder.constUndef(else_b, result_ty);
        }
        try self.builder.br(ctx.current_block, join_b.id, &.{else_v});

        // join
        ctx.current_block = join_b;
        return join_param;
    }

    // Lower function literal to a named function and return its symbol name.
    fn materializeFunctionLiteral(self: *LowerTir, ctx: *FunctionContext, fun: *const ast.FunctionLit) anyerror![]const u8 {
        _ = ctx;
        // Synthesize a private symbol
        var buf: [64]u8 = undefined;
        const name = try std.fmt.bufPrint(&buf, "__lambda${}", .{g_lambda_counter});
        g_lambda_counter += 1;

        // Determine type & result
        const fn_ty_id = self.expr_types.get(@ptrCast(fun)) orelse return LowerError.SemanticError;
        const fn_ty = self.type_arena.get(fn_ty_id).Function;
        const f = try self.builder.addFunction(name, fn_ty.result);

        // params
        for (fun.params.items, 0..) |p, i| {
            _ = try self.builder.addFuncParam(f, extractParamName(p), fn_ty.params[i]);
        }
        const entry = try self.builder.addBlock(f);
        var inner = FunctionContext.init(self.allocator, &self.builder, f, entry, self.type_arena, self.void_t, self.bool_t);
        defer inner.deinit();
        // bind parameters into inner scope
        for (f.params.items, 0..) |pp, i| {
            try inner.bindImm(pp.name orelse try std.fmt.allocPrint(self.allocator, "arg{}", .{i}), pp.id);
        }
        if (fun.body) |body| try self.lowerBlockStmts(&inner, &body) else self.builder.retVoid(entry);
        return try self.dup(name);
    }

    // Lower closure similarly; naive capture: find free names and pass as extra params (TODO).
    fn materializeClosure(self: *LowerTir, ctx: *FunctionContext, clos: *const ast.Closure) anyerror![]const u8 {
        _ = ctx;
        var buf: [64]u8 = undefined;
        const name = try std.fmt.bufPrint(&buf, "__closure${}", .{g_lambda_counter});
        g_lambda_counter += 1;
        const fn_ty_id = self.expr_types.get(@ptrCast(clos)) orelse return LowerError.SemanticError;
        const fn_ty = self.type_arena.get(fn_ty_id).Function;
        const f = try self.builder.addFunction(name, fn_ty.result);
        // params
        for (clos.params.items, 0..) |p, i| {
            _ = try self.builder.addFuncParam(f, extractParamName(p), fn_ty.params[i]);
        }
        const entry = try self.builder.addBlock(f);
        var inner = FunctionContext.init(self.allocator, &self.builder, f, entry, self.type_arena, self.void_t, self.bool_t);
        defer inner.deinit();
        for (f.params.items, 0..) |pp, i| {
            try inner.bindImm(pp.name orelse try std.fmt.allocPrint(self.allocator, "arg{}", .{i}), pp.id);
        }
        // body is a single expression
        const rv = try self.lowerExpr(&inner, clos.body);
        self.builder.ret(entry, rv);
        return try self.dup(name);
    }

    fn materializeThunkOfExpr(self: *LowerTir, ctx: *FunctionContext, expr: *const ast.Expr, base: []const u8) anyerror![]const u8 {
        _ = ctx;
        var buf: [64]u8 = undefined;
        const name = try std.fmt.bufPrint(&buf, "{s}${}", .{ base, g_lambda_counter });
        g_lambda_counter += 1;
        // result type = type(expr)
        const res_ty = self.getExprType(expr) orelse return LowerError.SemanticError;
        const f = try self.builder.addFunction(name, res_ty);
        const entry = try self.builder.addBlock(f);
        var inner = FunctionContext.init(self.allocator, &self.builder, f, entry, self.type_arena, self.void_t, self.bool_t);
        defer inner.deinit();
        const rv = try self.lowerExpr(&inner, expr);
        self.builder.ret(entry, rv);
        return try self.dup(name);
    }

    fn constPathToString(self: *LowerTir, ctx: *FunctionContext, pp: *const ast.PathPattern) anyerror!tir.ValueId {
        // Serialize segments "a::b::C" -> string
        var buf = ArrayList(u8).init(self.allocator);
        defer buf.deinit();
        for (pp.segments.items, 0..) |seg, i| {
            if (i != 0) try buf.appendSlice("::");
            try buf.appendSlice(seg.name);
        }
        return self.builder.constString(ctx.current_block, try self.requireStringType(), buf.items);
    }

    fn dup(self: *LowerTir, s: []const u8) anyerror![]const u8 {
        const mem = try self.allocator.alloc(u8, s.len);
        std.mem.copyForwards(u8, mem, s);
        return mem;
    }

    // Basic placeholder: compute field index by name.
    // TODO: Replace with a real lookup using `types.zig` metadata.
    fn resolveStructFieldIndex(self: *LowerTir, _struct_ty: types.TypeId, _name: []const u8) anyerror!u32 {
        _ = self;
        _ = _struct_ty;
        _ = _name;
        // Without type metadata, fall back to 0 to keep lowering flowing.
        // Callers should ensure correctness later in codegen/verifier.
        return 0;
    }

    //==========================================================================
    // Tiny utilities
    //==========================================================================

    fn extractParamName(p: ast.Param) ?[]const u8 {
        if (p.pat) |pat| {
            return switch (pat.*) {
                .Binding => pat.Binding.name,
                else => null,
            };
        }
        return null;
    }
};

//==============================================================================
// FunctionContext & Var bindings
//==============================================================================

const VarKind = enum { Imm, Ptr };

const VarBinding = struct {
    kind: VarKind,
    v: tir.ValueId,
};

const LoopTarget = struct {
    label: ?[]const u8,
    break_block: *tir.Block, // raw exit block (pre-join)
    continue_block: *tir.Block, // backedge header
    join_block: *tir.Block, // value join for loop-as-expression
    join_param: tir.ValueId, // result parameter
    result_ty: types.TypeId,
    scope_depth: usize, // scope height when loop began
};

const DeferEntry = struct { expr: *const ast.Expr, is_err_only: bool };
const Scope = struct { defers: ArrayList(DeferEntry) };

const FunctionContext = struct {
    allocator: Allocator,
    builder: *tir.Builder,
    func: *tir.Function,
    current_block: *tir.Block,
    type_arena: *types.TypeArena,
    void_t: types.TypeId,
    bool_t: types.TypeId,
    bindings: StringHashMap(VarBinding),
    loop_stack: ArrayList(LoopTarget),
    scopes: ArrayList(Scope),

    fn init(
        allocator: Allocator,
        builder: *tir.Builder,
        func: *tir.Function,
        entry: *tir.Block,
        type_arena: *types.TypeArena,
        void_t: types.TypeId,
        bool_t: types.TypeId,
    ) FunctionContext {
        return .{
            .allocator = allocator,
            .builder = builder,
            .func = func,
            .current_block = entry,
            .type_arena = type_arena,
            .void_t = void_t,
            .bool_t = bool_t,
            .bindings = StringHashMap(VarBinding).init(allocator),
            .loop_stack = ArrayList(LoopTarget).init(allocator),
            .scopes = ArrayList(Scope).init(allocator),
        };
    }

    fn deinit(self: *FunctionContext) void {
        self.bindings.deinit();
        self.loop_stack.deinit();
        for (self.scopes.items) |*s| s.defers.deinit();
        self.scopes.deinit();
    }

    fn bindImm(self: *FunctionContext, name: []const u8, v: tir.ValueId) anyerror!void {
        try self.bindings.put(name, .{ .kind = .Imm, .v = v });
    }
    fn bindMut(self: *FunctionContext, name: []const u8, ptr: tir.ValueId) anyerror!void {
        try self.bindings.put(name, .{ .kind = .Ptr, .v = ptr });
    }
    fn lookup(self: *FunctionContext, name: []const u8) ?VarBinding {
        return self.bindings.get(name);
    }

    fn pushLoop(
        self: *FunctionContext,
        label: ?[]const u8,
        break_b: *tir.Block,
        cont_b: *tir.Block,
        join_b: *tir.Block,
        join_param: tir.ValueId,
        result_ty: types.TypeId,
    ) anyerror!void {
        try self.loop_stack.append(.{
            .label = label,
            .break_block = break_b,
            .continue_block = cont_b,
            .join_block = join_b,
            .join_param = join_param,
            .result_ty = result_ty,
            .scope_depth = self.scopes.items.len,
        });
    }
    fn popLoop(self: *FunctionContext) void {
        _ = self.loop_stack.pop();
    }

    // ---- scope & defer management ----
    fn pushScope(self: *FunctionContext) anyerror!void {
        const s = Scope{ .defers = ArrayList(DeferEntry).init(self.allocator) };
        try self.scopes.append(s);
    }
    fn popScope(self: *FunctionContext) void {
        const s = self.scopes.pop();
        s.?.defers.deinit();
    }
    fn addDefer(self: *FunctionContext, expr: *const ast.Expr, is_err_only: bool) anyerror!void {
        if (self.scopes.items.len == 0) {
            // ensure we always have a scope (shouldn't happen if callers pushScope)
            try self.pushScope();
        }
        const top = &self.scopes.items[self.scopes.items.len - 1];
        try top.defers.append(.{ .expr = expr, .is_err_only = is_err_only });
    }

    fn findLoop(self: *FunctionContext, label: ?[]const u8) ?*LoopTarget {
        if (label == null) {
            if (self.loop_stack.items.len == 0) return null;
            return &self.loop_stack.items[self.loop_stack.items.len - 1];
        }
        const l = label.?;
        var i: isize = @intCast(self.loop_stack.items.len - 1);
        while (i >= 0) : (i -= 1) {
            if (self.loop_stack.items[@intCast(i)].label) |lb| {
                if (std.mem.eql(u8, lb, l)) return &self.loop_stack.items[@intCast(i)];
            }
        }
        return null;
    }
};
