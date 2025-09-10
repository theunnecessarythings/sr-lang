const std = @import("std");
const ast = @import("ast.zig");
const Loc = @import("lexer.zig").Token.Loc;
const Diagnostics = @import("diagnostics.zig").Diagnostics;

pub const Checker = struct {
    allocator: std.mem.Allocator,
    diags: *Diagnostics,

    // context stacks
    func_stack: std.ArrayListUnmanaged(FunctionCtx) = .{},
    loop_stack: std.ArrayListUnmanaged(LoopCtx) = .{},

    // meta notes de-dup
    warned_meta: bool = false,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics) Checker {
        return .{ .allocator = allocator, .diags = diags };
    }

    pub fn deinit(self: *Checker) void {
        self.func_stack.deinit(self.allocator);
        self.loop_stack.deinit(self.allocator);
    }

    pub fn run(self: *Checker, program: *ast.Unit) !void {
        for (program.decls.items) |*d| try self.checkDecl(d);
    }

    const FunctionCtx = struct {
        result_ty: ?*ast.Expr,
    };

    const LoopCtx = struct { label: ?[]const u8 };

    fn pushFunc(self: *Checker, result_ty: ?*ast.Expr) !void {
        try self.func_stack.append(self.allocator, .{ .result_ty = result_ty });
    }
    fn popFunc(self: *Checker) void {
        if (self.func_stack.items.len > 0) {
            _ = self.func_stack.pop();
        }
    }
    fn inFunction(self: *const Checker) bool {
        return self.func_stack.items.len > 0;
    }
    fn currentFunc(self: *const Checker) ?FunctionCtx {
        if (self.func_stack.items.len == 0) return null;
        return self.func_stack.items[self.func_stack.items.len - 1];
    }

    fn pushLoop(self: *Checker, label: ?[]const u8) !void {
        try self.loop_stack.append(self.allocator, .{ .label = label });
    }
    fn popLoop(self: *Checker) void {
        if (self.loop_stack.items.len > 0) {
            _ = self.loop_stack.pop();
        }
    }
    fn inLoop(self: *const Checker) bool {
        return self.loop_stack.items.len > 0;
    }

    fn checkDecl(self: *Checker, d: *ast.Decl) !void {
        if (d.ty) |ty| try self.checkTypeExpr(ty);
        try self.checkExpr(d.value);
        if (d.binding) |pat| {
            try self.checkPattern(pat);
        }
    }

    fn checkStmt(self: *Checker, s: *const ast.Statement) !void {
        switch (s.*) {
            .Expr => |e| {
                var em = e;
                try self.checkExpr(&em);
            },
            .Decl => |d| {
                var dm = d;
                try self.checkDecl(&dm);
            },
            .Assign => |a| {
                try self.checkExpr(a.left);
                try self.checkExpr(a.right);
            },
            .Insert => |ins| {
                if (!self.warned_meta) {
                    _ = self.diags.addNote(ins.loc, "checker: insert not expanded yet; walking only", .{}) catch {};
                    self.warned_meta = true;
                }
                try self.checkExpr(ins.expr);
            },
            .Return => |ret| {
                if (!self.inFunction()) {
                    try self.diags.addError(ret.loc, "'return' used outside of a function", .{});
                } else {
                    const f = self.currentFunc().?;
                    if (f.result_ty == null and ret.value != null) {
                        try self.diags.addError(ret.loc, "return with a value in a void function", .{});
                    }
                    if (f.result_ty != null and ret.value == null) {
                        try self.diags.addError(ret.loc, "missing return value", .{});
                    }
                    if (ret.value) |v| try self.checkExpr(v);
                }
            },
            .Break => |br| {
                if (!self.inLoop()) try self.diags.addError(br.loc, "'break' used outside of a loop", .{});
                if (br.value) |v| try self.checkExpr(v);
            },
            .Continue => |c| {
                if (!self.inLoop()) try self.diags.addError(c.loc, "'continue' used outside of a loop", .{});
            },
            .Unreachable => |_| {},
            .Defer => |df| {
                if (!self.inFunction()) try self.diags.addError(df.loc, "'defer' only valid inside a function", .{});
                try self.checkExpr(df.expr);
            },
            .ErrDefer => |ed| {
                if (!self.inFunction()) try self.diags.addError(ed.loc, "'errdefer' only valid inside a function", .{});
                try self.checkExpr(ed.expr);
            },
        }
    }

    fn checkBlock(self: *Checker, b: *const ast.Block) !void {
        for (b.items.items) |*st| try self.checkStmt(st);
    }

    fn checkExpr(self: *Checker, e: *ast.Expr) anyerror!void {
        switch (e.*) {
            // literals and ids
            .IntLit, .FloatLit, .BoolLit, .StringLit, .CharLit, .NullLit, .UndefLit, .Identifier => {},

            // builtin type in expression position: allowed only in type-context; flag otherwise
            .Type => |*bt| {
                try self.checkBuiltinType(bt);
            },

            // compound literals
            .TupleLit => |t| for (t.elems.items) |sub| try self.checkExpr(sub),
            .ArrayLit => |a| for (a.elems.items) |sub| try self.checkExpr(sub),
            .MapLit => |m| for (m.entries.items) |kv| {
                try self.checkExpr(kv.key);
                try self.checkExpr(kv.value);
            },
            .StructLit => |st| for (st.fields.items) |f| try self.checkExpr(f.value),
            .VariantLit => |v| if (v.value) |sub| try self.checkExpr(sub),
            .EnumLit => |v| if (v.value) |sub| try self.checkExpr(sub),
            .FunctionLit => |fnc| {
                // params
                var seen = std.StringHashMap(void).init(self.allocator);
                defer seen.deinit();
                for (fnc.params.items) |p| {
                    if (p.pat) |pat| {
                        if (pat.* == .Binding) {
                            const name = pat.Binding.name;
                            if (seen.get(name) != null) {
                                try self.diags.addError(pat.Binding.loc, "duplicate parameter '{s}'", .{name});
                            } else {
                                _ = seen.put(name, {}) catch {};
                            }
                        }
                        try self.checkPattern(pat);
                    }
                    if (p.ty) |ty| try self.checkTypeExpr(ty);
                    if (p.value) |dv| try self.checkExpr(dv);
                }
                if (fnc.result_ty) |rt| try self.checkTypeExpr(rt);
                if (fnc.body) |body| {
                    try self.pushFunc(fnc.result_ty);
                    defer self.popFunc();
                    try self.checkBlock(&body);
                }
            },

            // prefix ops
            .UnaryPlus => |u| try self.checkExpr(u.right),
            .UnaryMinus => |u| try self.checkExpr(u.right),
            .AddressOf => |u| try self.checkExpr(u.right),
            .LogicalNot => |u| try self.checkExpr(u.right),

            // range
            .Range => |r| {
                if (r.start) |s| try self.checkExpr(s);
                if (r.end) |en| try self.checkExpr(en);
            },

            // infix ops
            .InfixAdd => |v| try self.checkBinary(v.left, v.right),
            .InfixSub => |v| try self.checkBinary(v.left, v.right),
            .InfixMul => |v| try self.checkBinary(v.left, v.right),
            .InfixDiv => |v| try self.checkBinary(v.left, v.right),
            .InfixMod => |v| try self.checkBinary(v.left, v.right),
            .InfixShl => |v| try self.checkBinary(v.left, v.right),
            .InfixShr => |v| try self.checkBinary(v.left, v.right),
            .InfixBitAnd => |v| try self.checkBinary(v.left, v.right),
            .InfixBitOr => |v| try self.checkBinary(v.left, v.right),
            .InfixBitXor => |v| try self.checkBinary(v.left, v.right),
            .InfixEq => |v| try self.checkBinary(v.left, v.right),
            .InfixNeq => |v| try self.checkBinary(v.left, v.right),
            .InfixLt => |v| try self.checkBinary(v.left, v.right),
            .InfixLte => |v| try self.checkBinary(v.left, v.right),
            .InfixGt => |v| try self.checkBinary(v.left, v.right),
            .InfixGte => |v| try self.checkBinary(v.left, v.right),
            .InfixLogicalAnd => |v| try self.checkBinary(v.left, v.right),
            .InfixLogicalOr => |v| try self.checkBinary(v.left, v.right),
            .InfixCatch => |v| try self.checkBinary(v.left, v.right),
            .InfixOrelse => |v| try self.checkBinary(v.left, v.right),

            // postfix
            .PostfixErrorUnwrap => |p| try self.checkExpr(p.expr),
            .PostfixOptionalUnwrap => |p| try self.checkExpr(p.expr),
            .PostfixDeref => |p| try self.checkExpr(p.expr),
            .PostfixIndex => |p| {
                try self.checkExpr(p.collection);
                try self.checkExpr(p.index);
            },
            .PostfixField => |p| try self.checkExpr(p.parent),
            .PostfixCall => |p| {
                try self.checkExpr(p.callee);
                for (p.args.items) |arg| try self.checkExpr(arg);
            },
            .PostfixAwait => |p| try self.checkExpr(p.expr),

            // casts
            .CastNormal => |c| {
                try self.checkExpr(c.expr);
                try self.checkTypeExpr(c.ty);
            },
            .CastBit => |c| {
                try self.checkExpr(c.expr);
                try self.checkTypeExpr(c.ty);
            },
            .CastSaturate => |c| {
                try self.checkExpr(c.expr);
                try self.checkTypeExpr(c.ty);
            },
            .CastWrap => |c| {
                try self.checkExpr(c.expr);
                try self.checkTypeExpr(c.ty);
            },
            .CastChecked => |c| {
                try self.checkExpr(c.expr);
                try self.checkTypeExpr(c.ty);
            },

            // control flow
            .If => |iff| {
                try self.checkExpr(iff.cond);
                try self.checkBlock(&iff.then_block);
                if (iff.else_block) |eb| try self.checkExpr(eb);
            },
            .While => |w| {
                if (w.cond) |c| try self.checkExpr(c);
                try self.pushLoop(w.label);
                defer self.popLoop();
                try self.checkBlock(&w.body);
            },
            .For => |f| {
                try self.checkPattern(f.pattern);
                try self.checkExpr(f.iterable);
                try self.pushLoop(f.label);
                defer self.popLoop();
                try self.checkBlock(&f.body);
            },
            .Match => |m| {
                try self.checkExpr(m.expr);
                for (m.arms.items) |arm| {
                    try self.checkPattern(arm.pattern);
                    if (arm.guard) |g| try self.checkExpr(g);
                    try self.checkExpr(arm.body);
                }
            },

            // blocks
            .Block => |b| try self.checkBlock(&b),
            .ComptimeBlock => |cb| {
                if (!self.warned_meta) {
                    _ = self.diags.addNote(cb.loc, "checker: comptime not executed yet; walking only", .{}) catch {};
                    self.warned_meta = true;
                }
                try self.checkBlock(&cb.block);
            },
            .CodeBlock => |code| {
                if (!self.warned_meta) {
                    _ = self.diags.addNote(code.loc, "checker: code block not evaluated; walking only", .{}) catch {};
                    self.warned_meta = true;
                }
                try self.checkBlock(&code.block);
            },
            .AsyncBlock => |ab| try self.checkExpr(ab.body),
            .MlirBlock => |_| {},
            .Closure => |cl| {
                // parameters
                for (cl.params.items) |p| {
                    if (p.pat) |pat| try self.checkPattern(pat);
                    if (p.ty) |ty| try self.checkTypeExpr(ty);
                    if (p.value) |dv| try self.checkExpr(dv);
                }
                if (cl.result_ty) |rt| try self.checkTypeExpr(rt);
                try self.pushFunc(cl.result_ty);
                defer self.popFunc();
                try self.checkExpr(cl.body);
            },

            // meta/introspection
            .Import => |imp| try self.checkExpr(imp.expr),
            .TypeOf => |t| try self.checkExpr(t.expr),
        }
    }

    fn checkBinary(self: *Checker, l: *ast.Expr, r: *ast.Expr) !void {
        try self.checkExpr(l);
        try self.checkExpr(r);
    }

    fn checkPattern(self: *Checker, p: *ast.Pattern) anyerror!void {
        switch (p.*) {
            .Wildcard => {},
            .Literal => |lit| try self.checkExpr(lit),
            .Path => |_| {},
            .Binding => |_| {},
            .Tuple => |t| for (t.elems.items) |sub| try self.checkPattern(sub),
            .Slice => |s| {
                for (s.elems.items) |sub| try self.checkPattern(sub);
                if (s.rest_binding) |rb| try self.checkPattern(rb);
            },
            .Struct => |st| for (st.fields.items) |f| try self.checkPattern(f.pattern),
            .VariantTuple => |vt| for (vt.elems.items) |sub| try self.checkPattern(sub),
            .VariantStruct => |vs| for (vs.fields.items) |f| try self.checkPattern(f.pattern),
            .Range => |r| {
                if (r.start) |s| try self.checkExpr(s);
                if (r.end) |en| try self.checkExpr(en);
            },
            .Or => |o| for (o.alts.items) |alt| try self.checkPattern(alt),
            .At => |a| try self.checkPattern(a.pattern),
        }
    }

    fn checkTypeExpr(self: *Checker, e: *ast.Expr) !void {
        switch (e.*) {
            .Type => |*b| try self.checkBuiltinType(b),
            .TypeOf => |t| try self.checkExpr(t.expr),
            .Identifier => {},
            .PostfixField => |pf| try self.checkExpr(pf.parent),
            // Accept tuple types written as (T1, T2, ...)
            .TupleLit => |t| {
                for (t.elems.items) |elem| try self.checkTypeExpr(elem);
            },
            // Function type: validate param and result types; no body required
            .FunctionLit => |fnc| {
                for (fnc.params.items) |p| {
                    if (p.ty) |ty| {
                        try self.checkTypeExpr(ty);
                    } else {
                        try self.diags.addError(p.loc, "parameter type required in function type", .{});
                    }
                }
                if (fnc.result_ty) |rt| try self.checkTypeExpr(rt) else {
                    try self.diags.addError(fnc.loc, "result type required in function type", .{});
                }
            },
            else => {
                const loc = exprLoc(e);
                try self.diags.addError(loc, "expected a type expression", .{});
            },
        }
    }

    fn checkBuiltinType(self: *Checker, b: *ast.BuiltinType) anyerror!void {
        switch (b.*) {
            .Tuple => |t| {
                for (t.elems.items) |e| {
                    try self.checkTypeExpr(e);
                }
            },
            .Array => |a| {
                try self.checkTypeExpr(a.elem);
                // require compile-time integer size (simple literal check)
                if (a.size.* != .IntLit) try self.diags.addError(exprLoc(a.size), "array size must be an integer literal", .{});
            },
            .DynArray => |u| try self.checkTypeExpr(u.elem),
            .MapType => |m| {
                try self.checkTypeExpr(m.key);
                try self.checkTypeExpr(m.value);
            },
            .Slice => |u| try self.checkTypeExpr(u.elem),
            .Optional => |u| try self.checkTypeExpr(u.elem),
            .ErrorSet => |es| {
                try self.checkTypeExpr(es.err);
                try self.checkTypeExpr(es.value);
            },
            .Struct => |st| {
                // duplicate field names
                var seen = std.StringHashMap(void).init(self.allocator);
                defer seen.deinit();
                for (st.fields.items) |f| {
                    if (seen.get(f.name) != null) {
                        try self.diags.addError(f.loc, "duplicate field '{s}'", .{f.name});
                    } else {
                        _ = seen.put(f.name, {}) catch {};
                    }
                    try self.checkTypeExpr(f.ty);
                    if (f.value) |v| try self.checkExpr(v);
                }
            },
            .Enum => |en| {
                var seen = std.StringHashMap(void).init(self.allocator);
                defer seen.deinit();
                for (en.fields.items) |f| {
                    if (seen.get(f.name) != null) {
                        try self.diags.addError(f.loc, "duplicate enum field '{s}'", .{f.name});
                    } else {
                        _ = seen.put(f.name, {}) catch {};
                    }
                    if (f.value) |v| try self.checkExpr(v);
                }
                if (en.discriminant) |d| {
                    if (d.* != .IntLit) try self.diags.addWarning(exprLoc(d), "enum discriminant should be an integer literal", .{});
                }
            },
            .Variant => |vr| {
                var seen = std.StringHashMap(void).init(self.allocator);
                defer seen.deinit();
                for (vr.fields.items) |f| {
                    if (seen.get(f.name) != null) {
                        try self.diags.addError(f.loc, "duplicate variant '{s}'", .{f.name});
                    } else {
                        _ = seen.put(f.name, {}) catch {};
                    }
                    if (f.ty) |ty| switch (ty) {
                        .Tuple => |elems| for (elems.items) |e| try self.checkTypeExpr(e),
                        .Struct => |fields| for (fields.items) |sf| try self.checkTypeExpr(sf.ty),
                    };
                    if (f.value) |v| try self.checkExpr(v);
                }
            },
            .Error => |vr| {
                var seen = std.StringHashMap(void).init(self.allocator);
                defer seen.deinit();
                for (vr.fields.items) |f| {
                    if (seen.get(f.name) != null) {
                        try self.diags.addError(f.loc, "duplicate error variant '{s}'", .{f.name});
                    } else {
                        _ = seen.put(f.name, {}) catch {};
                    }
                    if (f.ty) |ty| switch (ty) {
                        .Tuple => |elems| for (elems.items) |e| try self.checkTypeExpr(e),
                        .Struct => |fields| for (fields.items) |sf| try self.checkTypeExpr(sf.ty),
                    };
                    if (f.value) |v| try self.checkExpr(v);
                }
            },
            .Union => |un| {
                var seen = std.StringHashMap(void).init(self.allocator);
                defer seen.deinit();
                for (un.fields.items) |f| {
                    if (seen.get(f.name) != null) {
                        try self.diags.addError(f.loc, "duplicate field '{s}'", .{f.name});
                    } else {
                        _ = seen.put(f.name, {}) catch {};
                    }
                    try self.checkTypeExpr(f.ty);
                    if (f.value) |v| try self.checkExpr(v);
                }
            },
            .Pointer => |p| try self.checkTypeExpr(p.elem),
            .Simd => |s| {
                try self.checkTypeExpr(s.elem);
                if (s.lanes.* != .IntLit) try self.diags.addError(exprLoc(s.lanes), "SIMD lanes must be an integer literal", .{});
            },
            .Complex => |c| try self.checkTypeExpr(c.elem),
            .Tensor => |t| {
                try self.checkTypeExpr(t.elem);
                for (t.shape.items) |len_expr| {
                    if (len_expr.* != .IntLit) try self.diags.addError(exprLoc(len_expr), "tensor dimension must be an integer literal", .{});
                }
            },
            .Type => |_| {},
            .Any => |_| {},
            .Noreturn => |_| {},
        }
    }

    fn exprLoc(e: *const ast.Expr) Loc {
        return switch (e.*) {
            .Type => |x| switch (x) {
                inline else => |v| v.loc,
            },
            inline else => |x| x.loc,
        };
    }
};
