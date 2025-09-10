const std = @import("std");
const cst = @import("cst.zig");
const Loc = @import("lexer.zig").Token.Loc;
const ast = @import("ast.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;

// Minimal second stage: checker + desugarer scaffold with a simple work queue.
// - Walks the AST and enqueues tasks for declarations and expressions.
// - Provides hooks for future type checking, desugaring, and comptime execution.
// - Emits no-op warnings sparingly for unimplemented metaprogramming actions.
pub const Checker = struct {
    allocator: std.mem.Allocator,
    diags: *Diagnostics,
    queue: std.array_list.Managed(Task),

    // Used to avoid spamming warnings for metaprogramming placeholders
    warned_meta: bool = false,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics) Checker {
        return .{ .allocator = allocator, .diags = diags, .queue = std.array_list.Managed(Task).init(allocator) };
    }

    pub fn deinit(self: *Checker) void {
        self.queue.deinit();
    }

    pub fn run(self: *Checker, program: *ast.Unit) !*ast.Unit {
        // Seed with top-level declarations from HIR
        for (program.decls.items) |*decl| {
            if (decl.ty) |t| try self.enqueue(.{ .TypeExpr = @constCast(t.ast_ref) });
            if (decl.lhs) |l| try self.enqueue(.{ .TypeExpr = @constCast(l.ast_ref) });
            try self.enqueue(.{ .TypeExpr = @constCast(decl.rhs.ast_ref) });
        }

        // Process tasks until fixed point (queue drained)
        while (self.queue.items.len > 0) {
            const task = self.queue.pop().?;
            try self.handle(task);
        }
        return program;
    }

    const Task = union(enum) {
        ResolveDecl: *cst.Decl,
        TypeExpr: *cst.Expr,
        DesugarExpr: *cst.Expr,
        // Metaprogramming hooks
        ComptimeBlock: *cst.Expr, // .Comptime (Block)
        InsertSite: *cst.Expr, // .Insert
    };

    fn enqueue(self: *Checker, task: Task) !void {
        try self.queue.append(task);
    }

    fn handle(self: *Checker, task: Task) !void {
        switch (task) {
            .ResolveDecl => |decl| try self.resolveDecl(decl),
            .TypeExpr => |expr| try self.typeExpr(expr),
            .DesugarExpr => |expr| try self.desugarExpr(expr),
            .ComptimeBlock => |expr| try self.handleComptime(expr),
            .InsertSite => |expr| try self.handleInsert(expr),
        }
    }

    fn resolveDecl(self: *Checker, decl: *cst.Decl) !void {
        if (decl.ty) |ty| try self.enqueue(.{ .TypeExpr = ty });
        if (decl.lhs) |lhs| try self.enqueue(.{ .TypeExpr = lhs });
        try self.enqueue(.{ .TypeExpr = decl.rhs });
        // Future: bind names, symbol table population, constant folding, etc.
    }

    fn desugarExpr(self: *Checker, expr: *cst.Expr) !void {
        // Placeholder for future desugaring passes. For now, just continue walking.
        try self.typeExpr(expr);
    }

    fn handleComptime(self: *Checker, expr: *cst.Expr) !void {
        // Until we implement execution, at least walk contained blocks/exprs
        if (!self.warned_meta) {
            // Emit a single note to indicate metaprogramming is not yet executed
            const here = exprLoc(expr);
            _ = self.diags.addNote(here, "checker: metaprogramming not executed yet; walking only", .{}) catch {};
            self.warned_meta = true;
        }

        switch (expr.*) {
            .Comptime => |ct| switch (ct) {
                .Block => |blk| try self.walkBlock(&blk),
                .Expr => |inner| try self.enqueue(.{ .TypeExpr = inner }),
            },
            else => {},
        }
    }

    fn handleInsert(self: *Checker, expr: *cst.Expr) !void {
        if (!self.warned_meta) {
            const loc = exprLoc(expr);
            _ = self.diags.addNote(loc, "checker: insert not expanded yet; placeholder", .{}) catch {};
            self.warned_meta = true;
        }
        // Still walk the inserted expression to collect potential diagnostics early
        switch (expr.*) {
            .Insert => |ins| try self.enqueue(.{ .TypeExpr = ins.expr }),
            else => {},
        }
    }

    fn typeExpr(self: *Checker, expr: *cst.Expr) !void {
        switch (expr.*) {
            .Literal => {},
            .Ident => {},
            .BuiltinType => {},
            .Unreachable => {},
            .Null => {},
            .Continue => {},

            .Prefix => |p| try self.enqueue(.{ .TypeExpr = p.right }),
            .Deref => |d| try self.enqueue(.{ .TypeExpr = d.expr }),
            .Infix => |i| {
                try self.enqueue(.{ .TypeExpr = i.left });
                try self.enqueue(.{ .TypeExpr = i.right });
            },
            .Field => |f| try self.enqueue(.{ .TypeExpr = f.parent }),
            .Index => |ix| {
                try self.enqueue(.{ .TypeExpr = ix.collection });
                try self.enqueue(.{ .TypeExpr = ix.index });
            },
            .Call => |c| {
                try self.enqueue(.{ .TypeExpr = c.callee });
                for (c.args.items) |arg| try self.enqueue(.{ .TypeExpr = arg });
            },
            .Array => |a| for (a.elems.items) |e| try self.enqueue(.{ .TypeExpr = e }),
            .Tuple => |t| for (t.elems.items) |e| try self.enqueue(.{ .TypeExpr = e }),
            .Map => |m| for (m.entries.items) |kv| {
                try self.enqueue(.{ .TypeExpr = kv.key });
                try self.enqueue(.{ .TypeExpr = kv.value });
            },
            .Struct => |st| for (st.fields.items) |fld| try self.enqueue(.{ .TypeExpr = fld.value }),
            .Return => |r| if (r.value) |v| try self.enqueue(.{ .TypeExpr = v }),
            .Break => |b| if (b.value) |v| try self.enqueue(.{ .TypeExpr = v }),
            .Defer => |d| try self.enqueue(.{ .TypeExpr = d.expr }),
            .ErrDefer => |ed| try self.enqueue(.{ .TypeExpr = ed.expr }),
            .ErrUnwrap => |eu| try self.enqueue(.{ .TypeExpr = eu.expr }),
            .Await => |aw| try self.enqueue(.{ .TypeExpr = aw.expr }),
            .Cast => |c| {
                try self.enqueue(.{ .TypeExpr = c.expr });
                try self.enqueue(.{ .TypeExpr = c.ty });
            },
            .Catch => |c| {
                try self.enqueue(.{ .TypeExpr = c.expr });
                try self.enqueue(.{ .TypeExpr = c.handler });
            },
            .Import => |imp| try self.enqueue(.{ .TypeExpr = imp.expr }),
            .TypeOf => |t| try self.enqueue(.{ .TypeExpr = t.expr }),

            .If => |iff| {
                try self.enqueue(.{ .TypeExpr = iff.cond });
                try self.walkBlock(&iff.then_block);
                if (iff.else_block) |eb|
                    try self.enqueue(.{ .TypeExpr = eb });
            },
            .While => |w| {
                if (w.cond) |c| try self.enqueue(.{ .TypeExpr = c });
                // Pattern checking TBD
                try self.walkBlock(&w.body);
            },
            .For => |f| {
                // Pattern checking TBD
                try self.enqueue(.{ .TypeExpr = f.iterable });
                try self.walkBlock(&f.body);
            },
            .Match => |m| {
                try self.enqueue(.{ .TypeExpr = m.expr });
                for (m.arms.items) |arm| {
                    // Pattern checking TBD
                    if (arm.guard) |g| try self.enqueue(.{ .TypeExpr = g });
                    try self.enqueue(.{ .TypeExpr = arm.body });
                }
            },

            .Function => |fnc| {
                for (fnc.params.items) |param| {
                    if (param.pat) |p| try self.enqueue(.{ .TypeExpr = p });
                    if (param.ty) |t| try self.enqueue(.{ .TypeExpr = t });
                    if (param.value) |v| try self.enqueue(.{ .TypeExpr = v });
                }
                if (fnc.result_ty) |t| try self.enqueue(.{ .TypeExpr = t });
                if (fnc.body) |body| try self.walkBlock(&body);
            },

            .Closure => |cl| {
                for (cl.params.items) |param| {
                    if (param.pat) |p| try self.enqueue(.{ .TypeExpr = p });
                    if (param.ty) |t| try self.enqueue(.{ .TypeExpr = t });
                    if (param.value) |v| try self.enqueue(.{ .TypeExpr = v });
                }
                if (cl.result_ty) |t| try self.enqueue(.{ .TypeExpr = t });
                try self.enqueue(.{ .TypeExpr = cl.body });
            },

            .Async => |a| try self.enqueue(.{ .TypeExpr = a.body }),

            .Comptime => |_| try self.enqueue(.{ .ComptimeBlock = expr }),
            .Code => |code_blk| try self.walkBlock(&code_blk.block),
            .Insert => |_| try self.enqueue(.{ .InsertSite = expr }),
            .Block => |blk| try self.walkBlock(&blk),
            .Mlir => unreachable, // MLIR should be lowered away before reaching here
        }
    }

    fn walkBlock(self: *Checker, block: *const cst.Block) !void {
        for (block.items.items) |*decl| try self.enqueue(.{ .ResolveDecl = decl });
    }
    
    fn exprLoc(e: *const cst.Expr) Loc {
        return switch (e.*) {
            .Literal => |x| x.loc,
            .Ident => |x| x.loc,
            .Prefix => |x| x.loc,
            .Deref => |x| x.loc,
            .Infix => |x| x.loc,
            .Await => |x| x.loc,
            .Array => |x| x.loc,
            .Tuple => |x| x.loc,
            .Map => |x| x.loc,
            .Function => |x| x.loc,
            .Block => |x| x.loc,
            .Comptime => |ct| switch (ct) { .Block => |blk| blk.loc, .Expr => |inner| exprLoc(inner) },
            .Code => |x| x.loc,
            .Insert => |x| x.loc,
            .Mlir => |x| x.loc,
            .Call => |x| x.loc,
            .Index => |x| x.loc,
            .Field => |x| x.loc,
            .Struct => |x| x.loc,
            .Return => |x| x.loc,
            .If => |x| x.loc,
            .While => |x| x.loc,
            .For => |x| x.loc,
            .Match => |x| x.loc,
            .Break => |x| x.loc,
            .Continue => |x| x.loc,
            .Unreachable => |x| x.loc,
            .Null => |x| x.loc,
            .Defer => |x| x.loc,
            .ErrDefer => |x| x.loc,
            .ErrUnwrap => |x| x.loc,
            .Catch => |x| x.loc,
            .Async => |x| x.loc,
            .Cast => |x| x.loc,
            .Import => |x| x.loc,
            .TypeOf => |x| x.loc,
            .Closure => |x| x.loc,
            .BuiltinType => |b| switch (b) {
                .Array => |x| x.loc,
                .DynArray => |x| x.loc,
                .MapType => |x| x.loc,
                .Slice => |x| x.loc,
                .Optional => |x| x.loc,
                .ErrorSet => |x| x.loc,
                .Error => |x| x.loc,
                .Struct => |x| x.loc,
                .Enum => |x| x.loc,
                .Variant => |x| x.loc,
                .Union => |x| x.loc,
                .Pointer => |x| x.loc,
                .Simd => |x| x.loc,
                .Complex => |x| x.loc,
                .Tensor => |x| x.loc,
                .Type => |x| x.loc,
                .Any => |x| x.loc,
                .Noreturn => |x| x.loc,
            },
        };
    }
};
