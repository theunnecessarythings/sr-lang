const std = @import("std");
const ast = @import("ast.zig");
const comptime_mod = @import("comptime.zig");

const Value = comptime_mod.ComptimeValue;
const Sequence = comptime_mod.Sequence;
const StructField = comptime_mod.StructField;
const StructValue = comptime_mod.StructValue;
const RangeValue = comptime_mod.RangeValue;
const MethodKey = struct {
    owner: ast.StrId,
    method: ast.StrId,
};
const MethodMap = std.AutoHashMap(MethodKey, ast.ExprId);
const FunctionValue = comptime_mod.FunctionValue;
const NumericValue = union(enum) {
    Int: i128,
    Float: f64,
};

pub const Binding = struct {
    name: ast.StrId,
    value: Value,
};

const FunctionKey = struct {
    decl_id: ast.DeclId,
    bindings_hash: u64,
};

fn keysEqual(a: FunctionKey, b: FunctionKey) bool {
    return a.decl_id.toRaw() == b.decl_id.toRaw() and a.bindings_hash == b.bindings_hash;
}

const FunctionSpecializationEntry = struct {
    key: FunctionKey,
    func_expr: ast.ExprId,
    bindings: BindingSnapshot,

    fn destroy(self: *FunctionSpecializationEntry, allocator: std.mem.Allocator) void {
        self.bindings.destroy(allocator);
    }
};

pub const SpecializationResult = struct {
    func: FunctionValue,
    snapshot: BindingSnapshot,
};

pub const BindingSnapshot = struct {
    bindings: std.ArrayList(Binding),
    hash: u64,

    pub fn lookup(self: *BindingSnapshot, name: ast.StrId) ?*Binding {
        for (self.bindings.items) |*binding| if (binding.name.eq(name)) return binding;
        return null;
    }

    pub fn destroy(self: *BindingSnapshot, allocator: std.mem.Allocator) void {
        for (self.bindings.items) |*binding| binding.value.destroy(allocator);
        self.bindings.deinit(allocator);
        self.hash = 0;
    }
};

pub const Interpreter = struct {
    allocator: std.mem.Allocator,
    ast: *ast.Ast,
    bindings: std.ArrayList(Binding),
    method_table: MethodMap,
    specializations: std.AutoHashMap(u128, FunctionSpecializationEntry),

    pub const Error = error{
        UnsupportedExpr,
        InvalidStatement,
        InvalidBinaryOperand,
        DivisionByZero,
        InvalidType,
        BindingNotFound,
        AllocationFailed,
        InvalidCall,
        MissingArgument,
        TooManyArguments,
        InvalidFieldAccess,
        InvalidIndexAccess,
    };

    pub fn init(allocator: std.mem.Allocator, ast_unit: *ast.Ast) anyerror!Interpreter {
        var interp = Interpreter{
            .allocator = allocator,
            .ast = ast_unit,
            .bindings = std.ArrayList(Binding).empty,
            .method_table = MethodMap.init(allocator),
            .specializations = std.AutoHashMap(u128, FunctionSpecializationEntry).init(allocator),
        };
        var success = false;
        defer if (!success) interp.method_table.deinit();
        defer if (!success) interp.specializations.deinit();
        try interp.registerMethods();
        success = true;
        return interp;
    }

    pub fn deinit(self: *Interpreter) void {
        for (self.bindings.items) |*binding| binding.value.destroy(self.allocator);
        self.bindings.deinit(self.allocator);
        self.method_table.deinit();
        var iter = self.specializations.iterator();
        while (iter.next()) |entry| entry.value_ptr.*.destroy(self.allocator);
        self.specializations.deinit();
    }

    pub fn evalExpr(self: *Interpreter, expr: ast.ExprId) anyerror!Value {
        const kind = self.ast.exprs.index.kinds.items[expr.toRaw()];
        return switch (kind) {
            .Literal => self.evalLiteral(self.ast.exprs.get(.Literal, expr)),
            .Ident => self.evalIdent(self.ast.exprs.get(.Ident, expr)),
            .Block => self.evalBlock(self.ast.exprs.get(.Block, expr)),
            .ComptimeBlock => {
                const block_row = self.ast.exprs.get(.ComptimeBlock, expr);
                const block_expr = self.ast.exprs.get(.Block, block_row.block);
                return try self.evalBlock(block_expr);
            },
            .Binary => self.evalBinary(self.ast.exprs.get(.Binary, expr)),
            .Unary => self.evalUnary(self.ast.exprs.get(.Unary, expr)),
            .If => self.evalIf(self.ast.exprs.get(.If, expr)),
            .FunctionLit => evalFunctionLit(expr),
            .ArrayLit => self.evalSequence(self.ast.exprs.get(.ArrayLit, expr).elems),
            .TupleLit => self.evalSequence(self.ast.exprs.get(.TupleLit, expr).elems),
            .Call => self.evalCall(self.ast.exprs.get(.Call, expr)),
            .FieldAccess => self.evalFieldAccess(self.ast.exprs.get(.FieldAccess, expr)),
            .IndexAccess => self.evalIndexAccess(self.ast.exprs.get(.IndexAccess, expr)),
            .StructLit => self.evalStructLit(self.ast.exprs.get(.StructLit, expr)),
            .Range => self.evalRange(self.ast.exprs.get(.Range, expr)),
            .Match => self.evalMatch(self.ast.exprs.get(.Match, expr)),
            .For => self.evalFor(self.ast.exprs.get(.For, expr)),
            .While => self.evalWhile(self.ast.exprs.get(.While, expr)),
            .Return => self.evalReturn(self.ast.exprs.get(.Return, expr)),
            else => return Error.UnsupportedExpr,
        };
    }

    pub fn bind(self: *Interpreter, name: ast.StrId, value: Value) !void {
        try self.setBinding(name, value);
    }

    pub fn lookup(self: *Interpreter, name: ast.StrId) anyerror!?Value {
        for (self.bindings.items) |binding| {
            if (binding.name.eq(name)) return try self.cloneValue(binding.value);
        }
        return null;
    }

    fn evalBlock(self: *Interpreter, block: ast.Rows.Block) anyerror!Value {
        var last_value: ?Value = null;
        const stmts = self.ast.stmts.stmt_pool.slice(block.items);
        for (stmts) |stmt_id| {
            if (try self.evalStatement(stmt_id, &last_value)) |value| {
                if (last_value) |*prev| prev.destroy(self.allocator);
                return value;
            }
        }
        if (last_value) |value| return value;
        return Value{ .Void = {} };
    }

    fn evalStatement(self: *Interpreter, stmt_id: ast.StmtId, last_value: *?Value) anyerror!?Value {
        const kind = self.ast.stmts.index.kinds.items[stmt_id.toRaw()];
        switch (kind) {
            .Expr => {
                const row = self.ast.stmts.get(.Expr, stmt_id);
                const result = try self.evalExpr(row.expr);
                if (last_value.*) |*prev| prev.destroy(self.allocator);
                last_value.* = result;
                return null;
            },
            .Decl => {
                const row = self.ast.stmts.get(.Decl, stmt_id);
                const decl = self.ast.exprs.Decl.get(row.decl);
                if (decl.pattern.isNone()) return Error.InvalidStatement;
                const pat_id = decl.pattern.unwrap();
                if (self.ast.pats.index.kinds.items[pat_id.toRaw()] != .Binding) return Error.InvalidStatement;
                const binding = self.ast.pats.get(.Binding, pat_id);
                const value = try self.evalExpr(decl.value);
                try self.setBinding(binding.name, value);
                return null;
            },
            .Assign => {
                const row = self.ast.stmts.get(.Assign, stmt_id);
                try self.evalAssignment(row);
                return null;
            },
            .Return => {
                const row = self.ast.stmts.get(.Return, stmt_id);
                if (row.value.isNone()) return Value{ .Void = {} };
                return try self.evalExpr(row.value.unwrap());
            },
            else => return Error.InvalidStatement,
        }
    }

    fn evalFunctionLit(expr: ast.ExprId) anyerror!Value {
        return Value{ .Function = .{ .expr = expr } };
    }

    fn evalAssignment(self: *Interpreter, row: ast.StmtRows.Assign) anyerror!void {
        const kind = self.ast.exprs.index.kinds.items[row.left.toRaw()];
        if (kind != .Ident) return Error.InvalidStatement;
        const ident = self.ast.exprs.get(.Ident, row.left);
        const value = try self.evalExpr(row.right);
        try self.setBinding(ident.name, value);
    }

    fn evalCall(self: *Interpreter, row: ast.Rows.Call) anyerror!Value {
        var callee_value: Value = .Void;
        var method_receiver: ?Value = null;
        defer if (method_receiver) |*recv| recv.destroy(self.allocator);

        const callee_kind = self.ast.exprs.index.kinds.items[row.callee.toRaw()];
        if (callee_kind == .FieldAccess) {
            const field_row = self.ast.exprs.get(.FieldAccess, row.callee);
            var parent = try self.evalExpr(field_row.parent);
            if (structOwner(parent)) |owner_name| {
                if (self.lookupMethod(owner_name, field_row.field)) |expr| {
                    callee_value = Value{ .Function = .{ .expr = expr } };
                    method_receiver = parent;
                } else {
                    callee_value = try self.evalFieldAccessWithParent(field_row, &parent, true);
                }
            } else {
                callee_value = try self.evalFieldAccessWithParent(field_row, &parent, true);
            }
        } else {
            callee_value = try self.evalExpr(row.callee);
        }
        defer callee_value.destroy(self.allocator);

        var args = try self.evalCallArgs(row.args);
        defer args.deinit(self.allocator);
        defer for (args.items) |*value| value.destroy(self.allocator);

        if (method_receiver) |recv| {
            try args.insert(self.allocator, 0, recv);
            method_receiver = null;
        }

        return switch (callee_value) {
            .Function => |func| try self.callFunction(func, &args),
            else => Error.InvalidCall,
        };
    }

    fn evalCallArgs(self: *Interpreter, range: ast.RangeExpr) anyerror!std.ArrayList(Value) {
        const exprs = self.ast.exprs.expr_pool.slice(range);
        if (exprs.len == 0) return .empty;
        var list = try std.ArrayList(Value).initCapacity(self.allocator, exprs.len);
        var success = false;
        defer if (!success) {
            for (list.items) |*value| value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < exprs.len) : (idx += 1) {
            list.appendAssumeCapacity(try self.evalExpr(exprs[idx]));
        }
        success = true;
        return list;
    }

    fn callFunction(self: *Interpreter, func: FunctionValue, args: *std.ArrayList(Value)) anyerror!Value {
        const row = self.ast.exprs.get(.FunctionLit, func.expr);
        const params = self.ast.exprs.param_pool.slice(row.params);
        if (!row.flags.is_variadic and args.items.len > params.len) return Error.TooManyArguments;
        var matches = std.ArrayList(Binding){};
        defer matches.deinit(self.allocator);
        var idx: usize = 0;
        while (idx < params.len) : (idx += 1) {
            const param = self.ast.exprs.Param.get(params[idx]);
            const is_variadic_param = row.flags.is_variadic and idx == params.len - 1;
            var value: Value = .Void;
            if (is_variadic_param) {
                value = try self.collectVariadicArgs(args, idx);
            } else if (idx < args.items.len) {
                value = args.items[idx];
                args.items[idx] = .Void;
            } else if (!param.value.isNone()) {
                value = try self.evalExpr(param.value.unwrap());
            } else {
                return Error.MissingArgument;
            }
            if (param.pat.isNone()) {
                value.destroy(self.allocator);
                continue;
            }
            const pattern = param.pat.unwrap();
            const before = matches.items.len;
            if (!try self.matchPattern(value, pattern, &matches)) {
                self.rollbackBindings(&matches, before);
                value.destroy(self.allocator);
                return Error.InvalidCall;
            }
            value.destroy(self.allocator);
        }
        var scope = try self.pushBindings(&matches);
        defer scope.deinit();
        if (row.body.isNone()) return Value{ .Void = {} };
        return try self.evalExpr(row.body.unwrap());
    }

    fn collectVariadicArgs(self: *Interpreter, args: *std.ArrayList(Value), start_idx: usize) anyerror!Value {
        if (start_idx >= args.items.len) return Value{ .Sequence = .{ .values = .empty } };
        const extra = args.items.len - start_idx;
        var list = try std.ArrayList(Value).initCapacity(self.allocator, extra);
        var success = false;
        defer if (!success) {
            for (list.items) |*value| value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = start_idx;
        while (idx < args.items.len) : (idx += 1) {
            list.appendAssumeCapacity(args.items[idx]);
            args.items[idx] = .Void;
        }
        success = true;
        return Value{ .Sequence = .{ .values = list } };
    }

    fn evalSequence(self: *Interpreter, expr_range: ast.RangeExpr) anyerror!Value {
        const exprs = self.ast.exprs.expr_pool.slice(expr_range);
        if (exprs.len == 0) return Value{ .Sequence = .{ .values = .empty } };
        var list = try std.ArrayList(Value).initCapacity(self.allocator, exprs.len);
        var success = false;
        defer if (!success) {
            for (list.items) |*value| value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < exprs.len) : (idx += 1) {
            const value = try self.evalExpr(exprs[idx]);
            list.appendAssumeCapacity(value);
        }
        success = true;
        return Value{ .Sequence = .{ .values = list } };
    }

    fn evalStructLit(self: *Interpreter, row: ast.Rows.StructLit) anyerror!Value {
        const field_ids = self.ast.exprs.sfv_pool.slice(row.fields);
        const count = field_ids.len;
        if (count == 0) return Value{ .Struct = .{ .fields = .empty, .owner = self.structTypeName(row.ty) } };
        var list = try std.ArrayList(StructField).initCapacity(self.allocator, count);
        var success = false;
        defer if (!success) {
            for (list.items) |*field| field.value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < count) : (idx += 1) {
            const field = self.ast.exprs.StructFieldValue.get(field_ids[idx]);
            if (field.name.isNone()) return Error.InvalidStatement;
            const value = try self.evalExpr(field.value);
            list.appendAssumeCapacity(StructField{
                .name = field.name.unwrap(),
                .value = value,
            });
        }
        const owner = self.structTypeName(row.ty);
        success = true;
        return Value{ .Struct = .{ .fields = list, .owner = owner } };
    }

    fn structTypeName(self: *Interpreter, ty: ast.OptExprId) ?ast.StrId {
        if (ty.isNone()) return null;
        return self.exprName(ty.unwrap());
    }

    fn exprName(self: *Interpreter, expr: ast.ExprId) ?ast.StrId {
        const kind = self.ast.exprs.index.kinds.items[expr.toRaw()];
        return switch (kind) {
            .Ident => self.ast.exprs.get(.Ident, expr).name,
            .FieldAccess => self.ast.exprs.get(.FieldAccess, expr).field,
            else => null,
        };
    }

    fn evalRange(self: *Interpreter, row: ast.Rows.Range) anyerror!Value {
        if (row.start.isNone() or row.end.isNone()) return Error.InvalidStatement;
        var start = try self.evalExpr(row.start.unwrap());
        defer start.destroy(self.allocator);
        var end = try self.evalExpr(row.end.unwrap());
        defer end.destroy(self.allocator);
        const start_int = try expectInt(start);
        const end_int = try expectInt(end);
        return Value{ .Range = RangeValue{ .start = start_int, .end = end_int, .inclusive = row.inclusive_right } };
    }

    fn evalFieldAccess(self: *Interpreter, row: ast.Rows.FieldAccess) anyerror!Value {
        var parent = try self.evalExpr(row.parent);
        return self.evalFieldAccessWithParent(row, &parent, true);
    }

    fn evalFieldAccessWithParent(
        self: *Interpreter,
        row: ast.Rows.FieldAccess,
        parent: *Value,
        destroy_parent: bool,
    ) anyerror!Value {
        const should_destroy = destroy_parent;
        defer if (should_destroy) parent.destroy(self.allocator);
        if (row.is_tuple) {
            const idx = try self.parseTupleIndex(row.field);
            return switch (parent.*) {
                .Sequence => |seq| {
                    if (idx >= seq.values.items.len) return Error.InvalidFieldAccess;
                    return try self.cloneValue(seq.values.items[idx]);
                },
                else => Error.InvalidFieldAccess,
            };
        }
        return switch (parent.*) {
            .Struct => |sv| {
                const struct_field = findStructField(sv, row.field);
                if (struct_field) |field| {
                    return try self.cloneValue(field.*.value);
                }
                return Error.InvalidFieldAccess;
            },
            else => Error.InvalidFieldAccess,
        };
    }

    fn evalIndexAccess(self: *Interpreter, row: ast.Rows.IndexAccess) anyerror!Value {
        var collection = try self.evalExpr(row.collection);
        defer collection.destroy(self.allocator);
        var index_val = try self.evalExpr(row.index);
        defer index_val.destroy(self.allocator);
        const idx = try expectIndex(index_val);
        return switch (collection) {
            .Sequence => |seq| {
                if (idx >= seq.values.items.len) return Error.InvalidIndexAccess;
                return try self.cloneValue(seq.values.items[idx]);
            },
            .String => |s| {
                if (idx >= s.len) return Error.InvalidIndexAccess;
                return Value{ .Int = @intCast(s[idx]) };
            },
            else => Error.InvalidIndexAccess,
        };
    }

    fn parseTupleIndex(self: *Interpreter, id: ast.StrId) anyerror!usize {
        const slice = self.ast.exprs.strs.get(id);
        return std.fmt.parseInt(usize, slice, 10) catch Error.InvalidFieldAccess;
    }

    fn expectIndex(value: Value) anyerror!usize {
        return switch (value) {
            .Int => |int_val| {
                if (int_val < 0) return Error.InvalidIndexAccess;
                const max: i128 = std.math.maxInt(usize);
                if (int_val > max) return Error.InvalidIndexAccess;
                return @intCast(int_val);
            },
            else => return Error.InvalidIndexAccess,
        };
    }

    fn evalMatch(self: *Interpreter, row: ast.Rows.Match) anyerror!Value {
        var scrut = try self.evalExpr(row.expr);
        defer scrut.destroy(self.allocator);
        const arms = self.ast.exprs.arm_pool.slice(row.arms);
        for (arms) |arm_id| {
            const arm = self.ast.exprs.MatchArm.get(arm_id);
            var matches = std.ArrayList(Binding){};
            defer matches.deinit(self.allocator);
            if (!try self.matchPattern(scrut, arm.pattern, &matches)) continue;
            var scope = try self.pushBindings(&matches);
            defer scope.deinit();
            if (!arm.guard.isNone()) {
                var guard_val = try self.evalExpr(arm.guard.unwrap());
                defer guard_val.destroy(self.allocator);
                if (!try valueToBool(guard_val)) continue;
            }
            return try self.evalExpr(arm.body);
        }
        return Value{ .Void = {} };
    }

    fn structOwner(value: Value) ?ast.StrId {
        return switch (value) {
            .Struct => value.Struct.owner,
            else => null,
        };
    }

    fn evalFor(self: *Interpreter, row: ast.Rows.For) anyerror!Value {
        var iterable = try self.evalExpr(row.iterable);
        defer iterable.destroy(self.allocator);
        const body = row.body;
        const pattern = row.pattern;
        switch (iterable) {
            .Range => |range| {
                var current = range.start;
                while (true) {
                    const done = if (range.inclusive) current > range.end else current >= range.end;
                    if (done) break;
                    _ = try self.runLoopIteration(pattern, body, Value{ .Int = current });
                    current += 1;
                }
            },
            .Sequence => |seq| {
                var idx: usize = 0;
                while (idx < seq.values.items.len) : (idx += 1) {
                    _ = try self.runLoopIteration(pattern, body, seq.values.items[idx]);
                }
            },
            else => return Error.InvalidType,
        }
        return Value{ .Void = {} };
    }

    fn runLoopIteration(self: *Interpreter, pattern: ast.PatternId, body: ast.ExprId, value: Value) anyerror!bool {
        var matches = std.ArrayList(Binding){};
        defer matches.deinit(self.allocator);
        if (!try self.matchPattern(value, pattern, &matches)) return false;
        var scope = try self.pushBindings(&matches);
        defer scope.deinit();
        var body_val = try self.evalExpr(body);
        body_val.destroy(self.allocator);
        return true;
    }

    fn evalWhile(self: *Interpreter, row: ast.Rows.While) anyerror!Value {
        const body = row.body;
        while (true) {
            var cond_value: Value = if (row.cond.isNone()) Value{ .Bool = true } else try self.evalExpr(row.cond.unwrap());
            if (row.is_pattern and !row.pattern.isNone()) {
                var matches = std.ArrayList(Binding){};
                defer matches.deinit(self.allocator);
                if (!try self.matchPattern(cond_value, row.pattern.unwrap(), &matches)) {
                    cond_value.destroy(self.allocator);
                    break;
                }
                cond_value.destroy(self.allocator);
                var scope = try self.pushBindings(&matches);
                defer scope.deinit();
                var body_val = try self.evalExpr(body);
                body_val.destroy(self.allocator);
                continue;
            }
            const cond_bool = try valueToBool(cond_value);
            cond_value.destroy(self.allocator);
            if (!cond_bool) break;
            var body_val = try self.evalExpr(body);
            body_val.destroy(self.allocator);
        }
        return Value{ .Void = {} };
    }

    fn evalLiteral(self: *Interpreter, literal: ast.Rows.Literal) anyerror!Value {
        return switch (literal.kind) {
            .int => Value{ .Int = @intCast(literal.data.int.value) },
            .float => Value{ .Float = literal.data.float.value },
            .bool => Value{ .Bool = literal.data.bool },
            .char => Value{ .Int = @intCast(literal.data.char) },
            .string => blk: {
                const slice = self.ast.exprs.strs.get(literal.data.string);
                const dup = try self.allocator.dupe(u8, slice);
                break :blk Value{ .String = dup };
            },
            .imaginary => Value{ .Float = literal.data.imaginary.value },
        };
    }

    fn evalIdent(self: *Interpreter, ident: ast.Rows.Ident) anyerror!Value {
        const found = try self.lookup(ident.name);
        if (found) |value| return value;
        return Error.BindingNotFound;
    }

    fn evalBinary(self: *Interpreter, row: ast.Rows.Binary) anyerror!Value {
        var left = try self.evalExpr(row.left);
        defer left.destroy(self.allocator);
        var right = try self.evalExpr(row.right);
        defer right.destroy(self.allocator);

        switch (row.op) {
            .add => return Value{ .Int = try expectInt(left) + try expectInt(right) },
            .sub => return Value{ .Int = try expectInt(left) - try expectInt(right) },
            .mul => return Value{ .Int = try expectInt(left) * try expectInt(right) },
            .div => {
                const divisor = try expectInt(right);
                if (divisor == 0) return Error.DivisionByZero;
                return Value{ .Int = @divTrunc(try expectInt(left), divisor) };
            },
            .mod => {
                const divisor = try expectInt(right);
                if (divisor == 0) return Error.DivisionByZero;
                return Value{ .Int = @rem(try expectInt(left), divisor) };
            },
            .logical_and => {
                const l = try valueToBool(left);
                if (!l) return Value{ .Bool = false };
                const r = try valueToBool(right);
                return Value{ .Bool = r };
            },
            .logical_or => {
                const l = try valueToBool(left);
                if (l) return Value{ .Bool = true };
                const r = try valueToBool(right);
                return Value{ .Bool = r };
            },
            .shl => {
                const l = try expectInt(left);
                const r: u7 = @intCast(try expectInt(right));
                return Value{ .Int = l << r };
            },
            .shr => {
                const l = try expectInt(left);
                const r: u7 = @intCast(try expectInt(right));
                return Value{ .Int = l >> r };
            },
            .bit_and => return Value{ .Int = try expectInt(left) & try expectInt(right) },
            .bit_or => return Value{ .Int = try expectInt(left) | try expectInt(right) },
            .bit_xor => return Value{ .Int = try expectInt(left) ^ try expectInt(right) },
            .lt => return Value{ .Bool = try compareLt(left, right) },
            .lte => return Value{ .Bool = try compareLte(left, right) },
            .gt => return Value{ .Bool = try compareGt(left, right) },
            .gte => return Value{ .Bool = try compareGte(left, right) },
            .eq => return Value{ .Bool = valuesEqual(left, right) },
            .neq => return Value{ .Bool = !valuesEqual(left, right) },
            else => return Error.InvalidBinaryOperand,
        }
    }

    fn evalUnary(self: *Interpreter, row: ast.Rows.Unary) anyerror!Value {
        var value = try self.evalExpr(row.expr);
        defer value.destroy(self.allocator);
        return switch (row.op) {
            .pos => Value{ .Int = try expectInt(value) },
            .neg => Value{ .Int = -try expectInt(value) },
            .logical_not => Value{ .Bool = !try valueToBool(value) },
            else => return Error.InvalidBinaryOperand,
        };
    }

    fn evalIf(self: *Interpreter, row: ast.Rows.If) anyerror!Value {
        var cond_val = try self.evalExpr(row.cond);
        defer cond_val.destroy(self.allocator);
        if (try valueToBool(cond_val)) {
            return try self.evalExpr(row.then_block);
        }
        if (row.else_block.isNone()) return Value{ .Void = {} };
        return try self.evalExpr(row.else_block.unwrap());
    }

    fn evalReturn(self: *Interpreter, row: ast.Rows.Return) anyerror!Value {
        if (row.value.isNone()) return Value{ .Void = {} };
        return try self.evalExpr(row.value.unwrap());
    }

    fn compareLt(left: Value, right: Value) anyerror!bool {
        const l = try numericValue(left);
        const r = try numericValue(right);
        return switch (l) {
            .Int => switch (r) {
                .Int => l.Int < r.Int,
                .Float => @as(f64, @floatFromInt(l.Int)) < r.Float,
            },
            .Float => switch (r) {
                .Int => l.Float < @as(f64, @floatFromInt(r.Int)),
                .Float => l.Float < r.Float,
            },
        };
    }

    fn compareLte(left: Value, right: Value) anyerror!bool {
        const l = try numericValue(left);
        const r = try numericValue(right);
        return switch (l) {
            .Int => switch (r) {
                .Int => l.Int <= r.Int,
                .Float => @as(f64, @floatFromInt(l.Int)) <= r.Float,
            },
            .Float => switch (r) {
                .Int => l.Float <= @as(f64, @floatFromInt(r.Int)),
                .Float => l.Float <= r.Float,
            },
        };
    }

    fn compareGt(left: Value, right: Value) anyerror!bool {
        const l = try numericValue(left);
        const r = try numericValue(right);
        return switch (l) {
            .Int => switch (r) {
                .Int => l.Int > r.Int,
                .Float => @as(f64, @floatFromInt(l.Int)) > r.Float,
            },
            .Float => switch (r) {
                .Int => l.Float > @as(f64, @floatFromInt(r.Int)),
                .Float => l.Float > r.Float,
            },
        };
    }

    fn compareGte(left: Value, right: Value) anyerror!bool {
        const l = try numericValue(left);
        const r = try numericValue(right);
        return switch (l) {
            .Int => switch (r) {
                .Int => l.Int >= r.Int,
                .Float => @as(f64, @floatFromInt(l.Int)) >= r.Float,
            },
            .Float => switch (r) {
                .Int => l.Float >= @as(f64, @floatFromInt(r.Int)),
                .Float => l.Float >= r.Float,
            },
        };
    }

    fn numericValue(value: Value) anyerror!NumericValue {
        return switch (value) {
            .Int => NumericValue{ .Int = value.Int },
            .Float => NumericValue{ .Float = value.Float },
            .Bool => NumericValue{ .Int = toInt(value.Bool) },
            else => return Error.InvalidBinaryOperand,
        };
    }

    pub fn setBinding(self: *Interpreter, name: ast.StrId, value: Value) !void {
        if (self.findBinding(name)) |binding| {
            binding.value.destroy(self.allocator);
            binding.value = value;
            return;
        }
        try self.bindings.append(self.allocator, .{ .name = name, .value = value });
    }

    fn registerMethods(self: *Interpreter) anyerror!void {
        const decl_ids = self.ast.exprs.decl_pool.slice(self.ast.unit.decls);
        for (decl_ids) |decl_id| {
            const decl = self.ast.exprs.Decl.get(decl_id);
            if (decl.method_path.isNone()) continue;
            const segs = self.ast.exprs.method_path_pool.slice(decl.method_path.asRange());
            if (segs.len < 2) continue;
            const owner_seg = self.ast.exprs.MethodPathSeg.get(segs[0]);
            const method_seg = self.ast.exprs.MethodPathSeg.get(segs[segs.len - 1]);
            const key = MethodKey{ .owner = owner_seg.name, .method = method_seg.name };
            if (self.method_table.get(key)) |_| continue;
            try self.method_table.put(key, decl.value);
        }
    }

    fn lookupMethod(self: *Interpreter, owner: ast.StrId, method: ast.StrId) ?ast.ExprId {
        const key = MethodKey{ .owner = owner, .method = method };
        if (self.method_table.get(key)) |entry| return entry;
        return null;
    }

    fn findBinding(self: *Interpreter, name: ast.StrId) ?*Binding {
        for (self.bindings.items) |*binding| if (binding.name.eq(name)) return binding;
        return null;
    }

    pub fn cloneValue(self: *Interpreter, value: Value) !Value {
        return switch (value) {
            .String => |s| blk: {
                const dup = try self.allocator.dupe(u8, s);
                break :blk Value{ .String = dup };
            },
            .Sequence => |seq| try self.cloneSequence(seq),
            .Struct => |sv| try self.cloneStruct(sv),
            .Function => |func| Value{ .Function = func },
            else => value,
        };
    }

    fn expectInt(value: Value) anyerror!i128 {
        return switch (value) {
            .Int => value.Int,
            .Bool => if (value.Bool) 1 else 0,
            else => return Error.InvalidBinaryOperand,
        };
    }

    fn valueToBool(value: Value) anyerror!bool {
        return switch (value) {
            .Bool => value.Bool,
            .Int => value.Int != 0,
            .Float => value.Float != 0.0,
            else => return Error.InvalidType,
        };
    }

    fn toInt(value: bool) i128 {
        return @intFromBool(value);
    }

    fn valuesEqual(left: Value, right: Value) bool {
        return switch (left) {
            .Int => |l| switch (right) {
                .Int => l == right.Int,
                .Float => @as(f64, @floatFromInt(l)) == right.Float,
                .Bool => l == toInt(right.Bool),
                else => false,
            },
            .Bool => |b| switch (right) {
                .Bool => b == right.Bool,
                .Int => toInt(b) == right.Int,
                .Float => @as(f64, @floatFromInt(toInt(b))) == right.Float,
                else => false,
            },
            .Float => |f| switch (right) {
                .Float => f == right.Float,
                .Int => f == @as(f64, @floatFromInt(right.Int)),
                .Bool => f == @as(f64, @floatFromInt(toInt(right.Bool))),
                else => false,
            },
            .String => |s| switch (right) {
                .String => std.mem.eql(u8, s, right.String),
                else => false,
            },
            .Sequence => |seq| switch (right) {
                .Sequence => sequencesEqual(seq, right.Sequence),
                else => false,
            },
            .Struct => |sv| switch (right) {
                .Struct => structValuesEqual(sv, right.Struct),
                else => false,
            },
            .Range => |rv| switch (right) {
                .Range => rv.start == right.Range.start and rv.end == right.Range.end and rv.inclusive == right.Range.inclusive,
                else => false,
            },
            .Function => |func| switch (right) {
                .Function => func.expr.toRaw() == right.Function.expr.toRaw(),
                else => false,
            },
            else => false,
        };
    }

    fn sequencesEqual(a: Sequence, b: Sequence) bool {
        if (a.values.items.len != b.values.items.len) return false;
        if (a.values.items.len == 0) return true;
        var idx: usize = 0;
        while (idx < a.values.items.len) : (idx += 1) {
            if (!valuesEqual(a.values.items[idx], b.values.items[idx])) return false;
        }
        return true;
    }

    fn structValuesEqual(a: StructValue, b: StructValue) bool {
        if (a.fields.items.len != b.fields.items.len) return false;
        if (!ownersEqual(a.owner, b.owner)) return false;
        if (a.fields.items.len == 0) return true;
        var idx: usize = 0;
        while (idx < a.fields.items.len) : (idx += 1) {
            const left_field = a.fields.items[idx];
            const right_field = b.fields.items[idx];
            if (!left_field.name.eq(right_field.name)) return false;
            if (!valuesEqual(left_field.value, right_field.value)) return false;
        }
        return true;
    }

    fn ownersEqual(a: ?ast.StrId, b: ?ast.StrId) bool {
        if (a == null and b == null) return true;
        if (a == null or b == null) return false;
        return a.?.eq(b.?);
    }

    fn cloneSequence(self: *Interpreter, seq: Sequence) anyerror!Value {
        if (seq.values.items.len == 0) return Value{ .Sequence = .{ .values = .empty } };
        var list = try std.ArrayList(Value).initCapacity(self.allocator, seq.values.items.len);
        var success = false;
        defer if (!success) {
            for (list.items) |*value| value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < seq.values.items.len) : (idx += 1) {
            list.appendAssumeCapacity(try self.cloneValue(seq.values.items[idx]));
        }
        success = true;
        return Value{ .Sequence = .{ .values = list } };
    }

    fn cloneStruct(self: *Interpreter, sv: StructValue) anyerror!Value {
        if (sv.fields.items.len == 0) return Value{ .Struct = .{ .fields = .empty, .owner = sv.owner } };
        var list = try std.ArrayList(StructField).initCapacity(self.allocator, sv.fields.items.len);
        var success = false;
        defer if (!success) {
            for (list.items) |*field| field.value.destroy(self.allocator);
            list.deinit(self.allocator);
        };
        var idx: usize = 0;
        while (idx < sv.fields.items.len) : (idx += 1) {
            list.appendAssumeCapacity(StructField{
                .name = sv.fields.items[idx].name,
                .value = try self.cloneValue(sv.fields.items[idx].value),
            });
        }
        success = true;
        return Value{ .Struct = .{ .fields = list, .owner = sv.owner } };
    }

    fn findStructField(sv: StructValue, name: ast.StrId) ?*StructField {
        var idx: usize = 0;
        while (idx < sv.fields.items.len) : (idx += 1) {
            if (sv.fields.items[idx].name.eq(name)) return &sv.fields.items[idx];
        }
        return null;
    }

    fn matchPattern(self: *Interpreter, value: Value, pid: ast.PatternId, matches: *std.ArrayList(Binding)) anyerror!bool {
        const kind = self.ast.pats.index.kinds.items[pid.toRaw()];
        switch (kind) {
            .Wildcard => return true,
            .Literal => {
                const row = self.ast.pats.get(.Literal, pid);
                var literal = try self.evalExpr(row.expr);
                defer literal.destroy(self.allocator);
                return valuesEqual(value, literal);
            },
            .Binding => {
                const row = self.ast.pats.get(.Binding, pid);
                var binding_value = try self.cloneValue(value);
                var success = false;
                defer if (!success) binding_value.destroy(self.allocator);
                try matches.append(self.allocator, .{ .name = row.name, .value = binding_value });
                success = true;
                return true;
            },
            .Tuple => return try self.matchTuplePattern(value, self.ast.pats.get(.Tuple, pid), matches),
            .Slice => return try self.matchSlicePattern(value, self.ast.pats.get(.Slice, pid), matches),
            .Struct => return try self.matchStructPattern(value, self.ast.pats.get(.Struct, pid), matches),
            .At => return try self.matchAtPattern(value, self.ast.pats.get(.At, pid), matches),
            else => return false,
        }
    }

    fn matchTuplePattern(self: *Interpreter, value: Value, row: ast.PatRows.Tuple, matches: *std.ArrayList(Binding)) anyerror!bool {
        return switch (value) {
            .Sequence => |seq| {
                const patterns = self.ast.pats.pat_pool.slice(row.elems);
                if (seq.values.items.len != patterns.len) return false;
                if (seq.values.items.len == 0) return true;
                const elems = seq.values.items[0..seq.values.items.len];
                var idx: usize = 0;
                while (idx < patterns.len) : (idx += 1) {
                    const before = matches.items.len;
                    if (!try self.matchPattern(elems[idx], patterns[idx], matches)) {
                        self.rollbackBindings(matches, before);
                        return false;
                    }
                }
                return true;
            },
            else => false,
        };
    }

    fn matchSlicePattern(self: *Interpreter, value: Value, row: ast.PatRows.Slice, matches: *std.ArrayList(Binding)) anyerror!bool {
        return switch (value) {
            .Sequence => |seq| {
                const patterns = self.ast.pats.pat_pool.slice(row.elems);
                const fixed: usize = if (row.has_rest) @intCast(row.rest_index) else patterns.len;
                if (seq.values.items.len < fixed) return false;
                if (fixed > 0) {
                    const elems = seq.values.items[0..seq.values.items.len];
                    var idx: usize = 0;
                    while (idx < fixed) : (idx += 1) {
                        const before = matches.items.len;
                        if (!try self.matchPattern(elems[idx], patterns[idx], matches)) {
                            self.rollbackBindings(matches, before);
                            return false;
                        }
                    }
                }
                if (!row.has_rest) return seq.values.items.len == patterns.len;
                const rest_index: usize = @intCast(row.rest_index);
                if (rest_index > seq.values.items.len) return false;
                if (row.rest_binding.isNone()) return true;
                const rest_pattern = row.rest_binding.unwrap();
                var rest_value = try self.cloneSequence(seq);
                const before_rest = matches.items.len;
                const matched_rest = try self.matchPattern(rest_value, rest_pattern, matches);
                rest_value.destroy(self.allocator);
                if (!matched_rest) {
                    self.rollbackBindings(matches, before_rest);
                    return false;
                }
                return true;
            },
            else => false,
        };
    }

    fn matchStructPattern(self: *Interpreter, value: Value, row: ast.PatRows.Struct, matches: *std.ArrayList(Binding)) anyerror!bool {
        return switch (value) {
            .Struct => |sv| {
                const fields = self.ast.pats.field_pool.slice(row.fields);
                if (!row.has_rest and sv.fields.items.len != fields.len) return false;
                for (fields) |field_id| {
                    const field = self.ast.pats.StructField.get(field_id);
                    const struct_field = findStructField(sv, field.name);
                    if (struct_field == null) return false;
                    const before = matches.items.len;
                    if (!try self.matchPattern(struct_field.?.value, field.pattern, matches)) {
                        self.rollbackBindings(matches, before);
                        return false;
                    }
                }
                return true;
            },
            else => false,
        };
    }

    fn matchAtPattern(self: *Interpreter, value: Value, row: ast.PatRows.At, matches: *std.ArrayList(Binding)) anyerror!bool {
        const before = matches.items.len;
        if (!try self.matchPattern(value, row.pattern, matches)) {
            self.rollbackBindings(matches, before);
            return false;
        }
        var clone = try self.cloneValue(value);
        var success = false;
        defer if (!success) clone.destroy(self.allocator);
        try matches.append(self.allocator, .{ .name = row.binder, .value = clone });
        success = true;
        return true;
    }

    fn rollbackBindings(self: *Interpreter, matches: *std.ArrayList(Binding), target_len: usize) void {
        var current = matches.items.len;
        while (current > target_len) : (current -= 1) {
            matches.items[current - 1].value.destroy(self.allocator);
        }
        matches.shrinkRetainingCapacity(target_len);
    }

    fn bindingHash(bindings: []const Binding) u64 {
        var hasher = std.hash.Wyhash.init(0);
        for (bindings) |binding| {
            const name_raw: u32 = binding.name.toRaw();
            hasher.update(std.mem.asBytes(&name_raw));
            const val_hash: u64 = comptime_mod.hashComptimeValue(binding.value);
            hasher.update(std.mem.asBytes(&val_hash));
        }
        return hasher.final();
    }

    pub fn captureBindingSnapshot(self: *Interpreter, matches: *std.ArrayList(Binding)) anyerror!BindingSnapshot {
        var snapshot = try std.ArrayList(Binding).initCapacity(self.allocator, matches.items.len);
        var hasher = std.hash.Wyhash.init(0);
        var success = false;
        defer if (!success) {
            for (snapshot.items) |*binding| binding.value.destroy(self.allocator);
            snapshot.deinit(self.allocator);
        };
        for (matches.items) |binding| {
            const cloned = try self.cloneValue(binding.value);
            try snapshot.append(self.allocator, .{ .name = binding.name, .value = cloned });
            const name_raw: u32 = binding.name.toRaw();
            hasher.update(std.mem.asBytes(&name_raw));
            const val_hash: u64 = comptime_mod.hashComptimeValue(binding.value);
            hasher.update(std.mem.asBytes(&val_hash));
        }
        success = true;
        return BindingSnapshot{ .bindings = snapshot, .hash = hasher.final() };
    }

    fn cloneSnapshot(self: *Interpreter, source: *BindingSnapshot) anyerror!BindingSnapshot {
        var cloned = try std.ArrayList(Binding).initCapacity(self.allocator, source.bindings.items.len);
        var success = false;
        defer if (!success) {
            for (cloned.items) |*binding| binding.value.destroy(self.allocator);
            cloned.deinit(self.allocator);
        };
        for (source.bindings.items) |binding| {
            const dup = try self.cloneValue(binding.value);
            try cloned.append(self.allocator, .{ .name = binding.name, .value = dup });
        }
        success = true;
        return BindingSnapshot{ .bindings = cloned, .hash = source.hash };
    }

    fn hashFunctionKey(key: FunctionKey) u128 {
        const decl_raw: u32 = key.decl_id.toRaw();
        return (@as(u128, key.bindings_hash) << 32) | @as(u128, decl_raw);
    }

    pub fn specializeFunction(self: *Interpreter, decl_id: ast.DeclId, matches: *std.ArrayList(Binding)) anyerror!SpecializationResult {
        const binding_hash = bindingHash(matches.items);
        const key = FunctionKey{ .decl_id = decl_id, .bindings_hash = binding_hash };
        const map_hash = hashFunctionKey(key);
        if (self.specializations.getPtr(map_hash)) |existing| {
            if (keysEqual(existing.key, key)) {
                return SpecializationResult{
                    .func = FunctionValue{ .expr = existing.func_expr },
                    .snapshot = try self.cloneSnapshot(&existing.bindings),
                };
            }
        }
        var snapshot = try self.captureBindingSnapshot(matches);
        const return_snapshot = try self.cloneSnapshot(&snapshot);
        var entry = FunctionSpecializationEntry{
            .key = key,
            .func_expr = self.ast.exprs.Decl.get(decl_id).value,
            .bindings = snapshot,
        };
        var success = false;
        defer if (!success) entry.destroy(self.allocator);
        try self.specializations.put(map_hash, entry);
        success = true;
        return SpecializationResult{
            .func = FunctionValue{ .expr = entry.func_expr },
            .snapshot = return_snapshot,
        };
    }

    const BindingScope = struct {
        interpreter: *Interpreter,
        prev_len: usize,
        replaced: std.ArrayList(Binding),
        active: bool,

        fn restore(self: *BindingScope) void {
            if (!self.active) return;
            var len = self.interpreter.bindings.items.len;
            while (len > self.prev_len) : (len -= 1) {
                self.interpreter.bindings.items[len - 1].value.destroy(self.interpreter.allocator);
            }
            self.interpreter.bindings.shrinkRetainingCapacity(self.prev_len);
            for (self.replaced.items) |binding| {
                if (self.interpreter.findBinding(binding.name)) |existing| {
                    existing.value.destroy(self.interpreter.allocator);
                    existing.value = binding.value;
                }
            }
            self.replaced.clearRetainingCapacity();
            self.active = false;
        }

        fn deinit(self: *BindingScope) void {
            self.restore();
            self.replaced.deinit(self.interpreter.allocator);
        }
    };

    fn pushBindings(self: *Interpreter, matches: *std.ArrayList(Binding)) anyerror!BindingScope {
        var scope = BindingScope{
            .interpreter = self,
            .prev_len = self.bindings.items.len,
            .replaced = .empty,
            .active = true,
        };
        var success = false;
        defer if (!success) {
            scope.restore();
            scope.replaced.deinit(self.allocator);
        };
        for (matches.items) |*binding| {
            const value = binding.value;
            binding.value = .Void;
            if (self.findBinding(binding.name)) |existing| {
                const old_value = try self.cloneValue(existing.value);
                try scope.replaced.append(self.allocator, .{ .name = binding.name, .value = old_value });
                existing.value.destroy(self.allocator);
                existing.value = value;
            } else {
                try self.bindings.append(self.allocator, .{ .name = binding.name, .value = value });
            }
        }
        success = true;
        return scope;
    }
};
