const std = @import("std");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const compile = @import("compile.zig");
const diagnostics = @import("diagnostics.zig");

/// Converts CST nodes into AST nodes per source file.
pub const Lower = @This();

gpa: std.mem.Allocator,
arena: std.heap.ArenaAllocator,
cst_program: *cst.CST,
ast_unit: *ast.Ast,
context: *compile.Context,
file_id: u32,
dependencies: std.ArrayList(ast.StrId),

pub const LowerResult = struct {
    ast_unit: *ast.Ast,
    dependencies: std.ArrayList(ast.StrId),

    pub fn deinit(self: *LowerResult, gpa: std.mem.Allocator) void {
        self.dependencies.deinit(gpa);
    }
};

/// Create a lower-pass bound to `program`/`file_id` that emits AST nodes into `context`.
pub fn init(
    gpa: std.mem.Allocator,
    program: *cst.CST,
    context: *compile.Context,
    file_id: u32,
) !Lower {
    const ast_unit = try gpa.create(ast.Ast);
    ast_unit.* = ast.Ast.init(gpa, program.interner, program.exprs.locs, context.type_store, file_id);
    return .{
        .gpa = gpa,
        .arena = std.heap.ArenaAllocator.init(gpa),
        .cst_program = program,
        .ast_unit = ast_unit,
        .context = context,
        .file_id = file_id,
        .dependencies = .empty,
    };
}

/// Release resources associated with `self`, including the owned AST unit.
pub fn deinit(self: *Lower) void {
    self.dependencies.deinit(self.gpa);
    self.ast_unit.deinit();
    self.gpa.destroy(self.ast_unit);
    self.arena.deinit();
}

/// Run lowering and ignore the returned AST value.
pub fn runLower(self: *Lower) !void {
    const result = try self.run();
    self.dependencies = result.dependencies;
}

/// Lower the entire CST into an AST unit and return it.
pub fn run(self: *Lower) !LowerResult {
    self.dependencies.clearRetainingCapacity();
    var unit: ast.Unit = .empty();

    unit.package_name = self.cst_program.program.package_name;
    unit.package_loc = self.cst_program.program.package_loc;

    // top-level decls -> ast.decl_pool range
    unit.decls = try self.lowerTopDecls(self.cst_program.program.top_decls);

    self.ast_unit.unit = unit;
    // Transfer ownership of dependencies to result
    const deps = self.dependencies;
    self.dependencies = .empty;
    return .{ .ast_unit = self.ast_unit, .dependencies = deps };
}

/// Track that the currently lowered file references `dependency`.
fn recordDependency(self: *Lower, dependency: ast.StrId) !void {
    try self.dependencies.append(self.gpa, dependency);
}

/// Helper to map CST ids to AST ids and push them into an AST pool.
/// Uses arena allocator to avoid malloc/free overhead on every list.
fn mapRange(
    self: *Lower,
    comptime CstId: type,
    comptime AstId: type,
    items: []const CstId,
    ast_pool: anytype,
    lowerFn: anytype,
) !ast.RangeOf(AstId) {
    if (items.len == 0) return ast_pool.pushMany(self.gpa, &[_]AstId{});

    // Arena alloc: fast bump pointer, no free needed
    const out_ids = try self.arena.allocator().alloc(AstId, items.len);

    for (items, 0..) |id, i| {
        out_ids[i] = try lowerFn(self, id);
    }
    return ast_pool.pushMany(self.ast_unit.gpa, out_ids);
}

/// Translate a CST attribute range (optional) into an AST attribute metadata range.
fn mapAttrRange(self: *Lower, r: cst.OptRangeAttr) !ast.OptRangeAttr {
    if (r.isNone()) return .none();
    const rr = r.asRange();
    const items = self.cst_program.exprs.attr_pool.slice(rr);
    const range = try self.mapRange(cst.AttributeId, ast.AttributeId, items, &self.ast_unit.exprs.attr_pool, Lower.lowerAttribute);
    return .some(range);
}

fn lowerAttribute(self: *Lower, id: cst.AttributeId) !ast.AttributeId {
    const row = self.cst_program.exprs.Attribute.get(id);
    const mapped: ast.Rows.Attribute = .{
        .name = row.name,
        .value = if (!row.value.isNone()) .some(try self.lowerExpr(row.value.unwrap())) else .none(),
        .loc = row.loc,
    };
    return self.ast_unit.exprs.Attribute.add(self.ast_unit.gpa, mapped);
}

/// Lower a range of CST parameters to their AST equivalents.
fn lowerParamRange(self: *Lower, r: cst.RangeOf(cst.ParamId)) !ast.RangeParam {
    const items = self.cst_program.exprs.param_pool.slice(r);
    return self.mapRange(cst.ParamId, ast.ParamId, items, &self.ast_unit.exprs.param_pool, Lower.lowerParam);
}

fn lowerParam(self: *Lower, id: cst.ParamId) !ast.ParamId {
    const row = self.cst_program.exprs.Param.get(id);
    const mapped: ast.Rows.Param = .{
        .pat = try self.lowerOptionalPatternFromExpr(row.pat),
        .ty = if (!row.ty.isNone()) .some(try self.lowerExpr(row.ty.unwrap())) else .none(),
        .value = if (!row.value.isNone()) .some(try self.lowerExpr(row.value.unwrap())) else .none(),
        .attrs = try self.mapAttrRange(row.attrs),
        .is_comptime = row.is_comptime,
        .loc = row.loc,
    };
    return self.ast_unit.exprs.Param.add(self.ast_unit.gpa, mapped);
}

/// Lower a range of CST key-value pairs (e.g., map entries, attributes).
fn lowerKeyValues(self: *Lower, r: cst.RangeOf(cst.KeyValueId)) !ast.RangeKeyValue {
    const items = self.cst_program.exprs.kv_pool.slice(r);
    return self.mapRange(cst.KeyValueId, ast.KeyValueId, items, &self.ast_unit.exprs.kv_pool, Lower.lowerKeyValue);
}

fn lowerKeyValue(self: *Lower, id: cst.KeyValueId) !ast.KeyValueId {
    const kv = self.cst_program.exprs.KeyValue.get(id);
    const mapped: ast.Rows.KeyValue = .{
        .key = try self.lowerExpr(kv.key),
        .value = try self.lowerExpr(kv.value),
        .loc = kv.loc,
    };
    return self.ast_unit.exprs.KeyValue.add(self.ast_unit.gpa, mapped);
}

/// Lower struct literal field values from CST to AST storage.
fn lowerStructFieldValues(self: *Lower, r: cst.RangeOf(cst.StructFieldValueId)) !ast.RangeStructFieldValue {
    const items = self.cst_program.exprs.sfv_pool.slice(r);
    return self.mapRange(cst.StructFieldValueId, ast.StructFieldValueId, items, &self.ast_unit.exprs.sfv_pool, Lower.lowerStructFieldValue);
}

fn lowerStructFieldValue(self: *Lower, id: cst.StructFieldValueId) !ast.StructFieldValueId {
    const f = self.cst_program.exprs.StructFieldValue.get(id);
    const mapped: ast.Rows.StructFieldValue = .{
        .name = if (!f.name.isNone()) .some(f.name.unwrap()) else .none(),
        .value = try self.lowerExpr(f.value),
        .loc = f.loc,
    };
    return self.ast_unit.exprs.StructFieldValue.add(self.ast_unit.gpa, mapped);
}

/// Lower declared struct fields in CST into AST field entries.
fn lowerStructFields(self: *Lower, r: cst.RangeOf(cst.StructFieldId)) !ast.RangeField {
    const items = self.cst_program.exprs.sfield_pool.slice(r);
    return self.mapRange(cst.StructFieldId, ast.StructFieldId, items, &self.ast_unit.exprs.sfield_pool, Lower.lowerStructField);
}

fn lowerStructField(self: *Lower, id: cst.StructFieldId) !ast.StructFieldId {
    const f = self.cst_program.exprs.StructField.get(id);
    const mapped: ast.Rows.StructField = .{
        .name = f.name,
        .ty = try self.lowerExpr(f.ty),
        .value = if (!f.value.isNone()) .some(try self.lowerExpr(f.value.unwrap())) else .none(),
        .attrs = try self.mapAttrRange(f.attrs),
        .loc = f.loc,
    };
    return self.ast_unit.exprs.StructField.add(self.ast_unit.gpa, mapped);
}

/// Transform enum field declarations from CST into AST enum members.
fn lowerEnumFields(self: *Lower, r: cst.RangeOf(cst.EnumFieldId)) !ast.RangeEnumField {
    const items = self.cst_program.exprs.efield_pool.slice(r);
    return self.mapRange(cst.EnumFieldId, ast.EnumFieldId, items, &self.ast_unit.exprs.efield_pool, Lower.lowerEnumField);
}

fn lowerEnumField(self: *Lower, id: cst.EnumFieldId) !ast.EnumFieldId {
    const f = self.cst_program.exprs.EnumField.get(id);
    const mapped: ast.Rows.EnumField = .{
        .name = f.name,
        .value = if (!f.value.isNone()) .some(try self.lowerExpr(f.value.unwrap())) else .none(),
        .attrs = try self.mapAttrRange(f.attrs),
        .loc = f.loc,
    };
    return self.ast_unit.exprs.EnumField.add(self.ast_unit.gpa, mapped);
}

/// Lower variant field metadata for AST variant type definitions.
fn lowerVariantFields(self: *Lower, r: cst.RangeOf(cst.VariantFieldId)) !ast.RangeVariantField {
    const items = self.cst_program.exprs.vfield_pool.slice(r);
    return self.mapRange(cst.VariantFieldId, ast.VariantFieldId, items, &self.ast_unit.exprs.vfield_pool, Lower.lowerVariantField);
}

fn lowerVariantField(self: *Lower, id: cst.VariantFieldId) !ast.VariantFieldId {
    const f = self.cst_program.exprs.VariantField.get(id);
    const pk: ast.VariantPayloadKind = switch (f.ty_tag) {
        .none => .none,
        .Tuple => .tuple,
        .Struct => .@"struct",
    };
    const mapped: ast.Rows.VariantField = .{
        .name = f.name,
        .payload_kind = pk,
        .payload_elems = if (f.ty_tag == .Tuple) .some(try self.lowerExprRange(f.tuple_elems)) else .none(),
        .payload_fields = if (f.ty_tag == .Struct) .some(try self.lowerStructFields(f.struct_fields)) else .none(),
        .value = if (!f.value.isNone()) .some(try self.lowerExpr(f.value.unwrap())) else .none(),
        .attrs = try self.mapAttrRange(f.attrs),
        .loc = f.loc,
    };
    return self.ast_unit.exprs.VariantField.add(self.ast_unit.gpa, mapped);
}

/// Lower a continuous range of expressions from CST to AST.
fn lowerExprRange(self: *Lower, r: cst.RangeOf(cst.ExprId)) !ast.RangeExpr {
    const items = self.cst_program.exprs.expr_pool.slice(r);
    return self.mapRange(cst.ExprId, ast.ExprId, items, &self.ast_unit.exprs.expr_pool, Lower.lowerExpr);
}

// ---------------- Top-level decls ----------------
/// Lower the top-level declarations for this file.
fn lowerTopDecls(self: *Lower, r: cst.RangeOf(cst.DeclId)) !ast.RangeDecl {
    const items = self.cst_program.exprs.decl_pool.slice(r);
    return self.mapRange(cst.DeclId, ast.DeclId, items, &self.ast_unit.exprs.decl_pool, Lower.lowerTopDecl);
}

/// Lower a single top-level declaration from CST to AST.
fn lowerTopDecl(self: *Lower, id: cst.DeclId) !ast.DeclId {
    const d = self.cst_program.exprs.Decl.get(id);
    const pattern = try self.lowerOptionalPatternFromExpr(d.lhs);
    const value = try self.lowerExpr(d.rhs);
    const ty: ast.OptExprId = if (!d.ty.isNone()) .some(try self.lowerExpr(d.ty.unwrap())) else .none();

    var method_path: ast.OptRangeMethodPathSeg = .none();
    if (!d.method_path.isNone()) {
        const segs = self.cst_program.exprs.method_path_pool.slice(d.method_path.asRange());
        const ids = try self.arena.allocator().alloc(ast.MethodPathSegId, segs.len);

        for (segs, 0..) |s, i| {
            const seg = self.cst_program.exprs.MethodPathSeg.get(s);
            ids[i] = self.ast_unit.exprs.addMethodPathSeg(.{ .name = seg.name, .loc = seg.loc });
        }

        const range = self.ast_unit.exprs.method_path_pool.pushMany(self.ast_unit.gpa, ids);
        method_path = .some(range);
    }

    const decl_row: ast.Rows.Decl = .{
        .pattern = pattern,
        .value = value,
        .ty = ty,
        .method_path = method_path,
        .flags = .{ .is_const = d.flags.is_const },
        .loc = d.loc,
    };
    const raw = self.ast_unit.exprs.Decl.add(self.ast_unit.gpa, decl_row);
    _ = self.ast_unit.exprs.decl_pool.push(self.ast_unit.gpa, raw);
    return raw;
}

// ---------------- Statements & Blocks ----------------
/// Lower a block expression from CST, returning the AST expression id.
fn lowerBlockExpr(self: *Lower, id: cst.ExprId) !ast.ExprId {
    const b = self.cst_program.exprs.get(.Block, id);
    const stmts_range = try self.lowerStmtRangeFromDecls(b.items);
    const row: ast.Rows.Block = .{ .items = stmts_range, .loc = b.loc };
    return self.ast_unit.exprs.add(.Block, row);
}

/// Lower a range of declaration-based statements into AST statements.
fn lowerStmtRangeFromDecls(self: *Lower, r: cst.RangeOf(cst.DeclId)) !ast.RangeStmt {
    const decls = self.cst_program.exprs.decl_pool.slice(r);
    return self.mapRange(cst.DeclId, ast.StmtId, decls, &self.ast_unit.stmts.stmt_pool, Lower.lowerStmtFromDecl);
}

/// Convert a declaration into a statement when lowering block bodies.
fn lowerStmtFromDecl(self: *Lower, id: cst.DeclId) !ast.StmtId {
    const d = self.cst_program.exprs.Decl.get(id);

    // Declaration-like (const or define :=)
    if (d.flags.is_const or (!d.lhs.isNone() and !d.flags.is_assign)) {
        const did = try self.lowerTopDecl(id);
        return self.ast_unit.stmts.add(.Decl, .{ .decl = did });
    }

    // Simple assignment
    if (d.flags.is_assign) {
        const lhs_expr = d.lhs.unwrap();
        const left = if (try self.patternFromAssignExpr(lhs_expr)) |pid|
            ast.StmtRows.AssignLhs{ .pattern = pid }
        else
            ast.StmtRows.AssignLhs{ .expr = try self.lowerExpr(lhs_expr) };

        const right = try self.lowerExpr(d.rhs);
        return self.ast_unit.stmts.add(.Assign, .{ .left = left, .right = right, .loc = d.loc });
    }

    // Compound assigns desugaring: Infix at top-level
    if (self.cst_program.kind(d.rhs) == .Infix) {
        const irow = self.cst_program.exprs.get(.Infix, d.rhs);
        if (try self.tryLowerCompoundAssign(&irow)) |stmt| return stmt;
    }

    // Statement-like RHS
    const kind = self.cst_program.kind(d.rhs);
    return switch (kind) {
        .Return => blk: {
            const r = self.cst_program.exprs.get(.Return, d.rhs);
            break :blk self.ast_unit.stmts.add(.Return, .{
                .value = if (!r.value.isNone()) .some(try self.lowerExpr(r.value.unwrap())) else .none(),
                .loc = r.loc,
            });
        },
        .Insert => blk: {
            const r = self.cst_program.exprs.get(.Insert, d.rhs);
            break :blk self.ast_unit.stmts.add(.Insert, .{
                .expr = try self.lowerExpr(r.expr),
                .loc = r.loc,
            });
        },
        .Break => blk: {
            const r = self.cst_program.exprs.get(.Break, d.rhs);
            break :blk self.ast_unit.stmts.add(.Break, .{
                .label = r.label,
                .value = if (!r.value.isNone()) .some(try self.lowerExpr(r.value.unwrap())) else .none(),
                .loc = r.loc,
            });
        },
        .Continue => blk: {
            const r = self.cst_program.exprs.get(.Continue, d.rhs);
            break :blk self.ast_unit.stmts.add(.Continue, .{ .label = r.label, .loc = r.loc });
        },
        .Unreachable => blk: {
            const r = self.cst_program.exprs.get(.Unreachable, d.rhs);
            break :blk self.ast_unit.stmts.add(.Unreachable, .{ .loc = r.loc });
        },
        .Defer => blk: {
            const r = self.cst_program.exprs.get(.Defer, d.rhs);
            break :blk self.ast_unit.stmts.add(.Defer, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        .ErrDefer => blk: {
            const r = self.cst_program.exprs.get(.ErrDefer, d.rhs);
            break :blk self.ast_unit.stmts.add(.ErrDefer, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        else => blk: {
            const e = try self.lowerExpr(d.rhs);
            break :blk self.ast_unit.stmts.add(.Expr, .{ .expr = e });
        },
    };
}

/// Attempt to rebuild a compound assignment (`+=`, `-=`) as a primitive AST statement.
fn tryLowerCompoundAssign(self: *Lower, i: *const cst.Rows.Infix) !?ast.StmtId {
    const op = i.op;
    const base_loc = i.loc;

    // Helper to extract binary op and flags to avoid repetitive calls
    const bin_info: struct { op: ast.BinaryOp, wrap: bool, sat: bool } = switch (op) {
        .add_assign => .{ .op = ast.BinaryOp.add, .wrap = false, .sat = false },
        .sub_assign => .{ .op = ast.BinaryOp.sub, .wrap = false, .sat = false },
        .mul_assign => .{ .op = ast.BinaryOp.mul, .wrap = false, .sat = false },
        .div_assign => .{ .op = ast.BinaryOp.div, .wrap = false, .sat = false },
        .mod_assign => .{ .op = ast.BinaryOp.mod, .wrap = false, .sat = false },
        .shl_assign => .{ .op = ast.BinaryOp.shl, .wrap = false, .sat = false },
        .shr_assign => .{ .op = ast.BinaryOp.shr, .wrap = false, .sat = false },
        .and_assign => .{ .op = ast.BinaryOp.bit_and, .wrap = false, .sat = false },
        .or_assign => .{ .op = ast.BinaryOp.bit_or, .wrap = false, .sat = false },
        .xor_assign => .{ .op = ast.BinaryOp.bit_xor, .wrap = false, .sat = false },
        .mul_wrap_assign => .{ .op = ast.BinaryOp.mul, .wrap = true, .sat = false },
        .add_wrap_assign => .{ .op = ast.BinaryOp.add, .wrap = true, .sat = false },
        .sub_wrap_assign => .{ .op = ast.BinaryOp.sub, .wrap = true, .sat = false },
        .mul_sat_assign => .{ .op = ast.BinaryOp.mul, .wrap = false, .sat = true },
        .add_sat_assign => .{ .op = ast.BinaryOp.add, .wrap = false, .sat = true },
        .sub_sat_assign => .{ .op = ast.BinaryOp.sub, .wrap = false, .sat = true },
        .shl_sat_assign => .{ .op = ast.BinaryOp.shl, .wrap = false, .sat = true },
        else => return null,
    };

    const L = try self.lowerExpr(i.left);
    const R = try self.lowerExpr(i.right);

    const rhs_expr = self.ast_unit.exprs.add(.Binary, .{
        .left = L,
        .right = R,
        .op = bin_info.op,
        .wrap = bin_info.wrap,
        .saturate = bin_info.sat,
        .loc = base_loc,
    });
    return self.ast_unit.stmts.add(.Assign, .{ .left = .{ .expr = L }, .right = rhs_expr, .loc = base_loc });
}

// ---------------- Expressions ----------------
/// Lower any expression node by dispatching on its variant.
fn lowerExpr(self: *Lower, id: cst.ExprId) anyerror!ast.ExprId {
    const kind = self.cst_program.kind(id);
    return switch (kind) {
        .Ident => blk: {
            const row = self.cst_program.exprs.get(.Ident, id);
            break :blk self.ast_unit.exprs.add(.Ident, .{ .name = row.name, .loc = row.loc });
        },
        .Splice => blk: {
            const row = self.cst_program.exprs.get(.Splice, id);
            break :blk self.ast_unit.exprs.add(.Splice, .{ .name = row.name, .loc = row.loc });
        },
        .Literal => try self.lowerLiteral(id),
        .Prefix => blk: {
            const p = self.cst_program.exprs.get(.Prefix, id);
            switch (p.op) {
                .range, .range_inclusive => {
                    break :blk self.ast_unit.exprs.add(.Range, .{
                        .start = .none(),
                        .end = .some(try self.lowerExpr(p.right)),
                        .inclusive_right = (p.op == .range_inclusive),
                        .loc = p.loc,
                    });
                },
                .plus => break :blk self.ast_unit.exprs.add(.Unary, .{ .expr = try self.lowerExpr(p.right), .op = .pos, .loc = p.loc }),
                .minus => break :blk self.ast_unit.exprs.add(.Unary, .{ .expr = try self.lowerExpr(p.right), .op = .neg, .loc = p.loc }),
                .address_of => break :blk self.ast_unit.exprs.add(.Unary, .{ .expr = try self.lowerExpr(p.right), .op = .address_of, .loc = p.loc }),
                .logical_not => break :blk self.ast_unit.exprs.add(.Unary, .{ .expr = try self.lowerExpr(p.right), .op = .logical_not, .loc = p.loc }),
            }
        },
        .Infix => try self.lowerInfix(id),
        .Deref => blk: {
            const r = self.cst_program.exprs.get(.Deref, id);
            break :blk self.ast_unit.exprs.add(.Deref, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        .ArrayLit => blk: {
            const r = self.cst_program.exprs.get(.ArrayLit, id);
            break :blk self.ast_unit.exprs.add(.ArrayLit, .{ .elems = try self.lowerExprRange(r.elems), .loc = r.loc });
        },
        .Tuple => blk: {
            const r = self.cst_program.exprs.get(.Tuple, id);
            const elems = try self.lowerExprRange(r.elems);
            break :blk if (r.is_type)
                self.ast_unit.exprs.add(.TupleType, .{ .elems = elems, .loc = r.loc })
            else
                self.ast_unit.exprs.add(.TupleLit, .{ .elems = elems, .loc = r.loc });
        },
        .Parenthesized => self.lowerExpr(self.cst_program.exprs.get(.Parenthesized, id).inner),
        .MapLit => blk: {
            const r = self.cst_program.exprs.get(.MapLit, id);
            break :blk self.ast_unit.exprs.add(.MapLit, .{ .entries = try self.lowerKeyValues(r.entries), .loc = r.loc });
        },
        .Call => blk: {
            const r = self.cst_program.exprs.get(.Call, id);
            break :blk self.ast_unit.exprs.add(.Call, .{
                .callee = try self.lowerExpr(r.callee),
                .args = try self.lowerExprRange(r.args),
                .loc = r.loc,
            });
        },
        .NamedArg => blk: {
            const r = self.cst_program.exprs.get(.NamedArg, id);
            break :blk self.ast_unit.exprs.add(.NamedArg, .{
                .name = r.name,
                .value = try self.lowerExpr(r.value),
                .loc = r.loc,
            });
        },
        .IndexAccess => blk: {
            const r = self.cst_program.exprs.get(.IndexAccess, id);
            break :blk self.ast_unit.exprs.add(.IndexAccess, .{
                .collection = try self.lowerExpr(r.collection),
                .index = try self.lowerExpr(r.index),
                .loc = r.loc,
            });
        },
        .FieldAccess => blk: {
            const r = self.cst_program.exprs.get(.FieldAccess, id);
            break :blk self.ast_unit.exprs.add(.FieldAccess, .{
                .parent = try self.lowerExpr(r.parent),
                .field = r.field,
                .is_tuple = r.is_tuple,
                .loc = r.loc,
            });
        },
        .StructLit => blk: {
            const r = self.cst_program.exprs.get(.StructLit, id);
            break :blk self.ast_unit.exprs.add(.StructLit, .{
                .fields = try self.lowerStructFieldValues(r.fields),
                .ty = if (!r.ty.isNone()) .some(try self.lowerExpr(r.ty.unwrap())) else .none(),
                .loc = r.loc,
            });
        },
        .Function => blk: {
            const f = self.cst_program.exprs.get(.Function, id);
            break :blk self.ast_unit.exprs.add(.FunctionLit, .{
                .params = try self.lowerParamRange(f.params),
                .result_ty = if (!f.result_ty.isNone()) .some(try self.lowerExpr(f.result_ty.unwrap())) else .none(),
                .body = if (!f.body.isNone()) .some(try self.lowerBlockExpr(f.body.unwrap())) else .none(),
                .raw_asm = if (!f.raw_asm.isNone()) .some(f.raw_asm.unwrap()) else .none(),
                .attrs = try self.mapAttrRange(f.attrs),
                .flags = .{
                    .is_proc = f.flags.is_proc,
                    .is_async = f.flags.is_async,
                    .is_variadic = f.flags.is_variadic,
                    .is_extern = f.flags.is_extern,
                    .is_test = f.flags.is_test,
                },
                .loc = f.loc,
            });
        },
        .Block => try self.lowerBlockExpr(id),
        .Comptime => blk: {
            const r = self.cst_program.exprs.get(.Comptime, id);
            if (r.is_block) {
                break :blk self.ast_unit.exprs.add(.ComptimeBlock, .{ .block = try self.lowerBlockExpr(r.payload), .loc = r.loc });
            } else {
                const e = try self.lowerExpr(r.payload);
                const stmt = self.ast_unit.stmts.add(.Expr, .{ .expr = e });
                const stmts = self.ast_unit.stmts.stmt_pool.pushMany(self.ast_unit.gpa, &[_]ast.StmtId{stmt});
                const blk_expr = self.ast_unit.exprs.add(.Block, .{ .items = stmts, .loc = r.loc });
                break :blk self.ast_unit.exprs.add(.ComptimeBlock, .{ .block = blk_expr, .loc = r.loc });
            }
        },
        .Code => blk: {
            const r = self.cst_program.exprs.get(.Code, id);
            break :blk self.ast_unit.exprs.add(.CodeBlock, .{ .block = try self.lowerBlockExpr(r.block), .loc = r.loc });
        },
        .Insert => blk: {
            const r = self.cst_program.exprs.get(.Insert, id);
            break :blk self.ast_unit.exprs.add(.Insert, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        .Mlir => blk: {
            const r = self.cst_program.exprs.get(.Mlir, id);
            const args_range = if (r.args.isNone()) ast.RangeExpr.empty() else try self.lowerExprRange(r.args.asRange());
            const cst_pieces = self.cst_program.exprs.mlir_piece_pool.slice(r.pieces);

            const piece_ids = try self.arena.allocator().alloc(ast.MlirPieceId, cst_pieces.len);
            for (cst_pieces, 0..) |pid, i| {
                const piece = self.cst_program.exprs.MlirPiece.get(pid);
                piece_ids[i] = self.ast_unit.exprs.addMlirPiece(.{ .kind = piece.kind, .text = piece.text });
            }

            break :blk self.ast_unit.exprs.add(.MlirBlock, .{
                .kind = r.kind,
                .text = r.text,
                .pieces = self.ast_unit.exprs.mlir_piece_pool.pushMany(self.ast_unit.gpa, piece_ids),
                .args = args_range,
                .result_ty = if (r.result_ty.isNone()) .none() else .some(try self.lowerExpr(r.result_ty.unwrap())),
                .loc = r.loc,
            });
        },
        .Return => blk: {
            const r = self.cst_program.exprs.get(.Return, id);
            break :blk self.ast_unit.exprs.add(.Return, .{
                .value = if (!r.value.isNone()) .some(try self.lowerExpr(r.value.unwrap())) else .none(),
                .loc = r.loc,
            });
        },
        .If => blk: {
            const r = self.cst_program.exprs.get(.If, id);
            break :blk self.ast_unit.exprs.add(.If, .{
                .cond = try self.lowerExpr(r.cond),
                .then_block = try self.lowerBlockExpr(r.then_block),
                .else_block = if (!r.else_block.isNone()) .some(try self.lowerExpr(r.else_block.unwrap())) else .none(),
                .loc = r.loc,
            });
        },
        .While => blk: {
            const r = self.cst_program.exprs.get(.While, id);
            break :blk self.ast_unit.exprs.add(.While, .{
                .cond = if (!r.cond.isNone()) .some(try self.lowerExpr(r.cond.unwrap())) else .none(),
                .pattern = if (!r.pattern.isNone()) .some(try self.lowerPattern(r.pattern.unwrap())) else .none(),
                .body = try self.lowerBlockExpr(r.body),
                .is_pattern = r.is_pattern,
                .label = r.label,
                .loc = r.loc,
            });
        },
        .For => blk: {
            const r = self.cst_program.exprs.get(.For, id);
            break :blk self.ast_unit.exprs.add(.For, .{
                .pattern = try self.lowerPattern(r.pattern),
                .iterable = try self.lowerExpr(r.iterable),
                .body = try self.lowerBlockExpr(r.body),
                .label = r.label,
                .loc = r.loc,
            });
        },
        .Match => blk: {
            const r = self.cst_program.exprs.get(.Match, id);
            break :blk self.ast_unit.exprs.add(.Match, .{
                .expr = try self.lowerExpr(r.expr),
                .arms = try self.lowerMatchArms(r.arms),
                .loc = r.loc,
            });
        },
        .Break => blk: {
            const r = self.cst_program.exprs.get(.Break, id);
            break :blk self.ast_unit.exprs.add(.Break, .{
                .label = r.label,
                .value = if (!r.value.isNone()) .some(try self.lowerExpr(r.value.unwrap())) else .none(),
                .loc = r.loc,
            });
        },
        .Continue => blk: {
            const r = self.cst_program.exprs.get(.Continue, id);
            break :blk self.ast_unit.exprs.add(.Continue, .{ .loc = r.loc, .label = r.label });
        },
        .Unreachable => blk: {
            const r = self.cst_program.exprs.get(.Unreachable, id);
            break :blk self.ast_unit.exprs.add(.Unreachable, .{ .loc = r.loc });
        },
        .Null => blk: {
            const r = self.cst_program.exprs.get(.Null, id);
            break :blk self.ast_unit.exprs.add(.NullLit, .{ .loc = r.loc });
        },
        .Undefined => blk: {
            const r = self.cst_program.exprs.get(.Undefined, id);
            break :blk self.ast_unit.exprs.add(.UndefLit, .{ .loc = r.loc });
        },
        .Defer => blk: {
            const r = self.cst_program.exprs.get(.Defer, id);
            break :blk self.ast_unit.exprs.add(.Defer, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        .ErrDefer => blk: {
            const r = self.cst_program.exprs.get(.ErrDefer, id);
            break :blk self.ast_unit.exprs.add(.ErrDefer, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        .ErrUnwrap => blk: {
            const r = self.cst_program.exprs.get(.ErrUnwrap, id);
            break :blk self.ast_unit.exprs.add(.ErrUnwrap, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        .OptionalUnwrap => blk: {
            const r = self.cst_program.exprs.get(.OptionalUnwrap, id);
            break :blk self.ast_unit.exprs.add(.OptionalUnwrap, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        .Await => blk: {
            const r = self.cst_program.exprs.get(.Await, id);
            break :blk self.ast_unit.exprs.add(.Await, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        .Closure => blk: {
            const r = self.cst_program.exprs.get(.Closure, id);
            break :blk self.ast_unit.exprs.add(.Closure, .{
                .params = try self.lowerParamRange(r.params),
                .result_ty = if (!r.result_ty.isNone()) .some(try self.lowerExpr(r.result_ty.unwrap())) else .none(),
                .body = try self.lowerExpr(r.body),
                .loc = r.loc,
            });
        },
        .Async => blk: {
            const r = self.cst_program.exprs.get(.Async, id);
            break :blk self.ast_unit.exprs.add(.AsyncBlock, .{ .body = try self.lowerExpr(r.body), .loc = r.loc });
        },
        .Cast => blk: {
            const r = self.cst_program.exprs.get(.Cast, id);
            break :blk self.ast_unit.exprs.add(.Cast, .{ .expr = try self.lowerExpr(r.expr), .ty = try self.lowerExpr(r.ty), .kind = r.kind, .loc = r.loc });
        },
        .Catch => blk: {
            const r = self.cst_program.exprs.get(.Catch, id);
            break :blk self.ast_unit.exprs.add(.Catch, .{
                .expr = try self.lowerExpr(r.expr),
                .binding_name = r.binding_name,
                .binding_loc = r.binding_loc,
                .handler = try self.lowerExpr(r.handler),
                .loc = r.loc,
            });
        },
        .Import => blk: {
            const r = self.cst_program.exprs.get(.Import, id);
            try self.recordDependency(r.path);
            break :blk self.ast_unit.exprs.add(.Import, .{ .path = r.path, .loc = r.loc });
        },
        .TypeOf => blk: {
            const r = self.cst_program.exprs.get(.TypeOf, id);
            break :blk self.ast_unit.exprs.add(.TypeOf, .{ .expr = try self.lowerExpr(r.expr), .loc = r.loc });
        },
        // Types
        .ArrayType => blk: {
            const t = self.cst_program.exprs.get(.ArrayType, id);
            break :blk self.ast_unit.exprs.add(.ArrayType, .{ .elem = try self.lowerExpr(t.elem), .size = try self.lowerExpr(t.size), .loc = t.loc });
        },
        .DynArrayType => blk: {
            const t = self.cst_program.exprs.get(.DynArrayType, id);
            break :blk self.ast_unit.exprs.add(.DynArrayType, .{ .elem = try self.lowerExpr(t.elem), .loc = t.loc });
        },
        .MapType => blk: {
            const t = self.cst_program.exprs.get(.MapType, id);
            break :blk self.ast_unit.exprs.add(.MapType, .{ .key = try self.lowerExpr(t.key), .value = try self.lowerExpr(t.value), .loc = t.loc });
        },
        .SliceType => blk: {
            const t = self.cst_program.exprs.get(.SliceType, id);
            break :blk self.ast_unit.exprs.add(.SliceType, .{ .elem = try self.lowerExpr(t.elem), .is_const = t.is_const, .loc = t.loc });
        },
        .OptionalType => blk: {
            const t = self.cst_program.exprs.get(.OptionalType, id);
            break :blk self.ast_unit.exprs.add(.OptionalType, .{ .elem = try self.lowerExpr(t.elem), .loc = t.loc });
        },
        .ErrorSetType => blk: {
            const t = self.cst_program.exprs.get(.ErrorSetType, id);
            break :blk self.ast_unit.exprs.add(.ErrorSetType, .{ .err = try self.lowerExpr(t.err), .value = try self.lowerExpr(t.value), .loc = t.loc });
        },
        .StructType => blk: {
            const t = self.cst_program.exprs.get(.StructType, id);
            break :blk self.ast_unit.exprs.add(.StructType, .{ .fields = try self.lowerStructFields(t.fields), .is_extern = t.is_extern, .attrs = try self.mapAttrRange(t.attrs), .loc = t.loc });
        },
        .EnumType => blk: {
            const t = self.cst_program.exprs.get(.EnumType, id);
            break :blk self.ast_unit.exprs.add(.EnumType, .{
                .fields = try self.lowerEnumFields(t.fields),
                .discriminant = if (!t.discriminant.isNone()) .some(try self.lowerExpr(t.discriminant.unwrap())) else .none(),
                .is_extern = t.is_extern,
                .attrs = try self.mapAttrRange(t.attrs),
                .loc = t.loc,
            });
        },
        .VariantLikeType => blk: {
            const t = self.cst_program.exprs.get(.VariantLikeType, id);
            break :blk self.ast_unit.exprs.add(.VariantType, .{ .fields = try self.lowerVariantFields(t.fields), .loc = t.loc });
        },
        .ErrorType => blk: {
            const t = self.cst_program.exprs.get(.ErrorType, id);
            break :blk self.ast_unit.exprs.add(.ErrorType, .{ .fields = try self.lowerVariantFields(t.fields), .loc = t.loc });
        },
        .UnionType => blk: {
            const t = self.cst_program.exprs.get(.UnionType, id);
            break :blk self.ast_unit.exprs.add(.UnionType, .{ .fields = try self.lowerStructFields(t.fields), .is_extern = t.is_extern, .attrs = try self.mapAttrRange(t.attrs), .loc = t.loc });
        },
        .PointerType => blk: {
            const t = self.cst_program.exprs.get(.PointerType, id);
            break :blk self.ast_unit.exprs.add(.PointerType, .{ .elem = try self.lowerExpr(t.elem), .is_const = t.is_const, .loc = t.loc });
        },
        .SimdType => blk: {
            const t = self.cst_program.exprs.get(.SimdType, id);
            break :blk self.ast_unit.exprs.add(.SimdType, .{ .elem = try self.lowerExpr(t.elem), .lanes = try self.lowerExpr(t.lanes), .loc = t.loc });
        },
        .ComplexType => blk: {
            const t = self.cst_program.exprs.get(.ComplexType, id);
            break :blk self.ast_unit.exprs.add(.ComplexType, .{ .elem = try self.lowerExpr(t.elem), .loc = t.loc });
        },
        .TensorType => blk: {
            const t = self.cst_program.exprs.get(.TensorType, id);
            break :blk self.ast_unit.exprs.add(.TensorType, .{ .elem = try self.lowerExpr(t.elem), .shape = try self.lowerExprRange(t.shape), .loc = t.loc });
        },
        .TypeType => self.ast_unit.exprs.add(.TypeType, .{ .loc = self.cst_program.exprs.get(.TypeType, id).loc }),
        .AnyType => self.ast_unit.exprs.add(.AnyType, .{ .loc = self.cst_program.exprs.get(.AnyType, id).loc }),
        .NoreturnType => self.ast_unit.exprs.add(.NoreturnType, .{ .loc = self.cst_program.exprs.get(.NoreturnType, id).loc }),
    };
}

/// Convert literal CST expressions (ints, strings, bools) into AST nodes.
fn lowerLiteral(self: *Lower, id: cst.ExprId) !ast.ExprId {
    const lit = self.cst_program.exprs.get(.Literal, id);
    const loc = lit.loc;

    switch (lit.tag_small) {
        .int => {
            const text = self.cst_program.exprs.strs.get(lit.value);
            const parsed = try LiteralScanner.parseIntLiteralText(self.gpa, text);
            return self.ast_unit.exprs.add(.Literal, .{
                .kind = .int,
                .data = .{ .int = .{ .text = lit.value, .value = parsed.value, .base = parsed.base, .valid = parsed.valid } },
                .loc = loc,
            });
        },
        .float => {
            const text = self.cst_program.exprs.strs.get(lit.value);
            const parsed = try LiteralScanner.parseFloatLiteralText(self.gpa, text);
            return self.ast_unit.exprs.add(.Literal, .{
                .kind = .float,
                .data = .{ .float = .{ .text = lit.value, .value = parsed.value, .valid = parsed.valid } },
                .loc = loc,
            });
        },
        .char => {
            const unescaped = try LiteralScanner.unescapeChar(self.cst_program.exprs.strs.get(lit.value));
            return self.ast_unit.exprs.add(.Literal, .{ .kind = .char, .data = .{ .char = unescaped }, .loc = loc });
        },
        .imaginary => {
            const s = self.cst_program.exprs.strs.get(lit.value);
            const trimmed = if (s.len > 0 and s[s.len - 1] == 'i') s[0 .. s.len - 1] else s;
            const parsed = try LiteralScanner.parseFloatLiteralText(self.gpa, trimmed);
            const sid = self.ast_unit.exprs.strs.intern(trimmed);
            return self.ast_unit.exprs.add(.Literal, .{
                .kind = .imaginary,
                .data = .{ .imaginary = .{ .text = sid, .value = parsed.value, .valid = parsed.valid } },
                .loc = loc,
            });
        },
        .true => return self.ast_unit.exprs.add(.Literal, .{ .kind = .bool, .data = .{ .bool = true }, .loc = loc }),
        .false => return self.ast_unit.exprs.add(.Literal, .{ .kind = .bool, .data = .{ .bool = false }, .loc = loc }),
        else => {
            const str = self.cst_program.exprs.strs.get(lit.value);
            const unescaped = try LiteralScanner.unescapeString(self.ast_unit.gpa, self.ast_unit.exprs.strs, str, lit.tag_small == .raw_string);
            return self.ast_unit.exprs.add(.Literal, .{ .kind = .string, .data = .{ .string = unescaped }, .loc = loc });
        },
    }
}

/// Lower infix/binary expressions, including special-case compound assignments.
fn lowerInfix(self: *Lower, id: cst.ExprId) !ast.ExprId {
    const i = self.cst_program.exprs.get(.Infix, id);
    const L = try self.lowerExpr(i.left);
    const R = try self.lowerExpr(i.right);
    const loc = i.loc;

    switch (i.op) {
        .range, .range_inclusive => return self.ast_unit.exprs.add(.Range, .{ .start = .some(L), .end = .some(R), .inclusive_right = (i.op == .range_inclusive), .loc = loc }),
        .error_catch => return self.ast_unit.exprs.add(.Catch, .{ .expr = L, .binding_name = .none(), .binding_loc = .none(), .handler = R, .loc = loc }),
        .unwrap_orelse => return self.ast_unit.exprs.add(.Binary, .{ .left = L, .right = R, .op = .@"orelse", .wrap = false, .saturate = false, .loc = loc }),
        .error_union => return self.ast_unit.exprs.add(.ErrorSetType, .{ .err = L, .value = R, .loc = loc }),
        else => {
            const map: struct { op: ast.BinaryOp, wrap: bool, sat: bool } = switch (i.op) {
                .add => .{ .op = ast.BinaryOp.add, .wrap = false, .sat = false },
                .sub => .{ .op = ast.BinaryOp.sub, .wrap = false, .sat = false },
                .mul => .{ .op = ast.BinaryOp.mul, .wrap = false, .sat = false },
                .div => .{ .op = ast.BinaryOp.div, .wrap = false, .sat = false },
                .mod => .{ .op = ast.BinaryOp.mod, .wrap = false, .sat = false },
                .shl => .{ .op = ast.BinaryOp.shl, .wrap = false, .sat = false },
                .shr => .{ .op = ast.BinaryOp.shr, .wrap = false, .sat = false },
                .b_and => .{ .op = ast.BinaryOp.bit_and, .wrap = false, .sat = false },
                .b_or => .{ .op = ast.BinaryOp.bit_or, .wrap = false, .sat = false },
                .b_xor => .{ .op = ast.BinaryOp.bit_xor, .wrap = false, .sat = false },
                .eq => .{ .op = ast.BinaryOp.eq, .wrap = false, .sat = false },
                .neq => .{ .op = ast.BinaryOp.neq, .wrap = false, .sat = false },
                .lt => .{ .op = ast.BinaryOp.lt, .wrap = false, .sat = false },
                .lte => .{ .op = ast.BinaryOp.lte, .wrap = false, .sat = false },
                .gt => .{ .op = ast.BinaryOp.gt, .wrap = false, .sat = false },
                .gte => .{ .op = ast.BinaryOp.gte, .wrap = false, .sat = false },
                .logical_and => .{ .op = ast.BinaryOp.logical_and, .wrap = false, .sat = false },
                .logical_or => .{ .op = ast.BinaryOp.logical_or, .wrap = false, .sat = false },
                .contains => .{ .op = ast.BinaryOp.contains, .wrap = false, .sat = false },
                .add_wrap => .{ .op = ast.BinaryOp.add, .wrap = true, .sat = false },
                .add_sat => .{ .op = ast.BinaryOp.add, .wrap = false, .sat = true },
                .sub_wrap => .{ .op = ast.BinaryOp.sub, .wrap = true, .sat = false },
                .sub_sat => .{ .op = ast.BinaryOp.sub, .wrap = false, .sat = true },
                .mul_wrap => .{ .op = ast.BinaryOp.mul, .wrap = true, .sat = false },
                .mul_sat => .{ .op = ast.BinaryOp.mul, .wrap = false, .sat = true },
                .shl_sat => .{ .op = ast.BinaryOp.shl, .wrap = false, .sat = true },
                else => .{ .op = ast.BinaryOp.add, .wrap = false, .sat = false }, // fallback
            };
            return self.ast_unit.exprs.add(.Binary, .{ .left = L, .right = R, .op = map.op, .wrap = map.wrap, .saturate = map.sat, .loc = loc });
        },
    }
}

/// Lower match arms (pattern + guard + body) for AST match expressions.
fn lowerMatchArms(self: *Lower, r: cst.RangeOf(cst.MatchArmId)) !ast.RangeMatchArm {
    const items = self.cst_program.exprs.arm_pool.slice(r);
    return self.mapRange(cst.MatchArmId, ast.MatchArmId, items, &self.ast_unit.exprs.arm_pool, Lower.lowerMatchArm);
}

fn lowerMatchArm(self: *Lower, id: cst.MatchArmId) !ast.MatchArmId {
    const a = self.cst_program.exprs.MatchArm.get(id);
    const mapped: ast.Rows.MatchArm = .{
        .pattern = try self.lowerPattern(a.pattern),
        .guard = if (!a.guard.isNone()) .some(try self.lowerExpr(a.guard.unwrap())) else .none(),
        .body = try self.lowerExpr(a.body),
        .loc = a.loc,
    };
    return self.ast_unit.exprs.MatchArm.add(self.ast_unit.gpa, mapped);
}

// ---------------- Patterns ----------------
/// Lower a pattern CST node into its AST counterpart.
fn lowerPattern(self: *Lower, id: cst.PatternId) !ast.PatternId {
    const kind = self.cst_program.kind(id);
    return switch (kind) {
        .Wildcard => self.ast_unit.pats.add(.Wildcard, .{ .loc = self.cst_program.pats.get(.Wildcard, id).loc }),
        .Literal => blk: {
            const p = self.cst_program.pats.get(.Literal, id);
            break :blk self.ast_unit.pats.add(.Literal, .{ .expr = try self.lowerExpr(p.expr), .loc = p.loc });
        },
        .Path => blk: {
            const p = self.cst_program.pats.get(.Path, id);
            break :blk self.ast_unit.pats.add(.Path, .{ .segments = try self.lowerPathSegs(p.segments), .loc = p.loc });
        },
        .Binding => blk: {
            const b = self.cst_program.pats.get(.Binding, id);
            break :blk self.ast_unit.pats.add(.Binding, .{ .name = b.name, .by_ref = b.by_ref, .is_mut = b.is_mut, .loc = b.loc });
        },
        .Parenthesized => self.lowerPattern(self.cst_program.pats.get(.Parenthesized, id).pattern),
        .Tuple => blk: {
            const t = self.cst_program.pats.get(.Tuple, id);
            break :blk self.ast_unit.pats.add(.Tuple, .{ .elems = try self.lowerPatRange(t.elems), .loc = t.loc });
        },
        .Slice => blk: {
            const s = self.cst_program.pats.get(.Slice, id);
            break :blk self.ast_unit.pats.add(.Slice, .{
                .elems = try self.lowerPatRange(s.elems),
                .has_rest = s.has_rest,
                .rest_index = s.rest_index,
                .rest_binding = if (!s.rest_binding.isNone()) .some(try self.lowerPattern(s.rest_binding.unwrap())) else .none(),
                .loc = s.loc,
            });
        },
        .Struct => blk: {
            const s = self.cst_program.pats.get(.Struct, id);
            break :blk self.ast_unit.pats.add(.Struct, .{
                .path = try self.lowerPathSegs(s.path),
                .fields = try self.lowerPatFields(s.fields),
                .has_rest = s.has_rest,
                .loc = s.loc,
            });
        },
        .VariantTuple => blk: {
            const v = self.cst_program.pats.get(.VariantTuple, id);
            break :blk self.ast_unit.pats.add(.VariantTuple, .{
                .path = try self.lowerPathSegs(v.path),
                .elems = try self.lowerPatRange(v.elems),
                .loc = v.loc,
            });
        },
        .VariantStruct => blk: {
            const v = self.cst_program.pats.get(.VariantStruct, id);
            break :blk self.ast_unit.pats.add(.VariantStruct, .{
                .path = try self.lowerPathSegs(v.path),
                .fields = try self.lowerPatFields(v.fields),
                .has_rest = v.has_rest,
                .loc = v.loc,
            });
        },
        .Range => blk: {
            const r = self.cst_program.pats.get(.Range, id);
            break :blk self.ast_unit.pats.add(.Range, .{
                .start = if (!r.start.isNone()) .some(try self.lowerExpr(r.start.unwrap())) else .none(),
                .end = if (!r.end.isNone()) .some(try self.lowerExpr(r.end.unwrap())) else .none(),
                .inclusive_right = r.inclusive_right,
                .loc = r.loc,
            });
        },
        .Or => blk: {
            const o = self.cst_program.pats.get(.Or, id);
            break :blk self.ast_unit.pats.add(.Or, .{ .alts = try self.lowerPatRange(o.alts), .loc = o.loc });
        },
        .At => blk: {
            const a = self.cst_program.pats.get(.At, id);
            break :blk self.ast_unit.pats.add(.At, .{ .binder = a.binder, .pattern = try self.lowerPattern(a.pattern), .loc = a.loc });
        },
    };
}

/// Lower a sequence of path segments into AST `PathSeg`s.
fn lowerPathSegs(self: *Lower, r: cst.RangeOf(cst.PathSegId)) !ast.RangePathSeg {
    const items = self.cst_program.pats.seg_pool.slice(r);
    return self.mapRange(cst.PathSegId, ast.PathSegId, items, &self.ast_unit.pats.seg_pool, Lower.lowerPathSeg);
}

fn lowerPathSeg(self: *Lower, id: cst.PathSegId) !ast.PathSegId {
    const s = self.cst_program.pats.PathSeg.get(id);
    const mapped: ast.PatRows.PathSeg = .{ .name = s.name, .by_ref = false, .is_mut = false, .loc = s.loc };
    return self.ast_unit.pats.PathSeg.add(self.ast_unit.gpa, mapped);
}

/// Lower struct pattern fields within a pattern clause.
fn lowerPatFields(self: *Lower, r: cst.RangeOf(cst.PatFieldId)) anyerror!ast.RangePatField {
    const items = self.cst_program.pats.field_pool.slice(r);
    return self.mapRange(cst.PatFieldId, ast.PatFieldId, items, &self.ast_unit.pats.field_pool, Lower.lowerPatField);
}

fn lowerPatField(self: *Lower, id: cst.PatFieldId) !ast.PatFieldId {
    const f = self.cst_program.pats.StructField.get(id);
    const mapped: ast.PatRows.StructField = .{ .name = f.name, .pattern = try self.lowerPattern(f.pattern), .loc = f.loc };
    return self.ast_unit.pats.StructField.add(self.ast_unit.gpa, mapped);
}

/// Lower a range of pattern elements (e.g., tuple patterns).
fn lowerPatRange(self: *Lower, r: cst.RangeOf(cst.PatternId)) anyerror!ast.RangePat {
    const items = self.cst_program.pats.pat_pool.slice(r);
    return self.mapRange(cst.PatternId, ast.PatternId, items, &self.ast_unit.pats.pat_pool, Lower.lowerPattern);
}

/// Extract path segments from a type expression for matching/lookup.
fn pathSegsFromTypeExpr(self: *Lower, id: cst.ExprId) !ast.RangePathSeg {
    var segs = std.ArrayList(ast.PathSegId){};
    defer segs.deinit(self.ast_unit.gpa); // We copy results into pool, can free ArrayList
    try self.collectPathSegs(id, &segs);
    return self.ast_unit.pats.seg_pool.pushMany(self.ast_unit.gpa, segs.items);
}

fn collectPathSegs(self: *Lower, id: cst.ExprId, segs: *std.ArrayList(ast.PathSegId)) anyerror!void {
    switch (self.cst_program.kind(id)) {
        .Ident => {
            const r = self.cst_program.exprs.get(.Ident, id);
            try segs.append(self.ast_unit.gpa, self.ast_unit.pats.PathSeg.add(self.ast_unit.gpa, .{ .name = r.name, .by_ref = false, .is_mut = false, .loc = r.loc }));
        },
        .FieldAccess => {
            const r = self.cst_program.exprs.get(.FieldAccess, id);
            try self.collectPathSegs(r.parent, segs);
            try segs.append(self.ast_unit.gpa, self.ast_unit.pats.PathSeg.add(self.ast_unit.gpa, .{ .name = r.field, .by_ref = false, .is_mut = false, .loc = r.loc }));
        },
        else => {},
    }
}

fn lowerOptionalPatternFromExpr(self: *Lower, e: cst.OptExprId) !ast.OptPatternId {
    if (e.isNone()) return .none();
    return if (try self.patternFromExpr(e.unwrap())) |pid| .some(pid) else .none();
}

/// Try to interpret an assignment LHS expression as a pattern literal.
fn patternFromAssignExpr(self: *Lower, id: cst.ExprId) !?ast.PatternId {
    return switch (self.cst_program.kind(id)) {
        .Tuple, .StructLit, .ArrayLit => self.patternFromExpr(id),
        else => null,
    };
}

/// Try to interpret an expression as a pattern literal.
fn patternFromExpr(self: *Lower, id: cst.ExprId) !?ast.PatternId {
    const kind = self.cst_program.kind(id);
    switch (kind) {
        .Ident => {
            const r = self.cst_program.exprs.get(.Ident, id);
            const name = self.cst_program.exprs.strs.get(r.name);
            return if (std.mem.eql(u8, name, "_"))
                self.ast_unit.pats.add(.Wildcard, .{ .loc = r.loc })
            else
                self.ast_unit.pats.add(.Binding, .{ .name = r.name, .by_ref = false, .is_mut = false, .loc = r.loc });
        },
        .ArrayLit => {
            const a = self.cst_program.exprs.get(.ArrayLit, id);
            const xs = self.cst_program.exprs.expr_pool.slice(a.elems);
            // Use arena for temporary storage
            const elem_pats = try self.arena.allocator().alloc(ast.PatternId, xs.len);

            var has_rest = false;
            var rest_idx: u32 = 0;
            var rest_pat: ast.OptPatternId = .none();
            var out_i: usize = 0;

            for (xs) |x| {
                if (self.cst_program.kind(x) == .Prefix) {
                    const p = self.cst_program.exprs.get(.Prefix, x);
                    if (p.op == .range) {
                        const sub = try self.patternFromExpr(p.right) orelse return null;
                        if (has_rest) {
                            try self.context.diags.addError(self.ast_unit.exprs.locs.get(p.loc), .pattern_shape_mismatch, .{});
                            return null;
                        }
                        has_rest = true;
                        rest_idx = @intCast(out_i);
                        rest_pat = .some(sub);
                        continue;
                    }
                }
                elem_pats[out_i] = try self.patternFromExpr(x) orelse return null;
                out_i += 1;
            }
            const range = self.ast_unit.pats.pat_pool.pushMany(self.ast_unit.gpa, elem_pats[0..out_i]);
            return self.ast_unit.pats.add(.Slice, .{ .elems = range, .has_rest = has_rest, .rest_index = rest_idx, .rest_binding = rest_pat, .loc = a.loc });
        },
        .Tuple => {
            const t = self.cst_program.exprs.get(.Tuple, id);
            const elems = self.cst_program.exprs.expr_pool.slice(t.elems);
            const out_ids = try self.arena.allocator().alloc(ast.PatternId, elems.len);
            for (elems, 0..) |e, i| out_ids[i] = try self.patternFromExpr(e) orelse return null;
            return self.ast_unit.pats.add(.Tuple, .{ .elems = self.ast_unit.pats.pat_pool.pushMany(self.ast_unit.gpa, out_ids), .loc = t.loc });
        },
        .StructLit => {
            const s = self.cst_program.exprs.get(.StructLit, id);
            const fields = self.cst_program.exprs.sfv_pool.slice(s.fields);
            const out_ids = try self.arena.allocator().alloc(ast.PatFieldId, fields.len);

            for (fields, 0..) |f_id, i| {
                const f = self.cst_program.exprs.StructFieldValue.get(f_id);
                if (f.name.isNone()) return null;
                out_ids[i] = self.ast_unit.pats.StructField.add(self.ast_unit.gpa, .{
                    .name = f.name.unwrap(),
                    .pattern = try self.patternFromExpr(f.value) orelse return null,
                    .loc = f.loc,
                });
            }
            const range = self.ast_unit.pats.field_pool.pushMany(self.ast_unit.gpa, out_ids);

            if (!s.ty.isNone()) {
                const path = try self.pathSegsFromTypeExpr(s.ty.unwrap());
                if (self.ast_unit.pats.seg_pool.slice(path).len >= 2) {
                    return self.ast_unit.pats.add(.VariantStruct, .{ .path = path, .fields = range, .has_rest = false, .loc = s.loc });
                }
            }
            return self.ast_unit.pats.add(.Struct, .{
                .path = self.ast_unit.pats.seg_pool.pushMany(self.ast_unit.gpa, &[_]ast.PathSegId{}),
                .fields = range,
                .has_rest = false,
                .loc = s.loc,
            });
        },
        .Call => {
            const r = self.cst_program.exprs.get(.Call, id);
            const args = self.cst_program.exprs.expr_pool.slice(r.args);
            const pats = try self.arena.allocator().alloc(ast.PatternId, args.len);
            for (args, 0..) |arg, i| pats[i] = try self.patternFromExpr(arg) orelse return null;
            return self.ast_unit.pats.add(.VariantTuple, .{
                .path = try self.pathSegsFromTypeExpr(r.callee),
                .elems = self.ast_unit.pats.pat_pool.pushMany(self.ast_unit.gpa, pats),
                .loc = r.loc,
            });
        },
        .FieldAccess => {
            const r = self.cst_program.exprs.get(.FieldAccess, id);
            return self.ast_unit.pats.add(.Path, .{ .segments = try self.pathSegsFromTypeExpr(id), .loc = r.loc });
        },
        inline else => |x| {
            const loc = self.ast_unit.exprs.locs.get(self.cst_program.exprs.get(x, id).loc);
            try self.context.diags.addError(loc, .expected_pattern_on_decl_lhs, .{});
            return null;
        },
    }
}

const LiteralScanner = struct {
    fn unescapeString(gpa: std.mem.Allocator, strs: *ast.StringInterner, quoted_str: []const u8, raw: bool) !ast.StrId {
        const inner = if (raw) std.mem.trim(u8, quoted_str[1..], "\"#") else quoted_str[1 .. quoted_str.len - 1];
        var buf: std.ArrayList(u8) = std.ArrayList(u8){};
        defer buf.deinit(gpa);

        var i: usize = 0;
        while (i < inner.len) : (i += 1) {
            if (inner[i] == '\\' and i + 1 < inner.len) {
                i += 1;
                switch (inner[i]) {
                    'n' => try buf.append(gpa, '\n'),
                    't' => try buf.append(gpa, '\t'),
                    'r' => try buf.append(gpa, '\r'),
                    '0' => try buf.append(gpa, 0),
                    else => try buf.append(gpa, inner[i]),
                }
            } else try buf.append(gpa, inner[i]);
        }
        return strs.intern(buf.items);
    }

    fn unescapeChar(quoted_char: []const u8) !u32 {
        const inner = quoted_char[1 .. quoted_char.len - 1];
        if (inner.len == 1) return inner[0];
        if (inner.len == 2 and inner[0] == '\\') {
            return switch (inner[1]) {
                'n' => 10,
                't' => 9,
                'r' => 13,
                '\\' => 92,
                '"' => 34,
                '\'' => 39,
                '0' => 0,
                else => inner[1],
            };
        }
        return '?';
    }

    fn parseIntLiteralText(gpa: std.mem.Allocator, text: []const u8) !struct { value: u128, base: u8, valid: bool } {
        if (text.len == 0) return .{ .value = 0, .base = 10, .valid = false };
        var base: u8 = 10;
        var src = text;
        if (src.len >= 2 and src[0] == '0') {
            switch (src[1]) {
                'b', 'B' => {
                    base = 2;
                    src = src[2..];
                },
                'o', 'O' => {
                    base = 8;
                    src = src[2..];
                },
                'x', 'X' => {
                    base = 16;
                    src = src[2..];
                },
                else => {},
            }
        }

        // Stack optimization: most ints fit in 128 bytes
        var buf: [128]u8 = undefined;
        var ptr: []u8 = undefined;
        var fallback_alloc: ?[]u8 = null;

        // Count length without underscores
        var len: usize = 0;
        for (src) |c| if (c != '_') {
            len += 1;
        };

        if (len == 0) return .{ .value = 0, .base = base, .valid = false };

        if (len <= 128) {
            ptr = &buf;
        } else {
            fallback_alloc = try gpa.alloc(u8, len);
            ptr = fallback_alloc.?;
        }
        defer if (fallback_alloc) |b| gpa.free(b);

        var idx: usize = 0;
        for (src) |c| {
            if (c != '_') {
                ptr[idx] = c;
                idx += 1;
            }
        }

        const valid_str = ptr[0..idx];
        const val = std.fmt.parseInt(u128, valid_str, base) catch return .{ .value = 0, .base = base, .valid = false };
        return .{ .value = val, .base = base, .valid = true };
    }

    fn parseFloatLiteralText(gpa: std.mem.Allocator, text: []const u8) !struct { value: f64, valid: bool } {
        if (text.len == 0) return .{ .value = 0.0, .valid = false };

        // Same stack optimization logic for floats
        var buf: [128]u8 = undefined;
        var ptr: []u8 = undefined;
        var fallback_alloc: ?[]u8 = null;

        var len: usize = 0;
        for (text) |c| if (c != '_') {
            len += 1;
        };
        if (len == 0) return .{ .value = 0.0, .valid = false };

        if (len <= 128) {
            ptr = &buf;
        } else {
            fallback_alloc = try gpa.alloc(u8, len);
            ptr = fallback_alloc.?;
        }
        defer if (fallback_alloc) |b| gpa.free(b);

        var idx: usize = 0;
        for (text) |c| {
            if (c != '_') {
                ptr[idx] = c;
                idx += 1;
            }
        }

        const val = std.fmt.parseFloat(f64, ptr[0..idx]) catch return .{ .value = 0.0, .valid = false };
        return .{ .value = val, .valid = true };
    }
};
