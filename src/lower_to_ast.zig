const std = @import("std");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const compile = @import("compile.zig");
const diagnostics = @import("diagnostics.zig");

pub const Lower = @This();
gpa: std.mem.Allocator,
cst_program: *const cst.CST,
ast_unit: *ast.Ast,
context: *compile.Context,
file_id: u32,

pub fn init(
    gpa: std.mem.Allocator,
    program: *const cst.CST,
    context: *compile.Context,
    file_id: u32,
) !Lower {
    const ast_unit = try gpa.create(ast.Ast);
    ast_unit.* = ast.Ast.init(gpa, program.interner, program.exprs.locs, context.type_store, file_id);
    return .{
        .gpa = gpa,
        .cst_program = program,
        .ast_unit = ast_unit,
        .context = context,
        .file_id = file_id,
    };
}

pub fn deinit(self: *Lower) void {
    self.ast_unit.deinit();
    self.gpa.destroy(self.ast_unit);
}

pub fn runLower(self: *Lower) !void {
    _ = try self.run();
}

pub fn run(self: *Lower) !*ast.Ast {
    var unit: ast.Unit = .empty();

    unit.package_name = self.cst_program.program.package_name;
    unit.package_loc = self.cst_program.program.package_loc;

    // top-level decls -> ast.decl_pool range
    unit.decls = try self.lowerTopDecls(self.cst_program.program.top_decls);

    self.ast_unit.unit = unit;
    return self.ast_unit;
}

fn recordDependency(self: *Lower, dependency: ast.StrId) !void {
    try self.context.compilation_unit.addDependency(self.file_id, dependency);
}

fn unescapeString(self: *Lower, quoted_str: []const u8, raw: bool) !ast.StrId {
    const inner_str = if (raw)
        std.mem.trim(u8, quoted_str[1..], "\"#")
    else
        quoted_str[1 .. quoted_str.len - 1];

    var unescaped_list = std.array_list.Managed(u8).init(self.gpa);
    defer unescaped_list.deinit();

    var i: usize = 0;
    while (i < inner_str.len) : (i += 1) {
        if (inner_str[i] == '\\') {
            i += 1;
            if (i >= inner_str.len) {
                try unescaped_list.append('\\');
                break;
            }
            switch (inner_str[i]) {
                'n' => try unescaped_list.append('\n'),
                't' => try unescaped_list.append('\t'),
                'r' => try unescaped_list.append('\r'),
                '\\' => try unescaped_list.append('\\'),
                '"' => try unescaped_list.append('"'),
                '\'' => try unescaped_list.append('\''),
                '0' => try unescaped_list.append(0),
                else => {
                    try unescaped_list.append('\\');
                    try unescaped_list.append(inner_str[i]);
                },
            }
        } else {
            try unescaped_list.append(inner_str[i]);
        }
    }
    return self.ast_unit.exprs.strs.intern(unescaped_list.items);
}

fn unescapeChar(_: *Lower, quoted_char: []const u8) !u32 {
    const inner_char_str = quoted_char[1 .. quoted_char.len - 1];

    var char_val: u32 = undefined;
    if (inner_char_str.len == 1) {
        char_val = inner_char_str[0];
    } else if (inner_char_str.len == 2 and inner_char_str[0] == '\\') {
        switch (inner_char_str[1]) {
            'n' => char_val = 10,
            't' => char_val = 9,
            'r' => char_val = 13,
            '\\' => char_val = 92,
            '"' => char_val = 34,
            '\'' => char_val = 39,
            '0' => char_val = 0,
            else => {
                char_val = inner_char_str[1];
            },
        }
    } else {
        char_val = '?'; // Indicate error or unhandled case
    }
    return char_val;
}

fn parseIntLiteralText(self: *Lower, text: []const u8) !struct { value: u128, base: u8, valid: bool } {
    if (text.len == 0) return .{ .value = 0, .base = 10, .valid = false };

    var base: u8 = 10;
    var digits = text;
    if (digits.len >= 2 and digits[0] == '0') {
        const prefix = digits[1];
        switch (prefix) {
            'b', 'B' => {
                base = 2;
                digits = digits[2..];
            },
            'o', 'O' => {
                base = 8;
                digits = digits[2..];
            },
            'x', 'X' => {
                base = 16;
                digits = digits[2..];
            },
            else => {},
        }
    }

    var valid = digits.len != 0;

    var buf: std.ArrayList(u8) = .empty;
    defer buf.deinit(self.gpa);
    for (digits) |c| {
        if (c == '_') continue;
        try buf.append(self.gpa, c);
    }
    if (buf.items.len == 0) valid = false;

    var value: u128 = 0;
    if (valid) {
        value = std.fmt.parseInt(u128, buf.items, base) catch blk: {
            valid = false;
            break :blk 0;
        };
    }

    return .{ .value = value, .base = base, .valid = valid };
}

fn parseFloatLiteralText(self: *Lower, text: []const u8) !struct { value: f64, valid: bool } {
    if (text.len == 0) return .{ .value = 0.0, .valid = false };
    var buf: std.ArrayList(u8) = .empty;
    defer buf.deinit(self.gpa);
    for (text) |c| {
        if (c == '_') continue;
        try buf.append(self.gpa, c);
    }
    var valid = buf.items.len != 0;
    var value: f64 = 0.0;
    if (valid) {
        value = std.fmt.parseFloat(f64, buf.items) catch blk: {
            valid = false;
            break :blk 0.0;
        };
    }
    return .{ .value = value, .valid = valid };
}

fn mapAttrRange(self: *Lower, r: cst.OptRangeAttr) !ast.OptRangeAttr {
    if (r.isNone()) return .none();
    const rr = r.asRange();
    const items = self.cst_program.exprs.attr_pool.slice(rr);
    var out_ids = try self.gpa.alloc(ast.AttributeId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const row = self.cst_program.exprs.Attribute.get(items[i]);
        const mapped: ast.Rows.Attribute = .{
            .name = row.name,
            .value = if (!row.value.isNone()) .some(try self.lowerExpr(row.value.unwrap())) else .none(),
            .loc = row.loc,
        };
        out_ids[i] = self.ast_unit.exprs.Attribute.add(self.gpa, mapped);
    }
    return .some(self.ast_unit.exprs.attr_pool.pushMany(self.gpa, out_ids));
}

fn lowerParamRange(self: *Lower, r: cst.RangeOf(cst.ParamId)) !ast.RangeParam {
    const items = self.cst_program.exprs.param_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.ParamId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const row = self.cst_program.exprs.Param.get(items[i]);
        const mapped: ast.Rows.Param = .{
            .pat = try self.lowerOptionalPatternFromExpr(row.pat),
            .ty = if (!row.ty.isNone()) .some(try self.lowerExpr(row.ty.unwrap())) else .none(),
            .value = if (!row.value.isNone()) .some(try self.lowerExpr(row.value.unwrap())) else .none(),
            .attrs = try self.mapAttrRange(row.attrs),
            .is_comptime = row.is_comptime,
            .loc = row.loc,
        };
        out_ids[i] = self.ast_unit.exprs.Param.add(self.gpa, mapped);
    }
    return self.ast_unit.exprs.param_pool.pushMany(self.gpa, out_ids);
}

fn lowerKeyValues(self: *Lower, r: cst.RangeOf(cst.KeyValueId)) !ast.RangeKeyValue {
    const items = self.cst_program.exprs.kv_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.KeyValueId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const kv = self.cst_program.exprs.KeyValue.get(items[i]);
        const mapped: ast.Rows.KeyValue = .{
            .key = try self.lowerExpr(kv.key),
            .value = try self.lowerExpr(kv.value),
            .loc = kv.loc,
        };
        out_ids[i] = self.ast_unit.exprs.KeyValue.add(self.gpa, mapped);
    }
    return self.ast_unit.exprs.kv_pool.pushMany(self.gpa, out_ids);
}

fn lowerStructFieldValues(self: *Lower, r: cst.RangeOf(cst.StructFieldValueId)) !ast.RangeStructFieldValue {
    const items = self.cst_program.exprs.sfv_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.StructFieldValueId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const f = self.cst_program.exprs.StructFieldValue.get(items[i]);
        const mapped: ast.Rows.StructFieldValue = .{
            .name = if (!f.name.isNone()) .some(f.name.unwrap()) else .none(),
            .value = try self.lowerExpr(f.value),
            .loc = f.loc,
        };
        out_ids[i] = self.ast_unit.exprs.StructFieldValue.add(self.gpa, mapped);
    }
    return self.ast_unit.exprs.sfv_pool.pushMany(self.gpa, out_ids);
}

fn lowerStructFields(self: *Lower, r: cst.RangeOf(cst.StructFieldId)) !ast.RangeField {
    const items = self.cst_program.exprs.sfield_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.StructFieldId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const f = self.cst_program.exprs.StructField.get(items[i]);
        const mapped: ast.Rows.StructField = .{
            .name = f.name,
            .ty = try self.lowerExpr(f.ty),
            .value = if (!f.value.isNone()) .some(try self.lowerExpr(f.value.unwrap())) else .none(),
            .attrs = try self.mapAttrRange(f.attrs),
            .loc = f.loc,
        };
        out_ids[i] = self.ast_unit.exprs.StructField.add(self.gpa, mapped);
    }
    return self.ast_unit.exprs.sfield_pool.pushMany(self.gpa, out_ids);
}

fn lowerEnumFields(self: *Lower, r: cst.RangeOf(cst.EnumFieldId)) !ast.RangeEnumField {
    const items = self.cst_program.exprs.efield_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.EnumFieldId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const f = self.cst_program.exprs.EnumField.get(items[i]);
        const mapped: ast.Rows.EnumField = .{
            .name = f.name,
            .value = if (!f.value.isNone()) .some(try self.lowerExpr(f.value.unwrap())) else .none(),
            .attrs = try self.mapAttrRange(f.attrs),
            .loc = f.loc,
        };
        out_ids[i] = self.ast_unit.exprs.EnumField.add(self.gpa, mapped);
    }
    return self.ast_unit.exprs.efield_pool.pushMany(self.gpa, out_ids);
}

fn lowerVariantFields(self: *Lower, r: cst.RangeOf(cst.VariantFieldId)) !ast.RangeVariantField {
    const items = self.cst_program.exprs.vfield_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.VariantFieldId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const f = self.cst_program.exprs.VariantField.get(items[i]);
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
        out_ids[i] = self.ast_unit.exprs.VariantField.add(self.gpa, mapped);
    }
    return self.ast_unit.exprs.vfield_pool.pushMany(self.gpa, out_ids);
}

fn lowerExprRange(self: *Lower, r: cst.RangeOf(cst.ExprId)) !ast.RangeExpr {
    const items = self.cst_program.exprs.expr_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.ExprId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) out_ids[i] = try self.lowerExpr(items[i]);
    return self.ast_unit.exprs.expr_pool.pushMany(self.gpa, out_ids);
}

// ---------------- Top-level decls ----------------
fn lowerTopDecls(self: *Lower, r: cst.RangeOf(cst.DeclId)) !ast.RangeDecl {
    const items = self.cst_program.exprs.decl_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.DeclId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) out_ids[i] = try self.lowerTopDecl(items[i]);
    return self.ast_unit.exprs.decl_pool.pushMany(self.gpa, out_ids);
}

fn lowerTopDecl(self: *Lower, id: cst.DeclId) !ast.DeclId {
    const d = self.cst_program.exprs.Decl.get(id);
    const pattern = try self.lowerOptionalPatternFromExpr(d.lhs);
    const value = try self.lowerExpr(d.rhs);
    const ty: ast.OptExprId = if (!d.ty.isNone()) .some(try self.lowerExpr(d.ty.unwrap())) else .none();
    var method_path: ast.OptRangeMethodPathSeg = .none();
    if (!d.method_path.isNone()) {
        const segs = self.cst_program.exprs.method_path_pool.slice(d.method_path.asRange());
        var ids = try self.gpa.alloc(ast.MethodPathSegId, segs.len);
        defer self.gpa.free(ids);

        var i: usize = 0;
        while (i < segs.len) : (i += 1) {
            const seg = self.cst_program.exprs.MethodPathSeg.get(segs[i]);
            const mapped: ast.Rows.MethodPathSeg = .{ .name = seg.name, .loc = seg.loc };
            ids[i] = self.ast_unit.exprs.addMethodPathSeg(mapped);
        }

        const range = self.ast_unit.exprs.method_path_pool.pushMany(self.gpa, ids);
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
    const raw = self.ast_unit.exprs.Decl.add(self.gpa, decl_row);
    _ = self.ast_unit.exprs.decl_pool.push(self.gpa, raw);
    return raw;
}

// ---------------- Statements & Blocks ----------------
fn lowerBlockExpr(self: *Lower, id: cst.ExprId) !ast.ExprId {
    const b = self.cst_program.exprs.get(.Block, id);
    const stmts_range = try self.lowerStmtRangeFromDecls(b.items);
    const row: ast.Rows.Block = .{ .items = stmts_range, .loc = b.loc };
    return self.ast_unit.exprs.add(.Block, row);
}

fn lowerStmtRangeFromDecls(self: *Lower, r: cst.RangeOf(cst.DeclId)) !ast.RangeStmt {
    const decls = self.cst_program.exprs.decl_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.StmtId, decls.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < decls.len) : (i += 1) out_ids[i] = try self.lowerStmtFromDecl(decls[i]);
    return self.ast_unit.stmts.stmt_pool.pushMany(self.gpa, out_ids);
}

fn lowerStmtFromDecl(self: *Lower, id: cst.DeclId) !ast.StmtId {
    const d = self.cst_program.exprs.Decl.get(id);

    // Declaration-like (const or define :=)
    if (d.flags.is_const or (!d.lhs.isNone() and !d.flags.is_assign)) {
        const did = try self.lowerTopDecl(id);
        return self.ast_unit.stmts.add(.Decl, .{ .decl = did });
    }

    // Simple assignment
    if (d.flags.is_assign) {
        const left = try self.lowerExpr(d.lhs.unwrap());
        const right = try self.lowerExpr(d.rhs);
        return self.ast_unit.stmts.add(.Assign, .{ .left = left, .right = right, .loc = d.loc });
    }

    // Compound assigns desugaring: Infix at top-level
    if (self.cst_program.exprs.index.kinds.items[d.rhs.toRaw()] == .Infix) {
        const irow = self.cst_program.exprs.get(.Infix, d.rhs);
        if (try self.tryLowerCompoundAssign(&irow)) |stmt| return stmt;
    }

    // Statement-like RHS
    const kind = self.cst_program.exprs.index.kinds.items[d.rhs.toRaw()];
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

fn tryLowerCompoundAssign(self: *Lower, i: *const cst.Rows.Infix) !?ast.StmtId {
    const op = i.op;
    const L = try self.lowerExpr(i.left);
    const R = try self.lowerExpr(i.right);
    const base_loc = i.loc;
    const mk = struct {
        fn bin(self_: *Lower, left: ast.ExprId, right: ast.ExprId, op2: ast.BinaryOp, wrap: bool, sat: bool, loc: ast.LocId) !ast.ExprId {
            const row: ast.Rows.Binary = .{
                .left = left,
                .right = right,
                .op = op2,
                .wrap = wrap,
                .saturate = sat,
                .loc = loc,
            };
            return self_.ast_unit.exprs.add(.Binary, row);
        }
    };

    return switch (op) {
        .add_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .add, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .sub_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .sub, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .mul_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .mul, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .div_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .div, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .mod_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .mod, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .shl_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .shl, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .shr_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .shr, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .and_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .bit_and, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .or_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .bit_or, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .xor_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .bit_xor, false, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .mul_wrap_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .mul, true, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .add_wrap_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .add, true, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .sub_wrap_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .sub, true, false, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .mul_sat_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .mul, false, true, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .add_sat_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .add, false, true, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .sub_sat_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .sub, false, true, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        .shl_sat_assign => blk: {
            const rhs_expr = try mk.bin(self, L, R, .shl, false, true, base_loc);
            break :blk self.ast_unit.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
        },
        else => null,
    };
}

// ---------------- Expressions ----------------
fn lowerExpr(self: *Lower, id: cst.ExprId) anyerror!ast.ExprId {
    const kind = self.cst_program.exprs.index.kinds.items[id.toRaw()];
    return switch (kind) {
        .Ident => blk: {
            const row = self.cst_program.exprs.get(.Ident, id);
            const mapped: ast.Rows.Ident = .{ .name = row.name, .loc = row.loc };
            break :blk self.ast_unit.exprs.add(.Ident, mapped);
        },
        .Literal => try self.lowerLiteral(id),
        .Prefix => blk: {
            const p = self.cst_program.exprs.get(.Prefix, id);
            switch (p.op) {
                .range, .range_inclusive => {
                    const rr: ast.Rows.Range = .{
                        .start = .none(),
                        .end = .some(try self.lowerExpr(p.right)),
                        .inclusive_right = (p.op == .range_inclusive),
                        .loc = p.loc,
                    };
                    break :blk self.ast_unit.exprs.add(.Range, rr);
                },
                .plus => break :blk self.ast_unit.exprs.add(.Unary, .{
                    .expr = try self.lowerExpr(p.right),
                    .op = .pos,
                    .loc = p.loc,
                }),
                .minus => break :blk self.ast_unit.exprs.add(.Unary, .{
                    .expr = try self.lowerExpr(p.right),
                    .op = .neg,
                    .loc = p.loc,
                }),
                .address_of => break :blk self.ast_unit.exprs.add(.Unary, .{
                    .expr = try self.lowerExpr(p.right),
                    .op = .address_of,
                    .loc = p.loc,
                }),
                .logical_not => break :blk self.ast_unit.exprs.add(.Unary, .{
                    .expr = try self.lowerExpr(p.right),
                    .op = .logical_not,
                    .loc = p.loc,
                }),
            }
        },
        .Infix => try self.lowerInfix(id),
        .Deref => blk: {
            const r = self.cst_program.exprs.get(.Deref, id);
            break :blk self.ast_unit.exprs.add(.Deref, .{
                .expr = try self.lowerExpr(r.expr),
                .loc = r.loc,
            });
        },
        .ArrayLit => blk: {
            const r = self.cst_program.exprs.get(.ArrayLit, id);
            break :blk self.ast_unit.exprs.add(.ArrayLit, .{
                .elems = try self.lowerExprRange(r.elems),
                .loc = r.loc,
            });
        },
        .Tuple => blk: {
            const r = self.cst_program.exprs.get(.Tuple, id);
            if (r.is_type) {
                break :blk self.ast_unit.exprs.add(.TupleType, .{
                    .elems = try self.lowerExprRange(r.elems),
                    .loc = r.loc,
                });
            } else {
                break :blk self.ast_unit.exprs.add(.TupleLit, .{
                    .elems = try self.lowerExprRange(r.elems),
                    .loc = r.loc,
                });
            }
        },
        .MapLit => blk: {
            const r = self.cst_program.exprs.get(.MapLit, id);
            break :blk self.ast_unit.exprs.add(.MapLit, .{
                .entries = try self.lowerKeyValues(r.entries),
                .loc = r.loc,
            });
        },
        .Call => blk: {
            const r = self.cst_program.exprs.get(.Call, id);
            break :blk self.ast_unit.exprs.add(.Call, .{
                .callee = try self.lowerExpr(r.callee),
                .args = try self.lowerExprRange(r.args),
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
            const params = try self.lowerParamRange(f.params);
            const result_ty: ast.OptExprId = if (!f.result_ty.isNone())
                .some(try self.lowerExpr(f.result_ty.unwrap()))
            else
                .none();
            const body: ast.OptExprId = if (!f.body.isNone())
                .some(try self.lowerBlockExpr(f.body.unwrap()))
            else
                .none();
            const row: ast.Rows.FunctionLit = .{
                .params = params,
                .result_ty = result_ty,
                .body = body,
                .raw_asm = if (!f.raw_asm.isNone()) .some(f.raw_asm.unwrap()) else .none(),
                .attrs = try self.mapAttrRange(f.attrs),
                .flags = .{
                    .is_proc = f.flags.is_proc,
                    .is_async = f.flags.is_async,
                    .is_variadic = f.flags.is_variadic,
                    .is_extern = f.flags.is_extern,
                },
                .loc = f.loc,
            };
            break :blk self.ast_unit.exprs.add(.FunctionLit, row);
        },
        .Block => try self.lowerBlockExpr(id),
        .Comptime => blk: {
            const r = self.cst_program.exprs.get(.Comptime, id);
            if (r.is_block) {
                const b = try self.lowerBlockExpr(r.payload);
                break :blk self.ast_unit.exprs.add(.ComptimeBlock, .{ .block = b, .loc = r.loc });
            } else {
                // Wrap expression in a block(expr_stmt)
                const e = try self.lowerExpr(r.payload);
                const stmt = self.ast_unit.stmts.add(.Expr, .{ .expr = e });
                const stmts = self.ast_unit.stmts.stmt_pool.pushMany(self.gpa, &[_]ast.StmtId{stmt});
                const blk_expr = self.ast_unit.exprs.add(.Block, .{ .items = stmts, .loc = r.loc });
                break :blk self.ast_unit.exprs.add(.ComptimeBlock, .{ .block = blk_expr, .loc = r.loc });
            }
        },
        .Code => blk: {
            const r = self.cst_program.exprs.get(.Code, id);
            const b = try self.lowerBlockExpr(r.block);
            break :blk self.ast_unit.exprs.add(.CodeBlock, .{ .block = b, .loc = r.loc });
        },
        .Insert => blk: {
            const r = self.cst_program.exprs.get(.Insert, id);
            break :blk self.ast_unit.exprs.add(.Insert, .{
                .expr = try self.lowerExpr(r.expr),
                .loc = r.loc,
            });
        },
        .Mlir => blk: {
            const r = self.cst_program.exprs.get(.Mlir, id);
            const args_range = if (r.args.isNone())
                ast.RangeExpr.empty()
            else
                try self.lowerExprRange(r.args.asRange());

            const cst_pieces = self.cst_program.exprs.mlir_piece_pool.slice(r.pieces);
            var piece_ids = std.ArrayListUnmanaged(ast.MlirPieceId){};
            defer piece_ids.deinit(self.gpa);
            for (cst_pieces) |pid| {
                const piece = self.cst_program.exprs.MlirPiece.get(pid);
                const new_id = self.ast_unit.exprs.addMlirPiece(.{ .kind = piece.kind, .text = piece.text });
                piece_ids.append(self.gpa, new_id) catch @panic("OOM");
            }
            const piece_range = self.ast_unit.exprs.mlir_piece_pool.pushMany(self.gpa, piece_ids.items);

            break :blk self.ast_unit.exprs.add(.MlirBlock, .{
                .kind = r.kind,
                .text = r.text,
                .pieces = piece_range,
                .args = args_range,
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
            const arms = try self.lowerMatchArms(r.arms);
            break :blk self.ast_unit.exprs.add(.Match, .{
                .expr = try self.lowerExpr(r.expr),
                .arms = arms,
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
            break :blk self.ast_unit.exprs.add(.Defer, .{
                .expr = try self.lowerExpr(r.expr),
                .loc = r.loc,
            });
        },
        .ErrDefer => blk: {
            const r = self.cst_program.exprs.get(.ErrDefer, id);
            break :blk self.ast_unit.exprs.add(.ErrDefer, .{
                .expr = try self.lowerExpr(r.expr),
                .loc = r.loc,
            });
        },
        .ErrUnwrap => blk: {
            const r = self.cst_program.exprs.get(.ErrUnwrap, id);
            break :blk self.ast_unit.exprs.add(.ErrUnwrap, .{
                .expr = try self.lowerExpr(r.expr),
                .loc = r.loc,
            });
        },
        .OptionalUnwrap => blk: {
            const r = self.cst_program.exprs.get(.OptionalUnwrap, id);
            break :blk self.ast_unit.exprs.add(.OptionalUnwrap, .{
                .expr = try self.lowerExpr(r.expr),
                .loc = r.loc,
            });
        },
        .Await => blk: {
            const r = self.cst_program.exprs.get(.Await, id);
            break :blk self.ast_unit.exprs.add(.Await, .{
                .expr = try self.lowerExpr(r.expr),
                .loc = r.loc,
            });
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
            break :blk self.ast_unit.exprs.add(.AsyncBlock, .{
                .body = try self.lowerExpr(r.body),
                .loc = r.loc,
            });
        },
        .Cast => blk: {
            const r = self.cst_program.exprs.get(.Cast, id);
            break :blk self.ast_unit.exprs.add(.Cast, .{
                .expr = try self.lowerExpr(r.expr),
                .ty = try self.lowerExpr(r.ty),
                .kind = r.kind,
                .loc = r.loc,
            });
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
            break :blk self.ast_unit.exprs.add(.Import, .{
                .path = r.path,
                .loc = r.loc,
            });
        },
        .TypeOf => blk: {
            const r = self.cst_program.exprs.get(.TypeOf, id);
            break :blk self.ast_unit.exprs.add(.TypeOf, .{
                .expr = try self.lowerExpr(r.expr),
                .loc = r.loc,
            });
        },

        // Types
        .ArrayType => blk: {
            const t = self.cst_program.exprs.get(.ArrayType, id);
            break :blk self.ast_unit.exprs.add(.ArrayType, .{
                .elem = try self.lowerExpr(t.elem),
                .size = try self.lowerExpr(t.size),
                .loc = t.loc,
            });
        },
        .DynArrayType => blk: {
            const t = self.cst_program.exprs.get(.DynArrayType, id);
            break :blk self.ast_unit.exprs.add(.DynArrayType, .{
                .elem = try self.lowerExpr(t.elem),
                .loc = t.loc,
            });
        },
        .MapType => blk: {
            const t = self.cst_program.exprs.get(.MapType, id);
            break :blk self.ast_unit.exprs.add(.MapType, .{
                .key = try self.lowerExpr(t.key),
                .value = try self.lowerExpr(t.value),
                .loc = t.loc,
            });
        },
        .SliceType => blk: {
            const t = self.cst_program.exprs.get(.SliceType, id);
            break :blk self.ast_unit.exprs.add(.SliceType, .{
                .elem = try self.lowerExpr(t.elem),
                .loc = t.loc,
            });
        },
        .OptionalType => blk: {
            const t = self.cst_program.exprs.get(.OptionalType, id);
            break :blk self.ast_unit.exprs.add(.OptionalType, .{
                .elem = try self.lowerExpr(t.elem),
                .loc = t.loc,
            });
        },
        .ErrorSetType => blk: {
            const t = self.cst_program.exprs.get(.ErrorSetType, id);
            break :blk self.ast_unit.exprs.add(.ErrorSetType, .{
                .err = try self.lowerExpr(t.err),
                .value = try self.lowerExpr(t.value),
                .loc = t.loc,
            });
        },
        .StructType => blk: {
            const t = self.cst_program.exprs.get(.StructType, id);
            break :blk self.ast_unit.exprs.add(.StructType, .{
                .fields = try self.lowerStructFields(t.fields),
                .is_extern = t.is_extern,
                .attrs = try self.mapAttrRange(t.attrs),
                .loc = t.loc,
            });
        },
        .EnumType => blk: {
            const t = self.cst_program.exprs.get(.EnumType, id);
            break :blk self.ast_unit.exprs.add(.EnumType, .{
                .fields = try self.lowerEnumFields(t.fields),
                .discriminant = if (!t.discriminant.isNone())
                    .some(try self.lowerExpr(t.discriminant.unwrap()))
                else
                    .none(),
                .is_extern = t.is_extern,
                .attrs = try self.mapAttrRange(t.attrs),
                .loc = t.loc,
            });
        },
        .VariantLikeType => blk: {
            const t = self.cst_program.exprs.get(.VariantLikeType, id);
            break :blk self.ast_unit.exprs.add(.VariantType, .{
                .fields = try self.lowerVariantFields(t.fields),
                .loc = t.loc,
            });
        },
        .ErrorType => blk: {
            const t = self.cst_program.exprs.get(.ErrorType, id);
            break :blk self.ast_unit.exprs.add(.ErrorType, .{
                .fields = try self.lowerVariantFields(t.fields),
                .loc = t.loc,
            });
        },
        .UnionType => blk: {
            const t = self.cst_program.exprs.get(.UnionType, id);
            break :blk self.ast_unit.exprs.add(.UnionType, .{
                .fields = try self.lowerStructFields(t.fields),
                .is_extern = t.is_extern,
                .attrs = try self.mapAttrRange(t.attrs),
                .loc = t.loc,
            });
        },
        .PointerType => blk: {
            const t = self.cst_program.exprs.get(.PointerType, id);
            break :blk self.ast_unit.exprs.add(.PointerType, .{
                .elem = try self.lowerExpr(t.elem),
                .is_const = t.is_const,
                .loc = t.loc,
            });
        },
        .SimdType => blk: {
            const t = self.cst_program.exprs.get(.SimdType, id);
            break :blk self.ast_unit.exprs.add(.SimdType, .{
                .elem = try self.lowerExpr(t.elem),
                .lanes = try self.lowerExpr(t.lanes),
                .loc = t.loc,
            });
        },
        .ComplexType => blk: {
            const t = self.cst_program.exprs.get(.ComplexType, id);
            break :blk self.ast_unit.exprs.add(.ComplexType, .{
                .elem = try self.lowerExpr(t.elem),
                .loc = t.loc,
            });
        },
        .TensorType => blk: {
            const t = self.cst_program.exprs.get(.TensorType, id);
            break :blk self.ast_unit.exprs.add(.TensorType, .{
                .elem = try self.lowerExpr(t.elem),
                .shape = try self.lowerExprRange(t.shape),
                .loc = t.loc,
            });
        },
        .TypeType => blk: {
            const t = self.cst_program.exprs.get(.TypeType, id);
            break :blk self.ast_unit.exprs.add(.TypeType, .{ .loc = t.loc });
        },
        .AnyType => blk: {
            const t = self.cst_program.exprs.get(.AnyType, id);
            break :blk self.ast_unit.exprs.add(.AnyType, .{ .loc = t.loc });
        },
        .NoreturnType => blk: {
            const t = self.cst_program.exprs.get(.NoreturnType, id);
            break :blk self.ast_unit.exprs.add(.NoreturnType, .{ .loc = t.loc });
        },
    };
}

fn lowerLiteral(self: *Lower, id: cst.ExprId) !ast.ExprId {
    const lit = self.cst_program.exprs.get(.Literal, id);
    // tag_small mapping: 1=int, 2=float, 3=string, 4=char, 5=imag, 6=true, 7=false
    const loc = lit.loc;
    return switch (lit.tag_small) {
        .int => blk: {
            const text = self.cst_program.exprs.strs.get(lit.value);
            const parsed = try self.parseIntLiteralText(text);
            break :blk self.ast_unit.exprs.add(.Literal, .{
                .kind = .int,
                .data = .{ .int = .{
                    .text = lit.value,
                    .value = parsed.value,
                    .base = parsed.base,
                    .valid = parsed.valid,
                } },
                .loc = loc,
            });
        },
        .float => blk_float: {
            const text = self.cst_program.exprs.strs.get(lit.value);
            const parsed = try self.parseFloatLiteralText(text);
            break :blk_float self.ast_unit.exprs.add(.Literal, .{
                .kind = .float,
                .data = .{ .float = .{ .text = lit.value, .value = parsed.value, .valid = parsed.valid } },
                .loc = loc,
            });
        },
        .char => blk: {
            const unescaped_char_val = try self.unescapeChar(self.cst_program.exprs.strs.get(lit.value));
            break :blk self.ast_unit.exprs.add(.Literal, .{
                .kind = .char,
                .data = .{ .char = unescaped_char_val },
                .loc = loc,
            });
        },
        .imaginary => blk_im: {
            const s = self.cst_program.exprs.strs.get(lit.value);
            const trimmed: []const u8 = if (s.len > 0 and s[s.len - 1] == 'i') s[0 .. s.len - 1] else s;
            const parsed = try self.parseFloatLiteralText(trimmed);
            const sid = self.ast_unit.exprs.strs.intern(trimmed);
            break :blk_im self.ast_unit.exprs.add(.Literal, .{
                .kind = .imaginary,
                .data = .{ .imaginary = .{ .text = sid, .value = parsed.value, .valid = parsed.valid } },
                .loc = loc,
            });
        },
        .true => self.ast_unit.exprs.add(.Literal, .{
            .kind = .bool,
            .data = .{ .bool = true },
            .loc = loc,
        }),
        .false => self.ast_unit.exprs.add(.Literal, .{
            .kind = .bool,
            .data = .{ .bool = false },
            .loc = loc,
        }),
        else => blk: {
            // fallback: treat as string
            const str = self.cst_program.exprs.strs.get(lit.value);
            const unescaped = try self.unescapeString(str, lit.tag_small == .raw_string);
            break :blk self.ast_unit.exprs.add(.Literal, .{
                .kind = .string,
                .data = .{ .string = unescaped },
                .loc = loc,
            });
        },
    };
}

fn lowerInfix(self: *Lower, id: cst.ExprId) !ast.ExprId {
    const i = self.cst_program.exprs.get(.Infix, id);
    const L = try self.lowerExpr(i.left);
    const R = try self.lowerExpr(i.right);
    const loc = i.loc;

    // ranges
    if (i.op == .range or i.op == .range_inclusive) {
        return self.ast_unit.exprs.add(.Range, .{
            .start = .some(L),
            .end = .some(R),
            .inclusive_right = (i.op == .range_inclusive),
            .loc = loc,
        });
    }

    // error catch maps to Catch
    if (i.op == .error_catch) {
        return self.ast_unit.exprs.add(.Catch, .{
            .expr = L,
            .binding_name = .none(),
            .binding_loc = .none(),
            .handler = R,
            .loc = loc,
        });
    }

    // orelse maps to Binary(op=orelse)
    if (i.op == .unwrap_orelse) {
        return self.ast_unit.exprs.add(.Binary, .{
            .left = L,
            .right = R,
            .op = .@"orelse",
            .wrap = false,
            .saturate = false,
            .loc = loc,
        });
    }

    // arithmetic/bitwise/logical
    const map_bin = struct {
        const Map = struct { op: ast.BinaryOp, wrap: bool, sat: bool };
        fn m(op: cst.InfixOp) ?Map {
            return switch (op) {
                .add => .{ .op = .add, .wrap = false, .sat = false },
                .sub => .{ .op = .sub, .wrap = false, .sat = false },
                .mul => .{ .op = .mul, .wrap = false, .sat = false },
                .div => .{ .op = .div, .wrap = false, .sat = false },
                .mod => .{ .op = .mod, .wrap = false, .sat = false },
                .shl => .{ .op = .shl, .wrap = false, .sat = false },
                .shr => .{ .op = .shr, .wrap = false, .sat = false },
                .b_and => .{ .op = .bit_and, .wrap = false, .sat = false },
                .b_or => .{ .op = .bit_or, .wrap = false, .sat = false },
                .b_xor => .{ .op = .bit_xor, .wrap = false, .sat = false },
                .eq => .{ .op = .eq, .wrap = false, .sat = false },
                .neq => .{ .op = .neq, .wrap = false, .sat = false },
                .lt => .{ .op = .lt, .wrap = false, .sat = false },
                .lte => .{ .op = .lte, .wrap = false, .sat = false },
                .gt => .{ .op = .gt, .wrap = false, .sat = false },
                .gte => .{ .op = .gte, .wrap = false, .sat = false },
                .logical_and => .{ .op = .logical_and, .wrap = false, .sat = false },
                .logical_or => .{ .op = .logical_or, .wrap = false, .sat = false },
                .add_wrap => .{ .op = .add, .wrap = true, .sat = false },
                .add_sat => .{ .op = .add, .wrap = false, .sat = true },
                .sub_wrap => .{ .op = .sub, .wrap = true, .sat = false },
                .sub_sat => .{ .op = .sub, .wrap = false, .sat = true },
                .mul_wrap => .{ .op = .mul, .wrap = true, .sat = false },
                .mul_sat => .{ .op = .mul, .wrap = false, .sat = true },
                .shl_sat => .{ .op = .shl, .wrap = false, .sat = true },
                else => null,
            };
        }
    };

    if (i.op == .error_union) {
        return self.ast_unit.exprs.add(.ErrorSetType, .{ .err = R, .value = L, .loc = loc });
    }
    if (map_bin.m(i.op)) |mm| {
        return self.ast_unit.exprs.add(.Binary, .{
            .left = L,
            .right = R,
            .op = mm.op,
            .wrap = mm.wrap,
            .saturate = mm.sat,
            .loc = loc,
        });
    }

    // fallback: treat as add
    return self.ast_unit.exprs.add(.Binary, .{
        .left = L,
        .right = R,
        .op = .add,
        .wrap = false,
        .saturate = false,
        .loc = loc,
    });
}

fn lowerMatchArms(self: *Lower, r: cst.RangeOf(cst.MatchArmId)) !ast.RangeMatchArm {
    const items = self.cst_program.exprs.arm_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.MatchArmId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const a = self.cst_program.exprs.MatchArm.get(items[i]);
        const mapped: ast.Rows.MatchArm = .{
            .pattern = try self.lowerPattern(a.pattern),
            .guard = if (!a.guard.isNone()) .some(try self.lowerExpr(a.guard.unwrap())) else .none(),
            .body = try self.lowerExpr(a.body),
            .loc = a.loc,
        };
        out_ids[i] = self.ast_unit.exprs.MatchArm.add(self.gpa, mapped);
    }
    return self.ast_unit.exprs.arm_pool.pushMany(self.gpa, out_ids);
}

// ---------------- Patterns ----------------
fn lowerPattern(self: *Lower, id: cst.PatternId) !ast.PatternId {
    const kind = self.cst_program.pats.index.kinds.items[id.toRaw()];
    return switch (kind) {
        .Wildcard => blk: {
            const w = self.cst_program.pats.get(.Wildcard, id);
            break :blk self.ast_unit.pats.add(.Wildcard, .{ .loc = w.loc });
        },
        .Literal => blk: {
            const p = self.cst_program.pats.get(.Literal, id);
            break :blk self.ast_unit.pats.add(.Literal, .{
                .expr = try self.lowerExpr(p.expr),
                .loc = p.loc,
            });
        },
        .Path => blk: {
            const p = self.cst_program.pats.get(.Path, id);
            const segs = try self.lowerPathSegs(p.segments);
            break :blk self.ast_unit.pats.add(.Path, .{ .segments = segs, .loc = p.loc });
        },
        .Binding => blk: {
            const b = self.cst_program.pats.get(.Binding, id);
            break :blk self.ast_unit.pats.add(.Binding, .{
                .name = b.name,
                .by_ref = b.by_ref,
                .is_mut = b.is_mut,
                .loc = b.loc,
            });
        },
        .Tuple => blk: {
            const t = self.cst_program.pats.get(.Tuple, id);
            const elems = try self.lowerPatRange(t.elems);
            break :blk self.ast_unit.pats.add(.Tuple, .{ .elems = elems, .loc = t.loc });
        },
        .Slice => blk: {
            const s = self.cst_program.pats.get(.Slice, id);
            const elems = try self.lowerPatRange(s.elems);
            break :blk self.ast_unit.pats.add(.Slice, .{
                .elems = elems,
                .has_rest = s.has_rest,
                .rest_index = s.rest_index,
                .rest_binding = if (!s.rest_binding.isNone())
                    .some(try self.lowerPattern(s.rest_binding.unwrap()))
                else
                    .none(),
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
            break :blk self.ast_unit.pats.add(.Or, .{
                .alts = try self.lowerPatRange(o.alts),
                .loc = o.loc,
            });
        },
        .At => blk: {
            const a = self.cst_program.pats.get(.At, id);
            break :blk self.ast_unit.pats.add(.At, .{
                .binder = a.binder,
                .pattern = try self.lowerPattern(a.pattern),
                .loc = a.loc,
            });
        },
    };
}

fn lowerPathSegs(self: *Lower, r: cst.RangeOf(cst.PathSegId)) !ast.RangePathSeg {
    const items = self.cst_program.pats.seg_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.PathSegId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const s = self.cst_program.pats.PathSeg.get(items[i]);
        const mapped: ast.PatRows.PathSeg = .{
            .name = s.name,
            .by_ref = false,
            .is_mut = false,
            .loc = s.loc,
        };
        out_ids[i] = self.ast_unit.pats.PathSeg.add(self.gpa, mapped);
    }
    return self.ast_unit.pats.seg_pool.pushMany(self.gpa, out_ids);
}

fn lowerPatFields(self: *Lower, r: cst.RangeOf(cst.PatFieldId)) anyerror!ast.RangePatField {
    const items = self.cst_program.pats.field_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.PatFieldId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const f = self.cst_program.pats.StructField.get(items[i]);
        const mapped: ast.PatRows.StructField = .{
            .name = f.name,
            .pattern = try self.lowerPattern(f.pattern),
            .loc = f.loc,
        };
        out_ids[i] = self.ast_unit.pats.StructField.add(self.gpa, mapped);
    }
    return self.ast_unit.pats.field_pool.pushMany(self.gpa, out_ids);
}

fn lowerPatRange(self: *Lower, r: cst.RangeOf(cst.PatternId)) anyerror!ast.RangePat {
    const items = self.cst_program.pats.pat_pool.slice(r);
    var out_ids = try self.gpa.alloc(ast.PatternId, items.len);
    defer self.gpa.free(out_ids);
    var i: usize = 0;
    while (i < items.len) : (i += 1) out_ids[i] = try self.lowerPattern(items[i]);
    return self.ast_unit.pats.pat_pool.pushMany(self.gpa, out_ids);
}

fn pathSegsFromTypeExpr(self: *Lower, id: cst.ExprId) !ast.RangePathSeg {
    var segs: std.ArrayList(ast.PathSegId) = .empty;
    defer segs.deinit(self.gpa);

    try self.collectPathSegs(id, &segs);
    return self.ast_unit.pats.seg_pool.pushMany(self.gpa, segs.items);
}
fn collectPathSegs(self: *Lower, id: cst.ExprId, segs: *std.ArrayList(ast.PathSegId)) anyerror!void {
    const kind = self.cst_program.exprs.index.kinds.items[id.toRaw()];
    switch (kind) {
        .Ident => {
            const r = self.cst_program.exprs.get(.Ident, id);
            const mapped: ast.PatRows.PathSeg = .{
                .name = r.name,
                .by_ref = false,
                .is_mut = false,
                .loc = r.loc,
            };
            const pid = self.ast_unit.pats.PathSeg.add(self.gpa, mapped);
            try segs.append(self.gpa, pid);
        },
        .FieldAccess => {
            const r = self.cst_program.exprs.get(.FieldAccess, id);
            try self.collectPathSegs(r.parent, segs);
            const mapped: ast.PatRows.PathSeg = .{
                .name = r.field,
                .by_ref = false,
                .is_mut = false,
                .loc = r.loc,
            };
            const pid = self.ast_unit.pats.PathSeg.add(self.gpa, mapped);
            try segs.append(self.gpa, pid);
        },
        else => {
            // Fallback: ignore non-path-like types (produce empty path)
        },
    }
}

fn lowerOptionalPatternFromExpr(self: *Lower, e: cst.OptExprId) !ast.OptPatternId {
    if (e.isNone()) return .none();
    if (try self.patternFromExpr(e.unwrap())) |pid| return .some(pid);
    return .none();
}

fn patternFromExpr(self: *Lower, id: cst.ExprId) !?ast.PatternId {
    const kind = self.cst_program.exprs.index.kinds.items[id.toRaw()];
    return switch (kind) {
        .Ident => blk: {
            const r = self.cst_program.exprs.get(.Ident, id);
            const name = self.cst_program.exprs.strs.get(r.name);
            if (std.mem.eql(u8, name, "_")) {
                break :blk self.ast_unit.pats.add(.Wildcard, .{ .loc = r.loc });
            } else {
                break :blk self.ast_unit.pats.add(.Binding, .{
                    .name = r.name,
                    .by_ref = false,
                    .is_mut = false,
                    .loc = r.loc,
                });
            }
        },
        .ArrayLit => blk: {
            const a = self.cst_program.exprs.get(.ArrayLit, id);
            const xs = self.cst_program.exprs.expr_pool.slice(a.elems);
            var elem_pats = try self.gpa.alloc(ast.PatternId, xs.len);
            defer self.gpa.free(elem_pats);
            var has_rest = false;
            var rest_idx: u32 = 0;
            var rest_pat: ast.OptPatternId = .none();
            var out_i: usize = 0;
            var i: usize = 0;
            while (i < xs.len) : (i += 1) {
                const ek = self.cst_program.exprs.index.kinds.items[xs[i].toRaw()];
                if (ek == .Prefix) {
                    const p = self.cst_program.exprs.get(.Prefix, xs[i]);
                    if (p.op == .range) {
                        const sub = try self.patternFromExpr(p.right) orelse return null;
                        if (has_rest) {
                            // Multiple rest segments are invalid in slice patterns
                            const loc = self.ast_unit.exprs.locs.get(p.loc);
                            try self.context.diags.addError(loc, .pattern_shape_mismatch, .{});
                            return null;
                        }
                        has_rest = true;
                        rest_idx = @intCast(out_i);
                        rest_pat = .some(sub);
                        continue;
                    }
                }
                const sub = try self.patternFromExpr(xs[i]) orelse return null;
                elem_pats[out_i] = sub;
                out_i += 1;
            }
            const range = self.ast_unit.pats.pat_pool.pushMany(self.gpa, elem_pats[0..out_i]);
            const mapped: ast.PatRows.Slice = .{
                .elems = range,
                .has_rest = has_rest,
                .rest_index = rest_idx,
                .rest_binding = rest_pat,
                .loc = a.loc,
            };
            break :blk self.ast_unit.pats.add(.Slice, mapped);
        },
        .Tuple => blk: {
            const t = self.cst_program.exprs.get(.Tuple, id);
            var out_ids = try self.gpa.alloc(ast.PatternId, t.elems.len);
            defer self.gpa.free(out_ids);
            const elems = self.cst_program.exprs.expr_pool.slice(t.elems);
            var i: usize = 0;
            while (i < elems.len) : (i += 1) {
                const sub = try self.patternFromExpr(elems[i]) orelse return null;
                out_ids[i] = sub;
            }
            const range = self.ast_unit.pats.pat_pool.pushMany(self.gpa, out_ids);
            break :blk self.ast_unit.pats.add(.Tuple, .{ .elems = range, .loc = t.loc });
        },
        .StructLit => blk: {
            const s = self.cst_program.exprs.get(.StructLit, id);
            const fields = self.cst_program.exprs.sfv_pool.slice(s.fields);
            var out_ids = try self.gpa.alloc(ast.PatFieldId, fields.len);
            defer self.gpa.free(out_ids);
            var i: usize = 0;
            while (i < fields.len) : (i += 1) {
                const f = self.cst_program.exprs.StructFieldValue.get(fields[i]);
                if (f.name.isNone()) return null;
                const sub = try self.patternFromExpr(f.value) orelse return null;
                const mapped: ast.PatRows.StructField = .{
                    .name = f.name.unwrap(),
                    .pattern = sub,
                    .loc = f.loc,
                };
                out_ids[i] = self.ast_unit.pats.StructField.add(self.gpa, mapped);
            }
            const range = self.ast_unit.pats.field_pool.pushMany(self.gpa, out_ids);
            if (!s.ty.isNone()) {
                const path = try self.pathSegsFromTypeExpr(s.ty.unwrap());
                const segs = self.ast_unit.pats.seg_pool.slice(path);
                if (segs.len >= 2) {
                    break :blk self.ast_unit.pats.add(.VariantStruct, .{
                        .path = path,
                        .fields = range,
                        .has_rest = false,
                        .loc = s.loc,
                    });
                }
            }
            const empty: []const ast.PathSegId = &[_]ast.PathSegId{};
            const path_range = self.ast_unit.pats.seg_pool.pushMany(self.gpa, empty);
            break :blk self.ast_unit.pats.add(.Struct, .{
                .path = path_range,
                .fields = range,
                .has_rest = false,
                .loc = s.loc,
            });
        },
        .Call => blk: {
            // Treat a Call with a path-like callee as a variant-tuple pattern: Type.Case(arg1, arg2, ...)
            const r = self.cst_program.exprs.get(.Call, id);
            const path = try self.pathSegsFromTypeExpr(r.callee);
            const args = self.cst_program.exprs.expr_pool.slice(r.args);
            var pats = try self.gpa.alloc(ast.PatternId, args.len);
            defer self.gpa.free(pats);
            var i: usize = 0;
            while (i < args.len) : (i += 1) {
                const sub = try self.patternFromExpr(args[i]) orelse return null;
                pats[i] = sub;
            }
            const pr = self.ast_unit.pats.pat_pool.pushMany(self.gpa, pats);
            break :blk self.ast_unit.pats.add(.VariantTuple, .{
                .path = path,
                .elems = pr,
                .loc = r.loc,
            });
        },
        .FieldAccess => blk: {
            // Treat a path-like expression as a tag-only pattern (enum member or variant case without payload)
            const r = self.cst_program.exprs.get(.FieldAccess, id);
            const path = try self.pathSegsFromTypeExpr(id);
            break :blk self.ast_unit.pats.add(.Path, .{ .segments = path, .loc = r.loc });
        },
        inline else => |x| {
            const loc_id = self.cst_program.exprs.get(x, id).loc;
            const loc = self.ast_unit.exprs.locs.get(loc_id);
            try self.context.diags.addError(loc, .expected_pattern_on_decl_lhs, .{});
            return null;
        },
    };
}
