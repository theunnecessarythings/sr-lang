const std = @import("std");
const cst = @import("cst_v2.zig");
const ast = @import("ast_v2.zig");
const diagnostics = @import("diagnostics_v2.zig");

// Lowering from CST v2 (DOD) to AST v2 (DOD)
pub const LowerV2 = struct {
    gpa: std.mem.Allocator,
    src: *const cst.CST,
    diags: *diagnostics.Diagnostics,

    out: ast.Ast,

    pub fn init(
        gpa: std.mem.Allocator,
        src: *const cst.CST,
        diags: *diagnostics.Diagnostics,
    ) LowerV2 {
        return .{
            .gpa = gpa,
            .src = src,
            .out = ast.Ast.init(gpa, src.exprs.strs),
            .diags = diags,
        };
    }

    pub fn deinit(self: *LowerV2) void {
        self.out.deinit();
    }

    pub fn run(self: *LowerV2) !ast.Ast {
        var unit: ast.Unit = .empty();

        // package info
        if (!self.src.program.package_name.isNone()) {
            const name = self.mapStr(self.src.program.package_name.unwrap());
            unit.package_name = ast.OptStrId.some(name);
        }
        if (!self.src.program.package_loc.isNone()) {
            const loc = self.mapLoc(self.src.program.package_loc.unwrap());
            unit.package_loc = ast.OptLocId.some(loc);
        }

        // top-level decls -> ast.decl_pool range
        unit.decls = try self.lowerTopDecls(self.src.program.top_decls);

        self.out.unit = unit;
        return self.out;
    }

    // ---------------- Infra: id/loc/range helpers ----------------
    fn mapStr(_: *LowerV2, s: cst.StrId) ast.StrId {
        return ast.StrId.fromRaw(s.toRaw());
    }
    fn mapOptStr(self: *LowerV2, s: cst.OptStrId) ast.OptStrId {
        if (s.isNone()) return ast.OptStrId.none();
        return ast.OptStrId.some(self.mapStr(s.unwrap()));
    }
    fn mapLoc(self: *LowerV2, l: cst.LocId) ast.LocId {
        const loc = self.src.exprs.locs.get(l);
        return self.out.exprs.locs.add(self.gpa, loc);
    }
    fn mapOptLoc(self: *LowerV2, l: cst.OptLocId) ast.OptLocId {
        if (l.isNone()) return ast.OptLocId.none();
        return ast.OptLocId.some(self.mapLoc(l.unwrap()));
    }

    fn mapAttrRange(self: *LowerV2, r: cst.OptRangeAttr) !ast.OptRangeAttr {
        if (r.isNone()) return ast.OptRangeAttr.none();
        const rr = r.asRange();
        const items = self.src.exprs.attr_pool.slice(rr);
        var out_ids = try self.gpa.alloc(ast.AttributeId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const row = self.src.exprs.Attribute.get(items[i].toRaw());
            const mapped: ast.Rows.Attribute = .{
                .name = self.mapStr(row.name),
                .value = if (!row.value.isNone()) ast.OptExprId.some(try self.lowerExpr(row.value.unwrap())) else ast.OptExprId.none(),
                .loc = self.mapLoc(row.loc),
            };
            out_ids[i] = ast.AttributeId.fromRaw(self.out.exprs.Attribute.add(self.gpa, mapped));
        }
        return ast.OptRangeAttr.some(self.out.exprs.attr_pool.pushMany(self.gpa, out_ids));
    }

    fn lowerParamRange(self: *LowerV2, r: cst.RangeOf(cst.ParamId)) !ast.RangeParam {
        const items = self.src.exprs.param_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.ParamId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const row = self.src.exprs.Param.get(items[i].toRaw());
            const mapped: ast.Rows.Param = .{
                .pat = try self.lowerOptionalPatternFromExpr(row.pat),
                .ty = if (!row.ty.isNone()) ast.OptExprId.some(try self.lowerExpr(row.ty.unwrap())) else ast.OptExprId.none(),
                .value = if (!row.value.isNone()) ast.OptExprId.some(try self.lowerExpr(row.value.unwrap())) else ast.OptExprId.none(),
                .attrs = try self.mapAttrRange(row.attrs),
                .loc = self.mapLoc(row.loc),
            };
            out_ids[i] = ast.ParamId.fromRaw(self.out.exprs.Param.add(self.gpa, mapped));
        }
        return self.out.exprs.param_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerKeyValues(self: *LowerV2, r: cst.RangeOf(cst.KeyValueId)) !ast.RangeKeyValue {
        const items = self.src.exprs.kv_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.KeyValueId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const kv = self.src.exprs.KeyValue.get(items[i].toRaw());
            const mapped: ast.Rows.KeyValue = .{ .key = try self.lowerExpr(kv.key), .value = try self.lowerExpr(kv.value), .loc = self.mapLoc(kv.loc) };
            out_ids[i] = ast.KeyValueId.fromRaw(self.out.exprs.KeyValue.add(self.gpa, mapped));
        }
        return self.out.exprs.kv_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerStructFieldValues(self: *LowerV2, r: cst.RangeOf(cst.StructFieldValueId)) !ast.RangeStructFieldValue {
        const items = self.src.exprs.sfv_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.StructFieldValueId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const f = self.src.exprs.StructFieldValue.get(items[i].toRaw());
            const mapped: ast.Rows.StructFieldValue = .{ .name = if (!f.name.isNone()) ast.OptStrId.some(self.mapStr(f.name.unwrap())) else ast.OptStrId.none(), .value = try self.lowerExpr(f.value), .loc = self.mapLoc(f.loc) };
            out_ids[i] = ast.StructFieldValueId.fromRaw(self.out.exprs.StructFieldValue.add(self.gpa, mapped));
        }
        return self.out.exprs.sfv_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerStructFields(self: *LowerV2, r: cst.RangeOf(cst.StructFieldId)) !ast.RangeField {
        const items = self.src.exprs.sfield_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.StructFieldId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const f = self.src.exprs.StructField.get(items[i].toRaw());
            const mapped: ast.Rows.StructField = .{
                .name = self.mapStr(f.name),
                .ty = try self.lowerExpr(f.ty),
                .value = if (!f.value.isNone()) ast.OptExprId.some(try self.lowerExpr(f.value.unwrap())) else ast.OptExprId.none(),
                .attrs = try self.mapAttrRange(f.attrs),
                .loc = self.mapLoc(f.loc),
            };
            out_ids[i] = ast.StructFieldId.fromRaw(self.out.exprs.StructField.add(self.gpa, mapped));
        }
        return self.out.exprs.sfield_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerEnumFields(self: *LowerV2, r: cst.RangeOf(cst.EnumFieldId)) !ast.RangeEnumField {
        const items = self.src.exprs.efield_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.EnumFieldId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const f = self.src.exprs.EnumField.get(items[i].toRaw());
            const mapped: ast.Rows.EnumField = .{
                .name = self.mapStr(f.name),
                .value = if (!f.value.isNone()) ast.OptExprId.some(try self.lowerExpr(f.value.unwrap())) else ast.OptExprId.none(),
                .attrs = try self.mapAttrRange(f.attrs),
                .loc = self.mapLoc(f.loc),
            };
            out_ids[i] = ast.EnumFieldId.fromRaw(self.out.exprs.EnumField.add(self.gpa, mapped));
        }
        return self.out.exprs.efield_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerVariantFields(self: *LowerV2, r: cst.RangeOf(cst.VariantFieldId)) !ast.RangeVariantField {
        const items = self.src.exprs.vfield_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.VariantFieldId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const f = self.src.exprs.VariantField.get(items[i].toRaw());
            const pk: ast.VariantPayloadKind = switch (f.ty_tag) {
                .none => .none,
                .Tuple => .tuple,
                .Struct => .@"struct",
            };
            const mapped: ast.Rows.VariantField = .{
                .name = self.mapStr(f.name),
                .payload_kind = pk,
                .payload_elems = if (f.ty_tag == .Tuple) ast.OptRangeExpr.some(try self.lowerExprRange(f.tuple_elems)) else ast.OptRangeExpr.none(),
                .payload_fields = if (f.ty_tag == .Struct) ast.OptRangeField.some(try self.lowerStructFields(f.struct_fields)) else ast.OptRangeField.none(),
                .value = if (!f.value.isNone()) ast.OptExprId.some(try self.lowerExpr(f.value.unwrap())) else ast.OptExprId.none(),
                .attrs = try self.mapAttrRange(f.attrs),
                .loc = self.mapLoc(f.loc),
            };
            out_ids[i] = ast.VariantFieldId.fromRaw(self.out.exprs.VariantField.add(self.gpa, mapped));
        }
        return self.out.exprs.vfield_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerExprRange(self: *LowerV2, r: cst.RangeOf(cst.ExprId)) !ast.RangeExpr {
        const items = self.src.exprs.expr_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.ExprId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) out_ids[i] = try self.lowerExpr(items[i]);
        return self.out.exprs.expr_pool.pushMany(self.gpa, out_ids);
    }

    // ---------------- Top-level decls ----------------
    fn lowerTopDecls(self: *LowerV2, r: cst.RangeOf(cst.DeclId)) !ast.RangeDecl {
        const items = self.src.exprs.decl_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.DeclId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) out_ids[i] = try self.lowerTopDecl(items[i]);
        return self.out.exprs.decl_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerTopDecl(self: *LowerV2, id: cst.DeclId) !ast.DeclId {
        const d = self.src.exprs.Decl.get(id.toRaw());
        const pattern = try self.lowerOptionalPatternFromExpr(d.lhs);
        const value = try self.lowerExpr(d.rhs);
        const ty = if (!d.ty.isNone()) ast.OptExprId.some(try self.lowerExpr(d.ty.unwrap())) else ast.OptExprId.none();
        const decl_row: ast.Rows.Decl = .{ .pattern = pattern, .value = value, .ty = ty, .flags = .{ .is_const = d.flags.is_const }, .loc = self.mapLoc(d.loc) };
        const raw = self.out.exprs.Decl.add(self.gpa, decl_row);
        const did = ast.DeclId.fromRaw(raw);
        _ = self.out.exprs.decl_pool.push(self.gpa, did);
        return did;
    }

    // ---------------- Statements & Blocks ----------------
    fn lowerBlockExpr(self: *LowerV2, id: cst.ExprId) !ast.ExprId {
        const b = self.src.exprs.get(.Block, id);
        const stmts_range = try self.lowerStmtRangeFromDecls(b.items);
        const row: ast.Rows.Block = .{ .items = stmts_range, .loc = self.mapLoc(b.loc) };
        return self.out.exprs.add(.Block, row);
    }

    fn lowerStmtRangeFromDecls(self: *LowerV2, r: cst.RangeOf(cst.DeclId)) !ast.RangeStmt {
        const decls = self.src.exprs.decl_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.StmtId, decls.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < decls.len) : (i += 1) out_ids[i] = try self.lowerStmtFromDecl(decls[i]);
        return self.out.stmts.stmt_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerStmtFromDecl(self: *LowerV2, id: cst.DeclId) !ast.StmtId {
        const d = self.src.exprs.Decl.get(id.toRaw());

        // Declaration-like (const or define :=)
        if (d.flags.is_const or (!d.lhs.isNone() and !d.flags.is_assign)) {
            const did = try self.lowerTopDecl(id);
            return self.out.stmts.add(.Decl, .{ .decl = did });
        }

        // Simple assignment
        if (d.flags.is_assign) {
            const left = try self.lowerExpr(d.lhs.unwrap());
            const right = try self.lowerExpr(d.rhs);
            return self.out.stmts.add(.Assign, .{ .left = left, .right = right, .loc = self.mapLoc(d.loc) });
        }

        // Compound assigns desugaring: Infix at top-level
        if (self.src.exprs.index.kinds.items[d.rhs.toRaw()] == .Infix) {
            const irow = self.src.exprs.get(.Infix, d.rhs);
            if (try self.tryLowerCompoundAssign(&irow)) |stmt| return stmt;
        }

        // Statement-like RHS
        const kind = self.src.exprs.index.kinds.items[d.rhs.toRaw()];
        return switch (kind) {
            .Return => blk: {
                const r = self.src.exprs.get(.Return, d.rhs);
                const val = if (!r.value.isNone()) ast.OptExprId.some(try self.lowerExpr(r.value.unwrap())) else ast.OptExprId.none();
                break :blk self.out.stmts.add(.Return, .{ .value = val, .loc = self.mapLoc(r.loc) });
            },
            .Insert => blk: {
                const r = self.src.exprs.get(.Insert, d.rhs);
                break :blk self.out.stmts.add(.Insert, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .Break => blk: {
                const r = self.src.exprs.get(.Break, d.rhs);
                break :blk self.out.stmts.add(.Break, .{ .label = self.mapOptStr(r.label), .value = if (!r.value.isNone()) ast.OptExprId.some(try self.lowerExpr(r.value.unwrap())) else ast.OptExprId.none(), .loc = self.mapLoc(r.loc) });
            },
            .Continue => blk: {
                const r = self.src.exprs.get(.Continue, d.rhs);
                break :blk self.out.stmts.add(.Continue, .{ .loc = self.mapLoc(r.loc) });
            },
            .Unreachable => blk: {
                const r = self.src.exprs.get(.Unreachable, d.rhs);
                break :blk self.out.stmts.add(.Unreachable, .{ .loc = self.mapLoc(r.loc) });
            },
            .Defer => blk: {
                const r = self.src.exprs.get(.Defer, d.rhs);
                break :blk self.out.stmts.add(.Defer, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .ErrDefer => blk: {
                const r = self.src.exprs.get(.ErrDefer, d.rhs);
                break :blk self.out.stmts.add(.ErrDefer, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            else => blk: {
                const e = try self.lowerExpr(d.rhs);
                break :blk self.out.stmts.add(.Expr, .{ .expr = e });
            },
        };
    }

    fn tryLowerCompoundAssign(self: *LowerV2, i: *const cst.Rows.Infix) !?ast.StmtId {
        const op = i.op;
        const L = try self.lowerExpr(i.left);
        const R = try self.lowerExpr(i.right);
        const base_loc = self.mapLoc(i.loc);
        const mk = struct {
            fn bin(self_: *LowerV2, left: ast.ExprId, right: ast.ExprId, op2: ast.BinaryOp, wrap: bool, sat: bool, loc: ast.LocId) !ast.ExprId {
                const row: ast.Rows.Binary = .{ .left = left, .right = right, .op = op2, .wrap = wrap, .saturate = sat, .loc = loc };
                return self_.out.exprs.add(.Binary, row);
            }
        };

        return switch (op) {
            .add_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .add, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .sub_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .sub, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .mul_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .mul, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .div_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .div, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .mod_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .mod, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .shl_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .shl, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .shr_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .shr, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .and_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .bit_and, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .or_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .bit_or, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .xor_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .bit_xor, false, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .mul_wrap_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .mul, true, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .add_wrap_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .add, true, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .sub_wrap_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .sub, true, false, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .mul_sat_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .mul, false, true, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .add_sat_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .add, false, true, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .sub_sat_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .sub, false, true, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            .shl_sat_assign => blk: {
                const rhs_expr = try mk.bin(self, L, R, .shl, false, true, base_loc);
                break :blk self.out.stmts.add(.Assign, .{ .left = L, .right = rhs_expr, .loc = base_loc });
            },
            else => null,
        };
    }

    // ---------------- Expressions ----------------
    fn lowerExpr(self: *LowerV2, id: cst.ExprId) anyerror!ast.ExprId {
        const kind = self.src.exprs.index.kinds.items[id.toRaw()];
        return switch (kind) {
            .Ident => blk: {
                const row = self.src.exprs.get(.Ident, id);
                const mapped: ast.Rows.Ident = .{ .name = self.mapStr(row.name), .loc = self.mapLoc(row.loc) };
                break :blk self.out.exprs.add(.Ident, mapped);
            },
            .Literal => try self.lowerLiteral(id),
            .Prefix => blk: {
                const p = self.src.exprs.get(.Prefix, id);
                switch (p.op) {
                    .range, .range_inclusive => {
                        const rr: ast.Rows.Range = .{
                            .start = ast.OptExprId.none(),
                            .end = ast.OptExprId.some(try self.lowerExpr(p.right)),
                            .inclusive_right = (p.op == .range_inclusive),
                            .loc = self.mapLoc(p.loc),
                        };
                        break :blk self.out.exprs.add(.Range, rr);
                    },
                    .plus => break :blk self.out.exprs.add(.Unary, .{ .expr = try self.lowerExpr(p.right), .op = .plus, .loc = self.mapLoc(p.loc) }),
                    .minus => break :blk self.out.exprs.add(.Unary, .{ .expr = try self.lowerExpr(p.right), .op = .minus, .loc = self.mapLoc(p.loc) }),
                    .address_of => break :blk self.out.exprs.add(.Unary, .{ .expr = try self.lowerExpr(p.right), .op = .address_of, .loc = self.mapLoc(p.loc) }),
                    .logical_not => break :blk self.out.exprs.add(.Unary, .{ .expr = try self.lowerExpr(p.right), .op = .logical_not, .loc = self.mapLoc(p.loc) }),
                }
            },
            .Infix => try self.lowerInfix(id),
            .Deref => blk: {
                const r = self.src.exprs.get(.Deref, id);
                break :blk self.out.exprs.add(.Deref, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .ArrayLit => blk: {
                const r = self.src.exprs.get(.ArrayLit, id);
                break :blk self.out.exprs.add(.ArrayLit, .{ .elems = try self.lowerExprRange(r.elems), .loc = self.mapLoc(r.loc) });
            },
            .Tuple => blk: {
                const r = self.src.exprs.get(.Tuple, id);
                if (r.is_type) {
                    break :blk self.out.exprs.add(.TupleType, .{ .elems = try self.lowerExprRange(r.elems), .loc = self.mapLoc(r.loc) });
                } else {
                    break :blk self.out.exprs.add(.TupleLit, .{ .elems = try self.lowerExprRange(r.elems), .loc = self.mapLoc(r.loc) });
                }
            },
            .MapLit => blk: {
                const r = self.src.exprs.get(.MapLit, id);
                break :blk self.out.exprs.add(.MapLit, .{ .entries = try self.lowerKeyValues(r.entries), .loc = self.mapLoc(r.loc) });
            },
            .Call => blk: {
                const r = self.src.exprs.get(.Call, id);
                break :blk self.out.exprs.add(.Call, .{ .callee = try self.lowerExpr(r.callee), .args = try self.lowerExprRange(r.args), .loc = self.mapLoc(r.loc) });
            },
            .IndexAccess => blk: {
                const r = self.src.exprs.get(.IndexAccess, id);
                break :blk self.out.exprs.add(.IndexAccess, .{ .collection = try self.lowerExpr(r.collection), .index = try self.lowerExpr(r.index), .loc = self.mapLoc(r.loc) });
            },
            .FieldAccess => blk: {
                const r = self.src.exprs.get(.FieldAccess, id);
                break :blk self.out.exprs.add(.FieldAccess, .{ .parent = try self.lowerExpr(r.parent), .field = self.mapStr(r.field), .is_tuple = r.is_tuple, .loc = self.mapLoc(r.loc) });
            },
            .StructLit => blk: {
                const r = self.src.exprs.get(.StructLit, id);
                const ty = if (!r.ty.isNone()) ast.OptExprId.some(try self.lowerExpr(r.ty.unwrap())) else ast.OptExprId.none();
                break :blk self.out.exprs.add(.StructLit, .{ .fields = try self.lowerStructFieldValues(r.fields), .ty = ty, .loc = self.mapLoc(r.loc) });
            },
            .Function => blk: {
                const f = self.src.exprs.get(.Function, id);
                const params = try self.lowerParamRange(f.params);
                const result_ty = if (!f.result_ty.isNone()) ast.OptExprId.some(try self.lowerExpr(f.result_ty.unwrap())) else ast.OptExprId.none();
                const body = if (!f.body.isNone()) ast.OptExprId.some(try self.lowerBlockExpr(f.body.unwrap())) else ast.OptExprId.none();
                const row: ast.Rows.FunctionLit = .{
                    .params = params,
                    .result_ty = result_ty,
                    .body = body,
                    .raw_asm = if (!f.raw_asm.isNone()) ast.OptStrId.some(self.mapStr(f.raw_asm.unwrap())) else ast.OptStrId.none(),
                    .attrs = try self.mapAttrRange(f.attrs),
                    .flags = .{ .is_proc = f.flags.is_proc, .is_async = f.flags.is_async, .is_variadic = f.flags.is_variadic, .is_extern = f.flags.is_extern },
                    .loc = self.mapLoc(f.loc),
                };
                break :blk self.out.exprs.add(.FunctionLit, row);
            },
            .Block => try self.lowerBlockExpr(id),
            .Comptime => blk: {
                const r = self.src.exprs.get(.Comptime, id);
                if (r.is_block) {
                    const b = try self.lowerBlockExpr(r.payload);
                    break :blk self.out.exprs.add(.ComptimeBlock, .{ .block = b, .loc = self.mapLoc(r.loc) });
                } else {
                    // Wrap expression in a block(expr_stmt)
                    const e = try self.lowerExpr(r.payload);
                    const stmt = self.out.stmts.add(.Expr, .{ .expr = e });
                    const stmts = self.out.stmts.stmt_pool.pushMany(self.gpa, &[_]ast.StmtId{stmt});
                    const blk_expr = self.out.exprs.add(.Block, .{ .items = stmts, .loc = self.mapLoc(r.loc) });
                    break :blk self.out.exprs.add(.ComptimeBlock, .{ .block = blk_expr, .loc = self.mapLoc(r.loc) });
                }
            },
            .Code => blk: {
                const r = self.src.exprs.get(.Code, id);
                const b = try self.lowerBlockExpr(r.block);
                break :blk self.out.exprs.add(.CodeBlock, .{ .block = b, .loc = self.mapLoc(r.loc) });
            },
            .Insert => blk: {
                const r = self.src.exprs.get(.Insert, id);
                break :blk self.out.exprs.add(.Insert, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .Mlir => blk: {
                const r = self.src.exprs.get(.Mlir, id);
                break :blk self.out.exprs.add(.MlirBlock, .{ .kind = r.kind, .text = self.mapStr(r.text), .loc = self.mapLoc(r.loc) });
            },
            .Return => blk: {
                const r = self.src.exprs.get(.Return, id);
                const val = if (!r.value.isNone()) ast.OptExprId.some(try self.lowerExpr(r.value.unwrap())) else ast.OptExprId.none();
                break :blk self.out.exprs.add(.Return, .{ .value = val, .loc = self.mapLoc(r.loc) });
            },
            .If => blk: {
                const r = self.src.exprs.get(.If, id);
                break :blk self.out.exprs.add(.If, .{ .cond = try self.lowerExpr(r.cond), .then_block = try self.lowerBlockExpr(r.then_block), .else_block = if (!r.else_block.isNone()) ast.OptExprId.some(try self.lowerExpr(r.else_block.unwrap())) else ast.OptExprId.none(), .loc = self.mapLoc(r.loc) });
            },
            .While => blk: {
                const r = self.src.exprs.get(.While, id);
                break :blk self.out.exprs.add(.While, .{ .cond = if (!r.cond.isNone()) ast.OptExprId.some(try self.lowerExpr(r.cond.unwrap())) else ast.OptExprId.none(), .pattern = if (!r.pattern.isNone()) ast.OptPatternId.some(try self.lowerPattern(r.pattern.unwrap())) else ast.OptPatternId.none(), .body = try self.lowerBlockExpr(r.body), .is_pattern = r.is_pattern, .label = self.mapOptStr(r.label), .loc = self.mapLoc(r.loc) });
            },
            .For => blk: {
                const r = self.src.exprs.get(.For, id);
                break :blk self.out.exprs.add(.For, .{ .pattern = try self.lowerPattern(r.pattern), .iterable = try self.lowerExpr(r.iterable), .body = try self.lowerBlockExpr(r.body), .label = self.mapOptStr(r.label), .loc = self.mapLoc(r.loc) });
            },
            .Match => blk: {
                const r = self.src.exprs.get(.Match, id);
                const arms = try self.lowerMatchArms(r.arms);
                break :blk self.out.exprs.add(.Match, .{ .expr = try self.lowerExpr(r.expr), .arms = arms, .loc = self.mapLoc(r.loc) });
            },
            .Break => blk: {
                const r = self.src.exprs.get(.Break, id);
                break :blk self.out.exprs.add(.Break, .{ .label = self.mapOptStr(r.label), .value = if (!r.value.isNone()) ast.OptExprId.some(try self.lowerExpr(r.value.unwrap())) else ast.OptExprId.none(), .loc = self.mapLoc(r.loc) });
            },
            .Continue => blk: {
                const r = self.src.exprs.get(.Continue, id);
                break :blk self.out.exprs.add(.Continue, .{ .loc = self.mapLoc(r.loc) });
            },
            .Unreachable => blk: {
                const r = self.src.exprs.get(.Unreachable, id);
                break :blk self.out.exprs.add(.Unreachable, .{ .loc = self.mapLoc(r.loc) });
            },
            .Null => blk: {
                const r = self.src.exprs.get(.Null, id);
                break :blk self.out.exprs.add(.NullLit, .{ .loc = self.mapLoc(r.loc) });
            },
            .Undefined => blk: {
                const r = self.src.exprs.get(.Undefined, id);
                break :blk self.out.exprs.add(.UndefLit, .{ .loc = self.mapLoc(r.loc) });
            },
            .Defer => blk: {
                const r = self.src.exprs.get(.Defer, id);
                break :blk self.out.exprs.add(.Defer, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .ErrDefer => blk: {
                const r = self.src.exprs.get(.ErrDefer, id);
                break :blk self.out.exprs.add(.ErrDefer, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .ErrUnwrap => blk: {
                const r = self.src.exprs.get(.ErrUnwrap, id);
                break :blk self.out.exprs.add(.ErrUnwrap, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .OptionalUnwrap => blk: {
                const r = self.src.exprs.get(.OptionalUnwrap, id);
                break :blk self.out.exprs.add(.OptionalUnwrap, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .Await => blk: {
                const r = self.src.exprs.get(.Await, id);
                break :blk self.out.exprs.add(.Await, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .Closure => blk: {
                const r = self.src.exprs.get(.Closure, id);
                break :blk self.out.exprs.add(.Closure, .{ .params = try self.lowerParamRange(r.params), .result_ty = if (!r.result_ty.isNone()) ast.OptExprId.some(try self.lowerExpr(r.result_ty.unwrap())) else ast.OptExprId.none(), .body = try self.lowerExpr(r.body), .loc = self.mapLoc(r.loc) });
            },
            .Async => blk: {
                const r = self.src.exprs.get(.Async, id);
                break :blk self.out.exprs.add(.AsyncBlock, .{ .body = try self.lowerExpr(r.body), .loc = self.mapLoc(r.loc) });
            },
            .Cast => blk: {
                const r = self.src.exprs.get(.Cast, id);
                break :blk self.out.exprs.add(.Cast, .{ .expr = try self.lowerExpr(r.expr), .ty = try self.lowerExpr(r.ty), .kind = r.kind, .loc = self.mapLoc(r.loc) });
            },
            .Catch => blk: {
                const r = self.src.exprs.get(.Catch, id);
                break :blk self.out.exprs.add(.Catch, .{ .expr = try self.lowerExpr(r.expr), .binding_name = self.mapOptStr(r.binding_name), .binding_loc = self.mapOptLoc(r.binding_loc), .handler = try self.lowerExpr(r.handler), .loc = self.mapLoc(r.loc) });
            },
            .Import => blk: {
                const r = self.src.exprs.get(.Import, id);
                break :blk self.out.exprs.add(.Import, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },
            .TypeOf => blk: {
                const r = self.src.exprs.get(.TypeOf, id);
                break :blk self.out.exprs.add(.TypeOf, .{ .expr = try self.lowerExpr(r.expr), .loc = self.mapLoc(r.loc) });
            },

            // Types
            .ArrayType => blk: {
                const t = self.src.exprs.get(.ArrayType, id);
                break :blk self.out.exprs.add(.ArrayType, .{ .elem = try self.lowerExpr(t.elem), .size = try self.lowerExpr(t.size), .loc = self.mapLoc(t.loc) });
            },
            .DynArrayType => blk: {
                const t = self.src.exprs.get(.DynArrayType, id);
                break :blk self.out.exprs.add(.DynArrayType, .{ .elem = try self.lowerExpr(t.elem), .loc = self.mapLoc(t.loc) });
            },
            .MapType => blk: {
                const t = self.src.exprs.get(.MapType, id);
                break :blk self.out.exprs.add(.MapType, .{ .key = try self.lowerExpr(t.key), .value = try self.lowerExpr(t.value), .loc = self.mapLoc(t.loc) });
            },
            .SliceType => blk: {
                const t = self.src.exprs.get(.SliceType, id);
                break :blk self.out.exprs.add(.SliceType, .{ .elem = try self.lowerExpr(t.elem), .loc = self.mapLoc(t.loc) });
            },
            .OptionalType => blk: {
                const t = self.src.exprs.get(.OptionalType, id);
                break :blk self.out.exprs.add(.OptionalType, .{ .elem = try self.lowerExpr(t.elem), .loc = self.mapLoc(t.loc) });
            },
            .ErrorSetType => blk: {
                const t = self.src.exprs.get(.ErrorSetType, id);
                break :blk self.out.exprs.add(.ErrorSetType, .{ .err = try self.lowerExpr(t.err), .value = try self.lowerExpr(t.value), .loc = self.mapLoc(t.loc) });
            },
            .StructType => blk: {
                const t = self.src.exprs.get(.StructType, id);
                break :blk self.out.exprs.add(.StructType, .{ .fields = try self.lowerStructFields(t.fields), .is_extern = t.is_extern, .attrs = try self.mapAttrRange(t.attrs), .loc = self.mapLoc(t.loc) });
            },
            .EnumType => blk: {
                const t = self.src.exprs.get(.EnumType, id);
                break :blk self.out.exprs.add(.EnumType, .{ .fields = try self.lowerEnumFields(t.fields), .discriminant = if (!t.discriminant.isNone()) ast.OptExprId.some(try self.lowerExpr(t.discriminant.unwrap())) else ast.OptExprId.none(), .is_extern = t.is_extern, .attrs = try self.mapAttrRange(t.attrs), .loc = self.mapLoc(t.loc) });
            },
            .VariantLikeType => blk: {
                const t = self.src.exprs.get(.VariantLikeType, id);
                break :blk self.out.exprs.add(.VariantType, .{ .fields = try self.lowerVariantFields(t.fields), .loc = self.mapLoc(t.loc) });
            },
            .ErrorType => blk: {
                const t = self.src.exprs.get(.ErrorType, id);
                break :blk self.out.exprs.add(.ErrorType, .{ .fields = try self.lowerVariantFields(t.fields), .loc = self.mapLoc(t.loc) });
            },
            .UnionType => blk: {
                const t = self.src.exprs.get(.UnionType, id);
                break :blk self.out.exprs.add(.UnionType, .{ .fields = try self.lowerStructFields(t.fields), .is_extern = t.is_extern, .attrs = try self.mapAttrRange(t.attrs), .loc = self.mapLoc(t.loc) });
            },
            .PointerType => blk: {
                const t = self.src.exprs.get(.PointerType, id);
                break :blk self.out.exprs.add(.PointerType, .{ .elem = try self.lowerExpr(t.elem), .is_const = t.is_const, .loc = self.mapLoc(t.loc) });
            },
            .SimdType => blk: {
                const t = self.src.exprs.get(.SimdType, id);
                break :blk self.out.exprs.add(.SimdType, .{ .elem = try self.lowerExpr(t.elem), .lanes = try self.lowerExpr(t.lanes), .loc = self.mapLoc(t.loc) });
            },
            .ComplexType => blk: {
                const t = self.src.exprs.get(.ComplexType, id);
                break :blk self.out.exprs.add(.ComplexType, .{ .elem = try self.lowerExpr(t.elem), .loc = self.mapLoc(t.loc) });
            },
            .TensorType => blk: {
                const t = self.src.exprs.get(.TensorType, id);
                break :blk self.out.exprs.add(.TensorType, .{ .elem = try self.lowerExpr(t.elem), .shape = try self.lowerExprRange(t.shape), .loc = self.mapLoc(t.loc) });
            },
            .TypeType => blk: {
                const t = self.src.exprs.get(.TypeType, id);
                break :blk self.out.exprs.add(.TypeType, .{ .loc = self.mapLoc(t.loc) });
            },
            .AnyType => blk: {
                const t = self.src.exprs.get(.AnyType, id);
                break :blk self.out.exprs.add(.AnyType, .{ .loc = self.mapLoc(t.loc) });
            },
            .NoreturnType => blk: {
                const t = self.src.exprs.get(.NoreturnType, id);
                break :blk self.out.exprs.add(.NoreturnType, .{ .loc = self.mapLoc(t.loc) });
            },
        };
    }

    fn lowerLiteral(self: *LowerV2, id: cst.ExprId) !ast.ExprId {
        const lit = self.src.exprs.get(.Literal, id);
        // tag_small mapping: 1=int, 2=float, 3=string, 4=char, 5=imag, 6=true, 7=false (per parser_v2)
        const loc = self.mapLoc(lit.loc);
        return switch (lit.tag_small) {
            1 => self.out.exprs.add(.Literal, .{ .kind = .int, .value = ast.OptStrId.some(self.mapStr(lit.value)), .bool_value = false, .char_value = 0, .loc = loc }),
            2 => self.out.exprs.add(.Literal, .{ .kind = .float, .value = ast.OptStrId.some(self.mapStr(lit.value)), .bool_value = false, .char_value = 0, .loc = loc }),
            3 => self.out.exprs.add(.Literal, .{ .kind = .string, .value = ast.OptStrId.some(self.mapStr(lit.value)), .bool_value = false, .char_value = 0, .loc = loc }),
            4 => blk: {
                // character literal; extract first codepoint if possible from source string
                const s = self.src.exprs.strs.get(lit.value);
                var ch: u32 = 0;
                // naive: assume like 'x' or escaped; best-effort
                if (s.len >= 3) {
                    // take first byte inside quotes
                    ch = s[1];
                }
                break :blk self.out.exprs.add(.Literal, .{ .kind = .char, .value = ast.OptStrId.none(), .bool_value = false, .char_value = ch, .loc = loc });
            },
            5 => blk_im: {
                // imaginary literal like 2i -> treat as integer literal "2" for typing
                const s = self.src.exprs.strs.get(lit.value);
                const trimmed: []const u8 = if (s.len > 0 and s[s.len - 1] == 'i') s[0 .. s.len - 1] else s;
                const sid = self.out.exprs.strs.intern(trimmed);
                break :blk_im self.out.exprs.add(.Literal, .{ .kind = .int, .value = ast.OptStrId.some(sid), .bool_value = false, .char_value = 0, .loc = loc });
            },
            6 => self.out.exprs.add(.Literal, .{ .kind = .bool, .value = ast.OptStrId.none(), .bool_value = true, .char_value = 0, .loc = loc }),
            7 => self.out.exprs.add(.Literal, .{ .kind = .bool, .value = ast.OptStrId.none(), .bool_value = false, .char_value = 0, .loc = loc }),
            else => self.out.exprs.add(.Literal, .{ .kind = .string, .value = ast.OptStrId.some(self.mapStr(lit.value)), .bool_value = false, .char_value = 0, .loc = loc }),
        };
    }

    fn lowerInfix(self: *LowerV2, id: cst.ExprId) !ast.ExprId {
        const i = self.src.exprs.get(.Infix, id);
        const L = try self.lowerExpr(i.left);
        const R = try self.lowerExpr(i.right);
        const loc = self.mapLoc(i.loc);

        // ranges
        if (i.op == .range or i.op == .range_inclusive) {
            return self.out.exprs.add(.Range, .{ .start = ast.OptExprId.some(L), .end = ast.OptExprId.some(R), .inclusive_right = (i.op == .range_inclusive), .loc = loc });
        }

        // error catch maps to Catch
        if (i.op == .error_catch) {
            return self.out.exprs.add(.Catch, .{ .expr = L, .binding_name = ast.OptStrId.none(), .binding_loc = ast.OptLocId.none(), .handler = R, .loc = loc });
        }

        // orelse maps to Binary(op=orelse)
        if (i.op == .unwrap_orelse) {
            return self.out.exprs.add(.Binary, .{ .left = L, .right = R, .op = .@"orelse", .wrap = false, .saturate = false, .loc = loc });
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
            return self.out.exprs.add(.ErrorSetType, .{ .err = R, .value = L, .loc = loc });
        }
        if (map_bin.m(i.op)) |mm| {
            return self.out.exprs.add(.Binary, .{ .left = L, .right = R, .op = mm.op, .wrap = mm.wrap, .saturate = mm.sat, .loc = loc });
        }

        // fallback: treat as add
        return self.out.exprs.add(.Binary, .{ .left = L, .right = R, .op = .add, .wrap = false, .saturate = false, .loc = loc });
    }

    fn lowerMatchArms(self: *LowerV2, r: cst.RangeOf(cst.MatchArmId)) !ast.RangeMatchArm {
        const items = self.src.exprs.arm_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.MatchArmId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const a = self.src.exprs.MatchArm.get(items[i].toRaw());
            const mapped: ast.Rows.MatchArm = .{
                .pattern = try self.lowerPattern(a.pattern),
                .guard = if (!a.guard.isNone()) ast.OptExprId.some(try self.lowerExpr(a.guard.unwrap())) else ast.OptExprId.none(),
                .body = try self.lowerExpr(a.body),
                .loc = self.mapLoc(a.loc),
            };
            out_ids[i] = ast.MatchArmId.fromRaw(self.out.exprs.MatchArm.add(self.gpa, mapped));
        }
        return self.out.exprs.arm_pool.pushMany(self.gpa, out_ids);
    }

    // ---------------- Patterns ----------------
    fn lowerPattern(self: *LowerV2, id: cst.PatternId) !ast.PatternId {
        const kind = self.src.pats.index.kinds.items[id.toRaw()];
        return switch (kind) {
            .Wildcard => blk: {
                const w = self.src.pats.get(.Wildcard, id);
                break :blk self.out.pats.add(.Wildcard, .{ .loc = self.mapLoc(w.loc) });
            },
            .Literal => blk: {
                const p = self.src.pats.get(.Literal, id);
                break :blk self.out.pats.add(.Literal, .{ .expr = try self.lowerExpr(p.expr), .loc = self.mapLoc(p.loc) });
            },
            .Path => blk: {
                const p = self.src.pats.get(.Path, id);
                const segs = try self.lowerPathSegs(p.segments);
                break :blk self.out.pats.add(.Path, .{ .segments = segs, .loc = self.mapLoc(p.loc) });
            },
            .Binding => blk: {
                const b = self.src.pats.get(.Binding, id);
                break :blk self.out.pats.add(.Binding, .{ .name = self.mapStr(b.name), .by_ref = b.by_ref, .is_mut = b.is_mut, .loc = self.mapLoc(b.loc) });
            },
            .Tuple => blk: {
                const t = self.src.pats.get(.Tuple, id);
                const elems = try self.lowerPatRange(t.elems);
                break :blk self.out.pats.add(.Tuple, .{ .elems = elems, .loc = self.mapLoc(t.loc) });
            },
            .Slice => blk: {
                const s = self.src.pats.get(.Slice, id);
                const elems = try self.lowerPatRange(s.elems);
                const rest = if (!s.rest_binding.isNone()) ast.OptPatternId.some(try self.lowerPattern(s.rest_binding.unwrap())) else ast.OptPatternId.none();
                break :blk self.out.pats.add(.Slice, .{ .elems = elems, .has_rest = s.has_rest, .rest_index = s.rest_index, .rest_binding = rest, .loc = self.mapLoc(s.loc) });
            },
            .Struct => blk: {
                const s = self.src.pats.get(.Struct, id);
                break :blk self.out.pats.add(.Struct, .{ .path = try self.lowerPathSegs(s.path), .fields = try self.lowerPatFields(s.fields), .has_rest = s.has_rest, .loc = self.mapLoc(s.loc) });
            },
            .VariantTuple => blk: {
                const v = self.src.pats.get(.VariantTuple, id);
                break :blk self.out.pats.add(.VariantTuple, .{ .path = try self.lowerPathSegs(v.path), .elems = try self.lowerPatRange(v.elems), .loc = self.mapLoc(v.loc) });
            },
            .VariantStruct => blk: {
                const v = self.src.pats.get(.VariantStruct, id);
                break :blk self.out.pats.add(.VariantStruct, .{ .path = try self.lowerPathSegs(v.path), .fields = try self.lowerPatFields(v.fields), .has_rest = v.has_rest, .loc = self.mapLoc(v.loc) });
            },
            .Range => blk: {
                const r = self.src.pats.get(.Range, id);
                break :blk self.out.pats.add(.Range, .{ .start = if (!r.start.isNone()) ast.OptExprId.some(try self.lowerExpr(r.start.unwrap())) else ast.OptExprId.none(), .end = if (!r.end.isNone()) ast.OptExprId.some(try self.lowerExpr(r.end.unwrap())) else ast.OptExprId.none(), .inclusive_right = r.inclusive_right, .loc = self.mapLoc(r.loc) });
            },
            .Or => blk: {
                const o = self.src.pats.get(.Or, id);
                break :blk self.out.pats.add(.Or, .{ .alts = try self.lowerPatRange(o.alts), .loc = self.mapLoc(o.loc) });
            },
            .At => blk: {
                const a = self.src.pats.get(.At, id);
                break :blk self.out.pats.add(.At, .{ .binder = self.mapStr(a.binder), .pattern = try self.lowerPattern(a.pattern), .loc = self.mapLoc(a.loc) });
            },
        };
    }

    fn lowerPathSegs(self: *LowerV2, r: cst.RangeOf(cst.PathSegId)) !ast.RangePathSeg {
        const items = self.src.pats.seg_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.PathSegId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const s = self.src.pats.PathSeg.get(items[i].toRaw());
            const mapped: ast.PatRows.PathSeg = .{ .name = self.mapStr(s.name), .by_ref = false, .is_mut = false, .loc = self.mapLoc(s.loc) };
            out_ids[i] = ast.PathSegId.fromRaw(self.out.pats.PathSeg.add(self.gpa, mapped));
        }
        return self.out.pats.seg_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerPatFields(self: *LowerV2, r: cst.RangeOf(cst.PatFieldId)) anyerror!ast.RangePatField {
        const items = self.src.pats.field_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.PatFieldId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) {
            const f = self.src.pats.StructField.get(items[i].toRaw());
            const mapped: ast.PatRows.StructField = .{ .name = self.mapStr(f.name), .pattern = try self.lowerPattern(f.pattern), .loc = self.mapLoc(f.loc) };
            out_ids[i] = ast.PatFieldId.fromRaw(self.out.pats.StructField.add(self.gpa, mapped));
        }
        return self.out.pats.field_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerPatRange(self: *LowerV2, r: cst.RangeOf(cst.PatternId)) anyerror!ast.RangePat {
        const items = self.src.pats.pat_pool.slice(r);
        var out_ids = try self.gpa.alloc(ast.PatternId, items.len);
        defer self.gpa.free(out_ids);
        var i: usize = 0;
        while (i < items.len) : (i += 1) out_ids[i] = try self.lowerPattern(items[i]);
        return self.out.pats.pat_pool.pushMany(self.gpa, out_ids);
    }

    fn lowerOptionalPatternFromExpr(self: *LowerV2, e: cst.OptExprId) !ast.OptPatternId {
        if (e.isNone()) return ast.OptPatternId.none();
        if (try self.patternFromExpr(e.unwrap())) |pid| return ast.OptPatternId.some(pid);
        return ast.OptPatternId.none();
    }

    fn patternFromExpr(self: *LowerV2, id: cst.ExprId) !?ast.PatternId {
        const kind = self.src.exprs.index.kinds.items[id.toRaw()];
        return switch (kind) {
            .Ident => blk: {
                const r = self.src.exprs.get(.Ident, id);
                const name = self.src.exprs.strs.get(r.name);
                if (std.mem.eql(u8, name, "_")) {
                    break :blk self.out.pats.add(.Wildcard, .{ .loc = self.mapLoc(r.loc) });
                } else {
                    break :blk self.out.pats.add(.Binding, .{ .name = self.mapStr(r.name), .by_ref = false, .is_mut = false, .loc = self.mapLoc(r.loc) });
                }
            },
            .Tuple => blk: {
                const t = self.src.exprs.get(.Tuple, id);
                var out_ids = try self.gpa.alloc(ast.PatternId, t.elems.len);
                defer self.gpa.free(out_ids);
                const elems = self.src.exprs.expr_pool.slice(t.elems);
                var i: usize = 0;
                while (i < elems.len) : (i += 1) {
                    const sub = try self.patternFromExpr(elems[i]) orelse return null;
                    out_ids[i] = sub;
                }
                const range = self.out.pats.pat_pool.pushMany(self.gpa, out_ids);
                break :blk self.out.pats.add(.Tuple, .{ .elems = range, .loc = self.mapLoc(t.loc) });
            },
            inline else => |x| {
                const loc_id = self.mapLoc(self.src.exprs.get(x, id).loc);
                const loc = self.out.exprs.locs.get(loc_id);
                try self.diags.addError(loc, .expected_pattern_on_decl_lhs, .{});
                return null;
            },
        };
    }
};
