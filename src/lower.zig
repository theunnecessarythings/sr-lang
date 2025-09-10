const std = @import("std");
const cst = @import("cst.zig");
const ast = @import("ast.zig");
const List = std.array_list.Managed;
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const Loc = @import("lexer.zig").Token.Loc;

// Lowering from CST to AST
// This pass converts parsed CST into the new AST shape.
pub const Lower = struct {
    allocator: std.mem.Allocator,
    diags: *Diagnostics,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics) Lower {
        return .{ .allocator = allocator, .diags = diags };
    }

    pub fn run(self: *Lower, program: *const cst.Program) !ast.Unit {
        var decls = List(ast.Decl).init(self.allocator);
        for (program.decls.items) |*d| {
            const lowered = try self.lowerTopDecl(d);
            try decls.append(lowered);
        }
        return .{ .decls = decls, .package = try self.lowerPackage(program.package) };
    }

    fn list(self: *Lower, comptime T: type) List(T) {
        return List(T).init(self.allocator);
    }

    fn alloc(self: *Lower, comptime T: type, value: T) !*T {
        const ptr = try self.allocator.create(T);
        ptr.* = value;
        return ptr;
    }

    inline fn mergeLoc(a: Loc, b: Loc) Loc {
        return .{ .start = if (a.start <= b.start) a.start else b.start, .end = if (a.end >= b.end) a.end else b.end };
    }

    fn locOfCstExpr(e: *const cst.Expr) Loc {
        return switch (e.*) {
            .Comptime => |ct| switch (ct) {
                .Block => |blk| blk.loc,
                .Expr => |inner| locOfCstExpr(inner),
            },
            .BuiltinType => |b| switch (b) {
                inline else => |x| x.loc,
            },
            inline else => |x| x.loc,
        };
    }

    fn lowerTopDecl(self: *Lower, d: *const cst.Decl) !ast.Decl {
        const binding = try self.lowerOptionalPatternFromExpr(d.lhs);
        const value = try self.lowerExpr(d.rhs);
        const ty = if (d.ty) |t| try self.lowerExpr(t) else null;
        return .{ .binding = binding, .value = value, .ty = ty, .is_const = d.is_const, .loc = d.loc };
    }

    fn lowerPackage(self: *Lower, p: ?cst.PackageDecl) !?ast.PackageDecl {
        _ = self;
        if (p) |pkg| return ast.PackageDecl{ .name = pkg.name, .loc = pkg.loc };
        return null;
    }

    // lowerOptionalBuiltinType removed: types lower generically via lowerExpr now

    fn lowerBuiltinTypeFromExpr(self: *Lower, e: *const cst.Expr) !?*ast.BuiltinType {
        return switch (e.*) {
            .BuiltinType => |b| try self.lowerBuiltinType(&b),
            else => null,
        };
    }

    fn lowerBuiltinTypeValue(self: *Lower, b: *const cst.BuiltinType) !ast.BuiltinType {
        return switch (b.*) {
            .Array => |a| ast.BuiltinType{ .Array = .{ .elem = try self.lowerExpr(a.elem), .size = try self.lowerExpr(a.size), .loc = a.loc } },
            .DynArray => |u| ast.BuiltinType{ .DynArray = .{ .elem = try self.lowerExpr(u.elem), .loc = u.loc } },
            .MapType => |m| ast.BuiltinType{ .MapType = .{ .key = try self.lowerExpr(m.key), .value = try self.lowerExpr(m.value), .loc = m.loc } },
            .Slice => |u| ast.BuiltinType{ .Slice = .{ .elem = try self.lowerExpr(u.elem), .loc = u.loc } },
            .Optional => |u| ast.BuiltinType{ .Optional = .{ .elem = try self.lowerExpr(u.elem), .loc = u.loc } },
            .ErrorSet => |es| ast.BuiltinType{ .ErrorSet = .{ .err = try self.lowerExpr(es.err), .value = try self.lowerExpr(es.value), .loc = es.loc } },
            .Struct => |st| blk: {
                var fields = list(self, ast.StructField);
                for (st.fields.items) |f| {
                    try fields.append(.{
                        .name = f.name,
                        .ty = try self.lowerExpr(f.ty),
                        .value = if (f.value) |v| try self.lowerExpr(v) else null,
                        .loc = f.loc,
                        .attrs = try self.lowerAttrs(f.attrs),
                    });
                }
                break :blk ast.BuiltinType{ .Struct = .{ .fields = fields, .loc = st.loc, .is_extern = st.is_extern, .attrs = try self.lowerAttrs(st.attrs) } };
            },
            .Enum => |en| blk: {
                var fields = list(self, ast.EnumField);
                for (en.fields.items) |f| {
                    try fields.append(.{ .name = f.name, .value = if (f.value) |v| try self.lowerExpr(v) else null, .loc = f.loc, .attrs = try self.lowerAttrs(f.attrs) });
                }
                break :blk ast.BuiltinType{ .Enum = .{ .fields = fields, .discriminant = if (en.discriminant) |d| try self.lowerExpr(d) else null, .is_extern = en.is_extern, .loc = en.loc, .attrs = try self.lowerAttrs(en.attrs) } };
            },
            .Variant => |vr| blk: {
                var fields = list(self, ast.VariantField);
                for (vr.fields.items) |f| {
                    const ty = if (f.ty) |t| switch (t) {
                        .Tuple => |elems| blk2: {
                            var lst = list(self, *ast.Expr);
                            for (elems.items) |e| try lst.append(try self.lowerExpr(e));
                            break :blk2 ast.VariantPayload{ .Tuple = lst };
                        },
                        .Struct => |s_fields| blk3: {
                            var lst = list(self, ast.StructField);
                            for (s_fields.items) |sf| {
                                try lst.append(.{ .name = sf.name, .ty = try self.lowerExpr(sf.ty), .value = if (sf.value) |v| try self.lowerExpr(v) else null, .loc = sf.loc, .attrs = try self.lowerAttrs(sf.attrs) });
                            }
                            break :blk3 ast.VariantPayload{ .Struct = lst };
                        },
                    } else null;
                    try fields.append(.{ .name = f.name, .ty = ty, .value = if (f.value) |v| try self.lowerExpr(v) else null, .loc = f.loc, .attrs = try self.lowerAttrs(f.attrs) });
                }
                break :blk ast.BuiltinType{ .Variant = .{ .fields = fields, .loc = vr.loc } };
            },
            .Error => |er| blk: {
                var fields = list(self, ast.VariantField);
                for (er.fields.items) |f| {
                    const ty = if (f.ty) |t| switch (t) {
                        .Tuple => |elems| blk2: {
                            var lst = list(self, *ast.Expr);
                            for (elems.items) |e| try lst.append(try self.lowerExpr(e));
                            break :blk2 ast.VariantPayload{ .Tuple = lst };
                        },
                        .Struct => |s_fields| blk3: {
                            var lst = list(self, ast.StructField);
                            for (s_fields.items) |sf| {
                                try lst.append(.{ .name = sf.name, .ty = try self.lowerExpr(sf.ty), .value = if (sf.value) |v| try self.lowerExpr(v) else null, .loc = sf.loc, .attrs = try self.lowerAttrs(sf.attrs) });
                            }
                            break :blk3 ast.VariantPayload{ .Struct = lst };
                        },
                    } else null;
                    try fields.append(.{ .name = f.name, .ty = ty, .value = if (f.value) |v| try self.lowerExpr(v) else null, .loc = f.loc, .attrs = try self.lowerAttrs(f.attrs) });
                }
                break :blk ast.BuiltinType{ .Error = .{ .fields = fields, .loc = er.loc } };
            },
            .Union => |un| blk: {
                var fields = list(self, ast.StructField);
                for (un.fields.items) |f| {
                    try fields.append(.{ .name = f.name, .ty = try self.lowerExpr(f.ty), .value = if (f.value) |v| try self.lowerExpr(v) else null, .loc = f.loc, .attrs = try self.lowerAttrs(f.attrs) });
                }
                break :blk ast.BuiltinType{ .Union = .{ .fields = fields, .loc = un.loc, .is_extern = un.is_extern, .attrs = try self.lowerAttrs(un.attrs) } };
            },
            .Pointer => |p| ast.BuiltinType{ .Pointer = .{ .elem = try self.lowerExpr(p.elem), .is_const = p.is_const, .loc = p.loc } },
            .Simd => |s| ast.BuiltinType{ .Simd = .{ .elem = try self.lowerExpr(s.elem), .lanes = try self.lowerExpr(s.lanes), .loc = s.loc } },
            .Complex => |c| ast.BuiltinType{ .Complex = .{ .elem = try self.lowerExpr(c.elem), .loc = c.loc } },
            .Tensor => |t| blk: {
                var shape = list(self, *ast.Expr);
                for (t.shape.items) |e| try shape.append(try self.lowerExpr(e));
                break :blk ast.BuiltinType{ .Tensor = .{ .elem = try self.lowerExpr(t.elem), .shape = shape, .loc = t.loc } };
            },
            .Type => |tt| ast.BuiltinType{ .Type = .{ .loc = tt.loc } },
            .Any => |aa| ast.BuiltinType{ .Any = .{ .loc = aa.loc } },
            .Noreturn => |nr| ast.BuiltinType{ .Noreturn = .{ .loc = nr.loc } },
        };
    }

    fn lowerBuiltinType(self: *Lower, b: *const cst.BuiltinType) !*ast.BuiltinType {
        const out = try self.lowerBuiltinTypeValue(b);
        return try self.alloc(ast.BuiltinType, out);
    }

    fn lowerAttrs(self: *Lower, attrs: ?List(cst.Attribute)) !?List(ast.Attribute) {
        if (attrs) |a| {
            var out = list(self, ast.Attribute);
            for (a.items) |it| try out.append(.{ .name = it.name, .value = if (it.value) |v| try self.lowerExpr(v) else null, .loc = it.loc });
            return out;
        }
        return null;
    }

    fn lowerOptionalPatternFromExpr(self: *Lower, e: ?*cst.Expr) !?*ast.Pattern {
        if (e) |expr| return try self.patternFromExpr(expr) else return null;
    }

    fn patternFromExpr(self: *Lower, e: *const cst.Expr) !?*ast.Pattern {
        return switch (e.*) {
            .Ident => |id| blk: {
                if (std.mem.eql(u8, id.name, "_")) {
                    break :blk try self.alloc(ast.Pattern, .{ .Wildcard = .{ .loc = id.loc } });
                } else {
                    break :blk try self.alloc(ast.Pattern, .{ .Binding = .{ .name = id.name, .by_ref = false, .is_mut = false, .loc = id.loc } });
                }
            },
            .Tuple => |t| blk: {
                var elems = list(self, *ast.Pattern);
                for (t.elems.items) |sube| {
                    if (try self.patternFromExpr(sube)) |p| try elems.append(p) else return null;
                }
                break :blk try self.alloc(ast.Pattern, .{ .Tuple = .{ .elems = elems, .loc = t.loc } });
            },
            else => null,
        };
    }

    fn lowerPattern(self: *Lower, p: *const cst.Pattern) !*ast.Pattern {
        const out = switch (p.*) {
            .Wildcard => |w| ast.Pattern{ .Wildcard = .{ .loc = w.loc } },
            .Literal => |lit| ast.Pattern{ .Literal = try self.lowerExpr(lit) },
            .Path => |path| blk: {
                var segs = list(self, ast.BindingPattern);
                for (path.segments.items) |s| try segs.append(.{ .name = s.name, .by_ref = false, .is_mut = false, .loc = s.loc });
                break :blk ast.Pattern{ .Path = .{ .segments = segs, .loc = path.loc } };
            },
            .Binding => |b| ast.Pattern{ .Binding = .{ .name = b.name, .by_ref = b.by_ref, .is_mut = b.is_mut, .loc = b.loc } },
            .Tuple => |t| blk: {
                var elems = list(self, *ast.Pattern);
                for (t.elems.items) |e| try elems.append(try self.lowerPattern(e));
                break :blk ast.Pattern{ .Tuple = .{ .elems = elems, .loc = t.loc } };
            },
            .Slice => |sl| blk: {
                var elems = list(self, *ast.Pattern);
                for (sl.elems.items) |e| try elems.append(try self.lowerPattern(e));
                break :blk ast.Pattern{ .Slice = .{ .elems = elems, .has_rest = sl.has_rest, .rest_index = sl.rest_index, .rest_binding = if (sl.rest_binding) |rb| try self.lowerPattern(rb) else null, .loc = sl.loc } };
            },
            .Struct => |st| blk: {
                var segs = list(self, ast.BindingPattern);
                for (st.path.items) |s| try segs.append(.{ .name = s.name, .by_ref = false, .is_mut = false, .loc = s.loc });
                var fields = list(self, ast.StructPatternField);
                for (st.fields.items) |f| try fields.append(.{ .name = f.name, .pattern = try self.lowerPattern(f.pattern), .loc = f.loc });
                break :blk ast.Pattern{ .Struct = .{ .path = segs, .fields = fields, .has_rest = st.has_rest, .loc = st.loc } };
            },
            .VariantTuple => |vt| blk: {
                var segs = list(self, ast.BindingPattern);
                for (vt.path.items) |s| try segs.append(.{ .name = s.name, .by_ref = false, .is_mut = false, .loc = s.loc });
                var elems = list(self, *ast.Pattern);
                for (vt.elems.items) |e| try elems.append(try self.lowerPattern(e));
                break :blk ast.Pattern{ .VariantTuple = .{ .path = segs, .elems = elems, .loc = vt.loc } };
            },
            .VariantStruct => |vs| blk: {
                var segs = list(self, ast.BindingPattern);
                for (vs.path.items) |s| try segs.append(.{ .name = s.name, .by_ref = false, .is_mut = false, .loc = s.loc });
                var fields = list(self, ast.StructPatternField);
                for (vs.fields.items) |f| try fields.append(.{ .name = f.name, .pattern = try self.lowerPattern(f.pattern), .loc = f.loc });
                break :blk ast.Pattern{ .VariantStruct = .{ .path = segs, .fields = fields, .has_rest = vs.has_rest, .loc = vs.loc } };
            },
            .Range => |r| ast.Pattern{ .Range = .{ .start = if (r.start) |s| try self.lowerExpr(s) else null, .end = if (r.end) |e2| try self.lowerExpr(e2) else null, .inclusive_right = r.inclusive_right, .loc = r.loc } },
            .Or => |o| blk: {
                var alts = list(self, *ast.Pattern);
                for (o.alts.items) |e| try alts.append(try self.lowerPattern(e));
                break :blk ast.Pattern{ .Or = .{ .alts = alts, .loc = o.loc } };
            },
            .At => |a| ast.Pattern{ .At = .{ .binder = a.binder, .pattern = try self.lowerPattern(a.pattern), .loc = a.loc } },
        };
        return try self.alloc(ast.Pattern, out);
    }

    fn lowerBlock(self: *Lower, b: *const cst.Block) !ast.Block {
        var items = list(self, ast.Statement);
        for (b.items.items) |*d| {
            const stmt = try self.lowerStmtFromDecl(d);
            try items.append(stmt);
        }
        return .{ .items = items, .loc = b.loc };
    }

    fn lowerStmtFromDecl(self: *Lower, d: *const cst.Decl) !ast.Statement {
        if (d.is_const) {
            const td = try self.lowerTopDecl(d);
            return .{ .Decl = td };
        }

        if (d.is_assign or d.lhs != null) {
            // Treat as assignment when we have a lhs in a block context
            const left = if (d.lhs) |l| try self.lowerExpr(l) else try self.lowerExpr(d.rhs);
            const right = try self.lowerExpr(d.rhs);
            return .{ .Assign = .{ .left = left, .right = right, .loc = d.loc } };
        }

        // Expression or statement-like RHS
        // Desugar compound assignments like a += b into Assign{ left=a, right=a + b }
        if (d.rhs.* == .Infix) {
            const i = d.rhs.Infix;
            if (try self.tryLowerCompoundAssign(&i)) |stmt| {
                return stmt;
            }
        }

        switch (d.rhs.*) {
            .Return => |r| return .{ .Return = .{ .value = if (r.value) |v| try self.lowerExpr(v) else null, .loc = r.loc } },
            .Break => |b| return .{ .Break = .{ .loc = b.loc, .label = b.label, .value = if (b.value) |v| try self.lowerExpr(v) else null } },
            .Continue => |c| return .{ .Continue = .{ .loc = c.loc } },
            .Unreachable => |u| return .{ .Unreachable = .{ .loc = u.loc } },
            .Defer => |df| return .{ .Defer = .{ .expr = try self.lowerExpr(df.expr), .loc = df.loc } },
            .ErrDefer => |edf| return .{ .ErrDefer = .{ .expr = try self.lowerExpr(edf.expr), .loc = edf.loc } },
            .Insert => |ins| return .{ .Insert = .{ .expr = try self.lowerExpr(ins.expr), .loc = ins.loc } },
            else => {},
        }
        const expr_ptr = try self.lowerExpr(d.rhs);
        return .{ .Expr = expr_ptr.* };
    }

    fn tryLowerCompoundAssign(self: *Lower, i: *const cst.Infix) !?ast.Statement {
        const L = try self.lowerExpr(i.left);
        const R = try self.lowerExpr(i.right);
        const rhs_expr = switch (i.op) {
            .add_assign => ast.Expr{ .InfixAdd = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = false } },
            .sub_assign => ast.Expr{ .InfixSub = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = false } },
            .mul_assign => ast.Expr{ .InfixMul = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = false } },
            .div_assign => ast.Expr{ .InfixDiv = .{ .left = L, .right = R, .loc = i.loc } },
            .mod_assign => ast.Expr{ .InfixMod = .{ .left = L, .right = R, .loc = i.loc } },
            .shl_assign => ast.Expr{ .InfixShl = .{ .left = L, .right = R, .loc = i.loc, .saturate = false } },
            .shr_assign => ast.Expr{ .InfixShr = .{ .left = L, .right = R, .loc = i.loc } },
            .and_assign => ast.Expr{ .InfixBitAnd = .{ .left = L, .right = R, .loc = i.loc } },
            .or_assign => ast.Expr{ .InfixBitOr = .{ .left = L, .right = R, .loc = i.loc } },
            .xor_assign => ast.Expr{ .InfixBitXor = .{ .left = L, .right = R, .loc = i.loc } },
            .mul_wrap_assign => ast.Expr{ .InfixMul = .{ .left = L, .right = R, .loc = i.loc, .wrap = true, .saturate = false } },
            .add_wrap_assign => ast.Expr{ .InfixAdd = .{ .left = L, .right = R, .loc = i.loc, .wrap = true, .saturate = false } },
            .sub_wrap_assign => ast.Expr{ .InfixSub = .{ .left = L, .right = R, .loc = i.loc, .wrap = true, .saturate = false } },
            .mul_sat_assign => ast.Expr{ .InfixMul = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = true } },
            .add_sat_assign => ast.Expr{ .InfixAdd = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = true } },
            .sub_sat_assign => ast.Expr{ .InfixSub = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = true } },
            .shl_sat_assign => ast.Expr{ .InfixShl = .{ .left = L, .right = R, .loc = i.loc, .saturate = true } },
            else => return null,
        };
        return .{ .Assign = .{ .left = L, .right = try self.alloc(ast.Expr, rhs_expr), .loc = i.loc } };
    }

    fn lowerParams(self: *Lower, params: List(cst.Param)) !List(ast.Param) {
        var out = list(self, ast.Param);
        for (params.items) |p| {
            try out.append(.{
                .pat = try self.lowerOptionalPatternFromExpr(p.pat),
                .ty = if (p.ty) |t| try self.lowerExpr(t) else null,
                .value = if (p.value) |v| try self.lowerExpr(v) else null,
                .loc = p.loc,
                .attrs = try self.lowerAttrs(p.attrs),
            });
        }
        return out;
    }

    fn lowerExpr(self: *Lower, e: *const cst.Expr) anyerror!*ast.Expr {
        const out = switch (e.*) {
            .Ident => |id| ast.Expr{ .Identifier = .{ .name = id.name, .loc = id.loc } },
            .Literal => |lit| try lowerLiteral(&lit),
            .BuiltinType => |bt| blk: {
                const v = try self.lowerBuiltinTypeValue(&bt);
                break :blk ast.Expr{ .Type = v };
            },
            .Array => |a| blk: {
                var elems = list(self, *ast.Expr);
                for (a.elems.items) |x| try elems.append(try self.lowerExpr(x));
                break :blk ast.Expr{ .ArrayLit = .{ .elems = elems, .loc = a.loc } };
            },
            .Tuple => |t| blk: {
                var elems = list(self, *ast.Expr);
                for (t.elems.items) |x| try elems.append(try self.lowerExpr(x));
                break :blk ast.Expr{ .TupleLit = .{ .elems = elems, .loc = t.loc } };
            },
            .Map => |m| blk: {
                var entries = list(self, ast.KeyValue);
                for (m.entries.items) |kv| try entries.append(.{ .key = try self.lowerExpr(kv.key), .value = try self.lowerExpr(kv.value), .loc = kv.loc });
                break :blk ast.Expr{ .MapLit = .{ .entries = entries, .loc = m.loc } };
            },
            .Struct => |st| blk: {
                var fields = list(self, ast.StructFieldValue);
                for (st.fields.items) |f| try fields.append(.{ .name = f.name, .value = try self.lowerExpr(f.value), .loc = f.loc });
                break :blk ast.Expr{ .StructLit = .{ .fields = fields, .loc = st.loc } };
            },
            .Call => |c| blk: {
                var args = list(self, *ast.Expr);
                for (c.args.items) |a| try args.append(try self.lowerExpr(a));
                break :blk ast.Expr{ .PostfixCall = .{ .callee = try self.lowerExpr(c.callee), .args = args, .loc = c.loc } };
            },
            .Field => |f| ast.Expr{ .PostfixField = .{ .parent = try self.lowerExpr(f.parent), .field = f.field, .is_tuple = f.is_tuple, .loc = f.loc } },
            .Index => |ix| ast.Expr{ .PostfixIndex = .{ .collection = try self.lowerExpr(ix.collection), .index = try self.lowerExpr(ix.index), .loc = ix.loc } },
            .Deref => |d| ast.Expr{ .PostfixDeref = .{ .expr = try self.lowerExpr(d.expr), .loc = d.loc } },
            .Await => |aw| ast.Expr{ .PostfixAwait = .{ .expr = try self.lowerExpr(aw.expr), .loc = aw.loc } },
            .Prefix => |p| switch (p.op) {
                .plus => ast.Expr{ .UnaryPlus = .{ .right = try self.lowerExpr(p.right), .loc = p.loc } },
                .minus => ast.Expr{ .UnaryMinus = .{ .right = try self.lowerExpr(p.right), .loc = p.loc } },
                .address_of => ast.Expr{ .AddressOf = .{ .right = try self.lowerExpr(p.right), .loc = p.loc } },
                .logical_not => ast.Expr{ .LogicalNot = .{ .right = try self.lowerExpr(p.right), .loc = p.loc } },
                .range => ast.Expr{ .Range = .{ .start = null, .end = try self.lowerExpr(p.right), .inclusive_right = false, .loc = p.loc } },
                .range_inclusive => ast.Expr{ .Range = .{ .start = null, .end = try self.lowerExpr(p.right), .inclusive_right = true, .loc = p.loc } },
            },
            .Infix => |i| try self.lowerInfix(&i),
            .Block => |blk| blk2: {
                const b = try self.lowerBlock(&blk);
                break :blk2 ast.Expr{ .Block = b };
            },
            .If => |iff| blk: {
                const then_b = try self.lowerBlock(&iff.then_block);
                break :blk ast.Expr{ .If = .{ .cond = try self.lowerExpr(iff.cond), .then_block = then_b, .else_block = if (iff.else_block) |e2| try self.lowerExpr(e2) else null, .loc = iff.loc } };
            },
            .While => |w| blk: {
                break :blk ast.Expr{ .While = .{ .cond = if (w.cond) |c| try self.lowerExpr(c) else null, .pattern = if (w.pattern) |p| try self.lowerPattern(p) else null, .body = try self.lowerBlock(&w.body), .loc = w.loc, .is_pattern = w.is_pattern, .label = w.label } };
            },
            .For => |f| blk: {
                break :blk ast.Expr{ .For = .{ .pattern = try self.lowerPattern(f.pattern), .iterable = try self.lowerExpr(f.iterable), .body = try self.lowerBlock(&f.body), .loc = f.loc, .label = f.label } };
            },
            .Match => |m| blk: {
                var arms = list(self, ast.MatchArm);
                for (m.arms.items) |arm| {
                    try arms.append(.{ .pattern = try self.lowerPattern(arm.pattern), .guard = if (arm.guard) |g| try self.lowerExpr(g) else null, .body = try self.lowerExpr(arm.body), .loc = arm.loc });
                }
                break :blk ast.Expr{ .Match = .{ .expr = try self.lowerExpr(m.expr), .arms = arms, .loc = m.loc } };
            },
            .Function => |fnc| blk: {
                const params = try self.lowerParams(fnc.params);
                const result_ty = if (fnc.result_ty) |t| try self.lowerExpr(t) else null;
                const body = if (fnc.body) |b| try self.lowerBlock(&b) else null;
                break :blk ast.Expr{ .FunctionLit = .{
                    .params = params,
                    .result_ty = result_ty,
                    .body = body,
                    .loc = fnc.loc,
                    .is_proc = fnc.is_proc,
                    .is_async = fnc.is_async,
                    .is_variadic = fnc.is_variadic,
                    .is_extern = fnc.is_extern,
                    .raw_asm = fnc.raw_asm,
                    .attrs = try self.lowerAttrs(fnc.attrs),
                } };
            },
            .Closure => |cl| blk: {
                const params = try self.lowerParams(cl.params);
                break :blk ast.Expr{ .Closure = .{ .params = params, .result_ty = if (cl.result_ty) |t| try self.lowerExpr(t) else null, .body = try self.lowerExpr(cl.body), .loc = cl.loc } };
            },
            .Async => |ab| ast.Expr{ .AsyncBlock = .{ .body = try self.lowerExpr(ab.body), .loc = ab.loc } },
            .Cast => |c| switch (c.kind) {
                .normal => ast.Expr{ .CastNormal = .{ .expr = try self.lowerExpr(c.expr), .ty = try self.lowerExpr(c.ty), .loc = c.loc } },
                .bitcast => ast.Expr{ .CastBit = .{ .expr = try self.lowerExpr(c.expr), .ty = try self.lowerExpr(c.ty), .loc = c.loc } },
                .saturate => ast.Expr{ .CastSaturate = .{ .expr = try self.lowerExpr(c.expr), .ty = try self.lowerExpr(c.ty), .loc = c.loc } },
                .wrap => ast.Expr{ .CastWrap = .{ .expr = try self.lowerExpr(c.expr), .ty = try self.lowerExpr(c.ty), .loc = c.loc } },
                .checked => ast.Expr{ .CastChecked = .{ .expr = try self.lowerExpr(c.expr), .ty = try self.lowerExpr(c.ty), .loc = c.loc } },
            },
            .Import => |imp| ast.Expr{ .Import = .{ .expr = try self.lowerExpr(imp.expr), .loc = imp.loc } },
            .TypeOf => |t| ast.Expr{ .TypeOf = .{ .expr = try self.lowerExpr(t.expr), .loc = t.loc } },
            .Catch => |c| blk: {
                const bind = if (c.binding) |b| ast.Identifier{ .name = b.name, .loc = b.loc } else null;
                break :blk ast.Expr{ .InfixCatch = .{ .left = try self.lowerExpr(c.expr), .right = try self.lowerExpr(c.handler), .binding = bind, .loc = c.loc } };
            },
            .Comptime => |ct| switch (ct) {
                .Block => |blk| ast.Expr{ .ComptimeBlock = .{ .block = try self.lowerBlock(&blk), .loc = blk.loc } },
                .Expr => |inner| blk: {
                    var items = list(self, ast.Statement);
                    const inner_expr = try self.lowerExpr(inner);
                    try items.append(.{ .Expr = inner_expr.* });
                    const loc = locOfCstExpr(inner);
                    break :blk ast.Expr{ .ComptimeBlock = .{ .block = .{ .items = items, .loc = loc }, .loc = loc } };
                },
            },
            .Code => |code_blk| ast.Expr{ .CodeBlock = .{ .block = try self.lowerBlock(&code_blk.block), .loc = code_blk.loc } },
            .Mlir => |ml| ast.Expr{ .MlirBlock = .{ .kind = switch (ml.kind) {
                .Module => .Module,
                .Type => .Type,
                .Attribute => .Attribute,
                .Operation => .Operation,
            }, .text = ml.text, .loc = ml.loc } },
            .ErrUnwrap => |eu| ast.Expr{ .PostfixErrorUnwrap = .{ .expr = try self.lowerExpr(eu.expr), .loc = eu.loc } },
            .Null => |n| ast.Expr{ .NullLit = .{ .loc = n.loc } },
            .Unreachable => |u| blk: {
                var items = list(self, ast.Statement);
                try items.append(.{ .Unreachable = .{ .loc = u.loc } });
                break :blk ast.Expr{ .Block = .{ .items = items, .loc = u.loc } };
            },
            .Return => |r| blk: {
                _ = self.diags.addError(r.loc, "'return' not allowed in expression position", .{}) catch {};
                var items = list(self, ast.Statement);
                try items.append(.{ .Return = .{ .value = if (r.value) |v| try self.lowerExpr(v) else null, .loc = r.loc } });
                break :blk ast.Expr{ .Block = .{ .items = items, .loc = r.loc } };
            },
            .Break => |b| blk: {
                _ = self.diags.addError(b.loc, "'break' not allowed in expression position", .{}) catch {};
                var items = list(self, ast.Statement);
                try items.append(.{ .Break = .{ .loc = b.loc, .label = b.label, .value = if (b.value) |v| try self.lowerExpr(v) else null } });
                break :blk ast.Expr{ .Block = .{ .items = items, .loc = b.loc } };
            },
            .Continue => |c| blk: {
                _ = self.diags.addError(c.loc, "'continue' not allowed in expression position", .{}) catch {};
                var items = list(self, ast.Statement);
                try items.append(.{ .Continue = .{ .loc = c.loc } });
                break :blk ast.Expr{ .Block = .{ .items = items, .loc = c.loc } };
            },
            .Defer => |d| blk: {
                _ = self.diags.addError(d.loc, "'defer' not allowed in expression position", .{}) catch {};
                var items = list(self, ast.Statement);
                try items.append(.{ .Defer = .{ .expr = try self.lowerExpr(d.expr), .loc = d.loc } });
                break :blk ast.Expr{ .Block = .{ .items = items, .loc = d.loc } };
            },
            .ErrDefer => |d| blk: {
                _ = self.diags.addError(d.loc, "'errdefer' not allowed in expression position", .{}) catch {};
                var items = list(self, ast.Statement);
                try items.append(.{ .ErrDefer = .{ .expr = try self.lowerExpr(d.expr), .loc = d.loc } });
                break :blk ast.Expr{ .Block = .{ .items = items, .loc = d.loc } };
            },
            .Insert => |ins| blk: {
                _ = self.diags.addError(ins.loc, "'insert' not allowed in expression position", .{}) catch {};
                var items = list(self, ast.Statement);
                try items.append(.{ .Insert = .{ .expr = try self.lowerExpr(ins.expr), .loc = ins.loc } });
                break :blk ast.Expr{ .Block = .{ .items = items, .loc = ins.loc } };
            },
        };
        return try self.alloc(ast.Expr, out);
    }

    fn lowerLiteral(lit: *const cst.Literal) !ast.Expr {
        return switch (lit.kind) {
            .integer_literal => ast.Expr{ .IntLit = .{ .value = lit.value, .loc = lit.loc } },
            .float_literal => ast.Expr{ .FloatLit = .{ .value = lit.value, .loc = lit.loc } },
            .string_literal, .raw_string_literal, .byte_string_literal, .raw_byte_string_literal => ast.Expr{ .StringLit = .{ .value = lit.value, .loc = lit.loc } },
            .char_literal, .byte_char_literal => ast.Expr{ .CharLit = .{ .value = 0, .loc = lit.loc } },
            .keyword_true => ast.Expr{ .BoolLit = .{ .value = true, .loc = lit.loc } },
            .keyword_false => ast.Expr{ .BoolLit = .{ .value = false, .loc = lit.loc } },
            .keyword_null => ast.Expr{ .NullLit = .{ .loc = lit.loc } },
            .keyword_undefined => ast.Expr{ .UndefLit = .{ .loc = lit.loc } },
            else => ast.Expr{ .StringLit = .{ .value = lit.value, .loc = lit.loc } },
        };
    }

    fn lowerInfix(self: *Lower, i: *const cst.Infix) !ast.Expr {
        const L = try self.lowerExpr(i.left);
        const R = try self.lowerExpr(i.right);
        return switch (i.op) {
            .add => .{ .InfixAdd = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = false } },
            .sub => .{ .InfixSub = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = false } },
            .mul => .{ .InfixMul = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = false } },
            .div => .{ .InfixDiv = .{ .left = L, .right = R, .loc = i.loc } },
            .mod => .{ .InfixMod = .{ .left = L, .right = R, .loc = i.loc } },
            .add_wrap => .{ .InfixAdd = .{ .left = L, .right = R, .loc = i.loc, .wrap = true, .saturate = false } },
            .add_sat => .{ .InfixAdd = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = true } },
            .sub_wrap => .{ .InfixSub = .{ .left = L, .right = R, .loc = i.loc, .wrap = true, .saturate = false } },
            .sub_sat => .{ .InfixSub = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = true } },
            .mul_wrap => .{ .InfixMul = .{ .left = L, .right = R, .loc = i.loc, .wrap = true, .saturate = false } },
            .mul_sat => .{ .InfixMul = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = true } },
            .shl => .{ .InfixShl = .{ .left = L, .right = R, .loc = i.loc, .saturate = false } },
            .shl_sat => .{ .InfixShl = .{ .left = L, .right = R, .loc = i.loc, .saturate = true } },
            .shr => .{ .InfixShr = .{ .left = L, .right = R, .loc = i.loc } },
            .b_and => .{ .InfixBitAnd = .{ .left = L, .right = R, .loc = i.loc } },
            .b_or => .{ .InfixBitOr = .{ .left = L, .right = R, .loc = i.loc } },
            .b_xor => .{ .InfixBitXor = .{ .left = L, .right = R, .loc = i.loc } },
            .eq => .{ .InfixEq = .{ .left = L, .right = R, .loc = i.loc } },
            .neq => .{ .InfixNeq = .{ .left = L, .right = R, .loc = i.loc } },
            .lt => .{ .InfixLt = .{ .left = L, .right = R, .loc = i.loc } },
            .lte => .{ .InfixLte = .{ .left = L, .right = R, .loc = i.loc } },
            .gt => .{ .InfixGt = .{ .left = L, .right = R, .loc = i.loc } },
            .gte => .{ .InfixGte = .{ .left = L, .right = R, .loc = i.loc } },
            .logical_and => .{ .InfixLogicalAnd = .{ .left = L, .right = R, .loc = i.loc } },
            .logical_or => .{ .InfixLogicalOr = .{ .left = L, .right = R, .loc = i.loc } },
            .range => .{ .Range = .{ .start = L, .end = R, .inclusive_right = false, .loc = i.loc } },
            .range_inclusive => .{ .Range = .{ .start = L, .end = R, .inclusive_right = true, .loc = i.loc } },
            .unwrap_orelse => .{ .InfixOrelse = .{ .left = L, .right = R, .loc = i.loc } },
            .error_catch => .{ .InfixCatch = .{ .left = L, .right = R, .binding = null, .loc = i.loc } },
            else => .{ .InfixAdd = .{ .left = L, .right = R, .loc = i.loc, .wrap = false, .saturate = false } },
        };
    }
};
