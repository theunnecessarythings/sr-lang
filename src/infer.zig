const std = @import("std");
const ast = @import("ast.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const Loc = @import("lexer.zig").Token.Loc;
const symbols = @import("symbols.zig");
const types = @import("types.zig");

pub const TypeInfo = struct {
    allocator: std.mem.Allocator,
    arena: types.TypeArena,
    expr_types: std.AutoHashMap(*const ast.Expr, types.TypeId),
    decl_types: std.AutoHashMap(*const ast.Decl, types.TypeId),

    pub fn init(allocator: std.mem.Allocator) TypeInfo {
        return .{
            .allocator = allocator,
            .arena = types.TypeArena.init(allocator),
            .expr_types = std.AutoHashMap(*const ast.Expr, types.TypeId).init(allocator),
            .decl_types = std.AutoHashMap(*const ast.Decl, types.TypeId).init(allocator),
        };
    }

    pub fn deinit(self: *TypeInfo) void {
        self.expr_types.deinit();
        self.decl_types.deinit();
        self.arena.deinit();
    }
};

pub const Typer = struct {
    allocator: std.mem.Allocator,
    diags: *Diagnostics,
    symtab: symbols.SymbolTable,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics) Typer {
        return .{ .allocator = allocator, .diags = diags, .symtab = symbols.SymbolTable.init(allocator) };
    }

    pub fn deinit(self: *Typer) void {
        self.symtab.deinit();
    }

    var t_bool: types.TypeId = 0;
    var t_i8: types.TypeId = 0;
    var t_u8: types.TypeId = 0;
    var t_i16: types.TypeId = 0;
    var t_u16: types.TypeId = 0;
    var t_i32: types.TypeId = 0;
    var t_u32: types.TypeId = 0;
    var t_i64: types.TypeId = 0;
    var t_u64: types.TypeId = 0;
    var t_f32: types.TypeId = 0;
    var t_f64: types.TypeId = 0;
    var t_string: types.TypeId = 0;
    var t_void: types.TypeId = 0;
    var t_any: types.TypeId = 0;

    fn typeFromIdentifier(id: []const u8) anyerror!?types.TypeId {
        if (std.mem.eql(u8, id, "bool")) return t_bool;
        if (std.mem.eql(u8, id, "i8")) return t_i8;
        if (std.mem.eql(u8, id, "i16")) return t_i16;
        if (std.mem.eql(u8, id, "i32")) return t_i32;
        if (std.mem.eql(u8, id, "i64")) return t_i64;
        if (std.mem.eql(u8, id, "u8")) return t_u8;
        if (std.mem.eql(u8, id, "u16")) return t_u16;
        if (std.mem.eql(u8, id, "u32")) return t_u32;
        if (std.mem.eql(u8, id, "u64")) return t_u64;
        if (std.mem.eql(u8, id, "f32")) return t_f32;
        if (std.mem.eql(u8, id, "f64")) return t_f64;
        if (std.mem.eql(u8, id, "string")) return t_string;
        if (std.mem.eql(u8, id, "void")) return t_void;
        if (std.mem.eql(u8, id, "any")) return t_any;
        return null;
    }

    pub fn run(self: *Typer, program: *ast.Unit) !TypeInfo {
        var info = TypeInfo.init(self.allocator);

        t_bool = try info.arena.mk(.{ .Bool = {} });
        t_i8 = try info.arena.mk(.{ .I8 = {} });
        t_u8 = try info.arena.mk(.{ .U8 = {} });
        t_i16 = try info.arena.mk(.{ .I16 = {} });
        t_u16 = try info.arena.mk(.{ .U16 = {} });
        t_i32 = try info.arena.mk(.{ .I32 = {} });
        t_u32 = try info.arena.mk(.{ .U32 = {} });
        t_i64 = try info.arena.mk(.{ .I64 = {} });
        t_u64 = try info.arena.mk(.{ .U64 = {} });
        t_f32 = try info.arena.mk(.{ .F32 = {} });
        t_f64 = try info.arena.mk(.{ .F64 = {} });
        t_string = try info.arena.mk(.{ .String = {} });
        t_void = try info.arena.mk(.{ .Void = {} });
        t_any = try info.arena.mk(.{ .Any = {} });

        _ = try self.symtab.push(); // root scope
        defer self.symtab.pop();

        for (program.decls.items) |*d| try self.visitDecl(&info, d);

        return info;
    }

    fn bindPattern(self: *Typer, origin: symbols.SymbolOrigin, p: *const ast.Pattern) void {
        switch (p.*) {
            .Wildcard => {},
            .Binding => |b| {
                const sym = symbols.Symbol{ .name = b.name, .kind = .Var, .loc = b.loc, .origin = origin };
                _ = self.symtab.current().declare(sym) catch {};
            },
            .Tuple => |tup| {
                for (tup.elems.items) |sub| self.bindPattern(origin, sub);
            },
            else => {},
        }
    }

    fn exprLoc(self: *Typer, e: *const ast.Expr) Loc {
        _ = self;
        return switch (e.*) {
            .IntLit => |x| x.loc,
            .FloatLit => |x| x.loc,
            .BoolLit => |x| x.loc,
            .StringLit => |x| x.loc,
            .CharLit => |x| x.loc,
            .NullLit => |x| x.loc,
            .UndefLit => |x| x.loc,
            .Identifier => |x| x.loc,
            .Type => |x| switch (x) {
                inline else => |v| v.loc,
            },
            inline else => |x| x.loc,
        };
    }

    fn typeOfExpr(self: *Typer, info: *TypeInfo, e: *const ast.Expr) anyerror!?types.TypeId {
        const ty = switch (e.*) {
            .IntLit => |_| try info.arena.mk(.{ .I32 = {} }),
            .FloatLit => |_| try info.arena.mk(.{ .F64 = {} }),
            .BoolLit => |_| try info.arena.mk(.{ .Bool = {} }),
            .StringLit => |_| try info.arena.mk(.{ .String = {} }),
            .CharLit => |_| try info.arena.mk(.{ .U32 = {} }),
            .NullLit => |_| null,
            .UndefLit => |_| null,
            .VariantLit => |v| blk_var: {
                if (v.value) |val| {
                    if (try self.typeOfExpr(info, val)) |vt| break :blk_var vt;
                }
                break :blk_var null;
            },
            .EnumLit => |en| blk_enum: {
                if (en.value) |val| {
                    if (try self.typeOfExpr(info, val)) |et| break :blk_enum et;
                }
                break :blk_enum null;
            },
            .InfixCatch => @panic("TODO"),
            .InfixOrelse => |o| blk_orelse: {
                if (try self.typeOfExpr(info, o.left)) |lt| {
                    const t = info.arena.get(lt);
                    if (@as(types.TypeKind, t) == .Optional) {
                        if (try self.typeOfExpr(info, o.right)) |rt| {
                            if (rt == t.Optional.elem) break :blk_orelse rt;
                        }
                    }
                }
                break :blk_orelse null;
            },
            .FunctionLit => |fnc| blk_fn: {
                var param_buf = try self.allocator.alloc(types.TypeId, fnc.params.items.len);
                for (fnc.params.items, 0..) |p, idx| {
                    if (p.ty) |pty| {
                        if (try self.typeFromTypeExpr(info, pty)) |ptid| {
                            param_buf[idx] = ptid;
                        } else break :blk_fn null;
                    } else break :blk_fn null;
                }
                var result_ty_id: types.TypeId = t_void;
                if (fnc.result_ty) |rt| {
                    if (try self.typeFromTypeExpr(info, rt)) |rid| {
                        result_ty_id = rid;
                    } else {
                        break :blk_fn null;
                    }
                }

                const fnty = try info.arena.mk(.{ .Function = .{ .params = param_buf, .result = result_ty_id, .is_variadic = fnc.is_variadic } });
                break :blk_fn fnty;
            },

            .Identifier => |id| blk_ident: {
                if (self.symtab.current().lookup(id.name)) |symbol| {
                    switch (symbol.origin) {
                        .Decl => |decl| {
                            if (info.decl_types.get(decl)) |tid|
                                break :blk_ident tid;

                            if (try self.typeOfExpr(info, decl.value)) |vt| {
                                // Memoize for later uses
                                try info.decl_types.put(decl, vt);
                                break :blk_ident vt;
                            }

                            // If we get here, we truly failed to type the decl’s RHS.
                            _ = self.diags.addError(self.exprLoc(&decl.value.*), "could not infer declaration type", .{}) catch {};
                            return error.TypeInferenceFailed;
                        },
                        .Param => |param| {
                            if (param.ty) |param_ty_expr| {
                                if (try self.typeFromTypeExpr(info, param_ty_expr)) |tid|
                                    break :blk_ident tid;
                            }
                        },
                    }
                }
                // Better message if it’s actually unknown:
                _ = self.diags.addError(self.exprLoc(e), "unknown identifier '{s}'", .{id.name}) catch {};
                return error.TypeInferenceFailed;
            },

            .TupleLit => |t| blk_tup: {
                var elem_tys = try self.allocator.alloc(types.TypeId, t.elems.items.len);
                for (t.elems.items, 0..) |elem, i| {
                    if (try self.typeOfExpr(info, elem)) |et| elem_tys[i] = et else break :blk_tup null;
                }
                break :blk_tup try info.arena.mk(.{ .Tuple = .{ .elems = elem_tys } });
            },
            .ArrayLit => |a| blk_arr: {
                if (a.elems.items.len == 0) break :blk_arr null; // need annotation
                var first_ty: ?types.TypeId = null;
                for (a.elems.items) |elem| {
                    if (try self.typeOfExpr(info, elem)) |et| {
                        if (first_ty) |ft| {
                            if (ft != et) break :blk_arr null; // non-uniform for now
                        } else first_ty = et;
                    } else break :blk_arr null;
                }
                const ety = first_ty.?;
                break :blk_arr try info.arena.mk(.{ .Array = .{ .elem = ety, .len = a.elems.items.len } });
            },
            .MapLit => |_| null,
            .StructLit => |_| null,
            .UnaryPlus => |u| self.typeOfExpr(info, u.right),
            .UnaryMinus => |u| self.typeOfExpr(info, u.right),
            .AddressOf => |u| blk_addr: {
                if (try self.typeOfExpr(info, u.right)) |rt| {
                    break :blk_addr try info.arena.mk(.{ .Ptr = .{ .elem = rt } });
                }
                break :blk_addr null;
            },
            .LogicalNot => |_| try info.arena.mk(.{ .Bool = {} }),
            .Range => |_| null,
            .InfixAdd => |b| blk_bin_add: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_add uty;
                break :blk_bin_add null;
            },
            .InfixSub => |b| blk_bin_sub: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_sub uty;
                break :blk_bin_sub null;
            },
            .InfixMul => |b| blk_bin_mul: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_mul uty;
                break :blk_bin_mul null;
            },
            .InfixDiv => |b| blk_bin_div: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_div uty;
                break :blk_bin_div null;
            },
            .InfixMod => |b| blk_bin_mod: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_mod uty;
                break :blk_bin_mod null;
            },
            .InfixShl => |b| blk_bin_shl: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_shl uty;
                break :blk_bin_shl null;
            },
            .InfixShr => |b| blk_bin_shr: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_shr uty;
                break :blk_bin_shr null;
            },
            .InfixBitAnd => |b| blk_bin_band: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_band uty;
                break :blk_bin_band null;
            },
            .InfixBitOr => |b| blk_bin_bor: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_bor uty;
                break :blk_bin_bor null;
            },
            .InfixBitXor => |b| blk_bin_bxor: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| if (rt) |rty| if (try self.unifyNumeric(info, lty, rty)) |uty| break :blk_bin_bxor uty;
                break :blk_bin_bxor null;
            },
            .InfixEq, .InfixNeq, .InfixLt, .InfixLte, .InfixGt, .InfixGte => try info.arena.mk(.{ .Bool = {} }),
            .InfixLogicalAnd => |b| blk_land: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| {
                    if (lty != t_bool) {
                        _ = self.diags.addError(self.exprLoc(b.left), "left operand of 'and' must be bool", .{}) catch {};
                    }
                }
                if (rt) |rty| {
                    if (rty != t_bool) {
                        _ = self.diags.addError(self.exprLoc(b.right), "right operand of 'and' must be bool", .{}) catch {};
                    }
                }
                break :blk_land t_bool;
            },
            .InfixLogicalOr => |b| blk_lor: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                if (lt) |lty| {
                    if (lty != t_bool) {
                        _ = self.diags.addError(self.exprLoc(b.left), "left operand of 'or' must be bool", .{}) catch {};
                    }
                }
                if (rt) |rty| {
                    if (rty != t_bool) {
                        _ = self.diags.addError(self.exprLoc(b.right), "right operand of 'or' must be bool", .{}) catch {};
                    }
                }
                break :blk_lor t_bool;
            },
            .PostfixErrorUnwrap => |p| self.typeOfExpr(info, p.expr),
            .PostfixOptionalUnwrap => |p| self.typeOfExpr(info, p.expr),
            .PostfixDeref => |p| blk_deref: {
                if (try self.typeOfExpr(info, p.expr)) |pt| {
                    const t = info.arena.get(pt);
                    if (@as(types.TypeKind, t) == .Ptr) break :blk_deref t.Ptr.elem;
                }
                break :blk_deref null;
            },
            .PostfixIndex => |p| blk_idx: {
                const ct = try self.typeOfExpr(info, p.collection);
                if (ct) |cid| {
                    const cty = info.arena.get(cid);
                    switch (@as(types.TypeKind, cty)) {
                        .Array => {
                            if (p.index.* == .Range) {
                                break :blk_idx try info.arena.mk(.{ .Slice = .{ .elem = cty.Array.elem } });
                            } else break :blk_idx cty.Array.elem;
                        },
                        .Slice => break :blk_idx cty.Slice.elem,
                        .String => {
                            if (p.index.* == .Range) {
                                break :blk_idx try info.arena.mk(.{ .String = {} });
                            }
                            break :blk_idx try info.arena.mk(.{ .U32 = {} });
                        },
                        else => {},
                    }
                }
                break :blk_idx null;
            },
            .PostfixField => |p| blk_field: {
                if (p.is_tuple) {
                    if (try self.typeOfExpr(info, p.parent)) |pt| {
                        const tty = info.arena.get(pt);
                        if (@as(types.TypeKind, tty) == .Tuple) {
                            const idx = std.fmt.parseInt(usize, p.field, 10) catch return null;
                            if (idx < tty.Tuple.elems.len) break :blk_field tty.Tuple.elems[idx];
                        }
                    }
                }
                break :blk_field null;
            },
            .PostfixCall => |call| blk_call: {
                if (try self.typeOfExpr(info, call.callee)) |cty| {
                    const ty = info.arena.get(cty);
                    if (@as(types.TypeKind, ty) == .Function) {
                        const params = ty.Function.params;
                        if (!ty.Function.is_variadic and call.args.items.len != params.len) {
                            _ = self.diags.addError(call.loc, "argument count mismatch: expected {}, got {}", .{ params.len, call.args.items.len }) catch {};
                        } else {
                            const upto = @min(params.len, call.args.items.len);
                            for (call.args.items, 0..) |arg, i| if (i < upto) {
                                if (try self.typeOfExpr(info, arg)) |at| {
                                    if (params[i] != at) {
                                        _ = self.diags.addWarning(call.loc, "argument {} type mismatch", .{i}) catch {};
                                    }
                                }
                            };
                        }
                        break :blk_call ty.Function.result;
                    }
                }
                break :blk_call null;
            },
            .PostfixAwait => |p| self.typeOfExpr(info, p.expr),
            .CastNormal => |c| self.typeFromTypeExpr(info, c.ty),
            .CastBit => |c| self.typeFromTypeExpr(info, c.ty),
            .CastSaturate => |c| self.typeFromTypeExpr(info, c.ty),
            .CastWrap => |c| self.typeFromTypeExpr(info, c.ty),
            .CastChecked => |c| self.typeFromTypeExpr(info, c.ty),
            .If => |iff| blk_if: {
                const ct = try self.typeOfExpr(info, iff.cond);
                if (ct) |cid| {
                    if (cid != t_bool)
                        _ = self.diags.addError(self.exprLoc(iff.cond), "if condition must be bool", .{}) catch {};
                }

                const then_ty = (try self.typeOfBlock(info, &iff.then_block)) orelse t_void;
                const else_ty = if (iff.else_block) |eb|
                    (try self.typeOfExpr(info, eb)) orelse t_void
                else
                    t_void;

                // both statement-like -> void
                if (then_ty == t_void and else_ty == t_void) break :blk_if t_void;

                // both value-producing and equal -> that type
                if (then_ty == else_ty) break :blk_if then_ty;

                // (optional) try numeric unification if you want
                if (try self.unifyNumeric(info, then_ty, else_ty)) |uty| break :blk_if uty;

                // Mismatch: report and treat as void so statement use is OK.
                _ = self.diags.addError(self.exprLoc(iff.cond), "if branches have mismatched types", .{}) catch {};
                break :blk_if t_void;
            },
            .While => |w| blk_while: {
                if (w.cond) |c| {
                    const ct = try self.typeOfExpr(info, c);
                    if (ct) |cid| {
                        if (cid != t_bool) _ = self.diags.addError(self.exprLoc(c), "while condition must be bool", .{}) catch {};
                    }
                }
                _ = try self.typeOfBlock(info, &w.body);
                break :blk_while null;
            },
            .For => |f| blk_for: {
                _ = try self.typeOfExpr(info, f.iterable);
                _ = try self.typeOfBlock(info, &f.body);
                break :blk_for null;
            },
            .Match => |m| blk_match: {
                _ = try self.typeOfExpr(info, m.expr);
                var arm_ty: ?types.TypeId = null;
                for (m.arms.items) |arm| {
                    if (try self.typeOfExpr(info, arm.body)) |bt| {
                        if (arm_ty) |prev| {
                            if (prev != bt) arm_ty = null;
                        } else arm_ty = bt;
                    }
                }
                break :blk_match arm_ty;
            },
            .Block => |b| self.typeOfBlock(info, &b),
            .ComptimeBlock => |_| null,
            .CodeBlock => |_| null,
            .AsyncBlock => |ab| self.typeOfExpr(info, ab.body),
            .MlirBlock => |_| null,
            .Closure => |cl| blk_cl: {
                var param_buf = try self.allocator.alloc(types.TypeId, cl.params.items.len);
                for (cl.params.items, 0..) |p, idx| {
                    if (p.ty) |pty| {
                        if (try self.typeFromTypeExpr(info, pty)) |ptid| param_buf[idx] = ptid else break :blk_cl null;
                    } else break :blk_cl null;
                }
                const res = if (cl.result_ty) |rt| try self.typeFromTypeExpr(info, rt) else null;
                if (res) |rid| {
                    _ = try self.typeOfExpr(info, cl.body);
                    break :blk_cl try info.arena.mk(.{ .Function = .{ .params = param_buf, .result = rid } });
                }
                break :blk_cl null;
            },
            .Import => |imp| self.typeOfExpr(info, imp.expr),
            .TypeOf => |t| self.typeOfExpr(info, t.expr),
            .Type => |_| null,
        };

        if (try ty) |tid| {
            try info.expr_types.put(e, tid);
        } else {
            std.debug.print("typeOfExpr: failed to infer type for {s}\n", .{@tagName(e.*)});
            _ = self.diags.addError(self.exprLoc(e), "could not infer expression type", .{}) catch {};
            return error.TypeInferenceFailed;
        }
        return ty;
    }

    fn typeFromTypeExpr(self: *Typer, info: *TypeInfo, e: *const ast.Expr) anyerror!?types.TypeId {
        const ty = switch (e.*) {
            .Identifier => |id| blk_ident: {
                if (try typeFromIdentifier(id.name)) |tid| break :blk_ident tid;
                break :blk_ident null;
            },
            .Type => |*bt| try self.typeFromBuiltin(info, @constCast(bt)),
            .TupleLit => |t| blk: {
                var elems = try self.allocator.alloc(types.TypeId, t.elems.items.len);
                for (t.elems.items, 0..) |elem, i| {
                    if (try self.typeFromTypeExpr(info, elem)) |et| {
                        elems[i] = et;
                    } else break :blk null;
                }
                break :blk try info.arena.mk(.{ .Tuple = .{ .elems = elems } });
            },
            .FunctionLit => |fnc| blk: {
                var param_buf = try self.allocator.alloc(types.TypeId, fnc.params.items.len);
                for (fnc.params.items, 0..) |p, idx| {
                    if (p.ty) |pty| {
                        if (try self.typeFromTypeExpr(info, pty)) |ptid| {
                            param_buf[idx] = ptid;
                        } else break :blk null;
                    } else break :blk null;
                }
                var result_ty_id: types.TypeId = t_void;
                if (fnc.result_ty) |rt| {
                    if (try self.typeFromTypeExpr(info, rt)) |rid| {
                        result_ty_id = rid;
                    } else {
                        break :blk null;
                    }
                }

                const fnty = try info.arena.mk(.{ .Function = .{
                    .params = param_buf,
                    .result = result_ty_id,
                    .is_variadic = fnc.is_variadic,
                } });
                break :blk fnty;
            },
            else => null,
        };
        if (ty) |tid| {
            try info.expr_types.put(e, tid);
        } else {
            _ = self.diags.addError(self.exprLoc(e), "could not resolve type expression", .{}) catch {};
        }
        return ty;
    }

    fn typeFromBuiltin(self: *Typer, info: *TypeInfo, b: *ast.BuiltinType) anyerror!?types.TypeId {
        return switch (b.*) {
            .Tuple => |_| null,
            .Pointer => |p| blk: {
                if (try self.typeFromTypeExpr(info, p.elem)) |et| {
                    break :blk try info.arena.mk(.{ .Ptr = .{ .elem = et, .is_const = p.is_const } });
                } else break :blk null;
            },
            .Slice => |s| blk: {
                if (try self.typeFromTypeExpr(info, s.elem)) |et| {
                    break :blk try info.arena.mk(.{ .Slice = .{ .elem = et } });
                } else break :blk null;
            },
            .Array => |a| blk: {
                if (try self.typeFromTypeExpr(info, a.elem)) |et| {
                    var len_val: usize = 0;
                    if (a.size.* == .IntLit) {
                        len_val = std.fmt.parseInt(usize, a.size.IntLit.value, 10) catch 0;
                    }
                    break :blk try info.arena.mk(.{ .Array = .{ .elem = et, .len = len_val } });
                } else break :blk null;
            },
            .MapType => |_| null,
            .DynArray => |d| blk: {
                if (try self.typeFromTypeExpr(info, d.elem)) |et| {
                    break :blk try info.arena.mk(.{ .Slice = .{ .elem = et } });
                } else break :blk null;
            },
            .Optional => |o| blk: {
                if (try self.typeFromTypeExpr(info, o.elem)) |et| {
                    break :blk try info.arena.mk(.{ .Optional = .{ .elem = et } });
                } else break :blk null;
            },
            .Struct => |st| blk: {
                var field_tys = try self.allocator.alloc(types.StructField, st.fields.items.len);
                for (st.fields.items, 0..) |f, idx| {
                    if (try self.typeFromTypeExpr(info, f.ty)) |ft| {
                        field_tys[idx] = .{ .name = f.name, .ty = ft };
                    } else break :blk null;
                }
                break :blk try info.arena.mk(.{ .Struct = .{ .fields = field_tys } });
            },
            .ErrorSet => |_| null,
            .Enum => |_| null,
            .Error => |_| null,
            .Variant => |_| null,
            .Union => |_| null,
            .Simd => |_| null,
            .Complex => |_| null,
            .Tensor => |_| null,
            .Type => |_| null,
            .Any => |_| t_any,
            .Noreturn => |_| null,
        };
    }

    fn unifyNumeric(self: *Typer, info: *TypeInfo, a: types.TypeId, b: types.TypeId) anyerror!?types.TypeId {
        _ = self;
        const ta = info.arena.get(a);
        const tb = info.arena.get(b);
        const ka: types.TypeKind = @as(types.TypeKind, ta);
        const kb: types.TypeKind = @as(types.TypeKind, tb);
        const is_float_a = ka == .F32 or ka == .F64;
        const is_float_b = kb == .F32 or kb == .F64;
        const is_int_a = ka == .I8 or ka == .I16 or ka == .I32 or ka == .I64 or ka == .U8 or ka == .U16 or ka == .U32 or ka == .U64;
        const is_int_b = kb == .I8 or kb == .I16 or kb == .I32 or kb == .I64 or kb == .U8 or kb == .U16 or kb == .U32 or kb == .U64;
        if ((is_float_a or is_int_a) and (is_float_b or is_int_b)) {
            if (is_float_a or is_float_b) return try info.arena.mk(.{ .F64 = {} });
            return try info.arena.mk(.{ .I32 = {} });
        }
        return null;
    }

    fn typeOfBlock(self: *Typer, info: *TypeInfo, b: *const ast.Block) anyerror!?types.TypeId {
        for (b.items.items) |*st| try self.visitStmt(info, st);

        if (b.items.items.len == 0)
            return t_void;

        const last = b.items.items[b.items.items.len - 1];
        return switch (last) {
            .Expr => try self.typeOfExpr(info, &last.Expr),
            else => t_void, // block used for effects only
        };
    }

    fn visitDecl(self: *Typer, info: *TypeInfo, d: *ast.Decl) !void {
        // Make the name visible *before* visiting the RHS.
        if (d.binding) |pat| self.bindPattern(.{ .Decl = d }, pat);

        // Type-check the initializer and get its type.
        try self.visitExpr(info, d.value);
        const rhs_ty = try self.typeOfExpr(info, d.value) orelse {
            _ = self.diags.addError(d.loc, "could not infer initializer type", .{}) catch {};
            return error.TypeInferenceFailed;
        };

        // If there’s an annotation, resolve & check it; else record the inferred type.
        if (d.ty) |ty_expr| {
            const annot_ty = try self.typeFromTypeExpr(info, ty_expr) orelse {
                _ = self.diags.addError(self.exprLoc(ty_expr), "could not resolve type annotation", .{}) catch {};
                return error.TypeInferenceFailed;
            };
            try info.decl_types.put(d, annot_ty);
            if (annot_ty != rhs_ty) {
                _ = self.diags.addError(d.loc, "initializer type mismatch", .{}) catch {};
            }
        } else {
            // <- THIS is the critical bit for `fmt := "sum=%d\n"`
            try info.decl_types.put(d, rhs_ty);
        }
    }

    fn visitStmt(self: *Typer, info: *TypeInfo, s: *ast.Statement) anyerror!void {
        switch (s.*) {
            .Expr => |*e| try self.visitExpr(info, e),
            .Decl => |*d| try self.visitDecl(info, d),
            .Assign => |a| {
                try self.visitExpr(info, a.left);
                try self.visitExpr(info, a.right);
            },
            .Insert => |ins| try self.visitExpr(info, ins.expr),
            .Return => |ret| if (ret.value) |v| try self.visitExpr(info, v),
            .Break => |br| if (br.value) |v| try self.visitExpr(info, v),
            .Continue => |_| {},
            .Unreachable => |_| {},
            .Defer => |df| try self.visitExpr(info, df.expr),
            .ErrDefer => |ed| try self.visitExpr(info, ed.expr),
        }
    }

    fn visitExpr(self: *Typer, info: *TypeInfo, e: *ast.Expr) !void {
        switch (e.*) {
            .TupleLit => |t| for (t.elems.items) |sub| try self.visitExpr(info, sub),
            .ArrayLit => |a| for (a.elems.items) |sub| try self.visitExpr(info, sub),
            .MapLit => |m| for (m.entries.items) |kv| {
                try self.visitExpr(info, kv.key);
                try self.visitExpr(info, kv.value);
            },
            .StructLit => |st| for (st.fields.items) |f| try self.visitExpr(info, f.value),
            .VariantLit => |v| if (v.value) |sub| try self.visitExpr(info, sub),
            .EnumLit => |v| if (v.value) |sub| try self.visitExpr(info, sub),
            .FunctionLit => |fnc| {
                _ = self.symtab.push() catch {};
                defer self.symtab.pop();
                for (fnc.params.items) |*p| {
                    if (p.pat) |pat| {
                        self.bindPattern(.{ .Param = p }, pat);
                    }
                }
                if (fnc.body) |body| {
                    for (body.items.items) |*stmt| {
                        try self.visitStmt(info, stmt);
                    }
                }
            },
            .UnaryPlus => |u| try self.visitExpr(info, u.right),
            .UnaryMinus => |u| try self.visitExpr(info, u.right),
            .AddressOf => |u| try self.visitExpr(info, u.right),
            .LogicalNot => |u| try self.visitExpr(info, u.right),
            .Range => |r| {
                if (r.start) |s| try self.visitExpr(info, s);
                if (r.end) |en| try self.visitExpr(info, en);
            },
            .InfixAdd => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixSub => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixMul => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixDiv => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixMod => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixShl => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixShr => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixBitAnd => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixBitOr => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixBitXor => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixEq => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixNeq => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixLt => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixLte => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixGt => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixGte => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixLogicalAnd => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixLogicalOr => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixCatch => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .InfixOrelse => |b| {
                try self.visitExpr(info, b.left);
                try self.visitExpr(info, b.right);
            },
            .PostfixErrorUnwrap => |p| try self.visitExpr(info, p.expr),
            .PostfixOptionalUnwrap => |p| try self.visitExpr(info, p.expr),
            .PostfixDeref => |p| try self.visitExpr(info, p.expr),
            .PostfixIndex => |p| {
                try self.visitExpr(info, p.collection);
                try self.visitExpr(info, p.index);
            },
            .PostfixField => |p| try self.visitExpr(info, p.parent),
            .PostfixCall => |p| {
                try self.visitExpr(info, p.callee);
                for (p.args.items) |arg| try self.visitExpr(info, arg);
            },
            .PostfixAwait => |p| try self.visitExpr(info, p.expr),
            .CastNormal => |c| {
                try self.visitExpr(info, c.expr);
                _ = try self.typeFromTypeExpr(info, c.ty);
            },
            .CastBit => |c| {
                try self.visitExpr(info, c.expr);
                _ = try self.typeFromTypeExpr(info, c.ty);
            },
            .CastSaturate => |c| {
                try self.visitExpr(info, c.expr);
                _ = try self.typeFromTypeExpr(info, c.ty);
            },
            .CastWrap => |c| {
                try self.visitExpr(info, c.expr);
                _ = try self.typeFromTypeExpr(info, c.ty);
            },
            .CastChecked => |c| {
                try self.visitExpr(info, c.expr);
                _ = try self.typeFromTypeExpr(info, c.ty);
            },
            .If => |iff| {
                try self.visitExpr(info, iff.cond);
                for (iff.then_block.items.items) |*st| try self.visitStmt(info, st);
                if (iff.else_block) |eb| try self.visitExpr(info, eb);
            },
            .While => |w| {
                if (w.cond) |c| try self.visitExpr(info, c);
                for (w.body.items.items) |*st| try self.visitStmt(info, st);
            },
            .For => |f| {
                try self.visitExpr(info, f.iterable);
                for (f.body.items.items) |*st| try self.visitStmt(info, st);
            },
            .Match => |m| {
                try self.visitExpr(info, m.expr);
                for (m.arms.items) |arm| try self.visitExpr(info, arm.body);
            },
            .Block => |b| for (b.items.items) |*st| try self.visitStmt(info, st),
            .ComptimeBlock => |cb| for (cb.block.items.items) |*st| try self.visitStmt(info, st),
            .CodeBlock => |cb| for (cb.block.items.items) |*st| try self.visitStmt(info, st),
            .AsyncBlock => |ab| try self.visitExpr(info, ab.body),
            .MlirBlock => |_| {},
            .Closure => |cl| {
                if (cl.result_ty) |rt| _ = rt;
                try self.visitExpr(info, cl.body);
            },
            .Import => |imp| try self.visitExpr(info, imp.expr),
            .TypeOf => |t| try self.visitExpr(info, t.expr),
            else => {},
        }
        if (try self.typeOfExpr(info, e)) |tid| {
            try info.expr_types.put(e, tid);
        }
    }

    fn printSymtab(self: *Typer) !void {
        var buffer: [256]u8 = undefined;
        var out = std.fs.File.stdout().writer(&buffer);
        const writer = &out.interface;
        var sym_printer = symbols.SymPrinter.init(writer);
        try sym_printer.printTop(&self.symtab);
    }
};
