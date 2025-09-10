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
    symtab: *symbols.SymbolTable,
    // simple top-level name -> decl map for identifier typing
    top_decls: std.StringHashMap(*ast.Decl) = undefined,

    pub fn init(allocator: std.mem.Allocator, diags: *Diagnostics, symtab: *symbols.SymbolTable) Typer {
        return .{ .allocator = allocator, .diags = diags, .symtab = symtab, .top_decls = std.StringHashMap(*ast.Decl).init(allocator) };
    }

    pub fn run(self: *Typer, program: *ast.Unit) !TypeInfo {
        var info = TypeInfo.init(self.allocator);

        // Seed a few primitive type handles
        const t_bool = try info.arena.mk(.{ .Bool = {} });
        const t_i32 = try info.arena.mk(.{ .I32 = {} });
        const t_u32 = try info.arena.mk(.{ .U32 = {} });
        const t_f64 = try info.arena.mk(.{ .F64 = {} });
        const t_string = try info.arena.mk(.{ .String = {} });
        _ = t_bool;
        _ = t_i32;
        _ = t_u32;
        _ = t_f64;
        _ = t_string;

        // Build simple top-level name map for identifiers
        for (program.decls.items) |*d| if (d.binding) |pat| if (bindingName(pat)) |name| {
            _ = self.top_decls.put(name, d) catch {};
        };

        // Walk decls deeply: record declared types and infer expression types
        for (program.decls.items) |*d| try self.visitDecl(&info, d);

        return info;
    }

    fn bindingName(p: *const ast.Pattern) ?[]const u8 {
        return switch (p.*) {
            .Binding => |b| b.name,
            else => null,
        };
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
        return switch (e.*) {
            // literals
            .IntLit => |_| try info.arena.mk(.{ .I32 = {} }),
            .FloatLit => |_| try info.arena.mk(.{ .F64 = {} }),
            .BoolLit => |_| try info.arena.mk(.{ .Bool = {} }),
            .StringLit => |_| try info.arena.mk(.{ .String = {} }),
            .CharLit => |_| try info.arena.mk(.{ .U32 = {} }),
            .NullLit => |_| null, // need context
            .UndefLit => |_| null, // need context
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
                // Function type: params must have types and a result type must be present
                var param_buf = try self.allocator.alloc(types.TypeId, fnc.params.items.len);
                for (fnc.params.items, 0..) |p, idx| {
                    if (p.ty) |pty| {
                        if (try self.typeFromTypeExpr(info, pty)) |ptid| {
                            param_buf[idx] = ptid;
                        } else break :blk_fn null;
                    } else break :blk_fn null;
                }
                if (fnc.result_ty) |rt| {
                    if (try self.typeFromTypeExpr(info, rt)) |rid| {
                        const fnty = try info.arena.mk(.{ .Function = .{ .params = param_buf, .result = rid, .is_variadic = fnc.is_variadic } });
                        break :blk_fn fnty;
                    } else break :blk_fn null;
                } else break :blk_fn null;
            },

            // identifiers: resolve to top-level decl if available
            .Identifier => |id| blk_ident: {
                if (self.top_decls.get(id.name)) |decl| {
                    // prefer declared type; else infer from value
                    if (info.decl_types.get(decl)) |tid| break :blk_ident tid;
                    if (try self.typeFromTypeExpr(info, decl.value)) |alias_ty| {
                        try info.decl_types.put(decl, alias_ty);
                        break :blk_ident alias_ty;
                    }
                    if (try self.typeOfExpr(info, decl.value)) |vt| break :blk_ident vt;
                }
                break :blk_ident null;
            },

            // compound literals
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
            .MapLit => |_| null, // not modeled yet
            .StructLit => |_| null, // requires named type or structural typing rules

            // unary
            .UnaryPlus => |u| self.typeOfExpr(info, u.right),
            .UnaryMinus => |u| self.typeOfExpr(info, u.right),
            .AddressOf => |u| blk_addr: {
                if (try self.typeOfExpr(info, u.right)) |rt| {
                    break :blk_addr try info.arena.mk(.{ .Ptr = .{ .elem = rt } });
                }
                break :blk_addr null;
            },
            .LogicalNot => |_| try info.arena.mk(.{ .Bool = {} }),

            // range (used mainly for slicing); leave untyped as value
            .Range => |_| null,

            // binary arithmetic and bitwise (split due to differing payload types)
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

            // comparisons and logical
            .InfixEq, .InfixNeq, .InfixLt, .InfixLte, .InfixGt, .InfixGte => try info.arena.mk(.{ .Bool = {} }),
            .InfixLogicalAnd => |b| blk_land: {
                const lt = try self.typeOfExpr(info, b.left);
                const rt = try self.typeOfExpr(info, b.right);
                const t_bool = try info.arena.mk(.{ .Bool = {} });
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
                const t_bool = try info.arena.mk(.{ .Bool = {} });
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

            // postfix
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
                            // string indexing yields u8; slicing yields string
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
                // Try using callee type if it's a function type
                if (try self.typeOfExpr(info, call.callee)) |cty| {
                    const ty = info.arena.get(cty);
                    if (@as(types.TypeKind, ty) == .Function) {
                        // arity/type checks (best-effort)
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

            // casts: yield target type
            .CastNormal => |c| self.typeFromTypeExpr(info, c.ty),
            .CastBit => |c| self.typeFromTypeExpr(info, c.ty),
            .CastSaturate => |c| self.typeFromTypeExpr(info, c.ty),
            .CastWrap => |c| self.typeFromTypeExpr(info, c.ty),
            .CastChecked => |c| self.typeFromTypeExpr(info, c.ty),

            // control flow
            .If => |iff| blk_if: {
                const ct = try self.typeOfExpr(info, iff.cond);
                if (ct) |cid| {
                    const t_bool = try info.arena.mk(.{ .Bool = {} });
                    if (cid != t_bool) _ = self.diags.addError(self.exprLoc(iff.cond), "if condition must be bool", .{}) catch {};
                }
                // attempt to infer from branches if both present
                var then_ty: ?types.TypeId = null;
                var else_ty: ?types.TypeId = null;
                // treat blocks as last expr type if single expr statement at end (best-effort)
                then_ty = try self.typeOfBlock(info, &iff.then_block);
                if (iff.else_block) |eb| else_ty = try self.typeOfExpr(info, eb);
                if (then_ty) |tt| {
                    if (else_ty) |et| {
                        if (tt == et) break :blk_if tt;
                    }
                }
                break :blk_if null;
            },
            .While => |w| blk_while: {
                if (w.cond) |c| {
                    const ct = try self.typeOfExpr(info, c);
                    if (ct) |cid| {
                        const t_bool = try info.arena.mk(.{ .Bool = {} });
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
                            if (prev != bt) arm_ty = null; // inconsistent; give up
                        } else arm_ty = bt;
                    }
                }
                break :blk_match arm_ty;
            },

            // blocks and others
            .Block => |b| self.typeOfBlock(info, &b),
            .ComptimeBlock => |_| null,
            .CodeBlock => |_| null,
            .AsyncBlock => |ab| self.typeOfExpr(info, ab.body),
            .MlirBlock => |_| null,
            .Closure => |cl| blk_cl: {
                // form a function type from params/result if available
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

            // meta/introspection
            .Import => |imp| self.typeOfExpr(info, imp.expr),
            .TypeOf => |t| self.typeOfExpr(info, t.expr),

            // builtin type in expr position has no runtime type
            .Type => |_| null,
        };
    }

    fn typeFromTypeExpr(self: *Typer, info: *TypeInfo, e: *const ast.Expr) anyerror!?types.TypeId {
        // placeholder: symbol resolution hooks will use self later
        return switch (e.*) {
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
                // Function type: params must have types and a result type must be present
                var param_buf = try self.allocator.alloc(types.TypeId, fnc.params.items.len);
                for (fnc.params.items, 0..) |p, idx| {
                    if (p.ty) |pty| {
                        if (try self.typeFromTypeExpr(info, pty)) |ptid| {
                            param_buf[idx] = ptid;
                        } else break :blk null;
                    } else break :blk null;
                }
                if (fnc.result_ty) |rt| {
                    if (try self.typeFromTypeExpr(info, rt)) |rid| {
                        const fnty = try info.arena.mk(.{ .Function = .{ .params = param_buf, .result = rid, .is_variadic = fnc.is_variadic } });
                        break :blk fnty;
                    } else break :blk null;
                } else break :blk null;
            },
            else => null,
        };
    }

    fn typeFromBuiltin(self: *Typer, info: *TypeInfo, b: *ast.BuiltinType) anyerror!?types.TypeId {
        // placeholder: symbol resolution hooks will use self later
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
            .MapType => |_| null, // not modeled yet
            .DynArray => |d| blk: {
                // model as slice
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
            .Any => |_| null,
            .Noreturn => |_| null,
        };
    }

    fn unifyNumeric(self: *Typer, info: *TypeInfo, a: types.TypeId, b: types.TypeId) anyerror!?types.TypeId {
        _ = self; // unused for now
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
            // default to i32 for now
            return try info.arena.mk(.{ .I32 = {} });
        }
        return null;
    }

    fn typeOfBlock(self: *Typer, info: *TypeInfo, b: *const ast.Block) anyerror!?types.TypeId {
        var last_ty: ?types.TypeId = null;
        for (b.items.items) |*st| try self.visitStmt(info, st);
        // best-effort: if last statement is expr, use its type
        if (b.items.items.len > 0) {
            const last = b.items.items[b.items.items.len - 1];
            if (last == .Expr) {
                last_ty = try self.typeOfExpr(info, &last.Expr);
            }
        }
        return last_ty;
    }

    fn visitDecl(self: *Typer, info: *TypeInfo, d: *ast.Decl) !void {
        var annot_ty: ?types.TypeId = null;
        if (d.ty) |ty_expr| {
            annot_ty = try self.typeFromTypeExpr(info, ty_expr);
            if (annot_ty) |tid| try info.decl_types.put(d, tid);
        } else {
            // If RHS is a type expression, this is a type alias; record its type
            if (try self.typeFromTypeExpr(info, d.value)) |tid| {
                try info.decl_types.put(d, tid);
            }
        }
        try self.visitExpr(info, d.value);
        if (try self.typeOfExpr(info, d.value)) |rhs_ty| {
            if (annot_ty) |tid| {
                if (tid != rhs_ty) {
                    _ = self.diags.addError(d.loc, "initializer type mismatch", .{}) catch {};
                }
            }
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
        // recurse first where needed to collect sub-expression types
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
                for (fnc.params.items) |p| {
                    if (p.value) |dv| try self.visitExpr(info, dv);
                }
                if (fnc.body) |body| for (body.items.items) |*st| try self.visitStmt(info, st);
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
            // .CastNormal, .CastBit, .CastSaturate, .CastWrap, .CastChecked => |c| try self.visitExpr(info, c.expr),
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
            _ = info.expr_types.put(e, tid) catch {};
        }
    }
};

fn findDecl(unit: *ast.Unit, name: []const u8) ?*ast.Decl {
    for (unit.decls.items) |*d| {
        if (d.binding) |pat| switch (pat.*) {
            .Binding => |b| if (std.mem.eql(u8, b.name, name)) return d,
            else => {},
        };
    }
    return null;
}

test "infer: literals, ops, tuple field, and string index" {
    const allocator = std.heap.page_allocator;
    var diags = @import("diagnostics.zig").Diagnostics.init(allocator);
    defer diags.deinit();

    const src =
        "package main\n" ++
        "a := 1 + 2\n" ++
        "b := true and false\n" ++
        "t := (1, 2.0)\n" ++
        "x := t.0\n" ++
        "s: string = \"hi\"\n" ++
        "c := s[0]\n";
    const srcz = try allocator.dupeZ(u8, src);
    defer allocator.free(srcz);

    var parser = @import("parser.zig").Parser.init(allocator, srcz, &diags);
    var cst_program = try parser.parse();
    var pl = @import("pipeline.zig").Pipeline.init(allocator, &diags);
    const result = try pl.run(&cst_program);
    defer {
        if (result.type_info) |ti| {
            ti.deinit();
            allocator.destroy(ti);
        }
        if (result.binder) |b| {
            var bm = b;
            bm.deinit();
        }
    }
    const ti = result.type_info.?;

    const a_decl = findDecl(&result.hir, "a").?;
    const b_decl = findDecl(&result.hir, "b").?;
    const x_decl = findDecl(&result.hir, "x").?;
    const c_decl = findDecl(&result.hir, "c").?;

    const t_i32 = try ti.arena.mk(.{ .I32 = {} });
    const t_bool = try ti.arena.mk(.{ .Bool = {} });
    const t_u32 = try ti.arena.mk(.{ .U32 = {} });

    const a_ty = (ti.expr_types.get(a_decl.value)).?;
    const b_ty = (ti.expr_types.get(b_decl.value)).?;
    const x_ty = (ti.expr_types.get(x_decl.value)).?;
    const c_ty = (ti.expr_types.get(c_decl.value)).?;

    try std.testing.expectEqual(t_i32, a_ty);
    try std.testing.expectEqual(t_bool, b_ty);
    try std.testing.expectEqual(t_i32, x_ty);
    try std.testing.expectEqual(t_u32, c_ty);
}

test "infer: decl annotation vs initializer mismatch" {
    const allocator = std.heap.page_allocator;
    var diags = @import("diagnostics.zig").Diagnostics.init(allocator);
    defer diags.deinit();

    const src =
        "package main\n" ++
        "x: i32 = 1.5\n"; // mismatch on purpose
    const srcz = try allocator.dupeZ(u8, src);
    defer allocator.free(srcz);

    var parser = @import("parser.zig").Parser.init(allocator, srcz, &diags);
    var cst_program = try parser.parse();
    var pl = @import("pipeline.zig").Pipeline.init(allocator, &diags);
    const result = try pl.run(&cst_program);
    defer {
        if (result.type_info) |ti| {
            ti.deinit();
            allocator.destroy(ti);
        }
        if (result.binder) |b| {
            var bm = b;
            bm.deinit();
        }
    }
    // Expect at least one error due to mismatch
    var has_err = false;
    for (diags.messages.items) |m| {
        if (m.severity == .err) { has_err = true; break; }
    }
    try std.testing.expect(has_err);
}
