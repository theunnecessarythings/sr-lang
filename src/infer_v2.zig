const std = @import("std");
const ast = @import("ast_v2.zig");
const Diagnostics = @import("diagnostics.zig").Diagnostics;
const symbols = @import("symbols_v2.zig");
const types = @import("types_v2.zig");

pub const TypeInfoV2 = struct {
    gpa: std.mem.Allocator,
    store: types.TypeStore,
    expr_types: std.ArrayListUnmanaged(?types.TypeId) = .{},
    decl_types: std.ArrayListUnmanaged(?types.TypeId) = .{},

    pub fn init(gpa: std.mem.Allocator) TypeInfoV2 {
        return .{ .gpa = gpa, .store = types.TypeStore.init(gpa) };
    }
    pub fn deinit(self: *@This()) void {
        self.expr_types.deinit(self.gpa);
        self.decl_types.deinit(self.gpa);
        self.store.deinit();
    }
};

pub const TyperV2 = struct {
    gpa: std.mem.Allocator,
    diags: *Diagnostics,
    symtab: symbols.SymbolStore,

    // cached commons
    t_bool: types.TypeId = undefined,
    t_i32: types.TypeId = undefined,
    t_f64: types.TypeId = undefined,
    t_string: types.TypeId = undefined,
    t_void: types.TypeId = undefined,
    t_any: types.TypeId = undefined,

    pub fn init(gpa: std.mem.Allocator, diags: *Diagnostics) TyperV2 {
        return .{ .gpa = gpa, .diags = diags, .symtab = symbols.SymbolStore.init(gpa) };
    }
    pub fn deinit(self: *@This()) void { self.symtab.deinit(); }

    pub fn run(self: *@This(), a: *const ast.Ast) !TypeInfoV2 {
        var info = TypeInfoV2.init(self.gpa);
        // Pre-size arrays
        const expr_len: usize = a.exprs.index.kinds.items.len;
        const decl_len: usize = a.exprs.Decl.list.len;
        try info.expr_types.appendNTimes(self.gpa, null, expr_len);
        try info.decl_types.appendNTimes(self.gpa, null, decl_len);

        self.t_bool = info.store.tBool();
        self.t_i32 = info.store.tI32();
        self.t_f64 = info.store.tF64();
        self.t_string = info.store.tString();
        self.t_void = info.store.tVoid();
        self.t_any = info.store.tAny();

        const root = try self.symtab.push(null);
        _ = root;
        defer self.symtab.pop();

        const decl_ids = a.exprs.decl_pool.slice(a.unit.decls);
        for (decl_ids) |did| try self.visitDecl(&info, a, did);
        return info;
    }

    fn visitDecl(self: *@This(), info: *TypeInfoV2, a: *const ast.Ast, did: ast.DeclId) !void {
        const d = a.exprs.Decl.get(did.toRaw());
        if (!d.pattern.isNone()) {
            const name = self.primaryNameOfPattern(a, d.pattern.unwrap());
            if (!name.isNone()) {
                _ = try self.symtab.declare(.{ .name = name.unwrap(), .kind = .Var, .loc = d.loc, .origin_decl = ast.OptDeclId.some(did), .origin_param = ast.OptParamId.none() });
            }
        }
        const rhs_ty = try self.typeOfExpr(info, a, d.value) orelse null;
        if (!d.ty.isNone()) {
            const annot_ty = try self.typeFromTypeExpr(info, a, d.ty.unwrap());
            if (annot_ty) |atid| {
                info.decl_types.items[did.toRaw()] = atid;
                if (rhs_ty) |rtid| {
                    if (rtid.toRaw() != atid.toRaw()) {
                        _ = self.diags.addError(a.exprs.locs.get(d.loc), "initializer type mismatch", .{}) catch {};
                    }
                }
            } else {
                _ = self.diags.addError(a.exprs.locs.get(d.loc), "could not resolve type annotation", .{}) catch {};
            }
        } else {
            if (rhs_ty) |rtid| info.decl_types.items[did.toRaw()] = rtid;
        }
    }

    fn primaryNameOfPattern(self: *@This(), a: *const ast.Ast, pid: ast.PatternId) ast.OptStrId {
        _ = self;
        const k = a.pats.index.kinds.items[pid.toRaw()];
        return switch (k) {
            .Binding => ast.OptStrId.some(a.pats.get(.Binding, pid).name),
            .Path => blk: {
                const p = a.pats.get(.Path, pid);
                const segs = a.pats.seg_pool.slice(p.segments);
                if (segs.len == 0) break :blk ast.OptStrId.none();
                break :blk ast.OptStrId.some(a.pats.PathSeg.get(segs[segs.len - 1].toRaw()).name);
            },
            else => ast.OptStrId.none(),
        };
    }

    fn typeOfExpr(self: *@This(), info: *TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) anyerror!?types.TypeId {
        if (info.expr_types.items[id.toRaw()]) |t| return t;
        const k = a.exprs.index.kinds.items[id.toRaw()];
        const tid: ?types.TypeId = switch (k) {
            .Literal => blk: {
                const lit = a.exprs.get(.Literal, id);
                const t: types.TypeId = switch (lit.kind) {
                    .int => self.t_i32,
                    .float => self.t_f64,
                    .bool => self.t_bool,
                    .string => self.t_string,
                    .char => info.store.tU32(),
                };
                break :blk t;
            },
            .Ident => blk_id: {
                const row = a.exprs.get(.Ident, id);
                if (self.lookup(a, row.name)) |sid| {
                    const srow = self.symtab.syms.get(sid.toRaw());
                    if (!srow.origin_decl.isNone()) if (info.decl_types.items[srow.origin_decl.unwrap().toRaw()]) |dt| break :blk_id dt;
                }
                break :blk_id null;
            },
            .Binary => blk_bin: {
                const row = a.exprs.get(.Binary, id);
                if (row.op == .@"orelse") {
                    const lt = try self.typeOfExpr(info, a, row.left) orelse break :blk_bin null;
                    const rt = try self.typeOfExpr(info, a, row.right) orelse break :blk_bin null;
                    if (self.isOptional(info, lt)) |elem| {
                        if (elem.toRaw() == rt.toRaw()) break :blk_bin rt;
                    }
                }
                break :blk_bin null;
            },
            .Unary => try self.typeOfExpr(info, a, a.exprs.get(.Unary, id).expr),
            .Range, .Deref, .ArrayLit, .TupleLit, .MapLit, .IndexAccess, .FieldAccess, .StructLit,
            .VariantLit, .EnumLit, .Call, .ComptimeBlock, .CodeBlock, .AsyncBlock, .MlirBlock, .Insert,
            .Return, .If, .While, .For, .Match, .Break, .Continue, .Unreachable, .NullLit, .UndefLit,
            .FunctionLit, .Block,
            .Defer, .ErrDefer, .ErrUnwrap, .OptionalUnwrap, .Await, .Closure, .Cast, .Catch, .Import, .TypeOf,
            => null,

            // treat builtin type expressions as 'any' in expr-position; real typing would separate modes
            .TupleType, .ArrayType, .DynArrayType, .MapType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType,
            .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType => self.t_any,
        };
        var out = tid;
        if (out == null and k == .IndexAccess) out = self.typeOfIndexAccess(info, a, id);
        if (out == null and k == .FieldAccess) out = self.typeOfFieldAccess(info, a, id);
        if (out) |tt| info.expr_types.items[id.toRaw()] = tt;
        return out;
    }
    fn lookup(self: *@This(), a: *const ast.Ast, name: ast.StrId) ?symbols.SymbolId {
        return self.symtab.lookup(a, self.symtab.currentId(), name);
    }

    fn isOptional(self: *@This(), info: *TypeInfoV2, id: types.TypeId) ?types.TypeId {
        _ = self;
        const k = info.store.index.kinds.items[id.toRaw()];
        if (k != .Optional) return null;
        const row = info.store.Optional.get(info.store.index.rows.items[id.toRaw()]);
        return row.elem;
    }

    // Best-effort expand: infer collection element types for indexing
    fn typeOfIndexAccess(self: *@This(), info: *TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) ?types.TypeId {
        const row = a.exprs.get(.IndexAccess, id);
        const ct = self.typeOfExpr(info, a, row.collection) catch return null;
        if (ct) |t| {
            const k = info.store.index.kinds.items[t.toRaw()];
            switch (k) {
                .Array => {
                    const r = info.store.Array.get(info.store.index.rows.items[t.toRaw()]);
                    return r.elem;
                },
                .Slice => {
                    const r = info.store.Slice.get(info.store.index.rows.items[t.toRaw()]);
                    return r.elem;
                },
                else => {},
            }
        }
        return null;
    }
    fn typeOfFieldAccess(self: *@This(), info: *TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) ?types.TypeId {
        const fr = a.exprs.get(.FieldAccess, id);
        const pt = self.typeOfExpr(info, a, fr.parent) catch return null;
        const ptv = pt orelse return null;
        var t = ptv;
        if (info.store.index.kinds.items[t.toRaw()] == .Ptr) t = info.store.Ptr.get(info.store.index.rows.items[t.toRaw()]).elem;
        if (fr.is_tuple and info.store.index.kinds.items[t.toRaw()] == .Tuple) {
            const rowt = info.store.Tuple.get(info.store.index.rows.items[t.toRaw()]);
            const idx = std.fmt.parseInt(usize, a.exprs.strs.get(fr.field), 10) catch return null;
            const ids = info.store.type_pool.slice(rowt.elems);
            if (idx < ids.len) return ids[idx];
        }
        return null;
    }

    fn typeFromTypeExpr(self: *@This(), info: *TypeInfoV2, a: *const ast.Ast, id: ast.ExprId) anyerror!?types.TypeId {
        const k = a.exprs.index.kinds.items[id.toRaw()];
        return switch (k) {
            .Ident => blk_ident: {
                const name = a.exprs.get(.Ident, id).name;
                const s = a.exprs.strs.get(name);
                if (std.mem.eql(u8, s, "bool")) break :blk_ident info.store.tBool();
                if (std.mem.eql(u8, s, "i8")) break :blk_ident info.store.tI8();
                if (std.mem.eql(u8, s, "i16")) break :blk_ident info.store.tI16();
                if (std.mem.eql(u8, s, "i32")) break :blk_ident info.store.tI32();
                if (std.mem.eql(u8, s, "i64")) break :blk_ident info.store.tI64();
                if (std.mem.eql(u8, s, "u8")) break :blk_ident info.store.tU8();
                if (std.mem.eql(u8, s, "u16")) break :blk_ident info.store.tU16();
                if (std.mem.eql(u8, s, "u32")) break :blk_ident info.store.tU32();
                if (std.mem.eql(u8, s, "u64")) break :blk_ident info.store.tU64();
                if (std.mem.eql(u8, s, "f32")) break :blk_ident info.store.tF32();
                if (std.mem.eql(u8, s, "f64")) break :blk_ident info.store.tF64();
                if (std.mem.eql(u8, s, "usize")) break :blk_ident info.store.tUsize();
                if (std.mem.eql(u8, s, "string")) break :blk_ident info.store.tString();
                if (std.mem.eql(u8, s, "void")) break :blk_ident info.store.tVoid();
                if (std.mem.eql(u8, s, "any")) break :blk_ident info.store.tAny();
                break :blk_ident null;
            },
            .TupleType => blk_tt: {
                const row = a.exprs.get(.TupleType, id);
                const ids = a.exprs.expr_pool.slice(row.elems);
                var buf = try self.gpa.alloc(types.TypeId, ids.len);
                defer self.gpa.free(buf);
                var i: usize = 0;
                while (i < ids.len) : (i += 1) {
                    buf[i] = (try self.typeFromTypeExpr(info, a, ids[i])) orelse break :blk_tt null;
                }
                break :blk_tt info.store.mkTuple(buf);
            },
            .ArrayType => blk_at: {
                const row = a.exprs.get(.ArrayType, id);
                const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_at null;
                var len_val: usize = 0;
                if (a.exprs.index.kinds.items[row.size.toRaw()] == .Literal) {
                    const lit = a.exprs.get(.Literal, row.size);
                    if (lit.kind == .int and !lit.value.isNone()) {
                        len_val = std.fmt.parseInt(usize, a.exprs.strs.get(lit.value.unwrap()), 10) catch 0;
                    }
                }
                break :blk_at info.store.mkArray(elem, len_val);
            },
            .DynArrayType => blk_dt: {
                const row = a.exprs.get(.DynArrayType, id);
                const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_dt null;
                break :blk_dt info.store.mkSlice(elem);
            },
            .SliceType => blk_st: { const row = a.exprs.get(.SliceType, id); const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_st null; break :blk_st info.store.mkSlice(elem); },
            .OptionalType => blk_ot: { const row = a.exprs.get(.OptionalType, id); const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_ot null; break :blk_ot info.store.mkOptional(elem); },
            .PointerType => blk_pt: { const row = a.exprs.get(.PointerType, id); const elem = (try self.typeFromTypeExpr(info, a, row.elem)) orelse break :blk_pt null; break :blk_pt info.store.mkPtr(elem, row.is_const); },
            .StructType => blk_sty: {
                const row = a.exprs.get(.StructType, id);
                const sfs = a.exprs.sfield_pool.slice(row.fields);
                var buf = try self.gpa.alloc(types.TypeStore.StructFieldArg, sfs.len);
                defer self.gpa.free(buf);
                var i: usize = 0;
                while (i < sfs.len) : (i += 1) {
                    const f = a.exprs.StructField.get(sfs[i].toRaw());
                    const ft = (try self.typeFromTypeExpr(info, a, f.ty)) orelse break :blk_sty null;
                    buf[i] = .{ .name = a.exprs.strs.get(f.name), .ty = ft };
                }
                break :blk_sty info.store.mkStruct(buf);
            },
            .FunctionLit => blk_fn: {
                const fnr = a.exprs.get(.FunctionLit, id);
                const params = a.exprs.param_pool.slice(fnr.params);
                var pbuf = try self.gpa.alloc(types.TypeId, params.len);
                defer self.gpa.free(pbuf);
                var i: usize = 0;
                while (i < params.len) : (i += 1) {
                    const p = a.exprs.Param.get(params[i].toRaw());
                    if (p.ty.isNone()) break :blk_fn null;
                    const pt = (try self.typeFromTypeExpr(info, a, p.ty.unwrap())) orelse break :blk_fn null;
                    pbuf[i] = pt;
                }
                const res = if (!fnr.result_ty.isNone()) (try self.typeFromTypeExpr(info, a, fnr.result_ty.unwrap())) else info.store.tVoid();
                if (res == null) break :blk_fn null;
                break :blk_fn info.store.mkFunction(pbuf, res.?, fnr.flags.is_variadic);
            },
            .AnyType => info.store.tAny(),
            .TypeType => null,
            else => null,
        };
    }
};
