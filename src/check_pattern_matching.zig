const std = @import("std");

const ast = @import("ast.zig");
const check_types = @import("check_types.zig");
const checker = @import("checker.zig");
const Checker = checker.Checker;
const diag = @import("diagnostics.zig");
const symbols = @import("symbols.zig");
const types = @import("types.zig");

/// Return field IDs for Variant/Error types so the same logic handles both.
inline fn getVariantOrErrorCases(self: *Checker, ty: types.TypeId) []const types.FieldId {
    return if (self.typeKind(ty) == .Variant)
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, ty).variants)
    else
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, ty).variants);
}

/// Look up the payload type associated with `case_name` for variant/error `ty`.
inline fn findCasePayload(self: *Checker, ty: types.TypeId, case_name: ast.StrId) ?types.TypeId {
    const cases = getVariantOrErrorCases(self, ty);
    for (cases) |fid| {
        const f = self.context.type_store.Field.get(fid);
        if (f.name.eq(case_name)) return f.ty;
    }
    return null;
}

const Interval = struct { a: i64, b: i64 };

const IntSet = struct {
    wildcard: bool = false,
    non_int: bool = false,
    points: std.ArrayList(i64) = .{},
    ranges: std.ArrayList(Interval) = .{},

    pub fn deinit(self: *IntSet, gpa: std.mem.Allocator) void {
        self.points.deinit(gpa);
        self.ranges.deinit(gpa);
    }
};

const IntCoverage = struct {
    wildcard: bool = false,
    points: std.AutoArrayHashMapUnmanaged(i64, void) = .{},
    ranges: std.ArrayList(Interval) = .{},

    pub fn deinit(self: *IntCoverage, gpa: std.mem.Allocator) void {
        self.points.deinit(gpa);
        self.ranges.deinit(gpa);
    }
};

inline fn intervalOverlaps(a: Interval, b: Interval) bool {
    return !(a.b < b.a or a.a > b.b);
}
inline fn pointInInterval(p: i64, r: Interval) bool {
    return p >= r.a and p <= r.b;
}

fn collectIntSet(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, out: *IntSet) !void {
    switch (ast_unit.kind(pid)) {
        .Wildcard => out.wildcard = true,
        .Literal => if (patternIntLiteral(ast_unit, pid)) |lit| {
            try out.points.append(self.gpa, lit);
        } else {
            out.non_int = true;
        },
        .Range => if (patternIntRange(ast_unit, pid)) |rr| {
            try out.ranges.append(self.gpa, .{ .a = rr.a, .b = rr.b });
        } else {
            out.non_int = true;
        },
        .Or => {
            const alts = ast_unit.pats.pat_pool.slice(ast_unit.pats.get(.Or, pid).alts);
            for (alts) |aid| {
                try collectIntSet(self, ast_unit, aid, out);
                if (out.wildcard) break;
            }
        },
        .At => try collectIntSet(self, ast_unit, ast_unit.pats.get(.At, pid).pattern, out),
        else => out.non_int = true,
    }
}

fn coverAddPointDetectOverlap(self: *Checker, cov: *IntCoverage, lit: i64) !bool {
    if (cov.points.contains(lit)) return true;
    for (cov.ranges.items) |r| if (pointInInterval(lit, r)) return true;
    try cov.points.put(self.gpa, lit, {});
    return false;
}

fn coverAddRangeDetectOverlap(self: *Checker, cov: *IntCoverage, new: Interval) !bool {
    var it = cov.points.iterator();
    while (it.next()) |entry| if (pointInInterval(entry.key_ptr.*, new)) return true;

    const ranges = cov.ranges.items;
    var i: usize = 0;
    while (i < ranges.len and ranges[i].a <= new.a) : (i += 1) {}
    if (i > 0 and intervalOverlaps(ranges[i - 1], new)) return true;
    if (i < ranges.len and intervalOverlaps(ranges[i], new)) return true;

    var merged = new;
    if (i > 0 and ranges[i - 1].b + 1 == merged.a) {
        merged.a = ranges[i - 1].a;
        _ = cov.ranges.orderedRemove(i - 1);
        i -= 1;
    }
    if (i < cov.ranges.items.len and merged.b + 1 == cov.ranges.items[i].a) {
        merged.b = cov.ranges.items[i].b;
        _ = cov.ranges.orderedRemove(i);
    }
    try cov.ranges.insert(self.gpa, i, merged);
    return false;
}

// Optimized unified binding collector
const BindingMap = std.AutoArrayHashMapUnmanaged(ast.StrId, types.TypeId);
const CollectContext = struct { checker: *Checker, map: *BindingMap };

fn collectBindingsWithType(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId, out: *BindingMap) !void {
    var ctx = CollectContext{ .checker = self, .map = out };
    var walker = check_types.PatternWalkerContext{
        .ctx = @ptrCast(&ctx),
        .onExpr = null,
        .onBinding = cbOnBinding,
        .onChildType = cbOnChildType,
    };
    try check_types.walkPattern(&walker, ast_unit, pid, value_ty);
}

fn cbOnBinding(ctx: *void, _: *ast.Ast, _: ast.PatternId, name: ast.StrId, ty: ?types.TypeId) anyerror!void {
    const self: *CollectContext = @ptrCast(@alignCast(ctx));
    if (ty) |t| try self.map.put(self.checker.gpa, name, t);
}

fn cbOnChildType(ctx: *void, _: *ast.Ast, _: ast.PatternId, p_ty: ?types.TypeId, _: ast.PatternId, desc: check_types.PatternChildDesc) ?types.TypeId {
    const self: *CollectContext = @ptrCast(@alignCast(ctx));
    return resolvePatternChildType(self.checker, p_ty, desc);
}

fn checkOrPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) !bool {
    const op = ast_unit.pats.get(.Or, pid);
    const alts = ast_unit.pats.pat_pool.slice(op.alts);
    if (alts.len == 0) return true;

    var base_map = BindingMap{};
    defer base_map.deinit(self.gpa);
    try collectBindingsWithType(self, ast_unit, alts[0], value_ty, &base_map);

    for (alts[1..]) |alt_id| {
        var alt_map = BindingMap{};
        defer alt_map.deinit(self.gpa);
        try collectBindingsWithType(self, ast_unit, alt_id, value_ty, &alt_map);

        if (base_map.count() != alt_map.count()) {
            try self.context.diags.addError(ast_unit.exprs.locs.get(op.loc), .or_pattern_binding_mismatch, .{});
            try self.context.diags.attachNote(self.context.diags.count(), null, .pattern_binding_help);
            return false;
        }

        var it = base_map.iterator();
        while (it.next()) |entry| {
            const alt_ty = alt_map.get(entry.key_ptr.*);
            if (alt_ty == null) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(op.loc), .or_pattern_binding_mismatch, .{});
            } else {
                try self.context.diags.addError(ast_unit.exprs.locs.get(op.loc), .or_pattern_binding_type_mismatch, .{});
            }
            return false;
        }
    }

    var any_ok = false;
    for (alts) |aid| any_ok = (try checkPattern(self, ctx, ast_unit, aid, value_ty, false)) or any_ok;
    return any_ok;
}

fn checkRangePattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) !bool {
    const rp = ast_unit.pats.get(.Range, pid);
    if (!rp.start.isNone()) _ = try self.checkExpr(ctx, ast_unit, rp.start.unwrap());
    if (!rp.end.isNone()) _ = try self.checkExpr(ctx, ast_unit, rp.end.unwrap());

    if (patternIntRange(ast_unit, pid)) |rng| {
        if (rng.b < rng.a) {
            try self.context.diags.addError(ast_unit.exprs.locs.get(rp.loc), .descending_range_pattern, .{});
            return false;
        }
    }
    return check_types.isIntegerKind(self, self.typeKind(value_ty));
}

fn checkStructPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId, emit: bool) !bool {
    if (self.typeKind(value_ty) != .Struct) {
        if (emit) try self.context.diags.addError(ast_unit.exprs.locs.get(ast_unit.pats.get(.Struct, pid).loc), .pattern_type_mismatch, .{});
        return false;
    }
    const st = self.context.type_store.get(.Struct, value_ty);
    const value_fields = self.context.type_store.field_pool.slice(st.fields);
    const pat_fields = ast_unit.pats.field_pool.slice(ast_unit.pats.get(.Struct, pid).fields);

    for (pat_fields) |pfid| {
        const pf = ast_unit.pats.StructField.get(pfid);
        var fty: ?types.TypeId = null;
        for (value_fields) |vfid| {
            const vf = self.context.type_store.Field.get(vfid);
            if (vf.name.eq(pf.name)) {
                fty = vf.ty;
                break;
            }
        }
        if (fty == null) {
            if (emit) try self.context.diags.addError(ast_unit.exprs.locs.get(ast_unit.pats.get(.Struct, pid).loc), .struct_pattern_field_mismatch, .{});
            return false;
        }
        if (!(try checkPattern(self, ctx, ast_unit, pf.pattern, fty.?, false))) return false;
    }
    return true;
}

fn checkVariantStructPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) !bool {
    const vs_pat = ast_unit.pats.get(.VariantStruct, pid);
    const vk = self.typeKind(value_ty);

    if (vk == .Struct) {
        // Redirect to standard struct check if type matches
        const st = self.context.type_store.get(.Struct, value_ty);
        const value_fields = self.context.type_store.field_pool.slice(st.fields);
        const pat_fields = ast_unit.pats.field_pool.slice(vs_pat.fields);

        for (pat_fields) |pfid| {
            const pf = ast_unit.pats.StructField.get(pfid);
            var fty: ?types.TypeId = null;
            for (value_fields) |vfid| {
                const vf = self.context.type_store.Field.get(vfid);
                if (vf.name.eq(pf.name)) {
                    fty = vf.ty;
                    break;
                }
            }
            if (fty == null or !(try checkPattern(self, ctx, ast_unit, pf.pattern, fty.?, false))) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(vs_pat.loc), .struct_pattern_field_mismatch, .{});
                return false;
            }
        }
        return true;
    }

    if (vk != .Variant and vk != .Error) return false;
    const segs = ast_unit.pats.seg_pool.slice(vs_pat.path);
    if (segs.len == 0) return false;

    const payload_ty = findCasePayload(self, value_ty, ast_unit.pats.PathSeg.get(segs[segs.len - 1]).name) orelse return false;
    if (self.typeKind(payload_ty) == .Void) return vs_pat.fields.len == 0;
    if (self.typeKind(payload_ty) != .Struct) return false;

    const st = self.context.type_store.get(.Struct, payload_ty);
    const value_fields = self.context.type_store.field_pool.slice(st.fields);
    const pat_fields = ast_unit.pats.field_pool.slice(vs_pat.fields);

    for (pat_fields) |pfid| {
        const pf = ast_unit.pats.StructField.get(pfid);
        var fty: ?types.TypeId = null;
        for (value_fields) |vfid| {
            const vf = self.context.type_store.Field.get(vfid);
            if (vf.name.eq(pf.name)) {
                fty = vf.ty;
                break;
            }
        }
        if (fty == null or !(try checkPattern(self, ctx, ast_unit, pf.pattern, fty.?, false))) {
            try self.context.diags.addError(ast_unit.exprs.locs.get(vs_pat.loc), .struct_pattern_field_mismatch, .{});
            return false;
        }
    }
    return true;
}

pub fn checkPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId, top_level: bool) anyerror!bool {
    return switch (ast_unit.kind(pid)) {
        .Or => checkOrPattern(self, ctx, ast_unit, pid, value_ty),
        .At => {
            const ap = ast_unit.pats.get(.At, pid);
            _ = try ctx.symtab.declare(.{ .name = ap.binder, .kind = .Var, .is_comptime = false, .loc = ap.loc, .origin_decl = .none(), .origin_param = .none() });
            return try checkPattern(self, ctx, ast_unit, ap.pattern, value_ty, top_level);
        },
        .Binding => {
            const bp = ast_unit.pats.get(.Binding, pid);
            _ = try ctx.symtab.declare(.{ .name = bp.name, .kind = .Var, .is_comptime = false, .loc = bp.loc, .origin_decl = .none(), .origin_param = .none() });
            if (@hasField(@TypeOf(bp), "pattern") and !bp.pattern.isNone()) return try checkPattern(self, ctx, ast_unit, bp.pattern.unwrap(), value_ty, false);
            return true;
        },
        .Range => checkRangePattern(self, ctx, ast_unit, pid, value_ty),
        .VariantTuple => {
            const vt = ast_unit.pats.get(.VariantTuple, pid);
            const vk = self.typeKind(value_ty);
            if (vk != .Variant and vk != .Error) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(vt.loc), .pattern_type_mismatch, .{});
                return false;
            }
            const segs = ast_unit.pats.seg_pool.slice(vt.path);
            const payload_ty = if (segs.len > 0) findCasePayload(self, value_ty, ast_unit.pats.PathSeg.get(segs[segs.len - 1]).name) else null;
            if (payload_ty == null) return false;
            const pk = self.typeKind(payload_ty.?);
            const elems = ast_unit.pats.pat_pool.slice(vt.elems);

            if (pk == .Void) return elems.len == 0;
            if (pk == .Tuple) {
                const tys = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, payload_ty.?).elems);
                if (elems.len != tys.len) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vt.loc), .tuple_arity_mismatch, .{});
                    return false;
                }
                for (elems, 0..) |e, i| if (!(try checkPattern(self, ctx, ast_unit, e, tys[i], false))) return false;
                return true;
            }
            if (elems.len != 1) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(vt.loc), .pattern_type_mismatch, .{});
                return false;
            }
            return try checkPattern(self, ctx, ast_unit, elems[0], payload_ty.?, false);
        },
        .Path => {
            const pp = ast_unit.pats.get(.Path, pid);
            const segs = ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) return false;
            const name = ast_unit.pats.PathSeg.get(segs[segs.len - 1]).name;
            switch (self.typeKind(value_ty)) {
                .Enum => {
                    const members = self.context.type_store.enum_member_pool.slice(self.context.type_store.get(.Enum, value_ty).members);
                    for (members) |m| if (self.context.type_store.EnumMember.get(m).name.eq(name)) return true;
                },
                .Variant, .Error => {
                    const cases = getVariantOrErrorCases(self, value_ty);
                    for (cases) |f| if (self.context.type_store.Field.get(f).name.eq(name)) return self.typeKind(self.context.type_store.Field.get(f).ty) == .Void;
                },
                else => {},
            }
            return false;
        },
        .VariantStruct => checkVariantStructPattern(self, ctx, ast_unit, pid, value_ty),
        .Wildcard => true,
        .Literal => {
            const lp = ast_unit.pats.get(.Literal, pid);
            const lit_ty = try self.checkExpr(ctx, ast_unit, lp.expr);
            if (self.typeKind(lit_ty) == .TypeError) return false;
            if (self.typeKind(lit_ty) == .String and top_level) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(lp.loc), .string_equality_in_match_not_supported, .{});
                return false;
            }
            if (self.assignable(value_ty, lit_ty) != .success) {
                if (top_level) try self.context.diags.addError(ast_unit.exprs.locs.get(lp.loc), .pattern_type_mismatch, .{});
                return false;
            }
            return true;
        },
        .Tuple => {
            if (self.typeKind(value_ty) != .Tuple) {
                if (top_level) try self.context.diags.addError(ast_unit.exprs.locs.get(ast_unit.pats.get(.Tuple, pid).loc), .pattern_shape_mismatch, .{});
                return false;
            }
            const elems = ast_unit.pats.pat_pool.slice(ast_unit.pats.get(.Tuple, pid).elems);
            const types_slice = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, value_ty).elems);
            if (elems.len != types_slice.len) {
                if (top_level) try self.context.diags.addError(ast_unit.exprs.locs.get(ast_unit.pats.get(.Tuple, pid).loc), .tuple_arity_mismatch, .{});
                return false;
            }
            for (elems, 0..) |e, i| if (!(try checkPattern(self, ctx, ast_unit, e, types_slice[i], false))) return false;
            return true;
        },
        .Slice => {
            const ap = ast_unit.pats.get(.Slice, pid);
            const vk = self.typeKind(value_ty);
            if (vk != .Array and vk != .Slice and vk != .DynArray) {
                if (top_level) try self.context.diags.addError(ast_unit.exprs.locs.get(ap.loc), .pattern_type_mismatch, .{});
                return false;
            }
            const elem_ty = switch (vk) {
                .Array => self.context.type_store.get(.Array, value_ty).elem,
                .Slice => self.context.type_store.get(.Slice, value_ty).elem,
                .DynArray => self.context.type_store.get(.DynArray, value_ty).elem,
                else => self.context.type_store.tAny(),
            };
            const elems = ast_unit.pats.pat_pool.slice(ap.elems);
            if (vk == .Array) {
                const arr_len = self.context.type_store.get(.Array, value_ty).len;
                if ((ap.has_rest and elems.len > arr_len) or (!ap.has_rest and elems.len != arr_len)) return false;
            }
            for (elems, 0..) |e, i| {
                if (ap.has_rest and i == ap.rest_index) continue;
                if (!(try checkPattern(self, ctx, ast_unit, e, elem_ty, false))) return false;
            }
            if (ap.has_rest and !ap.rest_binding.isNone()) {
                const is_const = if (vk == .Slice) self.context.type_store.get(.Slice, value_ty).is_const else false;
                if (!(try checkPattern(self, ctx, ast_unit, ap.rest_binding.unwrap(), self.context.type_store.mkSlice(elem_ty, is_const), false))) return false;
            }
            return true;
        },
        .Struct => checkStructPattern(self, ctx, ast_unit, pid, value_ty, top_level),
    };
}

pub fn checkMatch(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const mr = ast_unit.exprs.get(.Match, id);
    const subj_ty = try self.checkExpr(ctx, ast_unit, mr.expr);
    if (self.typeKind(subj_ty) == .TypeError) return self.context.type_store.tTypeError();
    const subj_kind = self.typeKind(subj_ty);
    const value_required = self.isValueReq(ctx);

    var result_ty: ?types.TypeId = null;
    var covered_true = false;
    var covered_false = false;
    var has_unguarded_wildcard = false;
    var has_guarded_wildcard = false;
    var bool_domain = true;
    var enum_domain = true;
    var unguarded_count: usize = 0;

    var enum_covered = std.AutoArrayHashMapUnmanaged(ast.StrId, void){};
    defer enum_covered.deinit(self.gpa);
    const enum_total = if (subj_kind == .Enum) self.context.type_store.enum_member_pool.slice(self.context.type_store.get(.Enum, subj_ty).members).len else 0;

    const is_int_subj = check_types.isIntegerKind(self, subj_kind);
    var int_cov = IntCoverage{};
    defer int_cov.deinit(self.gpa);

    const arms = ast_unit.exprs.arm_pool.slice(mr.arms);
    for (arms) |aid| {
        const arm = ast_unit.exprs.MatchArm.get(aid);
        try self.pushMatchBinding(ctx, arm.pattern, subj_ty);
        defer self.popMatchBinding(ctx);

        _ = try ctx.symtab.push(ctx.symtab.currentId());
        defer ctx.symtab.pop();
        try declareBindingsInPattern(self, ctx, ast_unit, arm.pattern, arm.loc, .anonymous);

        if (!(try checkPattern(self, ctx, ast_unit, arm.pattern, subj_ty, true))) return self.context.type_store.tTypeError();

        if (!arm.guard.isNone()) {
            const gty = try self.checkExpr(ctx, ast_unit, arm.guard.unwrap());
            if (self.typeKind(gty) == .TypeError) return self.context.type_store.tTypeError();
            if (!gty.eq(self.context.type_store.tBool())) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(arm.loc), .non_boolean_condition, .{});
                return self.context.type_store.tTypeError();
            }
            if (patternCoversWildcard(ast_unit, arm.pattern)) has_guarded_wildcard = true;
        } else {
            if (is_int_subj) {
                var aset = IntSet{};
                defer aset.deinit(self.gpa);
                try collectIntSet(self, ast_unit, arm.pattern, &aset);

                if (int_cov.wildcard or (aset.wildcard and int_cov.wildcard) or (!aset.non_int and int_cov.wildcard)) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(arm.loc), .unreachable_match_arm, .{});
                    return self.context.type_store.tTypeError();
                }
                if (aset.wildcard) int_cov.wildcard = true;

                if (!aset.wildcard and !aset.non_int) {
                    for (aset.points.items) |p| if (try coverAddPointDetectOverlap(self, &int_cov, p)) {
                        try self.context.diags.addError(ast_unit.exprs.locs.get(arm.loc), .overlapping_match_arm, .{});
                        return self.context.type_store.tTypeError();
                    };
                    for (aset.ranges.items) |r| if (try coverAddRangeDetectOverlap(self, &int_cov, r)) {
                        try self.context.diags.addError(ast_unit.exprs.locs.get(arm.loc), .overlapping_match_arm, .{});
                        return self.context.type_store.tTypeError();
                    };
                }
            }

            unguarded_count += 1;
            switch (subj_kind) {
                .Bool => {
                    if (patternCoversWildcard(ast_unit, arm.pattern)) has_unguarded_wildcard = true else {
                        const t = patternCoversBoolValue(ast_unit, arm.pattern, true);
                        const f = patternCoversBoolValue(ast_unit, arm.pattern, false);
                        covered_true = covered_true or t;
                        covered_false = covered_false or f;
                        if (!(t or f)) bool_domain = false;
                    }
                },
                .Enum => {
                    if (patternCoversWildcard(ast_unit, arm.pattern)) has_unguarded_wildcard = true else {
                        try recordEnumTagsCovered(self, ast_unit, arm.pattern, subj_ty, &enum_covered);
                        if (!isEnumTagPattern(self, ast_unit, arm.pattern, subj_ty)) enum_domain = false;
                    }
                },
                else => {
                    if (patternCoversWildcard(ast_unit, arm.pattern)) has_unguarded_wildcard = true;
                },
            }
        }

        const body_ty = try self.checkExpr(ctx, ast_unit, arm.body);
        if (self.typeKind(body_ty) == .TypeError) return self.context.type_store.tTypeError();
        if (value_required) {
            if (result_ty == null) result_ty = body_ty else if (!result_ty.?.eq(body_ty)) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(mr.loc), .if_branch_type_mismatch, .{});
                return self.context.type_store.tTypeError();
            }
        }
    }

    var non_exhaustive = false;
    switch (subj_kind) {
        .Bool => if (bool_domain and !has_unguarded_wildcard and !(covered_true and covered_false)) {
            non_exhaustive = true;
        },
        .Enum => if (enum_domain and !has_unguarded_wildcard and enum_total != 0 and enum_covered.count() < enum_total) {
            non_exhaustive = true;
        },
        else => if (unguarded_count == 0 and has_guarded_wildcard) {
            non_exhaustive = true;
        },
    }

    if (non_exhaustive) {
        try self.context.diags.addError(ast_unit.exprs.locs.get(mr.loc), .non_exhaustive_match, .{});
        const missing = switch (subj_kind) {
            .Bool => try missingBoolMatchCases(self, covered_true, covered_false),
            .Enum => try missingEnumMatchCases(self, subj_ty, &enum_covered),
            else => null,
        };
        if (missing) |m| try self.context.diags.attachNoteArgs(self.context.diags.count() - 1, null, .exhaustiveness_hint, checker.StringNotePayload{ .value = m });
        try self.context.diags.attachNoteArgs(self.context.diags.count() - 1, null, .add_wildcard, .{});
        return self.context.type_store.tTypeError();
    }
    return if (value_required) (result_ty orelse self.context.type_store.tVoid()) else self.context.type_store.tVoid();
}

fn patternIntLiteral(ast_unit: *ast.Ast, pid: ast.PatternId) ?i64 {
    return switch (ast_unit.kind(pid)) {
        .Literal => {
            const lp = ast_unit.pats.get(.Literal, pid);
            if (ast_unit.kind(lp.expr) != .Literal) return null;
            const lit = ast_unit.exprs.get(.Literal, lp.expr);
            if (lit.kind != .int or !lit.data.int.valid or lit.data.int.value > std.math.maxInt(i64)) return null;
            return @intCast(lit.data.int.value);
        },
        .At => patternIntLiteral(ast_unit, ast_unit.pats.get(.At, pid).pattern),
        else => null,
    };
}

fn patternIntRange(ast_unit: *ast.Ast, pid: ast.PatternId) ?Interval {
    const rp = switch (ast_unit.kind(pid)) {
        .Range => ast_unit.pats.get(.Range, pid),
        .At => ast_unit.pats.get(.Range, ast_unit.pats.get(.At, pid).pattern),
        else => return null,
    };
    if (rp.start.isNone() or rp.end.isNone()) return null;
    const s_val = patternIntLiteral(ast_unit, ast_unit.pats.add(.Literal, .{ .expr = rp.start.unwrap(), .loc = rp.loc })) orelse return null;
    const e_val_raw = patternIntLiteral(ast_unit, ast_unit.pats.add(.Literal, .{ .expr = rp.end.unwrap(), .loc = rp.loc })) orelse return null;
    const e_val = if (rp.inclusive_right) e_val_raw else e_val_raw - 1;
    if (e_val < s_val) return null;
    return .{ .a = s_val, .b = e_val };
}

fn patternCoversWildcard(ast_unit: *ast.Ast, pid: ast.PatternId) bool {
    return switch (ast_unit.kind(pid)) {
        .Wildcard => true,
        .Or => blk: {
            for (ast_unit.pats.pat_pool.slice(ast_unit.pats.get(.Or, pid).alts)) |aid| if (patternCoversWildcard(ast_unit, aid)) break :blk true;
            break :blk false;
        },
        .At => patternCoversWildcard(ast_unit, ast_unit.pats.get(.At, pid).pattern),
        else => false,
    };
}

fn patternCoversBoolValue(ast_unit: *ast.Ast, pid: ast.PatternId, val: bool) bool {
    switch (ast_unit.kind(pid)) {
        .Path => {
            const segs = ast_unit.pats.seg_pool.slice(ast_unit.pats.get(.Path, pid).segments);
            if (segs.len == 0) return false;
            const s = ast_unit.exprs.strs.get(ast_unit.pats.PathSeg.get(segs[segs.len - 1]).name);
            return (val and std.mem.eql(u8, s, "true")) or (!val and std.mem.eql(u8, s, "false"));
        },
        .Literal => {
            const lp = ast_unit.pats.get(.Literal, pid);
            if (ast_unit.kind(lp.expr) != .Literal) return false;
            const lit = ast_unit.exprs.get(.Literal, lp.expr);
            return lit.kind == .bool and lit.data.bool == val;
        },
        .Or => {
            for (ast_unit.pats.pat_pool.slice(ast_unit.pats.get(.Or, pid).alts)) |aid| if (patternCoversBoolValue(ast_unit, aid, val)) return true;
            return false;
        },
        .At => return patternCoversBoolValue(ast_unit, ast_unit.pats.get(.At, pid).pattern, val),
        else => return false,
    }
}

fn recordEnumTagsCovered(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, enum_ty: types.TypeId, out: *std.AutoArrayHashMapUnmanaged(ast.StrId, void)) !void {
    switch (ast_unit.kind(pid)) {
        .Path => {
            const segs = ast_unit.pats.seg_pool.slice(ast_unit.pats.get(.Path, pid).segments);
            if (segs.len == 0) return;
            const name = ast_unit.pats.PathSeg.get(segs[segs.len - 1]).name;
            for (self.context.type_store.enum_member_pool.slice(self.context.type_store.get(.Enum, enum_ty).members)) |mid| {
                const m = self.context.type_store.EnumMember.get(mid);
                if (m.name.eq(name)) {
                    _ = try out.put(self.gpa, m.name, {});
                    return;
                }
            }
        },
        .Or => for (ast_unit.pats.pat_pool.slice(ast_unit.pats.get(.Or, pid).alts)) |aid| try recordEnumTagsCovered(self, ast_unit, aid, enum_ty, out),
        .At => try recordEnumTagsCovered(self, ast_unit, ast_unit.pats.get(.At, pid).pattern, enum_ty, out),
        else => {},
    }
}

fn isEnumTagPattern(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, enum_ty: types.TypeId) bool {
    return switch (ast_unit.kind(pid)) {
        .Wildcard => true,
        .Path => blk: {
            const segs = ast_unit.pats.seg_pool.slice(ast_unit.pats.get(.Path, pid).segments);
            if (segs.len == 0) break :blk false;
            const name = ast_unit.pats.PathSeg.get(segs[segs.len - 1]).name;
            for (self.context.type_store.enum_member_pool.slice(self.context.type_store.get(.Enum, enum_ty).members)) |mid| if (self.context.type_store.EnumMember.get(mid).name.eq(name)) break :blk true;
            break :blk false;
        },
        .Or => blk: {
            for (ast_unit.pats.pat_pool.slice(ast_unit.pats.get(.Or, pid).alts)) |aid| if (!isEnumTagPattern(self, ast_unit, aid, enum_ty)) break :blk false;
            break :blk true;
        },
        .At => isEnumTagPattern(self, ast_unit, ast_unit.pats.get(.At, pid).pattern, enum_ty),
        else => false,
    };
}

fn missingBoolMatchCases(self: *Checker, covered_true: bool, covered_false: bool) !?ast.StrId {
    var buf = std.ArrayList(u8){};
    defer buf.deinit(self.gpa);
    if (!covered_true) try buf.appendSlice(self.gpa, "true");
    if (!covered_true and !covered_false) try buf.appendSlice(self.gpa, ", ");
    if (!covered_false) try buf.appendSlice(self.gpa, "false");
    return if (buf.items.len > 0) self.context.interner.intern(buf.items) else null;
}

fn missingEnumMatchCases(self: *Checker, enum_ty: types.TypeId, covered: *std.AutoArrayHashMapUnmanaged(ast.StrId, void)) !?ast.StrId {
    var buf = std.ArrayList(u8){};
    defer buf.deinit(self.gpa);
    const members = self.context.type_store.enum_member_pool.slice(self.context.type_store.get(.Enum, enum_ty).members);
    var first = true;
    for (members) |mid| {
        const m = self.context.type_store.EnumMember.get(mid);
        if (covered.get(m.name) == null) {
            if (!first) try buf.appendSlice(self.gpa, ", ");
            try buf.appendSlice(self.gpa, self.context.interner.get(m.name));
            first = false;
        }
    }
    return if (buf.items.len > 0) self.context.interner.intern(buf.items) else null;
}

pub const BindingOrigin = union(enum) { decl: ast.DeclId, param: ast.ParamId, anonymous };

pub fn declareBindingsInPattern(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, pid: ast.PatternId, loc: ast.LocId, origin: BindingOrigin) !void {
    var decl_ctx = PatternBindingDeclarer{ .checker = self, .ctx = ctx, .loc = loc, .origin = origin };
    var walker = check_types.PatternWalkerContext{ .ctx = @ptrCast(&decl_ctx), .onExpr = null, .onBinding = patternBindingDeclarerOnBinding, .onChildType = null };
    try check_types.walkPattern(&walker, ast_unit, pid, null);
}

const PatternBindingDeclarer = struct { checker: *Checker, ctx: *Checker.CheckerContext, loc: ast.LocId, origin: BindingOrigin };
fn patternBindingDeclarerOnBinding(ctx: *void, ast_unit: *ast.Ast, _: ast.PatternId, name: ast.StrId, _: ?types.TypeId) anyerror!void {
    const d: *PatternBindingDeclarer = @ptrCast(@alignCast(ctx));
    const is_comptime = switch (d.origin) {
        .decl => |did| switch (ast_unit.kind(ast_unit.exprs.Decl.get(did).value)) {
            .Literal, .MlirBlock, .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType, .MapType, .ComptimeBlock, .TypeOf => true,
            else => false,
        },
        .param => |par| ast_unit.exprs.Param.get(par).is_comptime,
        .anonymous => false,
    };
    _ = try d.ctx.symtab.declare(.{ .name = name, .kind = if (d.origin == .param) .Param else .Var, .is_comptime = is_comptime, .loc = d.loc, .origin_decl = if (d.origin == .decl) .some(d.origin.decl) else .none(), .origin_param = if (d.origin == .param) .some(d.origin.param) else .none() });
}

pub const PatternShapeCheck = enum { ok, tuple_arity_mismatch, struct_pattern_field_mismatch, pattern_shape_mismatch };

const PatternShapeMode = enum { decl, assign };

fn checkPatternShape(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId, mode: PatternShapeMode) PatternShapeCheck {
    const pk = self.typeKind(value_ty);
    switch (ast_unit.kind(pid)) {
        .Wildcard, .Binding => return .ok,
        .Tuple => {
            if (pk != .Tuple) return .pattern_shape_mismatch;
            const vals = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, value_ty).elems);
            const elems = ast_unit.pats.pat_pool.slice(ast_unit.pats.get(.Tuple, pid).elems);
            if (elems.len != vals.len) return .tuple_arity_mismatch;
            for (elems, 0..) |e, i| if (checkPatternShape(self, ast_unit, e, vals[i], mode) != .ok) return .pattern_shape_mismatch;
            return .ok;
        },
        .Struct => {
            if (pk != .Struct) return .pattern_shape_mismatch;
            const vfields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, value_ty).fields);
            for (ast_unit.pats.field_pool.slice(ast_unit.pats.get(.Struct, pid).fields)) |pfid| {
                const pf = ast_unit.pats.StructField.get(pfid);
                var fty: ?types.TypeId = null;
                for (vfields) |vfid| {
                    const vf = self.context.type_store.Field.get(vfid);
                    if (vf.name.eq(pf.name)) {
                        fty = vf.ty;
                        break;
                    }
                }
                if (fty == null) return .struct_pattern_field_mismatch;
                if (checkPatternShape(self, ast_unit, pf.pattern, fty.?, mode) != .ok) return .pattern_shape_mismatch;
            }
            return .ok;
        },
        .Slice => {
            if (pk != .Array and pk != .Slice and pk != .DynArray) return .pattern_shape_mismatch;
            const elem_ty = switch (pk) {
                .Array => self.context.type_store.get(.Array, value_ty).elem,
                .Slice => self.context.type_store.get(.Slice, value_ty).elem,
                .DynArray => self.context.type_store.get(.DynArray, value_ty).elem,
                else => self.context.type_store.tAny(),
            };
            const sl = ast_unit.pats.get(.Slice, pid);
            const elems = ast_unit.pats.pat_pool.slice(sl.elems);
            if (pk == .Array) {
                const len = self.context.type_store.get(.Array, value_ty).len;
                if ((sl.has_rest and elems.len > len) or (!sl.has_rest and elems.len != len)) return .pattern_shape_mismatch;
            }
            for (elems) |e| if (checkPatternShape(self, ast_unit, e, elem_ty, mode) != .ok) return .pattern_shape_mismatch;
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const is_const = if (pk == .Slice) self.context.type_store.get(.Slice, value_ty).is_const else false;
                if (checkPatternShape(self, ast_unit, sl.rest_binding.unwrap(), self.context.type_store.mkSlice(elem_ty, is_const), mode) != .ok) return .pattern_shape_mismatch;
            }
            return .ok;
        },
        else => return if (mode == .decl) .ok else .pattern_shape_mismatch,
    }
}

pub fn checkPatternShapeForDecl(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) PatternShapeCheck {
    return checkPatternShape(self, ast_unit, pid, value_ty, .decl);
}

/// Validate assignment patterns (binding/tuple/struct/slice) against a value type.
pub fn checkPatternShapeForAssignPattern(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) PatternShapeCheck {
    return checkPatternShape(self, ast_unit, pid, value_ty, .assign);
}

pub fn checkPatternShapeForAssignExpr(self: *Checker, ast_unit: *ast.Ast, expr: ast.ExprId, value_ty: types.TypeId) PatternShapeCheck {
    const vk = self.typeKind(value_ty);
    switch (ast_unit.kind(expr)) {
        .Ident => return .ok,
        .TupleLit => {
            if (vk != .Tuple) return .pattern_shape_mismatch;
            const elems = ast_unit.exprs.expr_pool.slice(ast_unit.exprs.get(.TupleLit, expr).elems);
            const tys = self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, value_ty).elems);
            if (elems.len != tys.len) return .tuple_arity_mismatch;
            for (elems, 0..) |e, i| if (checkPatternShapeForAssignExpr(self, ast_unit, e, tys[i]) != .ok) return .pattern_shape_mismatch;
            return .ok;
        },
        .StructLit => {
            if (vk != .Struct) return .pattern_shape_mismatch;
            const vfields = self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, value_ty).fields);
            for (ast_unit.exprs.sfv_pool.slice(ast_unit.exprs.get(.StructLit, expr).fields)) |pfid| {
                const pf = ast_unit.exprs.StructFieldValue.get(pfid);
                if (pf.name.isNone()) return .pattern_shape_mismatch;
                var fty: ?types.TypeId = null;
                for (vfields) |vfid| {
                    const vf = self.context.type_store.Field.get(vfid);
                    if (vf.name.eq(pf.name.unwrap())) {
                        fty = vf.ty;
                        break;
                    }
                }
                if (fty == null) return .struct_pattern_field_mismatch;
                if (checkPatternShapeForAssignExpr(self, ast_unit, pf.value, fty.?) != .ok) return .pattern_shape_mismatch;
            }
            return .ok;
        },
        .ArrayLit => {
            if (vk != .Array and vk != .Slice and vk != .DynArray) return .pattern_shape_mismatch;
            const elem_ty = switch (vk) {
                .Array => self.context.type_store.get(.Array, value_ty).elem,
                .Slice => self.context.type_store.get(.Slice, value_ty).elem,
                .DynArray => self.context.type_store.get(.DynArray, value_ty).elem,
                else => self.context.type_store.tAny(),
            };
            const elems = ast_unit.exprs.expr_pool.slice(ast_unit.exprs.get(.ArrayLit, expr).elems);
            var has_rest = false;
            for (elems) |e| {
                if (ast_unit.kind(e) == .Range) {
                    if (has_rest) return .pattern_shape_mismatch;
                    has_rest = true;
                    const rr = ast_unit.exprs.get(.Range, e);
                    if (!rr.end.isNone() and ast_unit.kind(rr.end.unwrap()) != .Ident) return .pattern_shape_mismatch;
                    continue;
                }
                if (checkPatternShapeForAssignExpr(self, ast_unit, e, elem_ty) != .ok) return .pattern_shape_mismatch;
            }
            if (vk == .Array) {
                const len = self.context.type_store.get(.Array, value_ty).len;
                if ((has_rest and elems.len - 1 > len) or (!has_rest and elems.len != len)) return .pattern_shape_mismatch;
            }
            return .ok;
        },
        else => return .pattern_shape_mismatch,
    }
}

pub fn collectPatternBindings(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, list: *std.ArrayList(ast.StrId)) !void {
    var ctx = PatternBindingCollector{ .gpa = self.gpa, .list = list };
    var walker = check_types.PatternWalkerContext{ .ctx = @ptrCast(&ctx), .onExpr = null, .onBinding = patternBindingCollectorOnBinding, .onChildType = null };
    try check_types.walkPattern(&walker, ast_unit, pid, null);
}
const PatternBindingCollector = struct { gpa: std.mem.Allocator, list: *std.ArrayList(ast.StrId) };
fn patternBindingCollectorOnBinding(ctx: *void, _: *ast.Ast, _: ast.PatternId, name: ast.StrId, _: ?types.TypeId) anyerror!void {
    const c: *PatternBindingCollector = @ptrCast(@alignCast(ctx));
    try c.list.append(c.gpa, name);
}

// Unified Child Type Resolver
fn resolvePatternChildType(self: *Checker, parent_ty: ?types.TypeId, desc: check_types.PatternChildDesc) ?types.TypeId {
    if (parent_ty == null) return null;
    const ty = parent_ty.?;
    const pk = self.typeKind(ty);
    return switch (desc) {
        .TupleElem => if (pk == .Tuple) self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, ty).elems)[desc.TupleElem] else null,
        .StructField => blk: {
            if (pk != .Struct) break :blk null;
            for (self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, ty).fields)) |fid| {
                const f = self.context.type_store.Field.get(fid);
                if (f.name.eq(desc.StructField)) return f.ty;
            }
            break :blk null;
        },
        .VariantTupleElem => blk: {
            if (pk != .Variant and pk != .Error) break :blk null;
            const pay = findCasePayload(self, ty, desc.VariantTupleElem.case_name) orelse return null;
            if (self.typeKind(pay) == .Tuple) return self.context.type_store.type_pool.slice(self.context.type_store.get(.Tuple, pay).elems)[desc.VariantTupleElem.index] else return if (desc.VariantTupleElem.index == 0) pay else null;
        },
        .VariantStructField => blk: {
            const sub_ty = if (pk == .Struct) ty else if (pk == .Variant or pk == .Error) (findCasePayload(self, ty, desc.VariantStructField.case_name) orelse return null) else return null;
            if (self.typeKind(sub_ty) != .Struct) return null;
            for (self.context.type_store.field_pool.slice(self.context.type_store.get(.Struct, sub_ty).fields)) |fid| {
                const f = self.context.type_store.Field.get(fid);
                if (f.name.eq(desc.VariantStructField.field_name)) return f.ty;
            }
            break :blk null;
        },
        .SliceElem => switch (pk) {
            .Array => self.context.type_store.get(.Array, ty).elem,
            .Slice => self.context.type_store.get(.Slice, ty).elem,
            .DynArray => self.context.type_store.get(.DynArray, ty).elem,
            else => null,
        },
        .SliceRest => blk: {
            const elem = switch (pk) {
                .Array => self.context.type_store.get(.Array, ty).elem,
                .Slice => self.context.type_store.get(.Slice, ty).elem,
                .DynArray => self.context.type_store.get(.DynArray, ty).elem,
                else => break :blk null,
            };
            const is_const = if (pk == .Slice) self.context.type_store.get(.Slice, ty).is_const else false;
            break :blk self.context.type_store.mkSlice(elem, is_const);
        },
        .OrAlt, .AtPattern => ty,
    };
}

// Single-binding type resolver (preserved for external use if needed, but optimized to use shared logic)
pub fn bindingTypeInPattern(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, name: ast.StrId, value_ty: types.TypeId) ?types.TypeId {
    var ctx = struct { checker: *Checker, target: ast.StrId, res: ?types.TypeId = null }{ .checker = self, .target = name };
    var walker = check_types.PatternWalkerContext{ .ctx = @ptrCast(&ctx), .onExpr = null, .onBinding = struct {
        fn f(c: *void, _: *ast.Ast, _: ast.PatternId, n: ast.StrId, t: ?types.TypeId) !void {
            const ptr: *@TypeOf(ctx) = @ptrCast(@alignCast(c));
            if (n.eq(ptr.target)) ptr.res = t;
        }
    }.f, .onChildType = struct {
        fn f(c: *void, _: *ast.Ast, _: ast.PatternId, pt: ?types.TypeId, _: ast.PatternId, d: check_types.PatternChildDesc) ?types.TypeId {
            return resolvePatternChildType(@as(*@TypeOf(ctx), @ptrCast(@alignCast(c))).checker, pt, d);
        }
    }.f };
    check_types.walkPattern(&walker, ast_unit, pid, value_ty) catch unreachable;
    return ctx.res;
}
