const Checker = @import("checker.zig").Checker;
const std = @import("std");
const ast = @import("ast.zig");
const types = @import("types.zig");
const symbols = @import("symbols.zig");
const check_types = @import("check_types.zig");

inline fn tk(self: *Checker, ty: types.TypeId) types.TypeKind {
    return self.context.type_info.store.index.kinds.items[ty.toRaw()];
}
inline fn row(self: *Checker, ty: types.TypeId) u32 {
    return self.context.type_info.store.index.rows.items[ty.toRaw()];
}
inline fn getVariantOrErrorCases(self: *Checker, ty: types.TypeId) []const types.FieldId {
    const k = tk(self, ty);
    return if (k == .Variant)
        self.context.type_info.store.field_pool.slice(self.context.type_info.store.Variant.get(row(self, ty)).variants)
    else
        self.context.type_info.store.field_pool.slice(self.context.type_info.store.Error.get(row(self, ty)).variants);
}
inline fn findCasePayload(self: *Checker, ty: types.TypeId, case_name: ast.StrId) ?types.TypeId {
    const cases = getVariantOrErrorCases(self, ty);
    for (cases) |fid| {
        const f = self.context.type_info.store.Field.get(fid.toRaw());
        if (f.name.toRaw() == case_name.toRaw()) return f.ty;
    }
    return null;
}

const Interval = struct { a: i64, b: i64 };

const IntSet = struct {
    wildcard: bool = false, // matches everything (e.g. `_` or contains `_` via `Or`)
    non_int: bool = false, // contains non-integer patterns; skip special int analysis
    points: std.ArrayListUnmanaged(i64) = .{},
    ranges: std.ArrayListUnmanaged(Interval) = .{},

    pub fn deinit(self: *IntSet, gpa: std.mem.Allocator) void {
        self.points.deinit(gpa);
        self.ranges.deinit(gpa);
    }
};

const IntCoverage = struct {
    wildcard: bool = false,
    points: std.AutoArrayHashMapUnmanaged(i64, void) = .{},
    // invariant: non-overlapping, sorted by a; merged on insert
    ranges: std.ArrayListUnmanaged(Interval) = .{},

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

/// Flattens a pattern into integer “points” and “intervals”, handling `Or` and `At`.
/// Leaves `non_int` set if we encounter shapes that aren't int literal/range/wildcard.
/// Treats `_` as wildcard; **NOTE:** a Binding is *not* treated as wildcard here
/// (consistent with existing exhaustiveness logic).
fn collectIntSet(self: *Checker, pid: ast.PatternId, out: *IntSet) !void {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Wildcard => {
            out.wildcard = true;
        },
        .Literal => {
            if (patternIntLiteral(self, pid)) |lit| {
                try out.points.append(self.gpa, lit);
            } else {
                out.non_int = true;
            }
        },
        .Range => {
            if (try patternIntRange(self, pid)) |rr| {
                try out.ranges.append(self.gpa, .{ .a = rr.a, .b = rr.b });
            } else {
                // either not an int range or invalid/empty
                out.non_int = true;
            }
        },
        .Or => {
            const op = self.ast_unit.pats.get(.Or, pid);
            const alts = self.ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| {
                try collectIntSet(self, aid, out);
                if (out.wildcard) break; // early if already everything
            }
        },
        .At => {
            const ap = self.ast_unit.pats.get(.At, pid);
            try collectIntSet(self, ap.pattern, out);
        },
        // everything else: treat as "non-int" for this specialized analysis
        else => out.non_int = true,
    }
}

/// Returns true if adding `lit` overlaps *already-covered* space.
fn coverAddPointDetectOverlap(self: *Checker, cov: *IntCoverage, lit: i64) !bool {
    if (cov.points.contains(lit)) return true;
    var i: usize = 0;
    while (i < cov.ranges.items.len) : (i += 1) {
        if (pointInInterval(lit, cov.ranges.items[i])) return true;
    }
    _ = try cov.points.put(self.gpa, lit, {});
    return false;
}

/// Insert interval with detection + merge. Returns true if it overlapped existing.
fn coverAddRangeDetectOverlap(self: *Checker, cov: *IntCoverage, new: Interval) !bool {
    // Check points against interval
    var it = cov.points.iterator();
    while (it.next()) |entry| {
        const p = entry.key_ptr.*;
        if (pointInInterval(p, new)) return true;
    }
    // Find insertion position, detect overlap, and merge if not overlapping
    var i: usize = 0;
    while (i < cov.ranges.items.len and cov.ranges.items[i].a <= new.a) : (i += 1) {}
    // Check neighbor on the left
    if (i > 0 and intervalOverlaps(cov.ranges.items[i - 1], new)) return true;
    // Check neighbor on the right
    if (i < cov.ranges.items.len and intervalOverlaps(cov.ranges.items[i], new)) return true;

    // Merge with adjacent if touching (optional). We keep "strict non-overlap" for diagnostics,
    // but coalesce abutting intervals for tighter coverage (a.b+1 == new.a etc.).
    var merged = new;
    // Merge left if adjacent
    if (i > 0 and cov.ranges.items[i - 1].b + 1 == merged.a) {
        merged.a = cov.ranges.items[i - 1].a;
        // remove left
        _ = cov.ranges.orderedRemove(i - 1);
        i -= 1;
    }
    // Merge right if adjacent
    if (i < cov.ranges.items.len and merged.b + 1 == cov.ranges.items[i].a) {
        merged.b = cov.ranges.items[i].b;
        _ = cov.ranges.orderedRemove(i);
    }

    try cov.ranges.insert(self.gpa, i, merged);
    return false;
}

pub fn checkPattern(
    self: *Checker,
    pid: ast.PatternId,
    value_ty: types.TypeId,
    top_level: bool,
) !bool {
    // Emit diagnostics only on top-level shape checks, but keep inner calls quiet.
    const emit = top_level;
    const kind = self.ast_unit.pats.index.kinds.items[pid.toRaw()];

    switch (kind) {
        .Or => {
            const op = self.ast_unit.pats.get(.Or, pid);
            const alts = self.ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| {
                if (try checkPattern(self, aid, value_ty, false)) return true;
            }
            return false;
        },
        .At => {
            const ap = self.ast_unit.pats.get(.At, pid);
            // x @ pat : bind x as a Var and check subpattern.
            _ = try self.symtab.declare(.{
                .name = ap.binder,
                .kind = .Var,
                .loc = ap.loc,
                .origin_decl = ast.OptDeclId.none(),
                .origin_param = ast.OptParamId.none(),
            });
            return try checkPattern(self, ap.pattern, value_ty, false);
        },
        .Range => {
            // Accept integer subjects only.
            return check_types.isIntegerKind(self, tk(self, value_ty));
        },
        .VariantTuple => {
            const vt_pat = self.ast_unit.pats.get(.VariantTuple, pid);
            const vk = tk(self, value_ty);
            if (vk != .Variant and vk != .Error) return false;

            const segs = self.ast_unit.pats.seg_pool.slice(vt_pat.path);
            if (segs.len == 0) return false;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());

            const payload_ty = findCasePayload(self, value_ty, last.name) orelse return false;
            const pk = tk(self, payload_ty);

            const elems = self.ast_unit.pats.pat_pool.slice(vt_pat.elems);
            if (pk == .Void) return elems.len == 0;

            if (pk != .Tuple) return false;
            const tup = self.context.type_info.store.Tuple.get(row(self, payload_ty));
            const tys = self.context.type_info.store.type_pool.slice(tup.elems);
            if (elems.len != tys.len) return false;

            for (elems, 0..) |eid, i| {
                if (!(try checkPattern(self, eid, tys[i], false))) return false;
            }
            return true;
        },
        .Path => {
            // Enum tags and tag-only Variant/Error patterns.
            const pp = self.ast_unit.pats.get(.Path, pid);
            const segs = self.ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) return false;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());
            const vk = tk(self, value_ty);

            switch (vk) {
                .Enum => {
                    const er = self.context.type_info.store.Enum.get(row(self, value_ty));
                    const members = self.context.type_info.store.enum_member_pool.slice(er.members);
                    for (members) |mid| {
                        const m = self.context.type_info.store.EnumMember.get(mid.toRaw());
                        if (m.name.toRaw() == last.name.toRaw()) return true;
                    }
                    return false;
                },
                .Variant, .Error => {
                    const cases = getVariantOrErrorCases(self, value_ty);
                    for (cases) |fid| {
                        const f = self.context.type_info.store.Field.get(fid.toRaw());
                        if (f.name.toRaw() == last.name.toRaw()) {
                            // tag-only allowed only when payload is void
                            return tk(self, f.ty) == .Void;
                        }
                    }
                    return false;
                },
                else => return false,
            }
        },
        .VariantStruct => {
            const vs_pat = self.ast_unit.pats.get(.VariantStruct, pid);
            const vk = tk(self, value_ty);

            // Struct sugar: allow `Type { ... }` against a struct value.
            if (vk != .Variant and vk != .Error) {
                if (vk == .Struct) {
                    const st = self.context.type_info.store.Struct.get(row(self, value_ty));
                    const value_fields = self.context.type_info.store.field_pool.slice(st.fields);
                    const pat_fields = self.ast_unit.pats.field_pool.slice(vs_pat.fields);

                    for (pat_fields) |pfid| {
                        const pf = self.ast_unit.pats.StructField.get(pfid.toRaw());
                        var found = false;
                        for (value_fields) |vfid| {
                            const vf = self.context.type_info.store.Field.get(vfid.toRaw());
                            if (vf.name.toRaw() == pf.name.toRaw()) {
                                found = true;
                                break;
                            }
                        }
                        if (!found) return false;
                    }
                    return true;
                }
                return false;
            }

            const segs = self.ast_unit.pats.seg_pool.slice(vs_pat.path);
            if (segs.len == 0) return false;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());

            const payload_ty = findCasePayload(self, value_ty, last.name) orelse return false;
            const pk = tk(self, payload_ty);

            if (pk == .Void) return vs_pat.fields.len == 0;
            if (pk != .Struct) return false;

            const st = self.context.type_info.store.Struct.get(row(self, payload_ty));
            const value_fields = self.context.type_info.store.field_pool.slice(st.fields);
            const pat_fields = self.ast_unit.pats.field_pool.slice(vs_pat.fields);

            for (pat_fields) |pfid| {
                const pf = self.ast_unit.pats.StructField.get(pfid.toRaw());
                var fty: ?types.TypeId = null;
                for (value_fields) |vfid| {
                    const vf = self.context.type_info.store.Field.get(vfid.toRaw());
                    if (vf.name.toRaw() == pf.name.toRaw()) {
                        fty = vf.ty;
                        break;
                    }
                }
                if (fty == null) return false;
                if (!(try checkPattern(self, pf.pattern, fty.?, false))) return false;
            }
            return true;
        },
        .Binding => {
            const bp = self.ast_unit.pats.get(.Binding, pid);
            // Declare the bound name.
            _ = try self.symtab.declare(.{
                .name = bp.name,
                .kind = .Var,
                .loc = bp.loc,
                .origin_decl = ast.OptDeclId.none(),
                .origin_param = ast.OptParamId.none(),
            });

            // Support nested binding subpattern if present in this AST.
            if (@hasField(@TypeOf(bp), "pattern")) {
                if (!bp.pattern.isNone()) {
                    return try checkPattern(self, bp.pattern.unwrap(), value_ty, false);
                }
            }
            return true;
        },
        .Wildcard => return true,
        .Literal => {
            // Literal patterns must type-check against subject type.
            const lp = self.ast_unit.pats.get(.Literal, pid);
            const pattern_loc = self.ast_unit.exprs.locs.get(lp.loc);
            const lit_expr_id = lp.expr;
            const lit_ty = (try self.checkExpr(lit_expr_id)) orelse return false;

            if (self.assignable(value_ty, lit_ty) != .success) {
                if (emit) try self.context.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                return false;
            }
            // Future: evaluate and compare values if not top-level.
            return true;
        },
        .Tuple => {
            const tp = self.ast_unit.pats.get(.Tuple, pid);
            const pattern_loc = self.ast_unit.exprs.locs.get(tp.loc);
            if (tk(self, value_ty) != .Tuple) {
                if (emit) try self.context.diags.addError(pattern_loc, .pattern_shape_mismatch, .{});
                return false;
            }
            const value_tuple_ty = self.context.type_info.store.Tuple.get(row(self, value_ty));
            const pattern_elems = self.ast_unit.pats.pat_pool.slice(tp.elems);
            const value_elems = self.context.type_info.store.type_pool.slice(value_tuple_ty.elems);

            if (pattern_elems.len != value_elems.len) {
                if (emit) try self.context.diags.addError(pattern_loc, .tuple_arity_mismatch, .{});
                return false;
            }
            for (pattern_elems, 0..) |pat_elem_id, i| {
                if (!(try checkPattern(self, pat_elem_id, value_elems[i], false))) return false;
            }
            return true;
        },
        .Slice => {
            const ap = self.ast_unit.pats.get(.Slice, pid);
            const pattern_loc = self.ast_unit.exprs.locs.get(ap.loc);
            const vk = tk(self, value_ty);
            if (vk != .Array and vk != .Slice and vk != .DynArray) {
                if (emit) try self.context.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                return false;
            }

            const elem_ty: types.TypeId = switch (vk) {
                .Array => self.context.type_info.store.Array.get(row(self, value_ty)).elem,
                .Slice => self.context.type_info.store.Slice.get(row(self, value_ty)).elem,
                .DynArray => self.context.type_info.store.DynArray.get(row(self, value_ty)).elem,
                else => unreachable,
            };

            const pattern_elems = self.ast_unit.pats.pat_pool.slice(ap.elems);
            if (vk == .Array) {
                const arr = self.context.type_info.store.Array.get(row(self, value_ty));
                // Allow rest to capture an empty slice; just require explicit <= length.
                if (ap.has_rest) {
                    if (pattern_elems.len > arr.len) return false;
                } else {
                    if (pattern_elems.len != arr.len) return false;
                }
            }

            for (pattern_elems, 0..) |pat_elem_id, i| {
                if (ap.has_rest and i == ap.rest_index) continue; // skip the rest placeholder
                if (!(try checkPattern(self, pat_elem_id, elem_ty, false))) return false;
            }

            if (ap.has_rest and !ap.rest_binding.isNone()) {
                if (!(try checkPattern(self, ap.rest_binding.unwrap(), self.context.type_info.store.mkSlice(elem_ty), false)))
                    return false;
            }
            return true;
        },
        .Struct => {
            const sp = self.ast_unit.pats.get(.Struct, pid);
            const pattern_loc = self.ast_unit.exprs.locs.get(sp.loc);
            if (tk(self, value_ty) != .Struct) {
                if (emit) try self.context.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                return false;
            }
            const value_struct_ty = self.context.type_info.store.Struct.get(row(self, value_ty));
            const pattern_fields = self.ast_unit.pats.field_pool.slice(sp.fields);
            const value_fields = self.context.type_info.store.field_pool.slice(value_struct_ty.fields);

            for (pattern_fields) |pat_field_id| {
                const pat_field = self.ast_unit.pats.StructField.get(pat_field_id.toRaw());
                var match_ty: ?types.TypeId = null;

                for (value_fields) |val_field_id| {
                    const val_field = self.context.type_info.store.Field.get(val_field_id.toRaw());
                    if (pat_field.name.toRaw() == val_field.name.toRaw()) {
                        match_ty = val_field.ty;
                        break;
                    }
                }

                if (match_ty == null) {
                    if (emit) try self.context.diags.addError(pattern_loc, .struct_pattern_field_mismatch, .{});
                    return false;
                }
                if (!(try checkPattern(self, pat_field.pattern, match_ty.?, false))) return false;
            }
            return true;
        },
    }
}

pub fn checkMatch(self: *Checker, id: ast.ExprId) !?types.TypeId {
    const mr = self.ast_unit.exprs.get(.Match, id);
    const subj_ty_opt = try self.checkExpr(mr.expr);
    if (subj_ty_opt == null) return null;
    const subj_ty = subj_ty_opt.?;
    const subj_kind = tk(self, subj_ty);
    const value_required = self.isValueReq();

    var result_ty: ?types.TypeId = null;

    // Exhaustiveness tracking (finite domains)
    var covered_true = false;
    var covered_false = false;
    var has_unguarded_wildcard = false;
    var has_guarded_wildcard = false;
    var bool_domain = true; // unguarded arms recognizable as bool-tag patterns
    var enum_domain = true; // unguarded arms recognizable as enum-tag patterns
    var unguarded_count: usize = 0;
    var enum_total: usize = 0;
    var enum_covered = std.AutoArrayHashMapUnmanaged(u32, void){};
    defer enum_covered.deinit(self.gpa);
    if (subj_kind == .Enum) {
        const er = self.context.type_info.store.Enum.get(row(self, subj_ty));
        enum_total = self.context.type_info.store.enum_member_pool.slice(er.members).len;
    }

    // Integer coverage (unguarded arms only)
    const is_int_subj = check_types.isIntegerKind(self, subj_kind);
    var int_cov = IntCoverage{};
    defer int_cov.deinit(self.gpa);

    const arms = self.ast_unit.exprs.arm_pool.slice(mr.arms);

    var i: usize = 0;
    while (i < arms.len) : (i += 1) {
        const arm = self.ast_unit.exprs.MatchArm.get(arms[i].toRaw());

        // Validate pattern against subject type.
        const ok = try checkPattern(self, arm.pattern, subj_ty, false);
        if (!ok) {
            // Restore legacy behavior: only emit when there's a single arm.
            if (arms.len == 1) {
                const pk = self.ast_unit.pats.index.kinds.items[arm.pattern.toRaw()];
                const loc = self.ast_unit.exprs.locs.get(arm.loc);
                if (pk == .Struct or pk == .VariantStruct) {
                    try self.context.diags.addError(loc, .struct_pattern_field_mismatch, .{});
                } else {
                    try self.context.diags.addError(loc, .pattern_shape_mismatch, .{});
                }
                return null;
            }
            // Multiple arms: silently skip invalid ones (as before).
            continue;
        }

        // Guard must be boolean if present.
        if (!arm.guard.isNone()) {
            const gty = try self.checkExpr(arm.guard.unwrap());
            if (gty == null) return null;
            if (gty.?.toRaw() != self.context.type_info.store.tBool().toRaw()) {
                try self.context.diags.addError(self.ast_unit.exprs.locs.get(arm.loc), .non_boolean_condition, .{});
                return null;
            }
            if (patternCoversWildcard(self, arm.pattern)) has_guarded_wildcard = true;
        } else {
            // Unguarded arm: perform integer overlap/unreachable and finite-domain tracking.
            if (is_int_subj) {
                const loc = self.ast_unit.exprs.locs.get(arm.loc);

                // Normalize this arm into an integer set (points/ranges/wildcard).
                var aset = IntSet{};
                defer aset.deinit(self.gpa);
                try collectIntSet(self, arm.pattern, &aset);

                if (aset.wildcard) {
                    if (int_cov.wildcard) {
                        try self.context.diags.addError(loc, .unreachable_match_arm, .{});
                        return null;
                    }
                    int_cov.wildcard = true; // later unguarded int arms are unreachable
                } else if (!aset.non_int) {
                    if (int_cov.wildcard) {
                        try self.context.diags.addError(loc, .unreachable_match_arm, .{});
                        return null;
                    }
                    // Points
                    var pi: usize = 0;
                    while (pi < aset.points.items.len) : (pi += 1) {
                        if (try coverAddPointDetectOverlap(self, &int_cov, aset.points.items[pi])) {
                            try self.context.diags.addError(loc, .overlapping_match_arm, .{});
                            return null;
                        }
                    }
                    // Ranges
                    var ri: usize = 0;
                    while (ri < aset.ranges.items.len) : (ri += 1) {
                        if (try coverAddRangeDetectOverlap(self, &int_cov, aset.ranges.items[ri])) {
                            try self.context.diags.addError(loc, .overlapping_match_arm, .{});
                            return null;
                        }
                    }
                }
            }

            // Finite-domain exhaustiveness accounting.
            unguarded_count += 1;
            switch (subj_kind) {
                .Bool => {
                    if (patternCoversWildcard(self, arm.pattern)) {
                        has_unguarded_wildcard = true;
                    } else {
                        const t = patternCoversBoolValue(self, arm.pattern, true);
                        const f = patternCoversBoolValue(self, arm.pattern, false);
                        covered_true = covered_true or t;
                        covered_false = covered_false or f;
                        if (!(t or f)) bool_domain = false;
                    }
                },
                .Enum => {
                    if (patternCoversWildcard(self, arm.pattern)) {
                        has_unguarded_wildcard = true;
                    } else {
                        recordEnumTagsCovered(self, arm.pattern, subj_ty, &enum_covered) catch {};
                        if (!isEnumTagPattern(self, arm.pattern, subj_ty)) enum_domain = false;
                    }
                },
                else => {
                    if (patternCoversWildcard(self, arm.pattern)) has_unguarded_wildcard = true;
                },
            }
        }

        // Body type checking / unification when match is used as a value.
        const body_ty = try self.checkExpr(arm.body);
        if (!value_required) continue;
        if (body_ty == null) return null;

        if (result_ty == null) {
            result_ty = body_ty;
        } else if (result_ty.?.toRaw() != body_ty.?.toRaw()) {
            // Reuse if-branch mismatch diagnostic.
            try self.context.diags.addError(self.ast_unit.exprs.locs.get(mr.loc), .if_branch_type_mismatch, .{});
            return null;
        }
    }

    // Exhaustiveness post-pass (limited domains).
    var non_exhaustive = false;
    switch (subj_kind) {
        .Bool => {
            if (bool_domain and !has_unguarded_wildcard and !(covered_true and covered_false))
                non_exhaustive = true;
        },
        .Enum => {
            if (enum_domain and !has_unguarded_wildcard and enum_total != 0 and enum_covered.count() < enum_total)
                non_exhaustive = true;
        },
        else => {
            // No finite domain; a purely guarded wildcard does not make it exhaustive.
            if (unguarded_count == 0 and has_guarded_wildcard) non_exhaustive = true;
        },
    }
    if (non_exhaustive) {
        try self.context.diags.addError(self.ast_unit.exprs.locs.get(mr.loc), .non_exhaustive_match, .{});
        return null;
    }

    if (!value_required) return self.context.type_info.store.tVoid();
    return result_ty;
}

fn patternIntLiteral(self: *Checker, pid: ast.PatternId) ?i64 {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Literal => {
            const lp = self.ast_unit.pats.get(.Literal, pid);
            if (self.ast_unit.exprs.index.kinds.items[lp.expr.toRaw()] != .Literal) return null;
            const lit = self.ast_unit.exprs.get(.Literal, lp.expr);
            if (lit.kind != .int or lit.value.isNone()) return null;
            const s = self.ast_unit.exprs.strs.get(lit.value.unwrap());
            return std.fmt.parseInt(i64, s, 10) catch null;
        },
        .At => {
            const ap = self.ast_unit.pats.get(.At, pid);
            return patternIntLiteral(self, ap.pattern);
        },
        else => return null,
    }
}

fn patternIntRange(self: *Checker, pid: ast.PatternId) !?struct { a: i64, b: i64 } {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Range => {
            const rp = self.ast_unit.pats.get(.Range, pid);
            if (rp.start.isNone() or rp.end.isNone()) return null;
            const sid = rp.start.unwrap();
            const eid = rp.end.unwrap();
            if (self.ast_unit.exprs.index.kinds.items[sid.toRaw()] != .Literal) return null;
            if (self.ast_unit.exprs.index.kinds.items[eid.toRaw()] != .Literal) return null;
            const sl = self.ast_unit.exprs.get(.Literal, sid);
            const el = self.ast_unit.exprs.get(.Literal, eid);
            if (sl.kind != .int or sl.value.isNone()) return null;
            if (el.kind != .int or el.value.isNone()) return null;
            const ss = self.ast_unit.exprs.strs.get(sl.value.unwrap());
            const es = self.ast_unit.exprs.strs.get(el.value.unwrap());
            const a: i64 = std.fmt.parseInt(i64, ss, 10) catch return null;
            const b_raw: i64 = std.fmt.parseInt(i64, es, 10) catch return null;
            const b: i64 = if (rp.inclusive_right) b_raw else b_raw - 1;
            if (b < a) return null; // avoid empty/invalid ranges
            return .{ .a = a, .b = b };
        },
        .At => {
            const ap = self.ast_unit.pats.get(.At, pid);
            return try patternIntRange(self, ap.pattern);
        },
        else => return null,
    }
}

fn patternCoversWildcard(self: *Checker, pid: ast.PatternId) bool {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Wildcard => true,
        .Or => blk: {
            const op = self.ast_unit.pats.get(.Or, pid);
            const alts = self.ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| if (patternCoversWildcard(self, aid)) break :blk true;
            break :blk false;
        },
        .At => patternCoversWildcard(self, self.ast_unit.pats.get(.At, pid).pattern),
        else => false,
    };
}

fn patternCoversBoolValue(self: *Checker, pid: ast.PatternId, val: bool) bool {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Path => blk: {
            const pp = self.ast_unit.pats.get(.Path, pid);
            const segs = self.ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) break :blk false;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());
            const s = self.ast_unit.exprs.strs.get(last.name);
            if (std.mem.eql(u8, s, "true")) break :blk val == true;
            if (std.mem.eql(u8, s, "false")) break :blk val == false;
            break :blk false;
        },
        .Literal => blk: {
            const lp = self.ast_unit.pats.get(.Literal, pid);
            const kind = self.ast_unit.exprs.index.kinds.items[lp.expr.toRaw()];
            if (kind != .Literal) break :blk false;
            const lit = self.ast_unit.exprs.get(.Literal, lp.expr);
            if (lit.kind != .bool) break :blk false;
            break :blk (lit.bool_value == val);
        },
        .Or => blk2: {
            const op = self.ast_unit.pats.get(.Or, pid);
            const alts = self.ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| if (patternCoversBoolValue(self, aid, val)) break :blk2 true;
            break :blk2 false;
        },
        .At => patternCoversBoolValue(self, self.ast_unit.pats.get(.At, pid).pattern, val),
        else => false,
    };
}

fn recordEnumTagsCovered(
    self: *Checker,
    pid: ast.PatternId,
    enum_ty: types.TypeId,
    out: *std.AutoArrayHashMapUnmanaged(u32, void),
) !void {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Path => {
            const pp = self.ast_unit.pats.get(.Path, pid);
            const segs = self.ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) return;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());
            const er = self.context.type_info.store.Enum.get(row(self, enum_ty));
            const members = self.context.type_info.store.enum_member_pool.slice(er.members);
            for (members) |mid| {
                const m = self.context.type_info.store.EnumMember.get(mid.toRaw());
                if (m.name.toRaw() == last.name.toRaw()) {
                    _ = try out.put(self.gpa, m.name.toRaw(), {});
                    break;
                }
            }
        },
        .Or => {
            const op = self.ast_unit.pats.get(.Or, pid);
            const alts = self.ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| try recordEnumTagsCovered(self, aid, enum_ty, out);
        },
        .At => try recordEnumTagsCovered(self, self.ast_unit.pats.get(.At, pid).pattern, enum_ty, out),
        else => {},
    }
}

fn isEnumTagPattern(self: *Checker, pid: ast.PatternId, enum_ty: types.TypeId) bool {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Wildcard => true,
        .Path => blk: {
            const pp = self.ast_unit.pats.get(.Path, pid);
            const segs = self.ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) break :blk false;
            const last = self.ast_unit.pats.PathSeg.get(segs[segs.len - 1].toRaw());
            const er = self.context.type_info.store.Enum.get(row(self, enum_ty));
            const members = self.context.type_info.store.enum_member_pool.slice(er.members);
            for (members) |mid| {
                const m = self.context.type_info.store.EnumMember.get(mid.toRaw());
                if (m.name.toRaw() == last.name.toRaw()) break :blk true;
            }
            break :blk false;
        },
        .Or => blk2: {
            const op = self.ast_unit.pats.get(.Or, pid);
            const alts = self.ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| if (!isEnumTagPattern(self, aid, enum_ty)) break :blk2 false;
            break :blk2 true;
        },
        .At => isEnumTagPattern(self, self.ast_unit.pats.get(.At, pid).pattern, enum_ty),
        else => false,
    };
}

fn structPatternFieldsMatch(self: *Checker, pid: ast.PatternId, value_ty: types.TypeId) bool {
    if (tk(self, value_ty) != .Struct) return false;
    const sp = self.ast_unit.pats.get(.Struct, pid);
    const value_struct_ty = self.context.type_info.store.Struct.get(row(self, value_ty));
    const pattern_fields = self.ast_unit.pats.field_pool.slice(sp.fields);
    const value_fields = self.context.type_info.store.field_pool.slice(value_struct_ty.fields);
    for (pattern_fields) |pat_field_id| {
        const pat_field = self.ast_unit.pats.StructField.get(pat_field_id.toRaw());
        var found = false;
        for (value_fields) |val_field_id| {
            const val_field = self.context.type_info.store.Field.get(val_field_id.toRaw());
            if (pat_field.name.toRaw() == val_field.name.toRaw()) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

pub const BindingOrigin = union(enum) { decl: ast.DeclId, param: ast.ParamId };

pub fn declareBindingsInPattern(self: *Checker, pid: ast.PatternId, loc: ast.LocId, origin: BindingOrigin) !void {
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Binding => {
            const b = self.ast_unit.pats.get(.Binding, pid);
            const rowv: symbols.SymbolRow = switch (origin) {
                .decl => |did| .{
                    .name = b.name,
                    .kind = .Var,
                    .loc = loc,
                    .origin_decl = ast.OptDeclId.some(did),
                    .origin_param = ast.OptParamId.none(),
                },
                .param => |par| .{
                    .name = b.name,
                    .kind = .Param,
                    .loc = loc,
                    .origin_decl = ast.OptDeclId.none(),
                    .origin_param = ast.OptParamId.some(par),
                },
            };
            _ = try self.symtab.declare(rowv);

            // Also declare nested bindings if the AST supports a subpattern.
            if (@hasField(@TypeOf(b), "pattern")) {
                if (!b.pattern.isNone()) try self.declareBindingsInPattern(b.pattern.unwrap(), loc, origin);
            }
        },
        .Wildcard => {},
        .Tuple => {
            const tp = self.ast_unit.pats.get(.Tuple, pid);
            const elems = self.ast_unit.pats.pat_pool.slice(tp.elems);
            for (elems) |eid| try declareBindingsInPattern(self, eid, loc, origin);
        },
        .Struct => {
            const sp = self.ast_unit.pats.get(.Struct, pid);
            const fields = self.ast_unit.pats.field_pool.slice(sp.fields);
            for (fields) |fid| {
                const f = self.ast_unit.pats.StructField.get(fid.toRaw());
                try declareBindingsInPattern(self, f.pattern, loc, origin);
            }
        },
        .Slice => {
            const ap = self.ast_unit.pats.get(.Slice, pid);
            const elems = self.ast_unit.pats.pat_pool.slice(ap.elems);
            for (elems) |eid| try declareBindingsInPattern(self, eid, loc, origin);
            if (ap.has_rest and !ap.rest_binding.isNone()) {
                try declareBindingsInPattern(self, ap.rest_binding.unwrap(), loc, origin);
            }
        },
        .Path, .Literal => {},
        else => {},
    }
}

const PatternShapeCheck = enum { ok, tuple_arity_mismatch, struct_field_mismatch, shape_mismatch };

pub fn checkPatternShapeForDecl(self: *Checker, pid: ast.PatternId, value_ty: types.TypeId) PatternShapeCheck {
    const pkind = tk(self, value_ty);
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];

    switch (k) {
        .Wildcard, .Binding => return .ok,

        .Tuple => {
            if (pkind != .Tuple) return .shape_mismatch;
            const tp = self.context.type_info.store.Tuple.get(row(self, value_ty));
            const vals = self.context.type_info.store.type_pool.slice(tp.elems);
            const pt = self.ast_unit.pats.get(.Tuple, pid);
            const elems = self.ast_unit.pats.pat_pool.slice(pt.elems);
            if (elems.len != vals.len) return .tuple_arity_mismatch;
            var i: usize = 0;
            while (i < elems.len) : (i += 1) {
                const res = checkPatternShapeForDecl(self, elems[i], vals[i]);
                if (res != .ok) return res;
            }
            return .ok;
        },

        .Struct => {
            if (pkind != .Struct) return .shape_mismatch;
            const sv = self.context.type_info.store.Struct.get(row(self, value_ty));
            const vfields = self.context.type_info.store.field_pool.slice(sv.fields);
            const sp = self.ast_unit.pats.get(.Struct, pid);
            const pfields = self.ast_unit.pats.field_pool.slice(sp.fields);

            var i: usize = 0;
            while (i < pfields.len) : (i += 1) {
                const pf = self.ast_unit.pats.StructField.get(pfields[i].toRaw());
                var fty: ?types.TypeId = null;

                var j: usize = 0;
                while (j < vfields.len) : (j += 1) {
                    const vf = self.context.type_info.store.Field.get(vfields[j].toRaw());
                    if (vf.name.toRaw() == pf.name.toRaw()) {
                        fty = vf.ty;
                        break;
                    }
                }
                if (fty == null) return .struct_field_mismatch;

                const res = checkPatternShapeForDecl(self, pf.pattern, fty.?);
                if (res != .ok) return res;
            }
            return .ok;
        },

        .Slice => {
            // Accept array/slice/dynarray; recurse on element patterns.
            if (pkind != .Array and pkind != .Slice and pkind != .DynArray) return .shape_mismatch;
            const elem_ty: types.TypeId = switch (pkind) {
                .Array => self.context.type_info.store.Array.get(row(self, value_ty)).elem,
                .Slice => self.context.type_info.store.Slice.get(row(self, value_ty)).elem,
                .DynArray => self.context.type_info.store.DynArray.get(row(self, value_ty)).elem,
                else => unreachable,
            };
            const sl = self.ast_unit.pats.get(.Slice, pid);
            const elems = self.ast_unit.pats.pat_pool.slice(sl.elems);

            if (pkind == .Array) {
                const arr = self.context.type_info.store.Array.get(row(self, value_ty));
                // Align with checkPattern: allow rest to capture empty.
                if (sl.has_rest) {
                    if (elems.len > arr.len) return .shape_mismatch;
                } else {
                    if (elems.len != arr.len) return .shape_mismatch;
                }
            }

            for (elems) |eid| {
                const res = checkPatternShapeForDecl(self, eid, elem_ty);
                if (res != .ok) return res;
            }
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const rest_res = checkPatternShapeForDecl(self, sl.rest_binding.unwrap(), self.context.type_info.store.mkSlice(elem_ty));
                if (rest_res != .ok) return rest_res;
            }
            return .ok;
        },

        .Path, .Literal => return .ok,
        else => return .ok,
    }
}

pub fn checkPatternShapeForAssignExpr(self: *Checker, expr: ast.ExprId, value_ty: types.TypeId) PatternShapeCheck {
    const vk = tk(self, value_ty);
    const k = self.ast_unit.exprs.index.kinds.items[expr.toRaw()];

    switch (k) {
        .Ident => return .ok,

        .TupleLit => {
            if (vk != .Tuple) return .shape_mismatch;
            const tl = self.ast_unit.exprs.get(.TupleLit, expr);
            const elems = self.ast_unit.exprs.expr_pool.slice(tl.elems);
            const trow = self.context.type_info.store.Tuple.get(row(self, value_ty));
            const tys = self.context.type_info.store.type_pool.slice(trow.elems);
            if (elems.len != tys.len) return .tuple_arity_mismatch;
            var i: usize = 0;
            while (i < elems.len) : (i += 1) {
                const res = checkPatternShapeForAssignExpr(self, elems[i], tys[i]);
                if (res != .ok) return res;
            }
            return .ok;
        },

        .StructLit => {
            if (vk != .Struct) return .shape_mismatch;
            const sv = self.context.type_info.store.Struct.get(row(self, value_ty));
            const vfields = self.context.type_info.store.field_pool.slice(sv.fields);
            const sl = self.ast_unit.exprs.get(.StructLit, expr);
            const pfields = self.ast_unit.exprs.sfv_pool.slice(sl.fields);

            var i: usize = 0;
            while (i < pfields.len) : (i += 1) {
                const pf = self.ast_unit.exprs.StructFieldValue.get(pfields[i].toRaw());
                if (pf.name.isNone()) return .shape_mismatch;

                var fty: ?types.TypeId = null;
                var j: usize = 0;
                while (j < vfields.len) : (j += 1) {
                    const vf = self.context.type_info.store.Field.get(vfields[j].toRaw());
                    if (vf.name.toRaw() == pf.name.unwrap().toRaw()) {
                        fty = vf.ty;
                        break;
                    }
                }
                if (fty == null) return .struct_field_mismatch;

                const res = checkPatternShapeForAssignExpr(self, pf.value, fty.?);
                if (res != .ok) return res;
            }
            return .ok;
        },

        .ArrayLit => {
            if (vk != .Array and vk != .Slice and vk != .DynArray) return .shape_mismatch;
            const elem_ty: types.TypeId = switch (vk) {
                .Array => self.context.type_info.store.Array.get(row(self, value_ty)).elem,
                .Slice => self.context.type_info.store.Slice.get(row(self, value_ty)).elem,
                .DynArray => self.context.type_info.store.DynArray.get(row(self, value_ty)).elem,
                else => unreachable,
            };

            const al = self.ast_unit.exprs.get(.ArrayLit, expr);
            const elems = self.ast_unit.exprs.expr_pool.slice(al.elems);

            var has_rest = false;
            var rest_index: usize = 0;

            var i: usize = 0;
            while (i < elems.len) : (i += 1) {
                const ek = self.ast_unit.exprs.index.kinds.items[elems[i].toRaw()];
                if (ek == .Range) {
                    if (has_rest) return .shape_mismatch; // multiple rest segments
                    has_rest = true;
                    rest_index = i;
                    continue; // validated below
                }
                const res = checkPatternShapeForAssignExpr(self, elems[i], elem_ty);
                if (res != .ok) return res;
            }

            if (vk == .Array) {
                const arr = self.context.type_info.store.Array.get(row(self, value_ty));
                if (has_rest) {
                    if (elems.len - 1 > arr.len) return .shape_mismatch; // minus the rest placeholder
                } else {
                    if (elems.len != arr.len) return .shape_mismatch;
                }
            }

            if (has_rest) {
                // Expect `a .. rest` where end (if any) is an identifier binding the remainder.
                const rr = self.ast_unit.exprs.get(.Range, elems[rest_index]);
                if (!rr.end.isNone()) {
                    const binder_kind = self.ast_unit.exprs.index.kinds.items[rr.end.unwrap().toRaw()];
                    if (binder_kind != .Ident) return .shape_mismatch;
                }
            }
            return .ok;
        },

        else => return .shape_mismatch,
    }
}

pub fn bindingTypeInPattern(self: *Checker, pid: ast.PatternId, name: ast.StrId, value_ty: types.TypeId) ?types.TypeId {
    const pk = tk(self, value_ty);
    const k = self.ast_unit.pats.index.kinds.items[pid.toRaw()];

    switch (k) {
        .Binding => {
            const b = self.ast_unit.pats.get(.Binding, pid);
            if (b.name.toRaw() == name.toRaw()) return value_ty;

            // Support nested subpattern if present.
            if (@hasField(@TypeOf(b), "pattern")) {
                if (!b.pattern.isNone()) return bindingTypeInPattern(self, b.pattern.unwrap(), name, value_ty);
            }
            return null;
        },
        .Wildcard => return null,

        .Tuple => {
            if (pk != .Tuple) return null;
            const tp = self.context.type_info.store.Tuple.get(row(self, value_ty));
            const elems_ty = self.context.type_info.store.type_pool.slice(tp.elems);
            const pp = self.ast_unit.pats.get(.Tuple, pid);
            const elems = self.ast_unit.pats.pat_pool.slice(pp.elems);
            if (elems.len != elems_ty.len) return null;
            var i: usize = 0;
            while (i < elems.len) : (i += 1) {
                if (bindingTypeInPattern(self, elems[i], name, elems_ty[i])) |bt| return bt;
            }
            return null;
        },

        .Struct => {
            if (pk != .Struct) return null;
            const st = self.context.type_info.store.Struct.get(row(self, value_ty));
            const fields_ty = self.context.type_info.store.field_pool.slice(st.fields);
            const sp = self.ast_unit.pats.get(.Struct, pid);
            const fields = self.ast_unit.pats.field_pool.slice(sp.fields);
            for (fields) |fid| {
                const pf = self.ast_unit.pats.StructField.get(fid.toRaw());
                var i: usize = 0;
                while (i < fields_ty.len) : (i += 1) {
                    const tf = self.context.type_info.store.Field.get(fields_ty[i].toRaw());
                    if (tf.name.toRaw() == pf.name.toRaw()) {
                        if (bindingTypeInPattern(self, pf.pattern, name, tf.ty)) |bt| return bt;
                        break;
                    }
                }
            }
            return null;
        },

        .Slice => {
            if (pk != .Array and pk != .Slice and pk != .DynArray) return null;
            const elem_ty: types.TypeId = switch (pk) {
                .Array => self.context.type_info.store.Array.get(row(self, value_ty)).elem,
                .Slice => self.context.type_info.store.Slice.get(row(self, value_ty)).elem,
                .DynArray => self.context.type_info.store.DynArray.get(row(self, value_ty)).elem,
                else => return null,
            };
            const sl = self.ast_unit.pats.get(.Slice, pid);
            const elems = self.ast_unit.pats.pat_pool.slice(sl.elems);
            for (elems) |eid| if (bindingTypeInPattern(self, eid, name, elem_ty)) |bt| return bt;
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const rest_ty = self.context.type_info.store.mkSlice(elem_ty);
                if (bindingTypeInPattern(self, sl.rest_binding.unwrap(), name, rest_ty)) |bt| return bt;
            }
            return null;
        },

        .Path, .Literal => return null,
        else => return null,
    }
}
