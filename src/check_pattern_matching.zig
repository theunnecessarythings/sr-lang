const std = @import("std");

const ast = @import("ast.zig");
const check_types = @import("check_types.zig");
const Checker = @import("checker.zig").Checker;
const symbols = @import("symbols.zig");
const types = @import("types.zig");

inline fn getVariantOrErrorCases(self: *Checker, ty: types.TypeId) []const types.FieldId {
    const k = self.typeKind(ty);
    return if (k == .Variant)
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Variant, ty).variants)
    else
        self.context.type_store.field_pool.slice(self.context.type_store.get(.Error, ty).variants);
}
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
fn collectIntSet(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, out: *IntSet) !void {
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Wildcard => {
            out.wildcard = true;
        },
        .Literal => {
            if (patternIntLiteral(self, ast_unit, pid)) |lit| {
                try out.points.append(self.gpa, lit);
            } else {
                out.non_int = true;
            }
        },
        .Range => {
            if (try patternIntRange(self, ast_unit, pid)) |rr| {
                try out.ranges.append(self.gpa, .{ .a = rr.a, .b = rr.b });
            } else {
                // either not an int range or invalid/empty
                out.non_int = true;
            }
        },
        .Or => {
            const op = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| {
                try collectIntSet(self, ast_unit, aid, out);
                if (out.wildcard) break; // early if already everything
            }
        },
        .At => {
            const ap = ast_unit.pats.get(.At, pid);
            try collectIntSet(self, ast_unit, ap.pattern, out);
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
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    value_ty: types.TypeId,
    top_level: bool,
) !bool {
    // Emit diagnostics only on top-level shape checks, but keep inner calls quiet.
    const emit = top_level;
    const kind = ast_unit.pats.index.kinds.items[pid.toRaw()];

    switch (kind) {
        .Or => {
            const op = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(op.alts);
            if (alts.len == 0) return true;

            // Check binding consistency
            var first_bindings: std.ArrayList(ast.StrId) = .empty;
            defer first_bindings.deinit(self.gpa);
            try collectPatternBindings(self, ast_unit, alts[0], &first_bindings);

            for (alts[1..]) |alt_id| {
                var alt_bindings: std.ArrayList(ast.StrId) = .empty;
                defer alt_bindings.deinit(self.gpa);
                try collectPatternBindings(self, ast_unit, alt_id, &alt_bindings);

                if (first_bindings.items.len != alt_bindings.items.len) {
                    std.debug.print("binding mismatch: first={}, alt_len={}\n", .{ first_bindings.items.len, alt_bindings.items.len });
                    try self.context.diags.addError(ast_unit.exprs.locs.get(op.loc), .or_pattern_binding_mismatch, .{});
                    return false;
                }

                for (first_bindings.items) |b1_name| {
                    var found = false;
                    for (alt_bindings.items) |b2_name| {
                        if (std.mem.eql(u8, ast_unit.exprs.strs.get(b1_name), ast_unit.exprs.strs.get(b2_name))) {
                            const b1_ty = bindingTypeInPattern(self, ast_unit, alts[0], b1_name, value_ty);
                            const b2_ty = bindingTypeInPattern(self, ast_unit, alt_id, b2_name, value_ty);
                            if (b1_ty == null or b2_ty == null or !b1_ty.?.eq(b2_ty.?)) {
                                try self.context.diags.addError(ast_unit.exprs.locs.get(op.loc), .or_pattern_binding_type_mismatch, .{});
                                return false;
                            }
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        std.debug.print("binding name not found\n", .{});
                        try self.context.diags.addError(ast_unit.exprs.locs.get(op.loc), .or_pattern_binding_mismatch, .{});
                        return false;
                    }
                }
            }

            var any_ok = false;
            for (alts) |aid| {
                const is_ok = try checkPattern(self, ctx, ast_unit, aid, value_ty, false);
                any_ok = any_ok or is_ok;
            }
            return any_ok;
        },
        .At => {
            const ap = ast_unit.pats.get(.At, pid);
            // x @ pat : bind x as a Var and check subpattern.
            _ = try ctx.symtab.declare(.{
                .name = ap.binder,
                .kind = .Var,
                .is_comptime = false,
                .loc = ap.loc,
                .origin_decl = .none(),
                .origin_param = .none(),
            });
            return try checkPattern(self, ctx, ast_unit, ap.pattern, value_ty, false);
        },
        .Range => {
            const rp = ast_unit.pats.get(.Range, pid);
            if (!rp.start.isNone()) {
                _ = try self.checkExpr(ctx, ast_unit, rp.start.unwrap());
            }
            if (!rp.end.isNone()) {
                _ = try self.checkExpr(ctx, ast_unit, rp.end.unwrap());
            }
            // If both bounds are integer literals, validate that the range is not descending/empty.
            if (!rp.start.isNone() and !rp.end.isNone()) {
                const sid = rp.start.unwrap();
                const eid = rp.end.unwrap();
                if (ast_unit.exprs.index.kinds.items[sid.toRaw()] == .Literal and
                    ast_unit.exprs.index.kinds.items[eid.toRaw()] == .Literal)
                {
                    const sl = ast_unit.exprs.get(.Literal, sid);
                    const el = ast_unit.exprs.get(.Literal, eid);
                    if (sl.kind == .int and el.kind == .int) {
                        const sa = switch (sl.data) {
                            .int => |info| info,
                            else => null,
                        };
                        const sb = switch (el.data) {
                            .int => |info| info,
                            else => null,
                        };
                        if (sa != null and sb != null and sa.?.valid and sb.?.valid) {
                            const max_i64: u128 = @intCast(std.math.maxInt(i64));
                            if (sa.?.value <= max_i64 and sb.?.value <= max_i64) {
                                const a: i64 = @intCast(sa.?.value);
                                const b_raw: i64 = @intCast(sb.?.value);
                                const b: i64 = if (rp.inclusive_right) b_raw else b_raw - 1;
                                if (b < a) {
                                    try self.context.diags.addError(ast_unit.exprs.locs.get(rp.loc), .descending_range_pattern, .{});
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
            // Accept integer subjects only.
            return check_types.isIntegerKind(self, self.typeKind(value_ty));
        },
        .VariantTuple => {
            const vt_pat = ast_unit.pats.get(.VariantTuple, pid);
            const vk = self.typeKind(value_ty);
            if (vk != .Variant and vk != .Error) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(vt_pat.loc), .pattern_type_mismatch, .{});
                return false;
            }

            const segs = ast_unit.pats.seg_pool.slice(vt_pat.path);
            if (segs.len == 0) return false;
            const last = ast_unit.pats.PathSeg.get(segs[segs.len - 1]);

            const payload_ty = findCasePayload(self, value_ty, last.name) orelse return false;
            const pk = self.typeKind(payload_ty);

            const elems = ast_unit.pats.pat_pool.slice(vt_pat.elems);
            if (pk == .Void) return elems.len == 0;

            // Accept both tuple and single-value payloads.
            if (pk == .Tuple) {
                const tup = self.context.type_store.get(.Tuple, payload_ty);
                const tys = self.context.type_store.type_pool.slice(tup.elems);
                if (elems.len != tys.len) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vt_pat.loc), .tuple_arity_mismatch, .{});
                    return false;
                }
                for (elems, 0..) |eid, i| {
                    if (!(try checkPattern(self, ctx, ast_unit, eid, tys[i], false))) return false;
                }
                return true;
            } else {
                // Non-tuple payload: require exactly one subpattern and check against payload type.
                if (elems.len != 1) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vt_pat.loc), .pattern_type_mismatch, .{});
                    return false;
                }
                return try checkPattern(self, ctx, ast_unit, elems[0], payload_ty, false);
            }
        },
        .Path => {
            // Enum tags and tag-only Variant/Error patterns.
            const pp = ast_unit.pats.get(.Path, pid);
            const segs = ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) return false;
            const last = ast_unit.pats.PathSeg.get(segs[segs.len - 1]);
            const vk = self.typeKind(value_ty);

            switch (vk) {
                .Enum => {
                    const er = self.context.type_store.get(.Enum, value_ty);
                    const members = self.context.type_store.enum_member_pool.slice(er.members);
                    for (members) |mid| {
                        const m = self.context.type_store.EnumMember.get(mid);
                        if (m.name.toRaw() == last.name.toRaw()) return true;
                    }
                    return false;
                },
                .Variant, .Error => {
                    const cases = getVariantOrErrorCases(self, value_ty);
                    for (cases) |fid| {
                        const f = self.context.type_store.Field.get(fid);
                        if (f.name.toRaw() == last.name.toRaw()) {
                            // tag-only allowed only when payload is void
                            return self.typeKind(f.ty) == .Void;
                        }
                    }
                    return false;
                },
                else => return false,
            }
        },
        .VariantStruct => {
            const vs_pat = ast_unit.pats.get(.VariantStruct, pid);
            const vk = self.typeKind(value_ty);

            // Struct sugar: allow `Type { ... }` against a struct value.
            if (vk != .Variant and vk != .Error) {
                if (vk == .Struct) {
                    const st = self.context.type_store.get(.Struct, value_ty);
                    const value_fields = self.context.type_store.field_pool.slice(st.fields);
                    const pat_fields = ast_unit.pats.field_pool.slice(vs_pat.fields);

                    for (pat_fields) |pfid| {
                        const pf = ast_unit.pats.StructField.get(pfid);
                        var fty: ?types.TypeId = null;
                        for (value_fields) |vfid| {
                            const vf = self.context.type_store.Field.get(vfid);
                            if (vf.name.toRaw() == pf.name.toRaw()) {
                                fty = vf.ty;
                                break;
                            }
                        }
                        if (fty == null) {
                            try self.context.diags.addError(ast_unit.exprs.locs.get(vs_pat.loc), .struct_pattern_field_mismatch, .{});
                            return false;
                        }
                        if (!(try checkPattern(self, ctx, ast_unit, pf.pattern, fty.?, false))) {
                            try self.context.diags.addError(ast_unit.exprs.locs.get(vs_pat.loc), .struct_pattern_field_mismatch, .{});
                            return false;
                        }
                    }
                    return true;
                }
                return false;
            }

            const segs = ast_unit.pats.seg_pool.slice(vs_pat.path);
            if (segs.len == 0) return false;
            const last = ast_unit.pats.PathSeg.get(segs[segs.len - 1]);

            const payload_ty = findCasePayload(self, value_ty, last.name) orelse return false;
            const pk = self.typeKind(payload_ty);

            if (pk == .Void) return vs_pat.fields.len == 0;
            if (pk != .Struct) return false;

            const st = self.context.type_store.get(.Struct, payload_ty);
            const value_fields = self.context.type_store.field_pool.slice(st.fields);
            const pat_fields = ast_unit.pats.field_pool.slice(vs_pat.fields);

            for (pat_fields) |pfid| {
                const pf = ast_unit.pats.StructField.get(pfid);
                var fty: ?types.TypeId = null;
                for (value_fields) |vfid| {
                    const vf = self.context.type_store.Field.get(vfid);
                    if (vf.name.toRaw() == pf.name.toRaw()) {
                        fty = vf.ty;
                        break;
                    }
                }
                if (fty == null) return false;
                if (!(try checkPattern(self, ctx, ast_unit, pf.pattern, fty.?, false))) {
                    try self.context.diags.addError(ast_unit.exprs.locs.get(vs_pat.loc), .struct_pattern_field_mismatch, .{});
                    return false;
                }
            }
            return true;
        },
        .Binding => {
            const bp = ast_unit.pats.get(.Binding, pid);
            // Declare the bound name.
            _ = try ctx.symtab.declare(.{
                .name = bp.name,
                .kind = .Var,
                .is_comptime = false,
                .loc = bp.loc,
                .origin_decl = .none(),
                .origin_param = .none(),
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
            const lp = ast_unit.pats.get(.Literal, pid);
            const pattern_loc = ast_unit.exprs.locs.get(lp.loc);
            const lit_expr_id = lp.expr;
            const lit_ty = try self.checkExpr(ctx, ast_unit, lit_expr_id);
            if (self.typeKind(lit_ty) == .TypeError) return false;
            const lit_kind = ast_unit.exprs.get(.Literal, lit_expr_id).kind;
            if (lit_kind == .string) {
                if (emit) try self.context.diags.addError(pattern_loc, .string_equality_in_match_not_supported, .{});
                return false;
            }

            if (self.assignable(value_ty, lit_ty) != .success) {
                if (emit) try self.context.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                return false;
            }
            // Future: evaluate and compare values if not top-level.
            return true;
        },
        .Tuple => {
            const tp = ast_unit.pats.get(.Tuple, pid);
            const pattern_loc = ast_unit.exprs.locs.get(tp.loc);
            if (self.typeKind(value_ty) != .Tuple) {
                if (emit) try self.context.diags.addError(pattern_loc, .pattern_shape_mismatch, .{});
                return false;
            }
            const value_tuple_ty = self.context.type_store.get(.Tuple, value_ty);
            const pattern_elems = ast_unit.pats.pat_pool.slice(tp.elems);
            const value_elems = self.context.type_store.type_pool.slice(value_tuple_ty.elems);

            if (pattern_elems.len != value_elems.len) {
                if (emit) try self.context.diags.addError(pattern_loc, .tuple_arity_mismatch, .{});
                return false;
            }
            for (pattern_elems, 0..) |pat_elem_id, i| {
                if (!(try checkPattern(self, ctx, ast_unit, pat_elem_id, value_elems[i], false))) return false;
            }
            return true;
        },
        .Slice => {
            const ap = ast_unit.pats.get(.Slice, pid);
            const pattern_loc = ast_unit.exprs.locs.get(ap.loc);
            const vk = self.typeKind(value_ty);
            if (vk != .Array and vk != .Slice and vk != .DynArray) {
                if (emit) try self.context.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                return false;
            }

            const elem_ty: types.TypeId = switch (vk) {
                .Array => self.context.type_store.get(.Array, value_ty).elem,
                .Slice => self.context.type_store.get(.Slice, value_ty).elem,
                .DynArray => self.context.type_store.get(.DynArray, value_ty).elem,
                else => self.context.type_store.tAny(),
            };

            const pattern_elems = ast_unit.pats.pat_pool.slice(ap.elems);
            if (vk == .Array) {
                const arr = self.context.type_store.get(.Array, value_ty);
                // Allow rest to capture an empty slice; just require explicit <= length.
                switch (arr.len) {
                    .Concrete => |l| {
                        if (ap.has_rest) {
                            if (pattern_elems.len > l) return false;
                        } else {
                            if (pattern_elems.len != l) return false;
                        }
                    },
                    .Unresolved => {},
                }
            }

            for (pattern_elems, 0..) |pat_elem_id, i| {
                if (ap.has_rest and i == ap.rest_index) continue; // skip the rest placeholder
                if (!(try checkPattern(self, ctx, ast_unit, pat_elem_id, elem_ty, false))) return false;
            }

            if (ap.has_rest and !ap.rest_binding.isNone()) {
                if (!(try checkPattern(self, ctx, ast_unit, ap.rest_binding.unwrap(), self.context.type_store.mkSlice(elem_ty), false)))
                    return false;
            }
            return true;
        },
        .Struct => {
            const sp = ast_unit.pats.get(.Struct, pid);
            const pattern_loc = ast_unit.exprs.locs.get(sp.loc);
            if (self.typeKind(value_ty) != .Struct) {
                if (emit) try self.context.diags.addError(pattern_loc, .pattern_type_mismatch, .{});
                return false;
            }
            const value_struct_ty = self.context.type_store.get(.Struct, value_ty);
            const pattern_fields = ast_unit.pats.field_pool.slice(sp.fields);
            const value_fields = self.context.type_store.field_pool.slice(value_struct_ty.fields);

            for (pattern_fields) |pat_field_id| {
                const pat_field = ast_unit.pats.StructField.get(pat_field_id);
                var match_ty: ?types.TypeId = null;

                for (value_fields) |val_field_id| {
                    const val_field = self.context.type_store.Field.get(val_field_id);
                    if (pat_field.name.toRaw() == val_field.name.toRaw()) {
                        match_ty = val_field.ty;
                        break;
                    }
                }

                if (match_ty == null) {
                    if (emit) try self.context.diags.addError(pattern_loc, .struct_pattern_field_mismatch, .{});
                    return false;
                }
                if (!(try checkPattern(self, ctx, ast_unit, pat_field.pattern, match_ty.?, false))) return false;
            }
            return true;
        },
    }
}

pub fn checkMatch(self: *Checker, ctx: *Checker.CheckerContext, ast_unit: *ast.Ast, id: ast.ExprId) !types.TypeId {
    const mr = ast_unit.exprs.get(.Match, id);
    const subj_ty = try self.checkExpr(ctx, ast_unit, mr.expr);
    if (self.typeKind(subj_ty) == .TypeError) return self.context.type_store.tTypeError();
    const subj_kind = self.typeKind(subj_ty);
    const value_required = self.isValueReq(ctx);

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
        const er = self.context.type_store.get(.Enum, subj_ty);
        enum_total = self.context.type_store.enum_member_pool.slice(er.members).len;
    }

    // Integer coverage (unguarded arms only)
    const is_int_subj = check_types.isIntegerKind(self, subj_kind);
    var int_cov = IntCoverage{};
    defer int_cov.deinit(self.gpa);

    const arms = ast_unit.exprs.arm_pool.slice(mr.arms);

    var i: usize = 0;
    while (i < arms.len) : (i += 1) {
        const arm = ast_unit.exprs.MatchArm.get(arms[i]);

        try self.pushMatchBinding(ctx, arm.pattern, subj_ty);
        defer self.popMatchBinding(ctx);

        _ = try ctx.symtab.push(ctx.symtab.currentId());
        defer ctx.symtab.pop();
        try declareBindingsInPattern(self, ctx, ast_unit, arm.pattern, arm.loc, .anonymous);

        // Validate pattern against subject type.
        const ok = try checkPattern(self, ctx, ast_unit, arm.pattern, subj_ty, true);
        if (!ok) {
            return self.context.type_store.tTypeError();
        }

        // Guard must be boolean if present.
        if (!arm.guard.isNone()) {
            const gty = try self.checkExpr(ctx, ast_unit, arm.guard.unwrap());
            if (self.typeKind(gty) == .TypeError) return self.context.type_store.tTypeError();
            if (gty.toRaw() != self.context.type_store.tBool().toRaw()) {
                try self.context.diags.addError(ast_unit.exprs.locs.get(arm.loc), .non_boolean_condition, .{});
                return self.context.type_store.tTypeError();
            }
            if (patternCoversWildcard(self, ast_unit, arm.pattern)) has_guarded_wildcard = true;
        } else {
            // Unguarded arm: perform integer overlap/unreachable and finite-domain tracking.
            if (is_int_subj) {
                const loc = ast_unit.exprs.locs.get(arm.loc);

                // Normalize this arm into an integer set (points/ranges/wildcard).
                var aset = IntSet{};
                defer aset.deinit(self.gpa);
                try collectIntSet(self, ast_unit, arm.pattern, &aset);

                if (aset.wildcard) {
                    if (int_cov.wildcard) {
                        try self.context.diags.addError(loc, .unreachable_match_arm, .{});
                        return self.context.type_store.tTypeError();
                    }
                    int_cov.wildcard = true; // later unguarded int arms are unreachable
                } else if (!aset.non_int) {
                    if (int_cov.wildcard) {
                        try self.context.diags.addError(loc, .unreachable_match_arm, .{});
                        return self.context.type_store.tTypeError();
                    }
                    // Points
                    var pi: usize = 0;
                    while (pi < aset.points.items.len) : (pi += 1) {
                        if (try coverAddPointDetectOverlap(self, &int_cov, aset.points.items[pi])) {
                            try self.context.diags.addError(loc, .overlapping_match_arm, .{});
                            return self.context.type_store.tTypeError();
                        }
                    }
                    // Ranges
                    var ri: usize = 0;
                    while (ri < aset.ranges.items.len) : (ri += 1) {
                        if (try coverAddRangeDetectOverlap(self, &int_cov, aset.ranges.items[ri])) {
                            try self.context.diags.addError(loc, .overlapping_match_arm, .{});
                            return self.context.type_store.tTypeError();
                        }
                    }
                }
            }

            // Finite-domain exhaustiveness accounting.
            unguarded_count += 1;
            switch (subj_kind) {
                .Bool => {
                    if (patternCoversWildcard(self, ast_unit, arm.pattern)) {
                        has_unguarded_wildcard = true;
                    } else {
                        const t = patternCoversBoolValue(self, ast_unit, arm.pattern, true);
                        const f = patternCoversBoolValue(self, ast_unit, arm.pattern, false);
                        covered_true = covered_true or t;
                        covered_false = covered_false or f;
                        if (!(t or f)) bool_domain = false;
                    }
                },
                .Enum => {
                    if (patternCoversWildcard(self, ast_unit, arm.pattern)) {
                        has_unguarded_wildcard = true;
                    } else {
                        recordEnumTagsCovered(self, ast_unit, arm.pattern, subj_ty, &enum_covered) catch {};
                        if (!isEnumTagPattern(self, ast_unit, arm.pattern, subj_ty)) enum_domain = false;
                    }
                },
                else => {
                    if (patternCoversWildcard(self, ast_unit, arm.pattern)) has_unguarded_wildcard = true;
                },
            }
        }

        // Body type checking / unification when match is used as a value.
        const body_ty = try self.checkExpr(ctx, ast_unit, arm.body);
        if (self.typeKind(body_ty) == .TypeError) return self.context.type_store.tTypeError();
        if (!value_required) continue;

        if (result_ty == null) {
            result_ty = body_ty;
        } else if (result_ty.?.toRaw() != body_ty.toRaw()) {
            // Reuse if-branch mismatch diagnostic.
            try self.context.diags.addError(ast_unit.exprs.locs.get(mr.loc), .if_branch_type_mismatch, .{});
            return self.context.type_store.tTypeError();
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
        try self.context.diags.addError(ast_unit.exprs.locs.get(mr.loc), .non_exhaustive_match, .{});
        return self.context.type_store.tTypeError();
    }

    if (!value_required) return self.context.type_store.tVoid();
    return result_ty orelse self.context.type_store.tVoid();
}

fn patternIntLiteral(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId) ?i64 {
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Literal => {
            const lp = ast_unit.pats.get(.Literal, pid);
            if (ast_unit.exprs.index.kinds.items[lp.expr.toRaw()] != .Literal) return null;
            const lit = ast_unit.exprs.get(.Literal, lp.expr);
            if (lit.kind != .int) return null;
            const info = switch (lit.data) {
                .int => |int_info| int_info,
                else => return null,
            };
            if (!info.valid) return null;
            const max_i64: u128 = @intCast(std.math.maxInt(i64));
            if (info.value > max_i64) return null;
            return @intCast(info.value);
        },
        .At => {
            const ap = ast_unit.pats.get(.At, pid);
            return patternIntLiteral(self, ast_unit, ap.pattern);
        },
        else => return null,
    }
}

fn patternIntRange(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId) !?struct { a: i64, b: i64 } {
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Range => {
            const rp = ast_unit.pats.get(.Range, pid);
            if (rp.start.isNone() or rp.end.isNone()) return null;
            const sid = rp.start.unwrap();
            const eid = rp.end.unwrap();
            if (ast_unit.exprs.index.kinds.items[sid.toRaw()] != .Literal) return null;
            if (ast_unit.exprs.index.kinds.items[eid.toRaw()] != .Literal) return null;
            const sl = ast_unit.exprs.get(.Literal, sid);
            const el = ast_unit.exprs.get(.Literal, eid);
            if (sl.kind != .int or el.kind != .int) return null;
            const sa = switch (sl.data) {
                .int => |int_info| int_info,
                else => return null,
            };
            const sb = switch (el.data) {
                .int => |int_info| int_info,
                else => return null,
            };
            if (!sa.valid or !sb.valid) return null;
            const max_i64: u128 = @intCast(std.math.maxInt(i64));
            if (sa.value > max_i64) return null;
            if (sb.value > max_i64) return null;
            const a: i64 = @intCast(sa.value);
            const b_raw: i64 = @intCast(sb.value);
            const b: i64 = if (rp.inclusive_right) b_raw else b_raw - 1;
            if (b < a) return null; // avoid empty/invalid ranges
            return .{ .a = a, .b = b };
        },
        .At => {
            const ap = ast_unit.pats.get(.At, pid);
            return try patternIntRange(self, ast_unit, ap.pattern);
        },
        else => return null,
    }
}

fn patternCoversWildcard(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId) bool {
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Wildcard => true,
        .Or => blk: {
            const op = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| if (patternCoversWildcard(self, ast_unit, aid)) break :blk true;
            break :blk false;
        },
        .At => patternCoversWildcard(self, ast_unit, ast_unit.pats.get(.At, pid).pattern),
        else => false,
    };
}

fn patternCoversBoolValue(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, val: bool) bool {
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Path => blk: {
            const pp = ast_unit.pats.get(.Path, pid);
            const segs = ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) break :blk false;
            const last = ast_unit.pats.PathSeg.get(segs[segs.len - 1]);
            const s = ast_unit.exprs.strs.get(last.name);
            if (std.mem.eql(u8, s, "true")) break :blk val == true;
            if (std.mem.eql(u8, s, "false")) break :blk val == false;
            break :blk false;
        },
        .Literal => blk: {
            const lp = ast_unit.pats.get(.Literal, pid);
            const kind = ast_unit.exprs.index.kinds.items[lp.expr.toRaw()];
            if (kind != .Literal) break :blk false;
            const lit = ast_unit.exprs.get(.Literal, lp.expr);
            if (lit.kind != .bool) break :blk false;
            const lit_val = switch (lit.data) {
                .bool => |b| b,
                else => break :blk false,
            };
            break :blk (lit_val == val);
        },
        .Or => blk2: {
            const op = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| if (patternCoversBoolValue(self, ast_unit, aid, val)) break :blk2 true;
            break :blk2 false;
        },
        .At => patternCoversBoolValue(self, ast_unit, ast_unit.pats.get(.At, pid).pattern, val),
        else => false,
    };
}

fn recordEnumTagsCovered(
    self: *Checker,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    enum_ty: types.TypeId,
    out: *std.AutoArrayHashMapUnmanaged(u32, void),
) !void {
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Path => {
            const pp = ast_unit.pats.get(.Path, pid);
            const segs = ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) return;
            const last = ast_unit.pats.PathSeg.get(segs[segs.len - 1]);
            const er = self.context.type_store.get(.Enum, enum_ty);
            const members = self.context.type_store.enum_member_pool.slice(er.members);
            for (members) |mid| {
                const m = self.context.type_store.EnumMember.get(mid);
                if (m.name.toRaw() == last.name.toRaw()) {
                    _ = try out.put(self.gpa, m.name.toRaw(), {});
                    break;
                }
            }
        },
        .Or => {
            const op = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| try recordEnumTagsCovered(self, ast_unit, aid, enum_ty, out);
        },
        .At => try recordEnumTagsCovered(self, ast_unit, ast_unit.pats.get(.At, pid).pattern, enum_ty, out),
        else => {},
    }
}

fn isEnumTagPattern(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, enum_ty: types.TypeId) bool {
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];
    return switch (k) {
        .Wildcard => true,
        .Path => blk: {
            const pp = ast_unit.pats.get(.Path, pid);
            const segs = ast_unit.pats.seg_pool.slice(pp.segments);
            if (segs.len == 0) break :blk false;
            const last = ast_unit.pats.PathSeg.get(segs[segs.len - 1]);
            const er = self.context.type_store.get(.Enum, enum_ty);
            const members = self.context.type_store.enum_member_pool.slice(er.members);
            for (members) |mid| {
                const m = self.context.type_store.EnumMember.get(mid);
                if (m.name.toRaw() == last.name.toRaw()) break :blk true;
            }
            break :blk false;
        },
        .Or => blk2: {
            const op = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(op.alts);
            for (alts) |aid| if (!isEnumTagPattern(self, ast_unit, aid, enum_ty)) break :blk2 false;
            break :blk2 true;
        },
        .At => isEnumTagPattern(self, ast_unit, ast_unit.pats.get(.At, pid).pattern, enum_ty),
        else => false,
    };
}

fn structPatternFieldsMatch(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, value_ty: types.TypeId) bool {
    if (self.typeKind(value_ty) != .Struct) return false;
    const sp = ast_unit.pats.get(.Struct, pid);
    const value_struct_ty = self.context.type_store.get(.Struct, value_ty);
    const pattern_fields = ast_unit.pats.field_pool.slice(sp.fields);
    const value_fields = self.context.type_store.field_pool.slice(value_struct_ty.fields);
    for (pattern_fields) |pat_field_id| {
        const pat_field = ast_unit.pats.StructField.get(pat_field_id);
        var found = false;
        for (value_fields) |val_field_id| {
            const val_field = self.context.type_store.Field.get(val_field_id);
            if (pat_field.name.toRaw() == val_field.name.toRaw()) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

pub const BindingOrigin = union(enum) { decl: ast.DeclId, param: ast.ParamId, anonymous };

pub fn declareBindingsInPattern(
    self: *Checker,
    ctx: *Checker.CheckerContext,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    loc: ast.LocId,
    origin: BindingOrigin,
) !void {
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (k) {
        .Binding => {
            const b = ast_unit.pats.get(.Binding, pid);
            const rowv: symbols.SymbolRow = switch (origin) {
                .decl => |did| blk: {
                    const d = ast_unit.exprs.Decl.get(did);
                    const rhs_kind = ast_unit.exprs.index.kinds.items[d.value.toRaw()];
                    const is_comptime_val = switch (rhs_kind) {
                        .Literal, .MlirBlock, .TupleType, .ArrayType, .DynArrayType, .SliceType, .OptionalType, .ErrorSetType, .ErrorType, .StructType, .EnumType, .VariantType, .UnionType, .PointerType, .SimdType, .ComplexType, .TensorType, .TypeType, .AnyType, .NoreturnType, .MapType, .ComptimeBlock => true,
                        else => false,
                    };
                    break :blk .{
                        .name = b.name,
                        .kind = .Var,
                        .is_comptime = is_comptime_val,
                        .loc = loc,
                        .origin_decl = .some(did),
                        .origin_param = .none(),
                    };
                },
                .param => |par| .{
                    .name = b.name,
                    .kind = .Param,
                    .is_comptime = ast_unit.exprs.Param.get(par).is_comptime,
                    .loc = loc,
                    .origin_decl = .none(),
                    .origin_param = .some(par),
                },
                .anonymous => .{
                    .name = b.name,
                    .kind = .Var,
                    .is_comptime = false,
                    .loc = loc,
                    .origin_decl = .none(),
                    .origin_param = .none(),
                },
            };
            _ = try ctx.symtab.declare(rowv);

            // Also declare nested bindings if the AST supports a subpattern.
            if (@hasField(@TypeOf(b), "pattern")) {
                if (!b.pattern.isNone()) try self.declareBindingsInPattern(b.pattern.unwrap(), loc, origin);
            }
        },
        .Wildcard => {},
        .Tuple => {
            const tp = ast_unit.pats.get(.Tuple, pid);
            const elems = ast_unit.pats.pat_pool.slice(tp.elems);
            for (elems) |eid| try declareBindingsInPattern(self, ctx, ast_unit, eid, loc, origin);
        },
        .Struct => {
            const sp = ast_unit.pats.get(.Struct, pid);
            const fields = ast_unit.pats.field_pool.slice(sp.fields);
            for (fields) |fid| {
                const f = ast_unit.pats.StructField.get(fid);
                try declareBindingsInPattern(self, ctx, ast_unit, f.pattern, loc, origin);
            }
        },
        .VariantTuple => {
            const vt = ast_unit.pats.get(.VariantTuple, pid);
            const elems = ast_unit.pats.pat_pool.slice(vt.elems);
            for (elems) |eid| try declareBindingsInPattern(self, ctx, ast_unit, eid, loc, origin);
        },
        .VariantStruct => {
            const vs = ast_unit.pats.get(.VariantStruct, pid);
            const fields = ast_unit.pats.field_pool.slice(vs.fields);
            for (fields) |fid| {
                const f = ast_unit.pats.StructField.get(fid);
                try declareBindingsInPattern(self, ctx, ast_unit, f.pattern, loc, origin);
            }
        },
        .Slice => {
            const ap = ast_unit.pats.get(.Slice, pid);
            const elems = ast_unit.pats.pat_pool.slice(ap.elems);
            for (elems) |eid| try declareBindingsInPattern(self, ctx, ast_unit, eid, loc, origin);
            if (ap.has_rest and !ap.rest_binding.isNone()) {
                try declareBindingsInPattern(self, ctx, ast_unit, ap.rest_binding.unwrap(), loc, origin);
            }
        },
        .Path, .Literal => {},
        else => {},
    }
}

const PatternShapeCheck = enum { ok, tuple_arity_mismatch, struct_pattern_field_mismatch, pattern_shape_mismatch };

pub fn checkPatternShapeForDecl(
    self: *Checker,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    value_ty: types.TypeId,
) PatternShapeCheck {
    const pkind = self.typeKind(value_ty);
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];

    switch (k) {
        .Wildcard, .Binding => return .ok,

        .Tuple => {
            if (pkind != .Tuple) return .pattern_shape_mismatch;
            const tp = self.context.type_store.get(.Tuple, value_ty);
            const vals = self.context.type_store.type_pool.slice(tp.elems);
            const pt = ast_unit.pats.get(.Tuple, pid);
            const elems = ast_unit.pats.pat_pool.slice(pt.elems);
            if (elems.len != vals.len) return .tuple_arity_mismatch;
            var i: usize = 0;
            while (i < elems.len) : (i += 1) {
                const res = checkPatternShapeForDecl(self, ast_unit, elems[i], vals[i]);
                if (res != .ok) return res;
            }
            return .ok;
        },

        .Struct => {
            if (pkind != .Struct) return .pattern_shape_mismatch;
            const sv = self.context.type_store.get(.Struct, value_ty);
            const vfields = self.context.type_store.field_pool.slice(sv.fields);
            const sp = ast_unit.pats.get(.Struct, pid);
            const pfields = ast_unit.pats.field_pool.slice(sp.fields);

            var i: usize = 0;
            while (i < pfields.len) : (i += 1) {
                const pf = ast_unit.pats.StructField.get(pfields[i]);
                var fty: ?types.TypeId = null;

                var j: usize = 0;
                while (j < vfields.len) : (j += 1) {
                    const vf = self.context.type_store.Field.get(vfields[j]);
                    if (vf.name.toRaw() == pf.name.toRaw()) {
                        fty = vf.ty;
                        break;
                    }
                }
                if (fty == null) return .struct_pattern_field_mismatch;

                const res = checkPatternShapeForDecl(self, ast_unit, pf.pattern, fty.?);
                if (res != .ok) return res;
            }
            return .ok;
        },

        .Slice => {
            // Accept array/slice/dynarray; recurse on element patterns.
            if (pkind != .Array and pkind != .Slice and pkind != .DynArray) return .pattern_shape_mismatch;
            const elem_ty: types.TypeId = switch (pkind) {
                .Array => self.context.type_store.get(.Array, value_ty).elem,
                .Slice => self.context.type_store.get(.Slice, value_ty).elem,
                .DynArray => self.context.type_store.get(.DynArray, value_ty).elem,
                else => self.context.type_store.tAny(),
            };
            const sl = ast_unit.pats.get(.Slice, pid);
            const elems = ast_unit.pats.pat_pool.slice(sl.elems);

            if (pkind == .Array) {
                const arr = self.context.type_store.get(.Array, value_ty);
                // Align with checkPattern: allow rest to capture empty.
                switch (arr.len) {
                    .Concrete => |l| {
                        if (sl.has_rest) {
                            if (elems.len > l) return .pattern_shape_mismatch;
                        } else {
                            if (elems.len != l) return .pattern_shape_mismatch;
                        }
                    },
                    .Unresolved => {},
                }
            }

            for (elems) |eid| {
                const res = checkPatternShapeForDecl(self, ast_unit, eid, elem_ty);
                if (res != .ok) return res;
            }
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const rest_res = checkPatternShapeForDecl(self, ast_unit, sl.rest_binding.unwrap(), self.context.type_store.mkSlice(elem_ty));
                if (rest_res != .ok) return rest_res;
            }
            return .ok;
        },

        .Path, .Literal => return .ok,
        else => return .ok,
    }
}

pub fn checkPatternShapeForAssignExpr(
    self: *Checker,
    ast_unit: *ast.Ast,
    expr: ast.ExprId,
    value_ty: types.TypeId,
) PatternShapeCheck {
    const vk = self.typeKind(value_ty);
    const k = ast_unit.exprs.index.kinds.items[expr.toRaw()];

    switch (k) {
        .Ident => return .ok,

        .TupleLit => {
            if (vk != .Tuple) return .pattern_shape_mismatch;
            const tl = ast_unit.exprs.get(.TupleLit, expr);
            const elems = ast_unit.exprs.expr_pool.slice(tl.elems);
            const trow = self.context.type_store.get(.Tuple, value_ty);
            const tys = self.context.type_store.type_pool.slice(trow.elems);
            if (elems.len != tys.len) return .tuple_arity_mismatch;
            var i: usize = 0;
            while (i < elems.len) : (i += 1) {
                const res = checkPatternShapeForAssignExpr(self, ast_unit, elems[i], tys[i]);
                if (res != .ok) return res;
            }
            return .ok;
        },

        .StructLit => {
            if (vk != .Struct) return .pattern_shape_mismatch;
            const sv = self.context.type_store.get(.Struct, value_ty);
            const vfields = self.context.type_store.field_pool.slice(sv.fields);
            const sl = ast_unit.exprs.get(.StructLit, expr);
            const pfields = ast_unit.exprs.sfv_pool.slice(sl.fields);

            var i: usize = 0;
            while (i < pfields.len) : (i += 1) {
                const pf = ast_unit.exprs.StructFieldValue.get(pfields[i]);
                if (pf.name.isNone()) return .pattern_shape_mismatch;

                var fty: ?types.TypeId = null;
                var j: usize = 0;
                while (j < vfields.len) : (j += 1) {
                    const vf = self.context.type_store.Field.get(vfields[j]);
                    if (vf.name.toRaw() == pf.name.unwrap().toRaw()) {
                        fty = vf.ty;
                        break;
                    }
                }
                if (fty == null) return .struct_pattern_field_mismatch;

                const res = checkPatternShapeForAssignExpr(self, ast_unit, pf.value, fty.?);
                if (res != .ok) return res;
            }
            return .ok;
        },

        .ArrayLit => {
            if (vk != .Array and vk != .Slice and vk != .DynArray) return .pattern_shape_mismatch;
            const elem_ty: types.TypeId = switch (vk) {
                .Array => self.context.type_store.get(.Array, value_ty).elem,
                .Slice => self.context.type_store.get(.Slice, value_ty).elem,
                .DynArray => self.context.type_store.get(.DynArray, value_ty).elem,
                else => self.context.type_store.tAny(),
            };

            const al = ast_unit.exprs.get(.ArrayLit, expr);
            const elems = ast_unit.exprs.expr_pool.slice(al.elems);

            var has_rest = false;
            var rest_index: usize = 0;

            var i: usize = 0;
            while (i < elems.len) : (i += 1) {
                const ek = ast_unit.exprs.index.kinds.items[elems[i].toRaw()];
                if (ek == .Range) {
                    if (has_rest) return .pattern_shape_mismatch; // multiple rest segments
                    has_rest = true;
                    rest_index = i;
                    continue; // validated below
                }
                const res = checkPatternShapeForAssignExpr(self, ast_unit, elems[i], elem_ty);
                if (res != .ok) return res;
            }

            if (vk == .Array) {
                const arr = self.context.type_store.get(.Array, value_ty);
                switch (arr.len) {
                    .Concrete => |l| {
                        if (has_rest) {
                            if (elems.len - 1 > l) return .pattern_shape_mismatch;
                        } else {
                            if (elems.len != l) return .pattern_shape_mismatch;
                        }
                    },
                    .Unresolved => {},
                }
            }

            if (has_rest) {
                // Expect `a .. rest` where end (if any) is an identifier binding the remainder.
                const rr = ast_unit.exprs.get(.Range, elems[rest_index]);
                if (!rr.end.isNone()) {
                    const binder_kind = ast_unit.exprs.index.kinds.items[rr.end.unwrap().toRaw()];
                    if (binder_kind != .Ident) return .pattern_shape_mismatch;
                }
            }
            return .ok;
        },

        else => return .pattern_shape_mismatch,
    }
}

pub fn collectPatternBindings(self: *Checker, ast_unit: *ast.Ast, pid: ast.PatternId, list: *std.ArrayList(ast.StrId)) !void {
    const kind = ast_unit.pats.index.kinds.items[pid.toRaw()];
    switch (kind) {
        .Binding => {
            const nm = ast_unit.pats.get(.Binding, pid).name;
            try list.append(self.gpa, nm);
        },
        .At => {
            const node = ast_unit.pats.get(.At, pid);
            try list.append(self.gpa, node.binder);
            try collectPatternBindings(self, ast_unit, node.pattern, list);
        },
        .Tuple => {
            const row = ast_unit.pats.get(.Tuple, pid);
            const elems = ast_unit.pats.pat_pool.slice(row.elems);
            for (elems) |child| try collectPatternBindings(self, ast_unit, child, list);
        },
        .Slice => {
            const row = ast_unit.pats.get(.Slice, pid);
            const elems = ast_unit.pats.pat_pool.slice(row.elems);
            for (elems) |child| try collectPatternBindings(self, ast_unit, child, list);
            if (!row.rest_binding.isNone())
                try collectPatternBindings(self, ast_unit, row.rest_binding.unwrap(), list);
        },
        .Struct => {
            const row = ast_unit.pats.get(.Struct, pid);
            const fields = ast_unit.pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const pf = ast_unit.pats.StructField.get(fid);
                try collectPatternBindings(self, ast_unit, pf.pattern, list);
            }
        },
        .VariantTuple => {
            const row = ast_unit.pats.get(.VariantTuple, pid);
            const elems = ast_unit.pats.pat_pool.slice(row.elems);
            for (elems) |child| try collectPatternBindings(self, ast_unit, child, list);
        },
        .VariantStruct => {
            const row = ast_unit.pats.get(.VariantStruct, pid);
            const fields = ast_unit.pats.field_pool.slice(row.fields);
            for (fields) |fid| {
                const pf = ast_unit.pats.StructField.get(fid);
                try collectPatternBindings(self, ast_unit, pf.pattern, list);
            }
        },
        .Or => {
            const row = ast_unit.pats.get(.Or, pid);
            const alts = ast_unit.pats.pat_pool.slice(row.alts);
            for (alts) |alt| try collectPatternBindings(self, ast_unit, alt, list);
            std.debug.print("collectPatternBindings Or len={}\n", .{alts.len});
        },
        else => {},
    }
}

pub fn bindingTypeInPattern(
    self: *Checker,
    ast_unit: *ast.Ast,
    pid: ast.PatternId,
    name: ast.StrId,
    value_ty: types.TypeId,
) ?types.TypeId {
    const pk = self.typeKind(value_ty);
    const k = ast_unit.pats.index.kinds.items[pid.toRaw()];

    switch (k) {
        .Binding => {
            const b = ast_unit.pats.get(.Binding, pid);
            if (b.name.eq(name)) return value_ty;

            // Support nested subpattern if present.
            if (@hasField(@TypeOf(b), "pattern")) {
                if (!b.pattern.isNone()) return bindingTypeInPattern(self, b.pattern.unwrap(), name, value_ty);
            }
            return null;
        },
        .Wildcard => return null,

        .At => {
            const at = ast_unit.pats.get(.At, pid);
            if (at.binder.eq(name)) return value_ty;
            return bindingTypeInPattern(self, ast_unit, at.pattern, name, value_ty);
        },

        .Tuple => {
            if (pk != .Tuple) return null;
            // const tp = self.context.type_store.Tuple.get(row(self, value_ty));
            const tp = self.context.type_store.get(.Tuple, value_ty);
            const elems_ty = self.context.type_store.type_pool.slice(tp.elems);
            const pp = ast_unit.pats.get(.Tuple, pid);
            const elems = ast_unit.pats.pat_pool.slice(pp.elems);
            if (elems.len != elems_ty.len) return null;
            var i: usize = 0;
            while (i < elems.len) : (i += 1) {
                if (bindingTypeInPattern(self, ast_unit, elems[i], name, elems_ty[i])) |bt| return bt;
            }
            return null;
        },

        .Struct => {
            if (pk != .Struct) return null;
            const st = self.context.type_store.get(.Struct, value_ty);
            const fields_ty = self.context.type_store.field_pool.slice(st.fields);
            const sp = ast_unit.pats.get(.Struct, pid);
            const fields = ast_unit.pats.field_pool.slice(sp.fields);
            for (fields) |fid| {
                const pf = ast_unit.pats.StructField.get(fid);
                var i: usize = 0;
                while (i < fields_ty.len) : (i += 1) {
                    const tf = self.context.type_store.Field.get(fields_ty[i]);
                    if (tf.name.toRaw() == pf.name.toRaw()) {
                        if (bindingTypeInPattern(self, ast_unit, pf.pattern, name, tf.ty)) |bt| return bt;
                        break;
                    }
                }
            }
            return null;
        },

        .Slice => {
            if (pk != .Array and pk != .Slice and pk != .DynArray) return null;
            const elem_ty: types.TypeId = switch (pk) {
                .Array => self.context.type_store.get(.Array, value_ty).elem,
                .Slice => self.context.type_store.get(.Slice, value_ty).elem,
                .DynArray => self.context.type_store.get(.DynArray, value_ty).elem,
                else => return null,
            };
            const sl = ast_unit.pats.get(.Slice, pid);
            const elems = ast_unit.pats.pat_pool.slice(sl.elems);
            for (elems) |eid| if (bindingTypeInPattern(self, ast_unit, eid, name, elem_ty)) |bt| return bt;
            if (sl.has_rest and !sl.rest_binding.isNone()) {
                const rest_ty = self.context.type_store.mkSlice(elem_ty);
                if (bindingTypeInPattern(self, ast_unit, sl.rest_binding.unwrap(), name, rest_ty)) |bt| return bt;
            }
            return null;
        },

        .VariantTuple => {
            if (!(pk == .Variant or pk == .Error)) return null;
            const vt = ast_unit.pats.get(.VariantTuple, pid);
            const segs = ast_unit.pats.seg_pool.slice(vt.path);
            if (segs.len == 0) return null;
            const last = ast_unit.pats.PathSeg.get(segs[segs.len - 1]);
            const pay = findCasePayload(self, value_ty, last.name) orelse return null;
            const elems = ast_unit.pats.pat_pool.slice(vt.elems);
            const pk2 = self.typeKind(pay);
            if (pk2 == .Void) return null;
            if (pk2 == .Tuple) {
                const tr = self.context.type_store.get(.Tuple, pay);
                const tys = self.context.type_store.type_pool.slice(tr.elems);
                if (tys.len != elems.len) return null;
                for (elems, 0..) |eid, i| if (bindingTypeInPattern(self, ast_unit, eid, name, tys[i])) |bt| return bt;
                return null;
            } else {
                if (elems.len != 1) return null;
                return bindingTypeInPattern(self, ast_unit, elems[0], name, pay);
            }
        },
        .VariantStruct => {
            if (!(pk == .Variant or pk == .Error)) {
                if (pk == .Struct) {
                    const st = self.context.type_store.get(.Struct, value_ty);
                    const fields_ty = self.context.type_store.field_pool.slice(st.fields);
                    const sp = ast_unit.pats.get(.VariantStruct, pid);
                    const fields = ast_unit.pats.field_pool.slice(sp.fields);
                    for (fields) |fid| {
                        const pf = ast_unit.pats.StructField.get(fid);
                        var i: usize = 0;
                        while (i < fields_ty.len) : (i += 1) {
                            const tf = self.context.type_store.Field.get(fields_ty[i]);
                            if (tf.name.toRaw() == pf.name.toRaw()) {
                                if (bindingTypeInPattern(self, ast_unit, pf.pattern, name, tf.ty)) |bt| return bt;
                                break;
                            }
                        }
                    }
                }
                return null;
            }
            const vs = ast_unit.pats.get(.VariantStruct, pid);
            const segs = ast_unit.pats.seg_pool.slice(vs.path);
            if (segs.len == 0) return null;
            const last = ast_unit.pats.PathSeg.get(segs[segs.len - 1]);
            const pay = findCasePayload(self, value_ty, last.name) orelse return null;
            if (self.typeKind(pay) != .Struct) return null;
            const st = self.context.type_store.get(.Struct, pay);
            const tfields = self.context.type_store.field_pool.slice(st.fields);
            const pfields = ast_unit.pats.field_pool.slice(vs.fields);
            for (pfields) |pfid| {
                const pf = ast_unit.pats.StructField.get(pfid);
                for (tfields) |tfid| {
                    const tf = self.context.type_store.Field.get(tfid);
                    if (tf.name.toRaw() == pf.name.toRaw()) {
                        if (bindingTypeInPattern(self, ast_unit, pf.pattern, name, tf.ty)) |bt| return bt;
                        break;
                    }
                }
            }
            return null;
        },
        .Path, .Literal => return null,
        else => return null,
    }
}
